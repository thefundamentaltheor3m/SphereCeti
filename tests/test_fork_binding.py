# SPDX-License-Identifier: Apache-2.0
"""Fork PRs: bind a trusted run through the event-attested PR binding, not GitHub's association.

GitHub reports a fork PR's pull_request_target run with an empty `pull_requests` list (SphereCeti
#54, run 45224210603). The trusted workflow therefore attests the event's PR number and base in the
trusted-build description; the head is the status's own commit.
"""
from copy import deepcopy
from pathlib import Path
import re
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools/project'))
from sphereceti.merge_checks import TOOLING_ATTESTATION, assess_checks
from test_merge_observation import evidence
from test_review_records import REPO

FORK = 'arajasek/SphereCeti'
LACKS = 'trusted run lacks the exact PR head/base association'
OTHER = 'trusted-build attests another PR or base'
DISAGREES = 'trusted run PR association disagrees with the attested PR binding'
REPOSITORY = 'trusted run head repository differs from the PR head repository'


class ForkBindingTest(unittest.TestCase):
    def setUp(self):
        self.context, _, _, self.pr, self.settings, self.statuses, self.run, self.jobs = evidence()

    def describe(self, pr=1, base=None, result='success'):
        return (f"Approved tooling build: {result}; tooling {self.context['tooling']}; "
                f"pr {pr}; base {base or self.context['base']}")

    def reasons(self, *, description=None, association=True, run_repo=REPO, pr_repo=REPO, context=None):
        statuses, run = deepcopy(self.statuses), deepcopy(self.run)
        if description is not None:
            statuses[0]['description'] = description
        if not association:
            run['pull_requests'] = []
        run['head_repository'] = {'full_name': run_repo}
        bound = {**self.context, 'head_repository': pr_repo, **(context or {})}
        return assess_checks(statuses, run, self.jobs, bound, self.settings)['reasons']

    def test_fork_pr_with_empty_association_is_bound_by_the_attestation(self):
        self.assertEqual(self.reasons(description=self.describe(), association=False,
                                      run_repo=FORK, pr_repo=FORK), [])
        # Without the attested binding, the same fork run cannot be bound at all.
        self.assertIn(LACKS, self.reasons(association=False, run_repo=FORK, pr_repo=FORK))

    def test_mismatched_pr_base_head_or_repository_is_refused(self):
        cases = {
            'another PR number': (dict(description=self.describe(pr=2), association=False), OTHER),
            'another base': (dict(description=self.describe(base='4'*40), association=False), OTHER),
            'run from another repository': (dict(description=self.describe(), association=False,
                                                 run_repo='mallory/SphereCeti', pr_repo=FORK), REPOSITORY),
            'PR head repository unknown': (dict(description=self.describe(), association=False,
                                                run_repo=FORK, pr_repo=None), REPOSITORY),
        }
        for name, (kwargs, reason) in cases.items():
            with self.subTest(name):
                self.assertIn(reason, self.reasons(**kwargs))
        # Another head: the run names a different head_sha, and the status lives on another commit.
        run = deepcopy(self.run)
        run.update(pull_requests=[], head_repository={'full_name': REPO}, head_sha='9'*40)
        statuses = deepcopy(self.statuses)
        statuses[0]['description'] = self.describe()
        reasons = assess_checks(statuses, run, self.jobs, {**self.context, 'head_repository': REPO},
                                self.settings)['reasons']
        self.assertIn('trusted run has wrong head_sha', reasons)
        other_commit = deepcopy(self.statuses)
        for status in other_commit:
            status['url'] = status['url'].rsplit('/', 1)[0] + '/' + '9'*40
        reasons = assess_checks(other_commit, self.run | {'head_repository': {'full_name': REPO}}, self.jobs,
                                {**self.context, 'head_repository': REPO}, self.settings)['reasons']
        self.assertIn('trusted-build has a wrong head/location', reasons)

    def test_same_repository_pr_passes_with_the_old_or_new_description(self):
        self.assertEqual(self.reasons(), [])                                  # old format + association
        self.assertEqual(self.reasons(description=self.describe()), [])       # new format + association
        # The association, when GitHub reports one, must agree with the attestation.
        self.assertIn(DISAGREES, self.reasons_with_association_base('4'*40))

    def reasons_with_association_base(self, base):
        run = deepcopy(self.run)
        run['pull_requests'][0]['base'] = {'sha': base}
        run['head_repository'] = {'full_name': REPO}
        statuses = deepcopy(self.statuses)
        statuses[0]['description'] = self.describe()
        return assess_checks(statuses, run, self.jobs, {**self.context, 'head_repository': REPO},
                             self.settings)['reasons']

    def test_a_status_attesting_another_pr_on_the_same_commit_is_refused(self):
        # One fork branch opened as PR 1 and PR 2: the newest trusted-build on the commit is PR 2's.
        self.assertIn(OTHER, self.reasons(description=self.describe(pr=2), association=False,
                                          run_repo=FORK, pr_repo=FORK))
        self.assertIn(OTHER, self.reasons(description=self.describe(pr=2)))

    def test_merge_still_requires_current_tooling_and_the_workflow_fits_github_limits(self):
        current = self.context['tooling']
        older = self.describe().replace(f'tooling {current}', 'tooling ' + 'e'*40)
        reasons = self.reasons(description=older, association=False, run_repo=FORK, pr_repo=FORK)
        self.assertIn('trusted-build ran with tooling other than approved main; refresh the trusted run', reasons)
        workflow = (Path(__file__).resolve().parents[1] / '.github/workflows/pr-build.yml').read_text()
        self.assertIn('PR_NUMBER: ${{ github.event.pull_request.number || inputs.pr }}', workflow)
        self.assertIn('BASE_SHA: ${{ github.event.pull_request.base.sha || needs.candidate.outputs.base }}', workflow)
        self.assertIn('build_description="Approved tooling $kind: $BUILD_RESULT; tooling $TOOLING_SHA; '
                      'pr $PR_NUMBER; base $BASE_SHA"', workflow)
        longest = f"Approved tooling build: cancelled; tooling {'a'*40}; pr 99999; base {'b'*40}"
        self.assertLessEqual(len(longest), 140)  # GitHub's commit-status description limit
        self.assertTrue(TOOLING_ATTESTATION.fullmatch(longest))
        self.assertIsNone(re.search(r'\$\{\{ *github\.event\.pull_request\.(title|body|head\.ref)', workflow))


class ForkReviewReadinessTest(unittest.TestCase):
    def test_fork_pr_is_review_ready_through_the_shared_assessor(self):
        from unittest.mock import patch
        from test_worker import FakeAPI, PROJECT
        from test_worker_checks import POLICY, evidence as scope_evidence
        from sphereceti.worker_cli import review_ci_summary
        for attested, expected in ((True, 'passed'), (False, 'failed')):
            raw, responses = scope_evidence()
            raw = {**raw, 'headRepository': {'nameWithOwner': FORK}}
            responses[2].update(pull_requests=[], head_repository={'full_name': FORK})
            if attested:
                responses[0][0]['description'] += f"; pr 1; base {'b'*40}"
            with self.subTest(attested=attested), patch('sphereceti.config.resource_text', return_value=POLICY):
                self.assertEqual(review_ci_summary(raw, PROJECT, FakeAPI(responses)), expected)


if __name__ == '__main__':
    unittest.main()
