# SPDX-License-Identifier: Apache-2.0
"""`sphereceti reviews`: the "Ready to merge" section and held fork runs, offline and read-only."""
from datetime import timedelta
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences, parse_policy
from sphereceti.ready_to_merge import HELD, HELD_STEP
from sphereceti.review_queue import queue, render
from sphereceti.review_records import RecordError
from sphereceti.review_select import select
from review_fixture import automation_policy
from sphereceti.local_review import RUBRICS
from sphereceti.review_records import make_record
from test_review_queue import BASE, HEAD, OLD, REPO, PROJECT, SurveyAPI, comment, pr

DIGESTS = ('dependency_digest', 'engine_digest', 'effective_rubrics_digest', 'installed_tooling_digest',
           'policy_digest', 'review_context_digest', 'description_digest')

CAROL, BOB = 2009342, 11
POLICY = parse_policy(automation_policy(authorized_reviewers=[f'user:{CAROL}', 'user:7', f'user:{BOB}']))
ARAJASEK = 'arajasek/SphereCeti'
# Main's ruleset requires GitHub Actions' `build` check (integration 15368), as on SphereCeti today.
RULES = [{'type': 'pull_request', 'parameters': {'required_approving_review_count': 1}},
         {'type': 'required_status_checks', 'parameters': {'required_status_checks': [
             {'context': 'build', 'integration_id': 15368}]}}]
GREEN = [{'__typename': 'CheckRun', 'status': 'COMPLETED', 'conclusion': 'SUCCESS'}]


def accepted(cid, number, head=HEAD, verdicts=None, login='carol', user_id=CAROL, advisory=False):
    """An official record: installed tooling matched approved main, so it is not advisory."""
    result = {'repository': REPO, 'pr': number, 'head': head, 'base': BASE, 'diff_base': BASE,
              'tooling': 'd' * 40, 'completion': 'complete', 'execution_mode': 'commit',
              'tooling_approved': True, 'installed_tooling_matches_T': not advisory, 'missing_context': [],
              'config_differences': [], 'verdicts': {r: 'approve' for r in RUBRICS} | (verdicts or {}),
              'reviews': {}, **{k: 'e' * 64 for k in DIGESTS}}
    c = comment(cid, number, make_record(result)[1], login, user_id=user_id)
    c['html_url'] = f'https://github.com/{REPO}/pull/{number}#issuecomment-{cid}'
    return c


def build(conclusion='success', status='completed', rid=500):
    return {'id': rid, 'name': 'build', 'head_sha': HEAD, 'status': status, 'conclusion': conclusion,
            'app': {'id': 15368}}


def run(name, conclusion, rid, workflow_id=None, status='completed'):
    return {'id': rid, 'name': name, 'workflow_id': workflow_id or rid, 'head_sha': HEAD, 'status': status,
            'conclusion': conclusion, 'run_attempt': 1}


class Hub:
    """Fixed read-only GitHub endpoints; any payload or unknown endpoint fails the test."""

    def __init__(self, comments=None):
        self.records, self.calls = comments or {}, []
        self.pulls, self.checks, self.runs, self.reviews, self.statuses = {}, {}, {}, {}, {}

    def comments(self, repository, number):
        self.calls.append(f'comments {number}')
        return self.records.get(number, [])

    def call(self, endpoint, *, payload=None, paginate=False, method=None):
        assert payload is None and method is None, 'the listing never writes'
        self.calls.append(endpoint)
        prefix = f'repos/{REPO}/'
        assert endpoint.startswith(prefix), endpoint
        path = endpoint[len(prefix):]
        if path == 'rules/branches/main':
            return RULES
        if path.startswith('pulls?state=closed'):
            return [[]]  # no merged parent for a stacked base branch
        if path.startswith('actions/runs?head_sha='):
            number = self.by_head(path.split('=')[1].split('&')[0])
            return [{'total_count': len(self.runs.get(number, [])), 'workflow_runs': self.runs.get(number, [])}]
        if path.startswith('commits/') and '/check-runs' in path:
            number = self.by_head(path.split('/')[1])
            return [{'total_count': 1, 'check_runs': self.checks.get(number, [build()])}]
        if path.startswith('commits/') and '/statuses' in path:
            return self.statuses.get(self.by_head(path.split('/')[1]), [])
        if path.startswith('pulls/') and path.endswith('/reviews?per_page=100'):
            assert paginate
            return [self.reviews.get(int(path.split('/')[1]), [])]
        if path.startswith('pulls/') and path.count('/') == 1:
            number = int(path.split('/')[1])
            return {'number': number, 'user': {'id': BOB}, 'head': {'sha': HEAD},
                    'mergeable_state': self.pulls.get(number, 'blocked')}
        raise RecordError(f'unexpected read {endpoint}')

    def by_head(self, head):
        assert head == HEAD, head
        return self.current


class ReadyToMergeTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-ready-')
        self.addCleanup(temp.cleanup)
        self.prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=temp.name)

    def listing(self, prs, hub):
        report = queue(PROJECT, POLICY, self.prefs, api=SurveyAPI(prs), client=hub)
        self.assertFalse([c for c in hub.calls if 'merge' in c.split('?')[0].rsplit('/', 1)[-1]])
        return report

    def one(self, hub, number=1, **updates):
        hub.current = number
        return self.listing([pr(number, 'bob', **updates)], hub)['ready_to_merge']

    def test_ready_without_an_approval_on_the_head_is_approve_and_merge(self):
        hub = Hub({1: [accepted(30, 1)]})
        section = self.one(hub)
        [item] = section['items']
        self.assertEqual(item['next_step'], 'approve + merge')
        self.assertEqual(item['record'], f'https://github.com/{REPO}/pull/1#issuecomment-30')
        self.assertEqual(item['record_publisher'], f'user:{CAROL}')
        self.assertEqual(item['required_checks'], {'build': 'passed'})
        self.assertEqual(section['not_ready'], [])
        self.assertEqual(section['required_checks'], ['build'])

    def test_json_shape_and_rendering_first(self):
        hub = Hub({1: [accepted(30, 1)]})
        hub.current = 1
        report = self.listing([pr(1, 'bob', title='Prove the thing')], hub)
        [item] = report['ready_to_merge']['items']
        self.assertEqual(set(report['ready_to_merge']), {'items', 'not_ready', 'required_checks'})
        self.assertEqual(set(item), {'pr', 'author', 'title', 'head', 'record', 'record_publisher', 'next_step',
                                     'approval', 'held_workflows', 'required_checks', 'review_ci', 'note',
                                     'mergeable_state', 'yours'})
        self.assertEqual(set(item['approval']), {'on_head', 'older_heads', 'changes_requested'})
        lines = render(report).split('\n')
        self.assertEqual(lines[1], 'Ready to merge (1):')
        self.assertEqual(lines[2], f'  #1 bob "Prove the thing" aaaaaaa: approve + merge; no approval on this '
                                   f'head; record https://github.com/{REPO}/pull/1#issuecomment-30')
        self.assertTrue(lines[3].startswith('Revised since your review'))

    def test_an_approval_on_the_current_head_means_merge_and_one_on_an_older_head_does_not(self):
        hub = Hub({1: [accepted(30, 1)]})
        hub.pulls[1] = 'unstable'  # the expected trusted-scope failure is not a required check
        hub.reviews[1] = [{'id': 1, 'user': {'id': 21, 'login': 'dave'}, 'state': 'APPROVED', 'commit_id': OLD}]
        [item] = self.one(hub)['items']
        self.assertEqual(item['next_step'], 'approve + merge')
        self.assertEqual([a['commit_id'] for a in item['approval']['older_heads']], [OLD])
        self.assertIn('no approval on this head (older-head approval by dave)', render_one(self, hub))
        hub.reviews[1].append({'id': 2, 'user': {'id': 22, 'login': 'erin'}, 'state': 'APPROVED',
                               'commit_id': HEAD})
        [item] = self.one(hub)['items']
        self.assertEqual(item['next_step'], 'merge')
        self.assertEqual([a['login'] for a in item['approval']['on_head']], ['erin'])
        # The author's own approval never counts.
        hub.reviews[1] = [{'id': 3, 'user': {'id': BOB}, 'state': 'APPROVED', 'commit_id': HEAD}]
        [item] = self.one(hub)['items']
        self.assertEqual(item['next_step'], 'approve + merge')

    def test_not_ready_stacked_nine_of_ten_stale_head_cancelled_conflicting(self):
        cases = {
            'stacked': (dict(baseRefName='branch-9'), [accepted(30, 1)],
                        'stacked on branch-9; merge its parent first'),
            'nine': ({}, [accepted(30, 1, verdicts={'naming': 'request_changes'})], None),
            'stale head': ({}, [accepted(30, 1, head=OLD)], None),
            'cancelled': ({}, [accepted(30, 1)], 'CI not done: build was cancelled on this head; re-run it'),
            'conflicting': (dict(mergeable='CONFLICTING'), [accepted(30, 1)], 'conflicting'),
            'by the author': ({}, [accepted(30, 1, login='bob', user_id=BOB)], None),
            'advisory': ({}, [accepted(30, 1, advisory=True)], None),
        }
        for name, (updates, comments, reason) in cases.items():
            with self.subTest(name):
                hub = Hub({1: comments})
                if name == 'cancelled':
                    hub.checks[1] = [build(rid=400), build('cancelled', rid=401)]
                section = self.one(hub, **updates)
                self.assertEqual(section['items'], [])
                self.assertEqual([i['reason'] for i in section['not_ready']], [reason] if reason else [])
                if name == 'stacked':  # no further reads for a PR that cannot be merged anyway
                    self.assertFalse([c for c in hub.calls if c.endswith('/pulls/1') or 'rules' in c])

    def test_a_contest_the_record_has_not_answered_keeps_it_out(self):
        # carol found a naming problem on the old head; the author contested it; carol's 10/10 record
        # on the new head does not answer the contest (its naming watermark predates it).
        contest = comment(31, 1, '/sphereceti contest naming\nThe name follows Mathlib.', 'bob', user_id=BOB)
        contest['author_association'] = 'CONTRIBUTOR'
        hub = Hub({1: [accepted(29, 1, head=OLD, verdicts={'naming': 'request_changes'}), contest,
                       accepted(32, 1)]})
        self.assertEqual(self.one(hub)['items'], [])
        hub = Hub({1: [accepted(29, 1, head=OLD, verdicts={'naming': 'request_changes'}), accepted(32, 1)]})
        self.assertEqual(len(self.one(hub)['items']), 1)

    def test_blocked_by_another_rule_is_not_ready(self):
        hub = Hub({1: [accepted(30, 1)]})
        hub.reviews[1] = [{'id': 2, 'user': {'id': 22, 'login': 'erin'}, 'state': 'APPROVED', 'commit_id': HEAD}]
        hub.pulls[1] = 'blocked'
        section = self.one(hub)
        self.assertEqual(section['items'], [])
        self.assertIn('blocked by another rule', section['not_ready'][0]['reason'])
        hub.reviews[1] = [{'id': 2, 'user': {'id': 22}, 'state': 'CHANGES_REQUESTED', 'commit_id': HEAD}]
        hub.pulls[1] = 'blocked'
        self.assertEqual(self.one(hub)['not_ready'][0]['reason'], 'changes requested by user:22')

    def test_held_fork_runs_wait_on_ci_like_arajasek_153(self):
        # Modeled on #153 at 5c590b4: a fork PR whose pull_request workflows (CI, Documentation and
        # cache, Progress sources) are held for approval, so `build` never appears on the head, while
        # the pull_request_target runs (Area labels, Trusted candidate) completed.
        hub = Hub({1: [accepted(30, 1)]})
        hub.checks[1] = [{'id': 1, 'name': 'label', 'head_sha': HEAD, 'status': 'completed',
                          'conclusion': 'success', 'app': {'id': 15368}}]
        hub.runs[1] = [run('Progress sources', 'action_required', 45461894130, 356490777),
                       run('Documentation and cache', 'action_required', 45461892121, 356512866),
                       run('CI', 'action_required', 45461892003, 342382824),
                       run('Area labels', 'success', 45461891728, 427846757),
                       run('Trusted candidate #153', 'success', 45461891935, 358051984)]
        hub.current = 1
        report = self.listing([pr(1, 'bob', headRepository={'nameWithOwner': ARAJASEK})], hub)
        [item] = report['ready_to_merge']['items']
        self.assertEqual(item['next_step'], HELD_STEP)
        self.assertEqual(item['held_workflows'], ['CI', 'Documentation and cache', 'Progress sources'])
        self.assertEqual(item['required_checks'], {'build': 'missing'})
        self.assertIn(f'aaaaaaa: {HELD_STEP} (CI, Documentation and cache, Progress sources)', render(report))
        # Approved and re-run: the latest run of each workflow decides, so the PR is ready again.
        hub.runs[1] += [run('CI', 'success', 45461899999, 342382824),
                        run('Documentation and cache', 'success', 45461899998, 356512866),
                        run('Progress sources', 'success', 45461899997, 356490777)]
        hub.checks[1].append(build(rid=600))
        [item] = self.one(hub, headRepository={'nameWithOwner': ARAJASEK})['items']
        self.assertEqual(item['next_step'], 'approve + merge')

    def test_awaiting_ci_names_held_fork_runs_wherever_readiness_says_so(self):
        pending = [{'__typename': 'CheckRun', 'status': 'QUEUED', 'conclusion': None}]
        hub = Hub()
        hub.current = 2
        hub.runs[2] = [run('CI', 'action_required', 10, 1), run('Area labels', 'success', 11, 2)]
        fork = pr(2, 'arajasek', statusCheckRollup=pending, headRepository={'nameWithOwner': ARAJASEK})
        same = pr(3, 'bob', statusCheckRollup=pending)
        report = self.listing([fork, same], hub)
        reasons = {i['pr']: i['reason'] for i in report['sections']['not_ready']}
        self.assertEqual(reasons, {2: f'awaits CI: {HELD} (CI)', 3: 'awaits CI (pending)'})
        self.assertIn(f'2 open PRs await CI (1 is {HELD})', report['not_ready_summary'])
        # Same-repository heads are never held, so they cost no runs read.
        self.assertEqual(len([c for c in hub.calls if 'actions/runs' in c]), 1)
        # Bare selection words it the same way.
        hub2 = Hub()
        hub2.current = 2
        hub2.runs[2] = hub.runs[2]
        selection = select(PROJECT, POLICY, self.prefs, api=SurveyAPI([fork]), client=hub2)
        self.assertEqual(selection['skipped'][0]['reason'], f'awaits CI: {HELD} (CI)')

    def test_a_ready_fork_pr_whose_runs_are_held_says_so_in_new_to_you(self):
        # #153 today: its rollup shows only the pull_request_target runs (CI never ran), so review
        # readiness passes and it is new to you; the entry names the held workflows.
        hub = Hub()
        hub.current = 4
        hub.runs[4] = [run('CI', 'action_required', 10, 1), run('Progress sources', 'action_required', 11, 2),
                       run('Area labels', 'success', 12, 3)]
        report = self.listing([pr(4, 'arajasek', headRepository={'nameWithOwner': ARAJASEK})], hub)
        [entry] = report['sections']['new']
        self.assertEqual(entry['held_workflows'], ['CI', 'Progress sources'])
        self.assertEqual(entry['reason'], f'ready; no review by you; CI held, {HELD} (CI, Progress sources)')

    def test_read_failures_raise(self):
        hub = Hub({1: [accepted(30, 1)]})
        hub.current = 1
        hub.checks[1] = None
        with self.assertRaises(RecordError):
            self.listing([pr(1, 'bob')], hub)


def render_one(test, hub):
    return render(queue(PROJECT, POLICY, test.prefs, api=SurveyAPI([pr(1, 'bob')]), client=hub))


if __name__ == '__main__':
    unittest.main()
