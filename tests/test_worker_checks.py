# SPDX-License-Identifier: Apache-2.0
"""Advisory scope exceptions never authenticate from a check's display name."""
from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.worker import WorkerError
from sphereceti.merge_checks import assess_checks, parse_checks
from sphereceti.worker_checks import HUMAN_SCOPE, NEEDS_REFRESH, PREDATES_MAIN
from sphereceti.worker_cli import ci_summary, review_ci_summary, review_readiness, survey
from test_worker import FakeAPI, PROJECT, gh_pr


POLICY = 'schema_version=1\nworkflow_id=71\nstatus_creator_ids=[42]\n'


def evidence():
    repository = PROJECT.repository
    url = f'https://github.com/{repository}/actions/runs/100/attempts/1'
    checks = [{'__typename': 'CheckRun', 'status': 'COMPLETED', 'conclusion': 'SUCCESS'},
              {'__typename': 'StatusContext', 'context': 'trusted-scope', 'state': 'FAILURE',
               'targetUrl': url}]
    statuses = [{'id': i, 'context': name, 'state': 'success' if name == 'trusted-build' else 'failure',
                 'description': (f"Approved tooling build: success; tooling {'b'*40}"
                                 if name == 'trusted-build' else HUMAN_SCOPE),
                 'creator': {'id': 42, 'type': 'Bot'},
                 'url': f'https://api.github.com/repos/{repository}/statuses/{"a"*40}',
                 'target_url': url, 'created_at': '2026-09-12T10:01:00Z'}
                for i, name in enumerate(('trusted-build', 'trusted-scope'), 1)]
    main = {'sha': 'b'*40}  # the PR base: the trusted run used current approved main's tooling
    # As GitHub reports it: a pull_request_target run's head_sha is the PR head.
    run = {'id': 100, 'run_attempt': 1, 'workflow_id': 71, 'path': '.github/workflows/pr-build.yml',
           'event': 'pull_request_target', 'status': 'completed', 'conclusion': 'success',
           'head_sha': 'a'*40, 'head_branch': 'feature', 'repository': {'full_name': repository},
           'head_repository': {'full_name': repository},
           'pull_requests': [{'number': 1, 'head': {'sha': 'a'*40}, 'base': {'sha': 'b'*40}}]}
    jobs = {'total_count': 2, 'jobs': [
        {'id': i, 'name': name, 'run_id': 100, 'run_attempt': 1, 'status': 'completed',
         'conclusion': 'success', 'started_at': '2026-09-12T10:00:00Z',
         'completed_at': '2026-09-12T10:02:00Z'} for i, name in enumerate(('candidate', 'status'), 1)]}
    return gh_pr(statusCheckRollup=checks), [statuses, main, run, jobs]


class WorkerCheckTests(unittest.TestCase):
    def readiness(self, raw=None, responses=None):
        default_raw, default_responses = evidence()
        api = FakeAPI(default_responses if responses is None else responses)
        with patch('sphereceti.config.resource_text', return_value=POLICY):
            result = review_ci_summary(default_raw if raw is None else raw, PROJECT, api)
        return result, api

    def test_exact_human_scope_exception_preserves_original_ci(self):
        raw, responses = evidence()
        self.assertEqual(ci_summary(raw['statusCheckRollup']), 'failed')
        value, api = self.readiness(raw, responses)
        self.assertEqual(value, 'passed')
        self.assertEqual(len(api.calls), 4)
        self.assertTrue(all(c[:5] == ['api', '--hostname', 'github.com', '--method', 'GET'] for c in api.calls))
        self.assertTrue(all(c[-1].startswith('repos/' + PROJECT.repository + '/') for c in api.calls))
        self.assertEqual(responses[0][1]['state'], 'failure')

    def test_survey_v2_reports_both_readiness_and_aggregate(self):
        raw, responses = evidence()
        api = FakeAPI([{'login': 'alice'}, raw, *responses])
        with patch('sphereceti.config.resource_text', return_value=POLICY):
            result = survey(PROJECT, (1,), api=api)
        self.assertEqual(result['schema'], 'sphereceti.worker-survey/v4')
        self.assertIsNone(result['pull_requests'][0]['review_note'])
        self.assertEqual(result['pull_requests'][0]['ci'], 'failed')
        self.assertEqual(result['pull_requests'][0]['review_ci'], 'passed')

    def test_unconfigured_producer_policy_has_no_exception_or_extra_reads(self):
        raw, _ = evidence()
        api = FakeAPI([])
        unconfigured = 'schema_version=1\nworkflow_id=0\nstatus_creator_ids=[]\n'
        with patch('sphereceti.config.resource_text', return_value=unconfigured):
            self.assertEqual(review_ci_summary(raw, PROJECT, api), 'failed')
        self.assertEqual(api.calls, [])

    def test_real_failures_pending_unknown_and_capped_rollups_stop_exception(self):
        raw, _ = evidence()
        passed, scope = raw['statusCheckRollup']
        inventories = [[dict(passed, conclusion='FAILURE'), scope],
                       [dict(passed, status='IN_PROGRESS'), scope],
                       [dict(passed, conclusion='SKIPPED'), scope],
                       [dict(passed, conclusion='NEUTRAL'), scope],
                       [passed]*99 + [scope], [scope], [passed, scope, deepcopy(scope)],
                       [passed, dict(passed, name='trusted-scope', conclusion='FAILURE')]]
        for checks in inventories:
            with self.subTest(checks=checks):
                value, api = self.readiness(gh_pr(statusCheckRollup=checks), [])
                self.assertNotEqual(value, 'passed')
                self.assertEqual(api.calls, [])

    def test_main_only_skipped_jobs_do_not_block_the_exception(self):
        """Regression: every PR here carries the docs-cache jobs deploy-pages and publish-cache,
        which run only for pushes to main and are SKIPPED on pull requests (SphereCeti #36,
        2026-11-23). Only those exact workflow/job pairs are ignored."""
        def skip(name, workflow='Documentation and cache', conclusion='SKIPPED'):
            return {'__typename': 'CheckRun', 'name': name, 'workflowName': workflow,
                    'status': 'COMPLETED', 'conclusion': conclusion}
        raw, responses = evidence()
        passed, scope = raw['statusCheckRollup']
        real = [passed]*21 + [skip('deploy-pages')]*3 + [skip('publish-cache')]*3 + [scope]
        self.assertEqual(self.readiness(gh_pr(statusCheckRollup=real), responses)[0], 'passed')
        for label, extra in (('other workflow', skip('deploy-pages', workflow='CI')),
                             ('other skipped job', skip('build')),
                             ('neutral main-only job', skip('deploy-pages', conclusion='NEUTRAL')),
                             ('failed main-only job', skip('publish-cache', conclusion='FAILURE')),
                             ('unnamed skipped run', {'__typename': 'CheckRun', 'status': 'COMPLETED',
                                                      'conclusion': 'SKIPPED'})):
            with self.subTest(blocked=label):
                value, api = self.readiness(gh_pr(statusCheckRollup=[passed, extra, scope]), [])
                self.assertNotEqual(value, 'passed')
                self.assertEqual(api.calls, [])
        only_skips = [skip('deploy-pages'), skip('publish-cache'), scope]
        self.assertNotEqual(self.readiness(gh_pr(statusCheckRollup=only_skips), [])[0], 'passed')

    def test_same_named_foreign_stale_or_wrong_scope_status_stays_failed(self):
        for change in ({'creator': {'id': 9, 'type': 'Bot'}},
                       {'creator': {'id': 42, 'type': 'User'}}, {'state': 'pending'},
                       {'description': 'Scope: mathematical; no merge authorization'},
                       {'created_at': '2026-09-11T10:01:00Z'}, {'url': 'https://attacker.invalid'},
                       {'target_url': 'https://github.com/other/repo/actions/runs/100/attempts/1'}):
            raw, responses = evidence()
            responses[0][1].update(change)
            with self.subTest(change=change):
                self.assertEqual(self.readiness(raw, responses)[0], 'failed')
        raw, responses = evidence()
        raw['statusCheckRollup'][1]['targetUrl'] += '0'
        self.assertEqual(self.readiness(raw, responses)[0], 'failed')

    def test_github_pull_request_target_run_shape_from_pr_36(self):
        """Regression: SphereCeti PR #36's trusted run 45084681934, as GitHub reported it (2026-11-22).

        GitHub gives a pull_request_target run's head_sha as the PR head (c2c0bf1), and records the
        tooling only as the associated PR's base.sha (d5290bd, approved main at the run's start)."""
        import json
        head, base = 'c2c0bf114ec96efa5921a8072cf05f7fe14a94a5', 'd5290bd870256d25fb3cbee09aa3f456652b111a'
        raw, responses = evidence()
        raw, responses = json.loads(json.dumps([raw, responses]).replace('a'*40, head).replace('b'*40, base))
        self.assertEqual(responses[2]['head_sha'], head)
        self.assertEqual(responses[2]['pull_requests'][0]['base']['sha'], responses[1]['sha'])
        self.assertEqual(self.readiness(raw, responses)[0], 'passed')
        # The same real evidence is still rejected with a wrong head, base, workflow or attempt.
        wrong = 'f'*40
        for label, mutate in (
                ('run head_sha', lambda r: r[2].update(head_sha=wrong)),
                ('association head', lambda r: r[2]['pull_requests'][0]['head'].update(sha=wrong)),
                ('association base', lambda r: r[2]['pull_requests'][0]['base'].update(sha=wrong)),
                ('approved main moved', lambda r: r[1].update(sha=wrong)),
                ('workflow id', lambda r: r[2].update(workflow_id=72)),
                ('workflow path', lambda r: r[2].update(path='.github/workflows/ci.yml')),
                ('event', lambda r: r[2].update(event='pull_request')),
                ('run attempt', lambda r: r[2].update(run_attempt=2))):
            changed = json.loads(json.dumps(responses))
            mutate(changed)
            if label == 'approved main moved':  # to a commit that does not contain the run's tooling
                changed.append({'status': 'diverged', 'merge_base_commit': {'sha': 'e'*40}})
            with self.subTest(wrong=label):
                self.assertEqual(self.readiness(raw, changed)[0], 'failed')

    def test_old_run_whose_association_shows_the_new_base_is_rejected(self):
        """Regression: GitHub reports a run's PR association with the PR's CURRENT base (all of #36's
        trusted runs since 2026-11-21 reported base 495ebff on 2026-11-23). An old successful run with
        an unchanged head therefore looks current through the association; only the published tooling
        attestation tells it apart."""
        raw, responses = evidence()
        self.assertEqual(self.readiness(raw, responses)[0], 'passed')
        old_tooling = 'e'*40
        stale = json.loads(json.dumps(responses))
        stale[0][0]['description'] = f'Approved tooling build: success; tooling {old_tooling}'
        self.assertEqual(stale[2]['pull_requests'][0]['base']['sha'], stale[1]['sha'])
        stale.append(WorkerError('GitHub survey failed'))  # compare: a SHA unknown to the repository
        self.assertEqual(self.readiness(raw, stale)[0], 'failed')
        for description in ('Approved tooling build: success', '', 'Approved tooling build: success; tooling ',
                            f"Approved tooling build: success; tooling {'b'*39}"):
            absent = json.loads(json.dumps(responses))
            absent[0][0]['description'] = description
            with self.subTest(description=description):
                self.assertEqual(self.readiness(raw, absent)[0], 'failed')

    def test_run_reporting_the_tooling_as_head_sha_is_rejected(self):
        # The earlier assumption: head_sha equal to approved main. GitHub never reports that for a
        # pull_request_target run, so such a run cannot be the trusted run for this PR head.
        raw, responses = evidence()
        responses[2]['head_sha'] = responses[1]['sha']
        self.assertEqual(self.readiness(raw, responses)[0], 'failed')

    def test_older_approved_main_tooling_is_review_ready_but_merge_stays_strict(self):
        # main has advanced past the PR's base and the run's attested tooling (both b...).
        main = 'e'*40
        for status, base, expected in (('ahead', 'b'*40, 'passed'),        # an approved ancestor
                                       ('identical', 'b'*40, 'passed'),
                                       ('diverged', 'b'*40, 'failed'),     # not an ancestor of main
                                       ('ahead', 'f'*40, 'failed')):       # merge base is another commit
            raw, responses = evidence()
            responses[1] = {'sha': main}
            responses.append({'status': status, 'merge_base_commit': {'sha': base}})
            with self.subTest(status=status, base=base):
                self.assertEqual(self.readiness(raw, responses)[0], expected)
        raw, responses = evidence()
        responses[1] = {'sha': main}
        responses.append({'status': 'ahead', 'merge_base_commit': {'sha': 'b'*40}})
        api = FakeAPI(responses)
        with patch('sphereceti.config.resource_text', return_value=POLICY):
            self.assertEqual(review_readiness(raw, PROJECT, api), ('passed', PREDATES_MAIN))
        # One compare serves both the tooling and the base, which are the same older main commit.
        self.assertEqual(sum('/compare/' in c[-1] for c in api.calls), 1)
        self.assertEqual(api.calls[-1][-1], f'repos/{PROJECT.repository}/compare/{"b"*40}...{main}')
        # The merge side keeps exact current evidence: the same run is refused for merging.
        statuses, _, run, jobs = evidence()[1]
        context = {'repository': PROJECT.repository, 'pr': 1, 'head': 'a'*40, 'base': 'b'*40, 'tooling': main}
        reasons = assess_checks(statuses, run, jobs['jobs'], context, parse_checks(POLICY))['reasons']
        self.assertIn('trusted-build ran with tooling other than approved main; refresh the trusted run', reasons)
        self.assertIn('PR base is not approved main; update the PR and refresh the trusted run', reasons)

    def test_unattested_build_awaits_a_refresh_and_stays_not_ready(self):
        raw, responses = evidence()
        responses[0][0]['description'] = 'Approved tooling build: success'
        api = FakeAPI(responses)
        with patch('sphereceti.config.resource_text', return_value=POLICY):
            self.assertEqual(review_readiness(raw, PROJECT, api), ('failed', NEEDS_REFRESH))

    def test_exact_workflow_attempt_head_base_and_jobs_are_required(self):
        for change in ({'path': '.github/workflows/other.yml'}, {'workflow_id': 72},
                       {'event': 'pull_request'}, {'head_sha': 'd'*40}, {'run_attempt': 2},
                       {'repository': {'full_name': 'other/repo'}}, {'pull_requests': []},
                       {'conclusion': 'failure'}, {'status': 'in_progress'}):
            raw, responses = evidence()
            responses[2].update(change)
            with self.subTest(change=change):
                self.assertEqual(self.readiness(raw, responses)[0], 'failed')
        for part in ('head', 'base'):
            raw, responses = evidence()
            responses[2]['pull_requests'][0][part]['sha'] = 'e'*40
            self.assertEqual(self.readiness(raw, responses)[0], 'failed')
        raw, responses = evidence()
        responses[3]['jobs'][0]['conclusion'] = 'failure'
        self.assertEqual(self.readiness(raw, responses)[0], 'failed')

    def test_newer_failed_or_incomplete_status_is_not_hidden_by_rollup(self):
        for context in ('trusted-build', 'ordinary-ci'):
            for state in ('failure', 'pending', 'error', None):
                raw, responses = evidence()
                responses[0].append(dict(responses[0][0], id=3, context=context, state=state))
                with self.subTest(context=context, state=state):
                    self.assertEqual(self.readiness(raw, responses)[0], 'failed')

    def test_incomplete_or_duplicate_status_and_job_inventories_abort(self):
        for inventory in (None, {}, [None]):
            raw, responses = evidence()
            responses[0] = inventory
            with self.subTest(inventory=inventory), self.assertRaises(WorkerError):
                self.readiness(raw, responses)
        for kind in ('status-cap', 'status-duplicate', 'job-cap', 'job-missing', 'job-duplicate'):
            raw, responses = evidence()
            if kind == 'status-cap':
                responses[0] = [dict(responses[0][0], id=i+1) for i in range(100)]
            elif kind == 'status-duplicate':
                responses[0].append(deepcopy(responses[0][0]))
            elif kind == 'job-cap':
                responses[3] = {'total_count': 100, 'jobs': responses[3]['jobs']*50}
            elif kind == 'job-missing':
                responses[3]['total_count'] = 3
            else:
                responses[3]['jobs'][1]['id'] = responses[3]['jobs'][0]['id']
            with self.subTest(kind=kind), self.assertRaises(WorkerError):
                self.readiness(raw, responses)

    def test_invalid_revisions_cannot_become_api_paths(self):
        for change in ({'headRefOid': 'main/statuses'}, {'baseRefOid': 'main'}, {'number': True}):
            raw, _ = evidence()
            raw.update(change)
            api = FakeAPI([])
            with patch('sphereceti.config.resource_text', return_value=POLICY), self.assertRaises(WorkerError):
                review_ci_summary(raw, PROJECT, api)
            self.assertEqual(api.calls, [])

    def test_malformed_nested_provenance_is_an_incomplete_observation(self):
        raw, responses = evidence()
        responses[2]['repository'] = 'unknown'
        with self.assertRaises(WorkerError):
            self.readiness(raw, responses)


if __name__ == '__main__':
    unittest.main()
