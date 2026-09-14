# SPDX-License-Identifier: Apache-2.0
"""Independent adversarial contracts for read-only single-roadmap planning."""
from dataclasses import replace
from datetime import datetime, timezone
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti import cli
from sphereceti.config import parse_project, parse_source_lock, resource_text, ConfigError
from sphereceti.worker import WorkerError, plan, targets
from sphereceti.worker_cli import GitHub, ci_summary, load_json, read_json, survey

NOW = datetime(2026, 9, 12, 12, 0, tzinfo=timezone.utc)
STAMP = NOW.strftime('%Y-%m-%dT%H:%M:%SZ')
# Keep the unapproved-roadmap fixtures explicit after the real roadmap is installed.
PROJECT = replace(parse_project(resource_text('sphereceti.toml')), phase='scaffold', roadmap_approved=False)
APPROVED = replace(PROJECT, phase='roadmap', roadmap_approved=True)


def pr(number=1, author='alice', **updates):
    result = dict(number=number, title=f'Work {number}', author=author, head='a'*40, base='b'*40,
                  updated_at=STAMP, state='OPEN', draft=False, mergeable='MERGEABLE', ci='passed')
    result.update(updates)
    return result


def snapshot(prs=None, **updates):
    result = dict(schema='sphereceti.worker-survey/v1', repository=PROJECT.repository,
                  actor='alice', observed_at=STAMP, scope=None, pull_requests=prs or [])
    result.update(updates)
    return result


def item(key='task', **updates):
    result = dict(id=key, summary='A coherent change', reference='README.md#layer-1',
                  status='remaining', effort='small', depends_on=[], blocked_by=[])
    result.update(updates)
    return result


def frontier(items=None, **updates):
    result = dict(schema='sphereceti.worker-frontier/v1', repository=PROJECT.repository,
                  implementation_repository=PROJECT.implementation_repository,
                  roadmap_revision='c'*40, implementation_revision='d'*40,
                  document=PROJECT.roadmap_document, targets=PROJECT.roadmap_targets,
                  observed_at=STAMP, items=items or [item()])
    result.update(updates)
    return result


def gh_pr(number=1, **updates):
    result = dict(number=number, title='Change', author={'login': 'alice'}, headRefOid='a'*40,
                  baseRefOid='b'*40, updatedAt='2020-01-01T00:00:00Z', state='OPEN', isDraft=False,
                  mergeable='MERGEABLE', statusCheckRollup=[{'__typename': 'CheckRun',
                  'status': 'COMPLETED', 'conclusion': 'SUCCESS'}])
    result.update(updates)
    return result


class FakeAPI:
    def __init__(self, responses):
        self.responses = iter(responses)
        self.calls = []

    def read(self, args):
        self.calls.append(args)
        result = next(self.responses)
        if isinstance(result, Exception):
            raise result
        return result


class PlannerTest(unittest.TestCase):
    def run_plan(self, data=None, project=PROJECT, **kwargs):
        return plan(data or snapshot(), project, now=NOW, **kwargs)

    def test_maintenance_first_and_one_selected_unit(self):
        report = self.run_plan(snapshot([pr(1, 'bob'), pr(2, ci='failed'),
                                        pr(3, mergeable='CONFLICTING')]))
        self.assertEqual([c['stage'] for c in report['candidates']],
                         ['rebase', 'ci-repair', 'review-assessment'])
        self.assertEqual(report['selected']['pr'], 3)
        self.assertFalse(report['executable'])
        self.assertTrue(report['advisory_only'])
        self.assertEqual(report['selected']['head'], 'a'*40)

    def test_maintenance_only_for_operator_case_insensitively(self):
        report = self.run_plan(snapshot([pr(1, 'bob', ci='failed'),
            pr(2, 'bob', mergeable='CONFLICTING'), pr(3, 'ALICE', draft=True, ci='failed')]))
        self.assertEqual([c['pr'] for c in report['candidates']], [3])

    def test_draft_closed_and_unknown_not_review_ready(self):
        for updates in ({'draft': True}, {'ci': 'unknown'}, {'ci': 'pending'}, {'mergeable': 'UNKNOWN'}):
            self.assertIsNone(self.run_plan(snapshot([pr(**updates)]))['selected'])
        for state in ('CLOSED', 'MERGED'):
            self.assertIsNone(self.run_plan(snapshot([pr(state=state)], scope=[1]), requested=(1,))['selected'])

    def test_stable_oldest_pr_ties(self):
        older = '2026-09-12T11:00:00Z'
        report = self.run_plan(snapshot([pr(3), pr(2, updated_at=older), pr(1, updated_at=older)]))
        self.assertEqual([c['pr'] for c in report['candidates']], [1, 2, 3])

    def test_strict_target_excludes_other_prs_and_frontier(self):
        report = self.run_plan(snapshot([pr(1), pr(2, ci='failed')]), APPROVED,
                               requested=(9,), frontier=frontier())
        self.assertIsNone(report['selected'])
        self.assertEqual([p['pr'] for p in report['pull_requests']], [9])
        self.assertIn('targeting', report['roadmap']['reason'])

    def test_targeted_snapshot_cannot_be_widened_or_missing(self):
        data = snapshot([pr(1)], scope=[1])
        for requested in (None, (2,), (1, 2), ()):
            with self.subTest(requested=requested), self.assertRaises(WorkerError):
                self.run_plan(data, requested=requested)
        self.assertEqual(self.run_plan(data, requested=(1,))['selected']['pr'], 1)
        with self.assertRaises(WorkerError):
            self.run_plan(snapshot([], scope=[1]), requested=(1,))

    def test_bad_and_empty_targets_fail_instead_of_becoming_unrestricted(self):
        for values in ([], [''], ['0'], ['-1'], ['1,'], ['1,,2'], ['1 2'], [' 1'], ['1.0'], ['#'],
                       [','.join(str(n) for n in range(1, 27))]):
            with self.subTest(values=values), self.assertRaises(WorkerError):
                targets(values)
        self.assertEqual(targets(['#3,2', '3']), (2, 3))
        self.assertIsNone(targets(None))

    def test_unknown_queue_is_not_empty(self):
        for data in (None, {}, snapshot(pull_requests=None), snapshot(pull_requests={})):
            with self.assertRaises(WorkerError):
                plan(data, PROJECT, now=NOW)
        self.assertIsNone(self.run_plan(snapshot())['selected'])

    def test_stale_future_and_invalid_times_fail(self):
        for time in ('2026-09-12T11:44:59Z', '2026-09-12T12:00:01Z', '2026-02-30T12:00:00Z',
                     '2026-09-12T12:00:00+00:00'):
            with self.subTest(time=time), self.assertRaises(WorkerError):
                self.run_plan(snapshot(observed_at=time))
        self.run_plan(snapshot(observed_at='2026-09-12T11:45:00Z'))

    def test_malformed_destination_identity_revisions_and_duplicate_prs_fail(self):
        variants = [snapshot(repository='attacker/repo'), snapshot(actor='alice\nspoof'),
                    snapshot([pr(head='main')]), snapshot([pr(number=True)]), snapshot([pr(), pr()]),
                    snapshot([pr(ci=[])]), snapshot([pr(draft=1)]), snapshot([pr(state='OTHER')]),
                    snapshot([pr(updated_at='2026-09-12T13:00:00Z')]),
                    snapshot([pr(state='CLOSED')]), snapshot(extra=True)]
        for data in variants:
            with self.subTest(data=data), self.assertRaises(WorkerError):
                self.run_plan(data)

    def test_input_identity_changes_with_head_or_estimates(self):
        first = self.run_plan(snapshot([pr()]))['input_digest']
        second = self.run_plan(snapshot([pr(head='f'*40)]))['input_digest']
        self.assertNotEqual(first, second)

    def test_unapproved_roadmap_never_offers_math(self):
        report = self.run_plan(frontier=frontier())
        self.assertIsNone(report['selected'])
        self.assertIn('No approved roadmap', report['roadmap']['reason'])

    def test_ready_low_effort_then_dependency_benefit(self):
        work = [item('cheap'), item('foundation'), item('next', depends_on=['foundation']),
                item('expensive', effort='large'), item('unknown', effort='unknown'),
                item('done', status='complete'), item('active', status='active'),
                item('waiting', depends_on=['active']), item('blocked', blocked_by=['needs decision']),
                item('ready', depends_on=['done'])]
        report = self.run_plan(project=APPROVED, frontier=frontier(work))
        self.assertEqual([c['work_id'] for c in report['candidates']],
                         ['foundation', 'cheap', 'ready', 'expensive', 'unknown'])
        self.assertEqual(report['selected']['destination'], PROJECT.implementation_repository)
        self.assertFalse(report['roadmap']['source_verified'])
        self.assertFalse(report['executable'])

    def test_small_blocked_work_never_outranks_ready_large_work(self):
        work = [item('blocked', depends_on=['large']), item('large', effort='large')]
        self.assertEqual(self.run_plan(project=APPROVED, frontier=frontier(work))['selected']['work_id'], 'large')

    def test_pr_maintenance_outranks_roadmap_estimates(self):
        report = self.run_plan(snapshot([pr(ci='failed')]), APPROVED, frontier=frontier())
        self.assertEqual(report['selected']['stage'], 'ci-repair')
        self.assertEqual(report['candidates'][-1]['stage'], 'roadmap')

    def test_frontier_must_describe_one_pinned_destination(self):
        variants = [frontier(repository='other/repo'), frontier(implementation_repository=PROJECT.repository),
                    frontier(roadmap_revision='main'), frontier(implementation_revision='f'*7),
                    frontier(document='other.md'), frontier(targets='Elsewhere.lean'),
                    frontier(observed_at='2026-09-12T11:00:00Z'), frontier(area='E8'),
                    frontier([item(reference='README.md')]), frontier([item(effort=True)])]
        for data in variants:
            with self.subTest(data=data), self.assertRaises(WorkerError):
                self.run_plan(project=APPROVED, frontier=data)

    def test_unknown_duplicate_self_and_cyclic_dependencies_fail(self):
        cases = [[item(depends_on=['missing'])], [item(), item()], [item(depends_on=['task'])],
                 [item('a', depends_on=['b']), item('b', depends_on=['a'])],
                 [item('a'), item('b', depends_on=['a', 'a'])]]
        for items in cases:
            with self.subTest(items=items), self.assertRaises(WorkerError):
                self.run_plan(project=APPROVED, frontier=frontier(items))


class SurveyTest(unittest.TestCase):
    def test_targeted_live_read_never_queries_unrelated_queue(self):
        api = FakeAPI([{'login': 'alice'}, gh_pr(9), gh_pr(11, state='CLOSED')])
        result = survey(PROJECT, (9, 11), api=api)
        self.assertEqual(result['scope'], [9, 11])
        self.assertEqual([call[:3] for call in api.calls[1:]], [['pr', 'view', '9'], ['pr', 'view', '11']])
        self.assertTrue(all('github.com/' + PROJECT.repository in call for call in api.calls[1:]))

    def test_complete_live_queue_and_detected_cap(self):
        api = FakeAPI([{'login': 'alice'}, [gh_pr(1), gh_pr(2)]])
        self.assertEqual(len(survey(PROJECT, api=api)['pull_requests']), 2)
        self.assertIn('101', api.calls[1])
        with self.assertRaises(WorkerError):
            survey(PROJECT, api=FakeAPI([{'login': 'alice'}, [gh_pr(n) for n in range(101)]]))

    def test_absent_target_and_partial_api_failure_abort_survey(self):
        for raw in (WorkerError('provider/API unavailable'), None, {}):
            with self.subTest(raw=raw), self.assertRaises(WorkerError):
                survey(PROJECT, (1, 2), api=FakeAPI([{'login': 'alice'}, gh_pr(), raw]))

    def test_wrong_returned_target_is_rejected(self):
        with self.assertRaises(WorkerError):
            survey(PROJECT, (1,), api=FakeAPI([{'login': 'alice'}, gh_pr(2)]))

    def test_check_summary_is_conservative(self):
        passed = {'__typename': 'CheckRun', 'status': 'COMPLETED', 'conclusion': 'SUCCESS'}
        self.assertEqual(ci_summary([passed]), 'passed')
        for raw in (None, [], [dict(passed, conclusion='SKIPPED')], [dict(passed, conclusion='NEUTRAL')], [passed]*100):
            self.assertEqual(ci_summary(raw), 'unknown')
        self.assertEqual(ci_summary([passed, dict(passed, conclusion='FAILURE')]), 'failed')
        self.assertEqual(ci_summary([{'__typename': 'StatusContext', 'state': 'PENDING'}]), 'pending')
        with self.assertRaises(WorkerError):
            ci_summary([{'__typename': 'SomethingNew'}])

    @patch('sphereceti.worker_cli.subprocess.run')
    def test_transport_is_host_fixed_read_only_and_bounded(self, run):
        run.return_value = subprocess.CompletedProcess([], 0, '{"login":"alice"}', '')
        with patch.dict(os.environ, {'GH_HOST': 'attacker.test'}):
            GitHub().read(['api', '--hostname', 'github.com', '--method', 'GET', 'user'])
        args, kwargs = run.call_args
        self.assertEqual(kwargs['env']['GH_HOST'], 'github.com')
        self.assertLessEqual(kwargs['timeout'], 45)
        for failure in (subprocess.TimeoutExpired('gh', 1), OSError('unavailable')):
            run.side_effect = failure
            with self.assertRaises(WorkerError):
                GitHub().read(['pr', 'list'])

    def test_deadline_expiry_never_starts_request(self):
        with patch('sphereceti.worker_cli.subprocess.run') as run:
            api = GitHub()
            api.deadline = 0
            with self.assertRaises(WorkerError):
                api.read(['pr', 'list'])
            run.assert_not_called()

    def test_duplicate_fields_and_nonfinite_json_fail(self):
        for raw in ('{"scope":null,"scope":[]}', '{"value":NaN}', 'null extra'):
            with self.assertRaises(WorkerError):
                load_json(raw)


class WorkerCLITest(unittest.TestCase):
    def test_offline_plan_never_calls_processes_even_with_provider_preferences(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            data = snapshot([pr(updated_at='2020-01-01T00:00:00Z')], observed_at=datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'))
            (path/'survey.json').write_text(json.dumps(data))
            (path/'operator.toml').write_text('provider = "paid"\nbudget_usd = 100')
            output = io.StringIO()
            with patch('sys.stdout', output), patch('subprocess.run') as run:
                code = cli.main(['worker', 'plan', '--snapshot', str(path/'survey.json'), '--json',
                                 '--operator-config', str(path/'operator.toml'), '--pr', '1'])
            self.assertEqual(code, 0)
            self.assertFalse(json.loads(output.getvalue())['executable'])
            run.assert_not_called()

    def test_no_execution_loop_area_or_provider_command_is_available(self):
        for extra in (['work'], ['plan', '--execute'], ['plan', '--loop'], ['plan', '--area', 'E8'],
                      ['plan', '--roadmap-only', 'E8'], ['plan', '--provider', 'codex'], ['plan', '--pr', '']):
            with self.subTest(extra=extra), patch('sys.stderr', io.StringIO()), patch('subprocess.run') as run:
                with self.assertRaises(SystemExit) as error:
                    cli.main(['worker', *extra])
                self.assertEqual(error.exception.code, 2)
                run.assert_not_called()

    def test_read_error_and_bad_input_are_nonzero(self):
        with patch('sys.stderr', io.StringIO()), self.assertRaises(SystemExit) as error:
            cli.main(['worker', 'plan', '--snapshot', '/does-not-exist'])
        self.assertEqual(error.exception.code, 2)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'huge.json'
            path.write_text(' '*2_000_001)
            with self.assertRaises(WorkerError):
                read_json(path)

    def test_reference_credit_does_not_relicense_upstream(self):
        source = resource_text('upstream-lock.toml')
        record = next(c for c in parse_source_lock(source) if c['name'] == 'worker')
        self.assertEqual(record['state'], 'reference-only')
        self.assertEqual(record['license_status'], 'unresolved')
        for state in ('imported', 'design-adapted'):
            with self.assertRaises(ConfigError):
                parse_source_lock(source.replace('state = "reference-only"', f'state = "{state}"'))


if __name__ == '__main__':
    unittest.main()
