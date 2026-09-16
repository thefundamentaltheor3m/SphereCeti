"""Adapted TauCeti lifecycle regression cases plus SphereCeti policy/race boundaries.

TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5 (Apache-2.0):
scripts/pr_status/test_{pr_labels,conflicts,stuck_alerts}.py, scripts/test_housekeeping.py.
"""
from copy import deepcopy
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools/project'))
from sphereceti import lifecycle as life, lifecycle_api as api
from sphereceti.config import parse_project, resource_text
from sphereceti.review_records import RecordError
from lifecycle_fixture import LifecycleFixture, installed_lifecycle_smoke
from review_fixture import commit, git

REPO = 'thefundamentaltheor3m/SphereCeti'
NOW = datetime(2026, 9, 12, tzinfo=timezone.utc)
SETTINGS = life.parse_settings(resource_text('lifecycle.toml'))


def pr():
    return {'number': 1, 'head': {'sha': 'a'*40},
            'base': {'sha': 'b'*40, 'ref': 'main', 'repo': {'full_name': REPO}},
            'state': 'open', 'merged': False, 'draft': False, 'auto_merge': None,
            'mergeable': True, 'labels': [], 'updated_at': '2026-09-01T00:00:00Z'}


def observation(state='eligible'):
    return {'repository': REPO, 'pr': 1, 'head': 'a'*40, 'base': 'b'*40, 'tooling': 'b'*40,
            'eligibility': state, 'merge_allowed': False}


def plan(p=None, state='eligible'):
    return life.pr_plan(p or pr(), observation(state), 'b'*40, SETTINGS, now=NOW)


class PlanningTests(unittest.TestCase):
    def test_shared_eligibility_labels_never_authorize_merge(self):
        for state, name in life.LABELS.items():
            result = plan(state=state)
            self.assertEqual(result['add'], [name])
            self.assertFalse(result['merge_allowed'])

    def test_conflict_is_independent_and_unknown_never_clears_it(self):
        p = pr(); p['mergeable'] = False
        result = plan(p, 'blocked')
        self.assertEqual(set(result['add']), {life.CONFLICT, life.LABELS['blocked']})
        p['labels'] = [life.CONFLICT]; p['mergeable'] = None
        result = plan(p, 'blocked')
        self.assertEqual(result['state'], 'unknown')
        self.assertNotIn(life.CONFLICT, result['remove'])
        p['mergeable'] = True
        self.assertIn(life.CONFLICT, plan(p)['remove'])

    def test_draft_hold_stack_and_human_automerge_are_untouched(self):
        for change in ({'draft': True}, {'labels': ['KEEP', life.CONFLICT]}, {'auto_merge': {}},
                       {'base': {**pr()['base'], 'ref': 'stack'}}):
            result = plan({**pr(), **change})
            self.assertEqual(result['state'], 'human_managed')
            self.assertFalse(result['add'] or result['remove'])

    def test_terminal_only_clears_owned_labels_and_ignores_review(self):
        p = pr(); p.update(state='closed', labels=[life.CONFLICT, 'human-custom'])
        result = life.pr_plan(p, None, 'b'*40, SETTINGS, now=NOW)
        self.assertEqual(result['remove'], [life.CONFLICT])

    def test_idempotency_preserves_unrelated_labels(self):
        p = pr(); p['labels'] = [life.LABELS['eligible'], 'human-custom']
        result = plan(p)
        self.assertFalse(result['add'] or result['remove'])
        self.assertEqual(result, plan(p))

    def test_quiet_is_advisory_and_age_boundary_is_explicit(self):
        self.assertEqual(plan()['alerts'], ['eligible_now_but_quiet'])
        self.assertEqual(plan(state='blocked')['recommendations'], ['human_review_of_quiet_blocked_pr'])
        p = pr(); p['updated_at'] = '2026-09-11T23:00:00Z'
        self.assertEqual(plan(p)['alerts'], [])
        p['updated_at'] = '2026-09-13T00:00:00Z'
        with self.assertRaises(RecordError): plan(p)

    def test_missing_or_stale_shared_observation_is_an_error(self):
        with self.assertRaises(RecordError):
            life.pr_plan(pr(), None, 'b'*40, SETTINGS, now=NOW)
        for key in ('repository', 'pr', 'head', 'base', 'tooling', 'eligibility', 'merge_allowed'):
            bad = observation(); bad[key] = 'wrong'
            with self.assertRaises(RecordError):
                life.pr_plan(pr(), bad, 'b'*40, SETTINGS, now=NOW)

    def test_missing_fields_unknown_boolean_and_duplicate_labels_fail(self):
        for key in ('auto_merge', 'updated_at', 'state', 'merged', 'draft', 'labels'):
            p = pr(); del p[key]
            with self.assertRaises((RecordError, KeyError)): plan(p)
        for change in ({'merged': None}, {'draft': 0}, {'mergeable': 'false'},
                       {'labels': ['keep', 'keep']}):
            with self.assertRaises(RecordError): plan({**pr(), **change})

    def test_settings_reject_invalid_switches_thresholds_and_unknown_keys(self):
        source = resource_text('lifecycle.toml')
        for bad in (source.replace('false', '"false"'), source.replace('writer_user_id = 0', 'writer_user_id = -1'),
                    source.replace('stuck_hours = 24', 'stuck_hours = 0'), source + '\nother=true\n'):
            with self.assertRaises(ValueError): life.parse_settings(bad)


class HealthTests(unittest.TestCase):
    workflow = {'id': 7, 'path': '.github/workflows/ci.yml', 'state': 'active'}

    def run_row(self, id=1, conclusion='failure', sha='a'*40, status='completed'):
        return {'id': id, 'workflow_id': 7, 'path': self.workflow['path'], 'event': 'push',
                'head_branch': 'main', 'repository': {'full_name': REPO}, 'head_sha': sha,
                'status': status, 'conclusion': conclusion, 'created_at': f'2026-09-{id:02d}T00:00:00Z'}

    def health(self, runs): return life.main_health('b'*40, self.workflow, runs, REPO)

    def test_pending_and_cancelled_tip_do_not_clear_known_red(self):
        for conclusion, status in ((None, 'in_progress'), ('cancelled', 'completed'), ('skipped', 'completed')):
            result = self.health([self.run_row(2, conclusion, 'b'*40, status), self.run_row()])
            self.assertEqual(result['state'], 'red')
            self.assertEqual(result['last_conclusive']['head_sha'], 'a'*40)

    def test_new_success_recovers_but_old_success_does_not_certify_tip(self):
        self.assertEqual(self.health([self.run_row(conclusion='success')])['state'], 'pending_tip')
        self.assertEqual(self.health([self.run_row(), self.run_row(2, 'success', 'b'*40)])['state'], 'green')

    def test_absent_or_inconclusive_window_is_unknown(self):
        for rows in ([], [self.run_row(conclusion='cancelled')]):
            result = self.health(rows)
            self.assertEqual(result['state'], 'unknown')
            self.assertFalse(result['current_tip_passed'])

    def test_wrong_workflow_event_repo_or_duplicate_run_is_error(self):
        for key in ('workflow_id', 'head_branch', 'event', 'path', 'repository', 'head_sha', 'status'):
            bad = self.run_row(); bad[key] = 'wrong'
            with self.assertRaises((RecordError, AttributeError)): self.health([bad])
        with self.assertRaises(RecordError): self.health([self.run_row(), self.run_row()])

    def test_disabled_workflow_is_explicit(self):
        self.assertEqual(life.main_health('b'*40, {**self.workflow, 'state':'disabled_manually'},
                                         [self.run_row(1, 'success', 'b'*40)], REPO)['state'], 'disabled')


class FakeBackend:
    def __init__(self):
        self.config = {'ready': True, 'settings': SETTINGS, 'main': 'b'*40}
        self.p = pr(); self.writes = []; self.reads = 0; self.advance = False
        self.fail_write = False; self.apply_on_error = False
    def setup(self, applying=False): return deepcopy(self.config)
    def queue(self): return [1, 2]
    def snapshot(self, number, setup):
        self.reads += 1
        result = plan(self.p)
        if self.advance and self.reads > 1: result['head'] = 'c'*40
        return result
    def change(self, number, action, name):
        self.writes.append((number, action, name))
        if not self.fail_write or self.apply_on_error:
            if action == 'add': self.p['labels'].append(name)
            else: self.p['labels'].remove(name)
        if self.fail_write: raise RecordError('ambiguous')
    def labels(self, number): return self.p['labels']


class ReconciliationTests(unittest.TestCase):
    def test_disabled_apply_never_enumerates_or_snapshots(self):
        backend = FakeBackend(); backend.config['ready'] = False
        with patch.object(backend, 'queue') as queue:
            result = api.reconcile(backend, applying=True)
        queue.assert_not_called(); self.assertEqual(backend.reads, 0)
        self.assertEqual(result['state'], 'disabled'); self.assertFalse(backend.writes)

    def test_preview_no_writes_and_duplicate_apply_converges(self):
        backend = FakeBackend()
        api.reconcile(backend, [1]); self.assertFalse(backend.writes)
        api.reconcile(backend, [1], applying=True)
        api.reconcile(backend, [1], applying=True)
        self.assertEqual(len(backend.writes), 1)

    def test_old_label_removed_before_replacement_one_write_per_sweep(self):
        backend = FakeBackend(); backend.p['labels'] = [life.LABELS['blocked']]
        api.reconcile(backend, applying=True)
        self.assertEqual(backend.writes, [(1, 'remove', life.LABELS['blocked'])])
        api.reconcile(backend, [1], applying=True)
        self.assertEqual(backend.p['labels'], [life.LABELS['eligible']])

    def test_evidence_or_policy_change_prevents_write(self):
        backend = FakeBackend(); backend.advance = True
        self.assertEqual(api.reconcile(backend, [1], applying=True)['state'], 'error')
        self.assertFalse(backend.writes)
        backend = FakeBackend()
        with patch.object(backend, 'setup', side_effect=[deepcopy(backend.config), {**backend.config, 'ready':False}]):
            self.assertEqual(api.reconcile(backend, [1], applying=True)['state'], 'error')
        self.assertFalse(backend.writes)

    def test_ambiguous_write_reads_back_without_retry(self):
        for applied in (False, True):
            backend = FakeBackend(); backend.fail_write = True; backend.apply_on_error = applied
            result = api.reconcile(backend, applying=True)
            self.assertEqual(len(backend.writes), 1)
            self.assertEqual(result['state'], 'reconcile_again' if applied else 'error')

    def test_one_unknown_or_error_does_not_starve_other_prs(self):
        backend = FakeBackend()
        with patch.object(backend, 'snapshot', side_effect=[RecordError('unknown'), plan()]):
            result = api.reconcile(backend, [1, 2])
        self.assertEqual(len(result['results']), 2)
        self.assertEqual(result['state'], 'error')
        backend.p['mergeable'] = None
        api.reconcile(backend, [1], applying=True)
        self.assertFalse(backend.writes)
        backend = FakeBackend()
        with patch.object(backend, 'snapshot', side_effect=[RecordError('unknown'), plan(), plan()]):
            result = api.reconcile(backend, [1, 2], applying=True)
        self.assertEqual(result['state'], 'error')
        self.assertEqual(len(backend.writes), 1)

    def test_writer_only_permits_fixed_labels_and_strips_reader_credentials(self):
        writer = api.LabelWriter(REPO, 'private')
        with patch.dict(os.environ, {'GH_TOKEN':'read', 'SECRET':'hidden'}, clear=True), \
                patch.object(api.subprocess, 'run', return_value=subprocess.CompletedProcess([], 0, '[]', '')) as run:
            writer.change(1, 'add', life.CONFLICT)
        self.assertEqual(run.call_args.kwargs['env'], {'GH_TOKEN':'private', 'GH_PROMPT_DISABLED':'1'})
        self.assertEqual(json.loads(run.call_args.kwargs['input']), {'labels':[life.CONFLICT]})
        for action, label in (('close', life.CONFLICT), ('add', 'human-label'), ('remove', '../escape')):
            with self.assertRaises(RecordError): writer.change(1, action, label)

    def test_paginated_inventory_rejects_missing_and_oversized_data(self):
        self.assertEqual(api.pages([[]]), [])
        for value in ([], {}, [None], [[{}]*1001]):
            with self.assertRaises(RecordError): api.pages(value)

    def test_source_cli_and_disabled_apply_with_get_only_fixture(self):
        with tempfile.TemporaryDirectory() as root:
            installed_lifecycle_smoke(None, Path(root))


class ActivationTests(unittest.TestCase):
    def test_both_switches_identity_resource_match_and_label_setup(self):
        with tempfile.TemporaryDirectory() as root:
            fixture = LifecycleFixture(Path(root))
            git(fixture.repo, 'checkout', '-q', fixture.tooling)
            automation = fixture.repo / 'policy/automation.toml'
            automation.write_text(automation.read_text().replace('posting = false', 'posting = true'))
            settings = fixture.repo / 'policy/lifecycle.toml'
            settings.write_text(settings.read_text().replace('labels_enabled = false', 'labels_enabled = true')
                                .replace('writer_user_id = 0', 'writer_user_id = 7'))
            tooling = commit(fixture.repo)
            files = api.tooling_files()
            for name in ('policy/lifecycle.toml', 'policy/automation.toml'):
                files[name] = (fixture.repo / name).read_bytes()
            actor = {'id': 7, 'type': 'User', 'site_admin': False}
            writer = SimpleNamespace(identity=lambda: actor)
            project = parse_project(resource_text('sphereceti.toml'))
            backend = api.Backend(SimpleNamespace(source_repo=fixture.repo, cache_dir=Path(root)/'cache'), project, writer)
            class Client:
                def call(self, endpoint):
                    if endpoint.endswith('/commits/main'): return {'sha': tooling}
                    from urllib.parse import unquote
                    return {'name': unquote(endpoint.rsplit('/', 1)[-1])}
                def revalidate(self): pass
            with patch.object(api, 'Reader', Client), patch.object(api, 'tooling_files', return_value=files):
                # Reader's production constructor takes the repository.
                with patch.object(api, 'Reader', side_effect=lambda repository: Client()):
                    self.assertTrue(backend.setup(True)['ready'])
                    actor['id'] = 8
                    with self.assertRaises(RecordError): backend.setup(True)
                    actor['id'] = 7
                    with patch.object(Client, 'call', side_effect=lambda endpoint:
                                      {'sha':tooling} if endpoint.endswith('/commits/main') else {'name':'wrong'}):
                        with self.assertRaises(RecordError): backend.setup(True)
                    # Installed code/resource drift prevents reaching the writer at all.
                    files['tools/project/sphereceti/lifecycle.py'] = b'wrong'
                    with patch.object(writer, 'identity') as identity:
                        self.assertFalse(backend.setup(True)['ready'])
                        identity.assert_not_called()
                    files['tools/project/sphereceti/lifecycle.py'] = (fixture.repo/'tools/project/sphereceti/lifecycle.py').read_bytes()
                    for path, old, new in ((settings, 'labels_enabled = true', 'labels_enabled = false'),
                                           (automation, 'posting = true', 'posting = false')):
                        original = path.read_text(); path.write_text(original.replace(old, new))
                        tooling = commit(fixture.repo)
                        files[str(path.relative_to(fixture.repo))] = path.read_bytes()
                        with patch.object(writer, 'identity') as identity:
                            self.assertFalse(backend.setup(True)['ready'])
                            identity.assert_not_called()
                        path.write_text(original); tooling = commit(fixture.repo)
                        files[str(path.relative_to(fixture.repo))] = path.read_bytes()


if __name__ == '__main__': unittest.main()
