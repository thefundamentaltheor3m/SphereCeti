"""TauCeti profiling contracts adapted to local advisory reporting.

Source: TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
scripts/perf/test_perf.py and scripts/test_profile_workflow.py (Apache-2.0).
Threshold, timeout, exact-source, and hostile-output cases are adapted below.
"""
import copy
import json
import math
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
from sphereceti import profiling as p, profile_runner as runner
from sphereceti.gate import GateError
from profiling_fixture import commit, fixture


class ProfileTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / 'repo'
        self.base, self.head = fixture(self.repo)
        self.manifest = p.plan(self.repo, self.head, self.base, self.head)

    def samples(self, old=50, new=80):
        return [{'path': 'SphereCeti/Basic.lean', 'side': side, 'revision': revision,
                 'plan_digest': self.manifest['plan_digest'], 'run_id': 'run',
                 'returncode': 0, 'status': 'ok', 'cpu_seconds': value, 'wall_seconds': value}
                for side, revision, value in (('base', self.base, old), ('head', self.head, new))]

    def test_exact_diff_ignores_dirty_checkout_and_labels_roadmap(self):
        (self.repo / 'SphereCeti/Basic.lean').write_text('uncommitted')
        self.assertEqual(p.plan(self.repo, self.head, self.base, self.head), self.manifest)
        (self.repo / 'SphereCetiRoadmap.lean').write_text('-- changed target\n')
        head = commit(self.repo)
        rows = p.plan(self.repo, self.head, self.base, head)['changes']
        self.assertEqual([row['category'] for row in rows], ['library', 'roadmap'])

    def test_branches_and_changed_configuration_are_rejected(self):
        with self.assertRaises(GateError):
            p.plan(self.repo, 'HEAD', self.base, self.head)
        (self.repo / 'lean-toolchain').write_text('changed')
        head = commit(self.repo)
        with self.assertRaisesRegex(GateError, 'identical'):
            p.plan(self.repo, self.head, self.base, head)
        with self.assertRaisesRegex(GateError, 'identical'):
            p.plan(self.repo, head, self.base, self.head)

    def test_merge_base_is_measured_instead_of_base_tip(self):
        subprocess.run(['git', '-C', str(self.repo), 'checkout', '-q', self.base], check=True)
        (self.repo / 'unrelated').write_text('base branch advanced')
        base_tip = commit(self.repo)
        self.assertEqual(p.plan(self.repo, self.head, base_tip, self.head)['diff_base'], self.base)

    def test_rename_is_explicit_removal_and_addition(self):
        (self.repo / 'SphereCeti/Basic.lean').rename(self.repo / 'SphereCeti/New.lean')
        head = commit(self.repo)
        entries = p.plan(self.repo, self.head, self.base, head)['changes']
        self.assertEqual([row['kind'] for row in entries], ['removed', 'added'])
        self.assertEqual(entries[0]['path'], 'SphereCeti/Basic.lean')

    def test_unsafe_source_and_symlink_rejected(self):
        bad = self.repo / 'SphereCeti/Bad|Name.lean'
        bad.write_text('-- bad path')
        with self.assertRaises(GateError):
            p.plan(self.repo, self.head, self.base, commit(self.repo))
        bad.unlink()
        bad.symlink_to('/etc/passwd')
        with self.assertRaises(GateError):
            p.plan(self.repo, self.head, self.base, commit(self.repo))

    def test_module_cap_and_empty_diff(self):
        self.assertEqual(p.plan(self.repo, self.head, self.head, self.head)['changes'], [])
        for index in range(33):
            (self.repo / f'SphereCeti/F{index}.lean').write_text('-- fixture')
        with self.assertRaisesRegex(GateError, '32'):
            p.plan(self.repo, self.head, self.base, commit(self.repo))

    def test_modified_thresholds_require_both_and_never_fail_report(self):
        for old, new, flagged in ((50, 79, False), (100, 140, False), (50, 80, True), (0, 30, True)):
            report = p.summarize(self.manifest, self.samples(old, new), 'run')
            self.assertEqual(report['state'], 'complete')
            self.assertEqual(report['rows'][0]['flagged'], flagged)
            self.assertFalse(report['merge_authority'])

    def test_added_threshold_and_removed_measurement(self):
        manifest = copy.deepcopy(self.manifest)
        manifest['changes'][0].update(kind='added', base_blob=None)
        for new, flagged in ((149, False), (150, True)):
            report = p.summarize(manifest, self.samples(new=new)[1:], 'run')
            self.assertEqual(report['rows'][0]['flagged'], flagged)
        manifest['changes'][0].update(kind='removed', base_blob='base', head_blob=None)
        self.assertEqual(p.summarize(manifest, [], 'run')['state'], 'error')

    def test_missing_failed_nonfinite_negative_boolean_values_are_errors(self):
        self.assertEqual(p.summarize(self.manifest, [], 'run')['state'], 'error')
        for side in (0, 1):
            for field, value in (('cpu_seconds', math.nan), ('wall_seconds', math.inf),
                                 ('cpu_seconds', -1), ('cpu_seconds', True),
                                 ('status', 'failed'), ('returncode', 124)):
                samples = self.samples()
                samples[side][field] = value
                report = p.summarize(self.manifest, samples, 'run')
                self.assertEqual(report['state'], 'error')
                self.assertFalse(report['rows'][0]['flagged'])

    def test_duplicate_unexpected_and_cross_run_samples_rejected(self):
        samples = self.samples()
        with self.assertRaises(ValueError):
            p.summarize(self.manifest, samples + samples, 'run')
        for field in ('revision', 'plan_digest', 'run_id', 'path'):
            changed = self.samples()
            changed[0][field] = 'wrong'
            with self.assertRaises(ValueError):
                p.summarize(self.manifest, changed, 'run')

    def test_markdown_revision_links_and_no_changes(self):
        report = p.summarize(self.manifest, self.samples(), 'run')
        rendered = p.markdown(report)
        self.assertIn(f'[{self.head[:7]}](https://github.com/', rendered)
        self.assertIn('(library)', rendered)
        empty = p.plan(self.repo, self.head, self.head, self.head)
        report = p.summarize(empty, [], 'run')
        self.assertEqual(report['state'], 'no_changes')
        self.assertIn('No changed', p.markdown(report))

    def test_installed_tools_must_match_recorded_revision(self):
        runner.verify_tools(self.repo, self.head)
        (self.repo / 'tools/project/sphereceti/profiling.py').write_text('changed tools')
        with self.assertRaisesRegex(GateError, 'differs'):
            runner.verify_tools(self.repo, commit(self.repo))

    def test_materialization_does_not_follow_candidate_filters(self):
        (self.repo / '.gitattributes').write_text('*.lean filter=malicious\n')
        sha = commit(self.repo)
        dest = self.root / 'candidate'
        runner.materialize(self.repo, sha, dest)
        self.assertEqual((dest / 'SphereCeti/Basic.lean').read_text(), 'def fixtureValue : Nat := 2\n')
        self.assertTrue((dest / '.lake/packages').is_dir())
        self.assertFalse((dest / '.git').exists())

    def test_counters_are_host_owned_and_candidate_output_not_parsed(self):
        raw = self.root / 'host.time'
        box = object.__new__(runner.ProfileSandbox)
        box.gate, box.candidate, box.toolchain, box.dependencies = map(Path, ('/gate', '/candidate', '/lean', '/deps'))
        def execute(command, timeout):
            self.assertEqual(command[:2], ['/usr/bin/time', '--quiet'])
            self.assertIn('/deps', command)
            self.assertIn('/project/.lake/packages', command)
            self.assertEqual(command[-5:], ['/toolchain/bin/lake', 'env', '/toolchain/bin/lean',
                                           '-j1', 'SphereCeti/Basic.lean'])
            raw.write_text('2.0 1.0\n')
            return 0
        with patch.object(runner, 'run_host', side_effect=execute):
            self.assertEqual(runner.measure(box, 'SphereCeti/Basic.lean', raw, 30)['cpu_seconds'], 3)
        for value in ('', 'nan 1', '-1 2', '1 2 extra'):
            raw.write_text(value)
            with self.assertRaises(ValueError):
                runner.counter(raw)

    def test_timeout_terminates_wrapper_process_group(self):
        started = time.monotonic()
        self.assertEqual(runner.run_host(['/bin/sh', '-c', "trap '' TERM; sleep 20"], .1), 124)
        self.assertLess(time.monotonic() - started, 3)

    def test_host_launcher_environment_and_logs_are_closed(self):
        with patch.object(runner.subprocess, 'Popen') as popen:
            popen.return_value.wait.return_value = 0
            runner.run_host(['/usr/bin/true'], 1)
        self.assertEqual(popen.call_args.kwargs['env'], {})
        self.assertEqual(popen.call_args.kwargs['stdout'], subprocess.DEVNULL)
        self.assertEqual(popen.call_args.kwargs['stderr'], subprocess.DEVNULL)

    def test_workspace_cannot_be_exposed_through_other_mounts(self):
        for dependencies, toolchain in ((self.root, Path('/lean')), (Path('/deps'), self.root)):
            with self.assertRaisesRegex(GateError, 'disjoint'):
                runner.run(self.repo, self.head, self.base, self.head,
                           self.root / 'output', toolchain, dependencies)

    def test_orchestration_preserves_failed_prebuild_as_report_error(self):
        dependencies = self.root / 'dependencies'
        dependencies.mkdir()
        toolchain = self.root / 'toolchain'
        (toolchain / 'bin').mkdir(parents=True)
        for name in ('lean', 'lake'):
            (toolchain / 'bin' / name).write_text('fixture binary')
        version = 'Lean (version 4.34.0-rc1, fixture)'
        with patch.object(runner, 'ProfileSandbox') as box, \
                patch.object(runner, 'verify_dependencies'), \
                patch.object(runner.subprocess, 'check_output', return_value=version), \
                patch.object(runner, 'materialize'), \
                patch.object(runner, 'plan', return_value=self.manifest), \
                patch.object(runner, 'verify_tools'), \
                patch.object(runner, 'tree', return_value={'tools/ci/bubblewrap.json': None}), \
                patch.object(runner, 'blob', return_value=b'{}'), \
                patch.object(runner, 'run_host', return_value=17), patch.object(runner, 'measure') as measure:
            report = runner.run(self.repo, self.head, self.base, self.head,
                                self.root / 'failed', toolchain, dependencies)
        measure.assert_not_called()
        self.assertEqual(box.return_value.probe.call_count, 2)
        self.assertEqual(report['state'], 'error')
        self.assertEqual([sample['returncode'] for sample in report['samples']], [17, 17])
        self.assertEqual(json.loads((self.root / 'failed/report.json').read_text()), report)


if __name__ == '__main__':
    unittest.main()
