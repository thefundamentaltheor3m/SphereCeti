# SPDX-License-Identifier: Apache-2.0
"""Smoke reports must distinguish a successful process from successful diagnostics."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'scripts'))
from smoke_cli import check_status, fixture_suites, run_step
from smoke_process import _subreaper


class SmokeReportTests(unittest.TestCase):
    def test_independently_landed_features_require_their_regressions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            base = fixture_suites(root)
            self.assertNotIn('test_authoring', base)
            source = root / 'tools/project/sphereceti/authoring.py'
            test = root / 'tests/test_authoring.py'
            source.parent.mkdir(parents=True)
            test.parent.mkdir()
            source.write_text('')
            with self.assertRaisesRegex(ValueError, 'incomplete smoke feature inventory'):
                fixture_suites(root)
            test.write_text('')
            self.assertIn('test_authoring', fixture_suites(root))
            source.unlink()
            with self.assertRaisesRegex(ValueError, 'incomplete smoke feature inventory'):
                fixture_suites(root)

    def stage(self, code, **kwargs):
        with tempfile.TemporaryDirectory() as directory:
            return run_step('fixture', [sys.executable, '-I', '-c', code], Path(directory),
                            kwargs.pop('timeout', 10), **kwargs)

    def test_exit_code_failure_is_reported(self):
        result = self.stage('raise SystemExit(7)')
        self.assertEqual(result['state'], 'failed')
        self.assertEqual(result['exit_code'], 7)

    def test_invalid_or_unknown_queue_is_not_success_despite_exit_zero(self):
        for value in ({}, [], {'queue': {'state': 'error'}},
                      {'queue': {'state': 'not_checked'}, 'setup': {'merging_ready': True}}):
            with self.subTest(value=value):
                result = self.stage(f'print({json.dumps(value)!r})', validate=check_status)
                self.assertEqual(result['state'], 'failed')
                self.assertEqual(result['exit_code'], 0)

    def test_offline_and_online_have_distinct_success_requirements(self):
        value = {'queue': {'state': 'not_checked'},
                 'setup': {'merging_ready': False, 'state': 'not_verified'}}
        raw = json.dumps(value)
        self.assertEqual(self.stage(f'print({raw!r})', validate=check_status)['state'], 'passed')
        with self.assertRaises(ValueError):
            check_status(raw, online=True)
        value['queue']['state'] = 'available'
        check_status(json.dumps(value), online=True)

    def test_timeout_stops_fixture_and_is_not_a_skip(self):
        result = self.stage('import time; time.sleep(30)', timeout=0.05)
        self.assertEqual(result['state'], 'failed')
        self.assertIn('timeout', result['reason'])
        self.assertTrue(result['cleanup_verified'])

    def test_timeout_reaps_detached_descendants_that_ignore_term(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pids = root / 'pids.json'
            # Both descendant generations leave the original session. SIGKILL of only
            # the stage's process group cannot reach either of them.
            leaf = 'import signal,time; signal.signal(signal.SIGTERM, signal.SIG_IGN); time.sleep(60)'
            bridge = (
                'import json,os,signal,subprocess,sys,time; '
                'signal.signal(signal.SIGTERM, signal.SIG_IGN); '
                f'child=subprocess.Popen([sys.executable,"-I","-c",{leaf!r}],start_new_session=True); '
                f'open({str(pids)!r},"w").write(json.dumps([os.getpid(),child.pid])); '
                'time.sleep(60)'
            )
            parent = (
                'import subprocess,sys,time; '
                f'subprocess.Popen([sys.executable,"-I","-c",{bridge!r}],start_new_session=True); '
                'time.sleep(60)'
            )
            previous = _subreaper()
            unrelated = subprocess.Popen([sys.executable, '-I', '-c', 'import time; time.sleep(60)'])
            try:
                result = run_step('detached', [sys.executable, '-I', '-c', parent], root, 0.5)
                self.assertEqual(result['state'], 'failed')
                self.assertIn('timeout', result['reason'])
                self.assertTrue(result['cleanup_verified'])
                self.assertTrue(pids.exists(), 'fixture must actually launch detached descendants')
                for pid in json.loads(pids.read_text()):
                    self.assertFalse(Path(f'/proc/{pid}').exists(), f'descendant {pid} survived or was not reaped')
                self.assertIsNone(unrelated.poll(), 'cleanup must not target unrelated caller children')
                self.assertEqual(_subreaper(), previous)
            finally:
                unrelated.terminate()
                unrelated.wait(timeout=5)

    def test_normal_exit_also_reaps_abandoned_detached_child(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            pidfile = root / 'child.pid'
            code = ('import subprocess,sys; '
                    'child=subprocess.Popen([sys.executable,"-I","-c","import time; time.sleep(60)"],'
                    'start_new_session=True); '
                    f'open({str(pidfile)!r},"w").write(str(child.pid))')
            result = run_step('abandoned', [sys.executable, '-I', '-c', code], root, 5)
            self.assertEqual(result['state'], 'failed')
            self.assertIn('left descendant', result['reason'])
            self.assertTrue(result['cleanup_verified'])
            self.assertFalse(Path(f'/proc/{pidfile.read_text()}').exists())

    def test_unsupported_host_fails_before_running_a_stage(self):
        with patch('smoke_process.sys.platform', 'unsupported'), patch('smoke_process.os.fork') as fork:
            result = self.stage('raise SystemExit(0)')
            self.assertEqual(result['state'], 'failed')
            self.assertIn('requires Linux', result['reason'])
            fork.assert_not_called()

    def test_supervisor_error_is_bounded_and_does_not_claim_cleanup(self):
        with patch('smoke_process._supervise', side_effect=RuntimeError('\u2603' * 100000)):
            result = self.stage('raise SystemExit(0)')
        self.assertEqual(result['state'], 'failed')
        self.assertFalse(result['cleanup_verified'])
        self.assertIn('supervisor failed: RuntimeError', result['reason'])
        self.assertLess(len(result['reason']), 500)


if __name__ == '__main__':
    unittest.main()
