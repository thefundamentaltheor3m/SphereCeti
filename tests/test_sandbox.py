"""Security contract tests; actual positive isolation + Lean build is a mandatory CI smoke."""
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
from sphereceti.sandbox import Sandbox, SandboxError, emit_candidate_output


class SandboxTest(unittest.TestCase):
    def box(self):
        # No host isolation is simulated here; these tests verify orchestration fail-closed.
        box = object.__new__(Sandbox)
        box.gate, box.candidate, box.toolchain = Path('/trusted'), Path('/candidate'), Path('/lean')
        return box

    def test_empty_launcher_environment_and_explicit_isolation(self):
        with patch('sphereceti.sandbox.subprocess.run') as run:
            self.box().run(['/usr/bin/true'])
        args, kwargs = run.call_args
        self.assertEqual(kwargs['env'], {})
        self.assertTrue(kwargs['capture_output'])
        for flag in ('--unshare-user', '--unshare-pid', '--unshare-net', '--unshare-ipc',
                     '--unshare-uts', '--unshare-cgroup', '--disable-userns', '--remount-ro'):
            self.assertIn(flag, args[0])
        self.assertNotIn('--unshare-all', args[0])
        self.assertEqual(args[0][args[0].index('--bind') + 1:][:2],
                         ['/candidate/.lake', '/project/.lake'])

    def test_startup_failure_prevents_candidate_command(self):
        box = self.box()
        with patch.object(box, 'run', return_value=subprocess.CompletedProcess([], 1, '', 'denied')) as run:
            with self.assertRaisesRegex(SandboxError, 'refusing candidate execution'):
                box.build()
        run.assert_called_once_with(['/usr/bin/true'])

    def test_probe_failure_prevents_candidate_command(self):
        box = self.box()
        with patch.object(box, 'probe', side_effect=SandboxError('probe failed')), patch.object(box, 'run') as run:
            with self.assertRaises(SandboxError):
                box.build()
        run.assert_not_called()

    def test_only_approved_build_script_runs_after_probe(self):
        box = self.box()
        with patch.object(box, 'probe') as probe, patch.object(box, 'run') as run:
            box.build()
        probe.assert_called_once()
        run.assert_called_once_with(['/usr/bin/bash', '/gate/scripts/sandbox-build.sh'], timeout=1800)

    def test_candidate_workflow_commands_are_wrapped_after_execution(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output), patch('sphereceti.sandbox.secrets.token_hex', return_value='secret'):
            emit_candidate_output('::error::forged\n::stop-commands::attacker\n')
        lines = output.getvalue().splitlines()
        self.assertEqual(lines[0], '::stop-commands::secret')
        self.assertEqual(lines[-1], '::secret::')
        self.assertEqual(lines[1], 'sandbox | ::error::forged')

    def test_pin_is_complete_and_mismatch_rejects_execution(self):
        elan = json.loads((ROOT / 'tools/ci/elan.json').read_text())
        self.assertEqual(elan['version'], 'v4.2.3')
        self.assertRegex(elan['archive_sha256'], r'^[0-9a-f]{64}$')
        pin = json.loads((ROOT / 'tools/ci/bubblewrap.json').read_text())
        for key in ('deb_sha256', 'binary_sha256'):
            self.assertRegex(pin[key], r'^[0-9a-f]{64}$')
        with patch.object(Path, 'is_dir', return_value=True), patch.object(Path, 'is_symlink', return_value=False), \
                patch.object(Path, 'read_bytes', return_value=b'unapproved executable'):
            with self.assertRaisesRegex(SandboxError, 'differs from approved pin'):
                Sandbox(ROOT, ROOT, ROOT)
