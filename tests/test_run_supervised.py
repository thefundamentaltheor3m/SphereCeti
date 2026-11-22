"""The supervised canary entry point: its shell exit status follows the documented contract."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/run_supervised.py"


class RunSupervisedTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="sphereceti-supervised-")
        self.addCleanup(temp.cleanup)
        self.cwd = Path(temp.name)
        # Modules a caller's cwd could use to shadow the supervisor under a non-isolated launch.
        for name in ("smoke_process.py", "json.py"):
            (self.cwd / name).write_text("raise SystemExit('shadowed module imported from cwd')\n")

    def run_script(self, *command, timeout="2100"):
        process = subprocess.run([sys.executable, "-I", str(SCRIPT), "--timeout", timeout, "--", *command],
                                 cwd=self.cwd, capture_output=True, text=True, timeout=120)
        report = json.loads(process.stdout.strip().splitlines()[-1])
        return process.returncode, report, process.stdout

    def test_worker_success_is_the_only_shell_success(self):
        code, report, stdout = self.run_script(sys.executable, "-c", "print('worker ok')")
        self.assertEqual(code, 0)
        self.assertEqual(report, {"cleanup_verified": True, "exit_code": 0})
        self.assertIn("worker ok", stdout)  # the command's own output is passed through

    def test_worker_failure_returns_the_worker_status(self):
        code, report, _ = self.run_script(sys.executable, "-c", "raise SystemExit(7)")
        self.assertEqual(code, 7)
        self.assertEqual(report, {"cleanup_verified": True, "exit_code": 7})

    def test_worker_ended_by_a_signal_returns_128_plus_the_signal(self):
        code, report, _ = self.run_script(sys.executable, "-c", "import os, signal; os.kill(os.getpid(), signal.SIGTERM)")
        self.assertEqual(code, 143)
        self.assertEqual(report["exit_code"], -15)

    def test_supervisor_timeout_returns_124_and_stops_every_descendant(self):
        pids = self.cwd / "pids.json"
        worker = ("import json, os, subprocess, sys, time\n"
                  "child = subprocess.Popen([sys.executable, '-c', 'import time\\nwhile True: time.sleep(1)'],"
                  " start_new_session=True)\n"
                  f"open({str(pids)!r}, 'w').write(json.dumps([os.getpid(), child.pid]))\n"
                  "while True: time.sleep(1)\n")
        start = time.monotonic()
        code, report, _ = self.run_script(sys.executable, "-I", "-c", worker, timeout="2")
        self.assertEqual(code, 124)
        self.assertEqual(report, {"cleanup_verified": True, "reason": "stage timeout; owned descendants stopped"})
        self.assertLess(time.monotonic() - start, 30)
        for pid in json.loads(pids.read_text()):  # the worker and its detached child
            self.assertFalse(Path(f"/proc/{pid}").exists(), pid)

    def test_unstartable_command_returns_126(self):
        code, report, _ = self.run_script(str(self.cwd / "missing-worker"))
        self.assertEqual(code, 126)
        self.assertNotIn("exit_code", report)

    def test_unverified_cleanup_returns_125(self):
        spec = importlib.util.spec_from_file_location("run_supervised_under_test", SCRIPT)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        for failure in (RuntimeError("stage descendants could not be reaped; cleanup is unverified"),
                        OSError("smoke cleanup requires Linux /proc, child subreapers and pidfds"),
                        KeyboardInterrupt()):
            with patch.object(module, "run_owned", side_effect=failure), \
                 patch("builtins.print") as printed:
                self.assertEqual(module.main(["--", "true"]), 125)
            report = json.loads(printed.call_args.args[0])
            self.assertIs(report["cleanup_verified"], False)
            self.assertIn("cleanup unverified", report["reason"])
        self.assertEqual(module.status({"cleanup_verified": True,
                                        "reason": "stage interrupted; owned descendants stopped"}), 130)
        # A stopped leftover descendant does not turn a worker success or failure into another code.
        left = "command left descendant processes; owned descendants stopped"
        self.assertEqual(module.status({"cleanup_verified": True, "exit_code": 0, "reason": left}), 0)
        self.assertEqual(module.status({"cleanup_verified": True, "exit_code": 7, "reason": left}), 7)

    def test_usage_errors_run_nothing(self):
        for args in ((), ("--timeout", "0", "--", "true"), ("--timeout", "inf", "--", "true")):
            process = subprocess.run([sys.executable, "-I", str(SCRIPT), *args], cwd=self.cwd,
                                     capture_output=True, text=True, timeout=60)
            self.assertEqual(process.returncode, 2, args)
            self.assertEqual(process.stdout, "")


if __name__ == "__main__":
    unittest.main()
