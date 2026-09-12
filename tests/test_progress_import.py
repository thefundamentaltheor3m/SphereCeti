"""Regression checks for the inactive import and its cooperative offline test harness."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "tools/progress"
spec = importlib.util.spec_from_file_location("progress_harness", ROOT / "scripts/run_progress_tests.py")
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)


class ProgressImportTests(unittest.TestCase):
    def run_fixture(self, text):
        with tempfile.TemporaryDirectory() as temp:
            script = Path(temp) / "probe.py"
            script.write_text(text)
            return harness.run_script(script)

    def test_manifest_integrity_and_original_regressions(self):
        manifest = json.loads((SOURCE / "import-manifest.json").read_text())
        self.assertEqual(manifest["repository"], "TauCetiProject/TauCetiProgress")
        self.assertEqual(manifest["commit"], "880e8b9737973bfbd8f1f214f4ac2ded67f5b856")
        self.assertEqual(len(manifest["files"]), 32)
        paths = set()
        modified = set()
        for row in manifest["files"]:
            name = row["destination"]
            self.assertNotIn(name, paths)
            paths.add(name)
            path = SOURCE / name
            self.assertFalse(path.is_symlink())
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            self.assertEqual(digest, row["import_sha256"], name)
            self.assertEqual(bool(path.stat().st_mode & 0o111), row["git_mode"] == "100755")
            if digest != row["upstream_sha256"]:
                modified.add(name)
            else:
                data = path.read_bytes()
                self.assertEqual(hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest(), row["git_blob"])
        self.assertEqual(modified, {"fixtures/collect.py", *(
            f"progress/{name}.py" for name in ("announce", "apply", "cli", "docs", "gate", "gh", "zulip")
        )})
        actual = {p.relative_to(SOURCE).as_posix() for folder in ("progress", "tests", "fixtures")
                  for p in (SOURCE / folder).rglob("*")
                  if p.is_file() and "__pycache__" not in p.parts}
        self.assertEqual(actual, {p for p in paths if p.startswith(("progress/", "tests/", "fixtures/"))})
        self.assertFalse((SOURCE / ".github").exists())

    def test_operational_entries_refuse_before_effects(self):
        result = self.run_fixture('''
from progress import cli, apply, announce, gate, gh, docs, zulip
import runpy
collect = runpy.run_path('.github/scripts/collect.py')
entries = [
 lambda: cli.cmd_due(None), lambda: cli.cmd_plan(None),
 lambda: cli.cmd_apply(None), lambda: cli.cmd_announce(None),
 lambda: apply.run(None, None, None, None), lambda: apply._run(None, None),
 lambda: announce.run(None), lambda: gate.main([]), lambda: gh.gh([]),
 lambda: docs.Docs()._fetch("https://example.invalid"),
 lambda: zulip.from_env(), lambda: zulip.Zulip("", "")._call("GET", "/"),
 lambda: collect['main']([]),
]
for entry in entries:
    try:
        entry()
    except RuntimeError as exc:
        assert "inactive Progress source import" in str(exc), str(exc)
    else:
        raise AssertionError("operational entry unexpectedly enabled")
''')
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_launchers_refuse_before_runtime_import(self):
        for path in (SOURCE / "progress/cli.py", SOURCE / "fixtures/collect.py"):
            with self.subTest(path=path):
                proc = subprocess.run([sys.executable, "-I", "-B", str(path), "--help"],
                                      capture_output=True, text=True, timeout=10)
                self.assertNotEqual(proc.returncode, 0)
                self.assertIn("inactive Progress source import", proc.stderr)
                self.assertNotIn("ModuleNotFoundError", proc.stderr)

    def test_harness_denies_external_operations_even_when_caught(self):
        attempts = [
            "import socket; socket.socket()",
            "import subprocess; subprocess.run(['gh', 'auth', 'status'])",
            "import subprocess; subprocess.run(['git', '-C', '/', 'log'])",
            "import subprocess; subprocess.run(['git', 'init', '/tmp/escape-progress'])",
            "import subprocess; subprocess.run(['git', 'push'])",
            "open('/tmp/escape-progress', 'w')",
        ]
        for code in attempts:
            with self.subTest(code=code):
                result = self.run_fixture("try:\n    " + code + "\nexcept BaseException:\n    pass\n")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("forbidden operation attempted", result.stderr)

    def test_harness_drops_credentials_and_models_unwritable_fixture(self):
        with patch.dict(os.environ, {"GH_TOKEN": "canary", "ZULIP_API_KEY": "canary",
                                     "OPENROUTER_API_KEY": "canary", "PYTHONPATH": "/invalid"}):
            result = self.run_fixture('''
import os
from pathlib import Path
assert not any(k in os.environ for k in ("GH_TOKEN", "ZULIP_API_KEY", "OPENROUTER_API_KEY", "PYTHONPATH"))
try:
    Path("/nonexistent/progress-test").mkdir(parents=True)
except PermissionError:
    pass
else:
    raise AssertionError("fixture must be unwritable")
''')
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
