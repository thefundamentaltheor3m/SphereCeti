"""SphereCeti's inactive import and offline test boundary; upstream tests stay unchanged."""

import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
REVIEW = ROOT / "tools" / "review"
spec = importlib.util.spec_from_file_location("review_test_harness", ROOT / "scripts/run_review_tests.py")
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)


class ReviewImportTests(unittest.TestCase):
    def helper(self, code):
        with tempfile.TemporaryDirectory() as scratch:
            path = Path(scratch) / "check.py"
            path.write_text(f"import sys\nsys.path.insert(0, {str(REVIEW / 'runner')!r})\n" + code)
            return harness.run_script(path)

    def test_import_mapping_and_unchanged_upstream_tests_and_rubrics(self):
        manifest = json.loads((REVIEW / "import-manifest.json").read_text())
        self.assertEqual(manifest["repository"], "TauCetiProject/TauCetiReview")
        self.assertEqual(manifest["commit"], "afb424eda89e8ac96d9eb69f6a88972055a4cd1b")
        mapped = set()
        changed = set()
        for item in manifest["files"]:
            path = REVIEW / item["destination"]
            self.assertNotIn(item["destination"], mapped)
            mapped.add(item["destination"])
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), item["import_sha256"], path)
            self.assertEqual("100755" if path.stat().st_mode & 0o111 else "100644", item["mode"], path)
            if item["upstream_sha256"] != item["import_sha256"]:
                changed.add(item["destination"])
        self.assertEqual(len(mapped), 57)
        self.assertEqual(changed, {f"runner/{name}.py" for name in (
            "archive", "cli", "costs", "merge_from_scoreboard", "post", "queue_reservation", "review", "sweep",
        )})
        for directory in ("runner", "rubrics", "tests", "fixtures"):
            actual = {p.relative_to(REVIEW).as_posix() for p in (REVIEW / directory).rglob("*")
                      if p.is_file() and "__pycache__" not in p.parts}
            self.assertEqual(actual, {p for p in mapped if p.startswith(directory + "/")})
        self.assertFalse((REVIEW / "pyproject.toml").exists())
        self.assertFalse((REVIEW / ".github").exists())

    def test_ten_rubrics_keep_upstream_order(self):
        tree = ast.parse((REVIEW / "runner/review.py").read_text())
        order = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
                     and any(isinstance(t, ast.Name) and t.id == "DEFAULT_RUBRICS" for t in n.targets))
        self.assertEqual(order, ["correctness", "reuse", "scope", "attribution", "api-design",
                                "generality", "placement", "naming", "documentation", "proof-quality"])
        for name in order:
            self.assertTrue((REVIEW / "rubrics" / f"{name}.md").is_file())

    def test_all_imported_launchers_are_inactive(self):
        for name in ("archive", "cli", "costs", "merge_from_scoreboard", "post",
                     "queue_reservation", "review", "sweep"):
            with self.subTest(launcher=name):
                result = harness.run_script(REVIEW / "runner" / f"{name}.py")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("SphereCeti I05 imports this engine inactive", result.stderr)

    def test_cli_sync_and_identity_do_not_use_upstream_writes(self):
        result = self.helper('''
import archive, cli, post
from types import SimpleNamespace
assert not archive.DATA_REPO
assert not cli.DEFAULT_CODE_REPO
assert not cli.DEFAULT_ROADMAP_REPO
assert not post.REVIEW_BOT
for fn, exception, message in (
    (cli.main, SystemExit, "adapter is not enabled"),
    (lambda: archive.sync("outbox", "data", "https://example.invalid/archive"),
     RuntimeError, "publishing is disabled"),
):
    try:
        fn()
    except exception as exc:
        assert message in str(exc)
    else:
        raise AssertionError("inactive entry point ran")
for returncode, stdout in ((1, ""), (0, ""), (1, "unverified")):
    post.subprocess.run = lambda *a, **k: SimpleNamespace(returncode=returncode, stdout=stdout)
    try:
        post.current_login()
    except RuntimeError:
        pass
    else:
        raise AssertionError("identity lookup did not fail closed")
post.subprocess.run = lambda *a, **k: SimpleNamespace(returncode=0, stdout="operator\\n")
assert post.current_login() == "operator"
''')
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_missing_resources_never_fetch_upstream_main(self):
        result = self.helper('''
import cli
cli.__file__ = "/missing-sphereceti-source/runner/cli.py"
try:
    cli.resolve_repo_dir(None)
except SystemExit as exc:
    assert exc.code == 1
else:
    raise AssertionError("missing resources accepted")
''')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("no mutable fallback", result.stderr)

    def test_offline_guard_rejects_even_caught_external_calls(self):
        for code in ("import subprocess; subprocess.run(['gh', 'api', 'user'])",
                     "import socket; socket.socket()", "import os; os.system('true')"):
            with self.subTest(code=code):
                result = self.helper(f"try:\n    {code}\nexcept BaseException:\n    pass\n")
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("external call attempted", result.stderr)


if __name__ == "__main__":
    unittest.main()
