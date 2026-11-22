"""The adapted Codex sandbox diagnostic: no credential, no model, no GitHub, fake Codex only."""
import ast
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "tools/review/runner"

FAKE_CODEX = r'''
import json, os, pathlib, sys
root = pathlib.Path(__file__).parent
args = sys.argv[1:]
home = os.environ.get("CODEX_HOME", "")
with (root / "codex-calls.jsonl").open("a") as stream:
    stream.write(json.dumps({"argv": args, "env": dict(os.environ),
                             "auth_seeded": bool(home) and pathlib.Path(home, "auth.json").exists()}) + "\n")
if args == ["--version"]:
    print("codex-cli 0.0.0-fake")
    sys.exit(0)
if args == ["sandbox", "--help"]:
    print("Usage: codex sandbox [COMMAND]...")
    sys.exit(0)
mode = (root / "mode").read_text()
if mode == "namespace":
    print("bwrap: Creating new namespace failed: Operation not permitted", file=sys.stderr)
    sys.exit(1)
assert args[0] == "sandbox" and "exec" not in args and "login" not in args
separator = args.index("--")
settings = [args[i + 1] for i, arg in enumerate(args[:separator]) if arg == "-c"]
assert 'sandbox_mode="read-only"' in settings and "shell_environment_policy.inherit=none" in settings
if not any(s.startswith("shell_environment_policy.set.PATH=") for s in settings):
    print("bubblewrap is unavailable", file=sys.stderr)
    sys.exit(101)
if not any(s.startswith("shell_environment_policy.set.TMPDIR=") for s in settings):
    print("registry lock: Read-only file system", file=sys.stderr)
    sys.exit(101)
shell = args[separator + 1:]
assert shell[:2] == ["/bin/sh", "-c"]
source, nonce, target = shell[4:7]
assert pathlib.Path(source).read_text().strip() == nonce and not pathlib.Path(target).exists()
print("TAUCETI_SANDBOX_READ_OK_WRITE_DENIED")
'''


def probe_script():
    tree = ast.parse((RUNNER / "sandbox_check.py").read_text())
    return next(ast.literal_eval(node.value) for node in tree.body if isinstance(node, ast.Assign)
                and any(isinstance(t, ast.Name) and t.id == "PROBE" for t in node.targets))


class ImportedProbeTest(unittest.TestCase):
    def test_probe_rejects_an_unsandboxed_shell(self):
        # Upstream tests/test_sandbox_check.py at 8cb4374, unchanged; relocated because the
        # offline review-test harness forbids executing /bin/sh.
        with tempfile.TemporaryDirectory() as tmp:
            source, target = Path(tmp) / "input", Path(tmp) / "target"
            source.write_text("nonce\n")
            result = subprocess.run(["/bin/sh", "-c", probe_script(), "probe", str(source), "nonce",
                                     str(target)], capture_output=True, text=True)
            self.assertEqual(result.returncode, 42, "a writable environment must never be reported healthy")


class SandboxCheckCommandTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="sphereceti-sandbox-check-")
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.bin, self.home = self.root / "bin", self.root / "home"
        self.bin.mkdir()
        (self.home / ".codex").mkdir(parents=True)
        (self.home / ".codex/auth.json").write_text('{"tokens": "SUBSCRIPTION-LOGIN-MUST-NOT-BE-SEEDED"}')
        (self.bin / "codex").write_text(f"#!{sys.executable}\n" + FAKE_CODEX)
        (self.bin / "codex").chmod(0o755)
        (self.bin / "mode").write_text("healthy")
        self.storage = self.root / "state"
        self.operator = self.root / "operator.toml"
        self.operator.write_text(f"storage = {json.dumps(str(self.storage))}\n")
        self.env = {**os.environ, "HOME": str(self.home),
                    "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
                    "OPENAI_API_KEY": "provider-secret-must-not-reach-codex",
                    "GH_TOKEN": "github-secret-must-not-reach-codex"}
        for name in ("PYTHONPATH", "CODEX_HOME"):
            self.env.pop(name, None)

    def run_check(self, *extra):
        launcher = [sys.executable, "-c", f"import sys; sys.path.insert(0, {str(ROOT / 'tools/project')!r}); "
                    "from sphereceti.cli import main; sys.exit(main())"]
        return subprocess.run([*launcher, "review-check-sandbox", "--operator-config", str(self.operator), *extra],
                              cwd=self.root, env=self.env, capture_output=True, text=True, timeout=120)

    def calls(self):
        path = self.bin / "codex-calls.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def assert_credential_free(self):
        calls = self.calls()
        self.assertTrue(calls)
        for call in calls:
            env = call["env"]
            self.assertEqual(env.get("OPENAI_API_KEY", ""), "")
            self.assertNotIn("GH_TOKEN", env)
            self.assertFalse(call["auth_seeded"], "the diagnostic must not seed a subscription login")
            rev = self.home / ".tauceti-rev"
            self.assertTrue(Path(env["CODEX_HOME"]).is_relative_to(rev))
            self.assertTrue(Path(env["TMPDIR"]).is_relative_to(rev))
            self.assertNotIn("SUBSCRIPTION-LOGIN", json.dumps(call))
        self.assertEqual(list((self.home / ".tauceti-rev").iterdir()), [])

    def test_comparisons_identify_restored_path_and_private_tmpdir(self):
        result = self.run_check("--compare-path", "--compare-tmpdir")
        self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        report = json.loads(result.stdout)
        self.assertTrue(report["ok"])
        self.assertEqual(report["stage"], "sandbox_probe")
        self.assertTrue(report["path_restoration_fixed_sandbox"])
        self.assertTrue(report["private_tmpdir_fixed_sandbox"])
        self.assertEqual(report["without_path"]["stderr"].strip(), "bubblewrap is unavailable")
        self.assertIn("Read-only file system", report["without_tmpdir"]["stderr"])
        self.assertEqual(report["source"]["commit"], "8cb4374133d429627c31d9835bfe6fc9d71771e9")
        self.assertEqual(report["workspace"], "private_scratch")
        self.assert_credential_free()
        probes = [c for c in self.calls() if "--" in c["argv"]]
        self.assertEqual(len(probes), 3)
        tmpdir = probes[0]["env"]["TMPDIR"]
        self.assertIn("shell_environment_policy.set.TMPDIR=" + json.dumps(tmpdir), probes[0]["argv"])
        # Staged engine and default workspace are removed; nothing else is written.
        self.assertEqual(list((self.storage / "thefundamentaltheor3m__SphereCeti/diagnostics").iterdir()), [])

    def test_real_error_is_reported_without_relaxing_the_sandbox(self):
        (self.bin / "mode").write_text("namespace")
        workspace = self.root / "workspace"
        workspace.mkdir()
        result = self.run_check("--cwd", str(workspace))
        self.assertEqual(result.returncode, 1, result.stderr)
        report = json.loads(result.stdout)
        self.assertFalse(report["ok"])
        self.assertIn("Operation not permitted", report["stderr"])
        self.assertEqual(report["workspace"], "provided")
        self.assertEqual(list(workspace.iterdir()), [])
        self.assert_credential_free()
        self.assertEqual(sum("--" in c["argv"] for c in self.calls()), 1)

    def test_missing_workspace_is_rejected_before_codex(self):
        result = self.run_check("--cwd", str(self.root / "missing"))
        self.assertEqual(result.returncode, 2)
        self.assertIn("--cwd must be an existing directory", result.stderr)
        self.assertEqual(self.calls(), [])


if __name__ == "__main__":
    unittest.main()
