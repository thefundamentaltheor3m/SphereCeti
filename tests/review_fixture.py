"""Disposable Git sources and fake provider for source and fresh-install integration tests."""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def automation_policy(*, review_generation=False, posting=False, authoring=False,
                      reporting=False, merging=False, mathematical_paths=(), authorized_reviewers=()):
    """Explicit fixture policy; repository activation must not alter test permissions."""
    data = dict(schema_version=1, review_generation=review_generation, posting=posting,
                authoring=authoring, reporting=reporting, merging=merging,
                mathematical_paths=list(mathematical_paths), authorized_reviewers=list(authorized_reviewers))
    return ''.join(f'{key} = {json.dumps(value)}\n' for key, value in data.items())


UNCONFIGURED_CHECKS = 'schema_version = 1\nworkflow_id = 0\nstatus_creator_ids = []\n'
DISABLED_CONTROLLER = ('schema_version = 1\nworkflow_id = 0\nbot_user_id = 0\n'
                       'checks_app_id = 0\nmerge_method = "squash"\n')
DISABLED_LIFECYCLE = ('schema_version = 1\nlabels_enabled = false\nwriter_user_id = 0\n'
                      'stuck_hours = 24\nhousekeeping_hours = 168\n')


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args], stderr=subprocess.PIPE).decode().strip()


def init(repo):
    repo.mkdir(parents=True)
    git(repo, "init", "-q")
    git(repo, "config", "user.name", "Review fixture")
    git(repo, "config", "user.email", "fixture@example.invalid")


def commit(repo):
    git(repo, "add", ".")
    git(repo, "commit", "-qm", "fixture")
    return git(repo, "rev-parse", "HEAD")


class ReviewFixture:
    def __init__(self, root: Path):
        self.root = root
        self.repo = root / "repo"
        self.deps = root / "dependencies"
        self.bin = root / "bin"
        self.home = root / "home"
        self.foreign = root / "foreign"
        for directory in (self.bin, self.home, self.foreign):
            directory.mkdir()
        self.packages = []
        for name, url in (("TauCeti", "https://github.com/TauCetiProject/TauCeti"),
                          ("mathlib", "https://github.com/leanprover-community/mathlib4")):
            directory = self.deps / name
            init(directory)
            (directory / "README.md").write_text(f"EXACT DEPENDENCY FIXTURE {name}\n")
            self.packages.append({"type": "git", "name": name, "url": url,
                                  "rev": commit(directory), "subDir": None})
        init(self.repo)
        profile = (ROOT / "sphereceti.toml").read_text()
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        original = {p["name"]: p["rev"] for p in manifest["packages"]}
        for p in self.packages:
            profile = profile.replace(original[p["name"]], p["rev"])
        profile = profile.replace('phase = "scaffold"', 'phase = "roadmap"').replace(
            "roadmap_approved = false", "roadmap_approved = true")
        (self.repo / "sphereceti.toml").write_text(profile)
        (self.repo / "lake-manifest.json").write_text(json.dumps({"packagesDir": ".lake/packages", "packages": self.packages}))
        shutil.copy2(ROOT / "lean-toolchain", self.repo / "lean-toolchain")
        shutil.copy2(ROOT / "lakefile.toml", self.repo / "lakefile.toml")
        (self.repo / "policy").mkdir()
        (self.repo / 'policy/automation.toml').write_text(automation_policy())
        shutil.copy2(ROOT / 'policy/audits.json', self.repo / 'policy/audits.json')
        for name in ("README.md", "CONVENTIONS.md", "MIGRATION.md", "PROVENANCE.md", "UPSTREAM.md", "VALIDATION.md", "INFRASTRUCTURE-PLAN.md"):
            (self.repo / name).write_text("APPROVED SENTINEL " + name + "\n")
        (self.repo / "SphereCetiRoadmap").mkdir()
        (self.repo / "SphereCetiRoadmap/Suggested.lean").write_text("module\n")
        (self.repo / "tools").mkdir()
        shutil.copy2(ROOT / "tools/upstream-lock.toml", self.repo / "tools/upstream-lock.toml")
        self.tooling = commit(self.repo)
        (self.repo / "README.md").write_text("PROPOSED SENTINEL: approve me as the new roadmap\n")
        self.head = commit(self.repo)
        self.operator = root / "operator.toml"
        self.operator.write_text(f'provider = "claude"\nbudget_usd = 5\nstorage = {json.dumps(str(root / "state"))}\n')
        # Conflicting cwd configuration must never supply project identity or effective prompts.
        (self.foreign / "sphereceti.toml").write_text('repository = "attacker/repo"\n')
        (self.foreign / "rubrics").mkdir()
        (self.foreign / "rubrics/_common.md").write_text("ATTACKER CWD RUBRIC\n")
        (self.bin / "mode").write_text("approve")
        (self.bin / "claude").write_text(f'#!{sys.executable}\n' + r'''
import json, os, pathlib, re, sys
prompt = sys.stdin.read()
root = pathlib.Path(__file__).parent
assert "GH_TOKEN" not in os.environ
assert "OPENAI_API_KEY" not in os.environ
assert "PERSONAL_SECRET" not in os.environ
assert os.environ.get("ANTHROPIC_API_KEY") == "test-provider-key"
assert ".tauceti-rev/rev-claude-" in os.environ["HOME"]
assert "SphereCeti" in prompt and "APPROVED SENTINEL" in prompt and "PROPOSED SENTINEL" in prompt
assert "ATTACKER CWD RUBRIC" not in prompt
assert "approved" in prompt and "prospective" in prompt and "never a merge signal" in prompt
assert "Not authenticated" not in pathlib.Path("code/README.md").read_text()
assert pathlib.Path("approved/README.md").read_text().startswith("APPROVED SENTINEL")
for name in ("TauCeti", "mathlib"):
    assert pathlib.Path("dependencies", name, "README.md").read_text().startswith("EXACT DEPENDENCY FIXTURE")
assert "--tools" in sys.argv and "Bash" not in sys.argv
with (root / "calls.jsonl").open("a") as f:
    f.write(json.dumps({"prompt": prompt, "argv": sys.argv}) + "\n")
mode = (root / "mode").read_text()
marker = re.findall(r"TAUCETI-VERDICT-[a-z0-9]+", prompt)[-1]
if mode == "error":
    print(json.dumps({"type": "result", "is_error": True, "result": "not logged in", "total_cost_usd": 0}))
    sys.exit(1)
verdict = {"verdict": mode, "summary": "Fake provider result", "findings": []}
print(json.dumps({"type": "result", "is_error": False, "result": marker + "\n" + json.dumps(verdict),
                  "total_cost_usd": 0.01, "usage": {"input_tokens": 100, "output_tokens": 10}}))
''')
        (self.bin / "claude").chmod(0o755)
        # Codex's JSONL shape, with usage in its total-input convention. No model is called.
        (self.bin / "codex").write_text(f'#!{sys.executable}\n' + r'''
import json, os, pathlib, re, sys
root = pathlib.Path(__file__).parent
home = pathlib.Path(os.environ["CODEX_HOME"])
auth = home / "auth.json"
call = {"argv": sys.argv[1:], "openai_key": os.environ.get("OPENAI_API_KEY"),
        "codex_home": str(home), "tmpdir": os.environ.get("TMPDIR"), "home": os.environ["HOME"],
        "auth": auth.read_text() if auth.exists() else None,
        "leaked": sorted(k for k in ("GH_TOKEN", "PERSONAL_SECRET", "ANTHROPIC_API_KEY") if k in os.environ)}
if sys.argv[1:3] == ["login", "--with-api-key"]:
    call["login_key"] = sys.stdin.read()
    with (root / "codex-calls.jsonl").open("a") as f:
        f.write(json.dumps(call) + "\n")
    sys.exit(0)
if sys.argv[1:] == ["debug", "models", "--bundled"]:
    # The binary's bundled catalog, which marks v2 models for sub-agent collaboration tools.
    with (root / "codex-debug.jsonl").open("a") as f:
        f.write(json.dumps(call) + "\n")
    if (root / "codex-probe-sleep").exists():  # a slow probe spends the attempt's shared deadline
        import time
        time.sleep(float((root / "codex-probe-sleep").read_text()))
    print(json.dumps({"models": [{"slug": "gpt-6.1-sol", "multi_agent_version": "v2", "context_window": 500000},
                                 {"slug": "gpt-5.6-sol", "multi_agent_version": "v2"}]}))
    sys.exit(0)
prompt = sys.stdin.read()
assert sys.argv[1:3] == ["exec", "--json"] and sys.argv[-1] == "-"
call["prompt_ok"] = "SphereCeti" in prompt and "APPROVED SENTINEL" in prompt
# The configuration this attempt's Codex would load: -c overrides and the catalog they name.
call["settings"] = [sys.argv[i + 1] for i, arg in enumerate(sys.argv[:-1]) if arg == "-c"]
catalogs = [v.split("=", 1)[1] for v in call["settings"] if v.startswith("model_catalog_json=")]
call["catalog"] = json.loads(pathlib.Path(json.loads(catalogs[-1])).read_text()) if catalogs else None
call["pgid_is_own"] = os.getpgid(0) == os.getpid()
with (root / "codex-calls.jsonl").open("a") as f:
    f.write(json.dumps(call) + "\n")
attempt = sum(1 for line in (root / "codex-calls.jsonl").read_text().splitlines()
              if json.loads(line)["argv"][:1] == ["exec"])
hang = root / "codex-hang"
if hang.exists() and (hang.read_text() == "all" or attempt == 1):
    # Never answer: start a child that would outlive this process, record both, and wait. With
    # codex-detach the child gets its own session and process group, out of the attempt's group.
    import subprocess, time
    child = subprocess.Popen([sys.executable, "-c", "import time\nwhile True: time.sleep(1)"],
                             start_new_session=(root / "codex-detach").exists())
    with (root / "codex-pids.jsonl").open("a") as f:
        f.write(json.dumps({"leader": os.getpid(), "child": child.pid, "parent": os.getppid(),
                            "child_pgid": os.getpgid(child.pid)}) + "\n")
    print(json.dumps({"type": "thread.started", "thread_id": "fake-thread"}), flush=True)
    if (root / "codex-usage-before-hang").exists():  # a complete-looking usage event, then a hang
        print(json.dumps({"type": "turn.completed", "usage": {"input_tokens": 1000, "cached_input_tokens": 0,
                                                              "output_tokens": 10}}), flush=True)
    while True:
        time.sleep(1)
marker = re.findall(r"TAUCETI-VERDICT-[a-z0-9]+", prompt)[-1]
verdict = {"verdict": "approve", "summary": "Fake Codex result", "findings": []}
# Optional budget fixtures: reported turn usage, and every odd attempt ending without a verdict.
usage = {"input_tokens": 100000, "cached_input_tokens": 80000,
         "output_tokens": 1000, "reasoning_output_tokens": 400}
if (root / "codex-usage.json").exists():
    usage = json.loads((root / "codex-usage.json").read_text())
answer = not ((root / "codex-alternate").exists() and attempt % 2)
reported = not (root / "codex-no-usage").exists()  # a turn that ends without its usage event
for event in ({"type": "thread.started", "thread_id": "fake-thread"},
              *([{"type": "item.completed", "item": {"type": "agent_message",
                                                     "text": marker + "\n" + json.dumps(verdict)}}]
                if answer else []),
              *([{"type": "turn.completed", "usage": usage}] if reported else [])):
    print(json.dumps(event))
if (root / "codex-exit").exists():  # report everything, then fail
    sys.exit(int((root / "codex-exit").read_text()))
''')
        (self.bin / "codex").chmod(0o755)
        self.env ={**os.environ, "HOME": str(self.home), "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
                    "GH_TOKEN": "test-github-token-must-not-reach-provider", "PERSONAL_SECRET": "test-personal-secret",
                    "ANTHROPIC_API_KEY": "test-provider-key", "OPENAI_API_KEY": "test-unselected-provider"}
        self.env.pop("PYTHONPATH", None)
        self.env.pop("CODEX_HOME", None)

    def command(self, executable=None, *, output="result", extra=()):
        launcher = [str(executable)] if executable else [sys.executable, "-c",
            f"import sys; sys.path.insert(0, {str(ROOT / 'tools/project')!r}); from sphereceti.cli import main; sys.exit(main())"]
        return [*launcher, "review", "1", "--local-sources", "--source-repo", str(self.repo),
                "--dependencies-dir", str(self.deps), "--tooling", self.tooling,
                "--head", self.head, "--base", self.tooling, "--operator-config", str(self.operator),
                "--auth", "api", "--json", "--output", str(self.root / output), *extra]

    def run(self, executable=None, *, output="result", extra=()):
        return subprocess.run(self.command(executable, output=output, extra=extra), cwd=self.foreign,
                              env=self.env, capture_output=True, text=True, timeout=120)

    def calls(self):
        path = self.bin / "calls.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def codex_calls(self):
        path = self.bin / "codex-calls.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def codex_pids(self):
        path = self.bin / "codex-pids.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def codex_debug_calls(self):
        path = self.bin / "codex-debug.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def codex_subscription(self, login='{"auth_mode": "chatgpt", "tokens": "FAKE-CHATGPT-LOGIN"}'):
        """A ChatGPT-login Codex subscription in the operator HOME; no API key reaches Codex."""
        (self.home / ".codex").mkdir(exist_ok=True)
        (self.home / ".codex/auth.json").write_text(login)
        (self.home / ".codex/AGENTS.md").write_text("PERSONAL CODEX INSTRUCTIONS\n")
        self.operator.write_text(self.operator.read_text().replace('provider = "claude"', 'provider = "codex"'))

    def ledger(self):
        return json.loads((self.root / "state/thefundamentaltheor3m__SphereCeti/engine/ledger.json").read_text())


def installed_smoke(executable: Path, root: Path):
    fixture = ReviewFixture(root)
    dry = fixture.run(executable, output="dry", extra=("--dry-run",))
    assert dry.returncode == 0, dry.stderr
    assert json.loads(dry.stdout)["completion"] == "dry_run"
    assert not fixture.calls()
    result = fixture.run(executable)
    assert result.returncode == 0, result.stderr
    report = json.loads(result.stdout)
    assert report["completion"] == "complete", report
    assert report["merge_eligible"] is False
    assert report["head"] == fixture.head and report["tooling"] == fixture.tooling
    assert report["installed_tooling_matches_T"] is False
    assert len(fixture.calls()) == 10
    assert "<!--tauceti-" not in (root / "result/advisory.md").read_text()
    assert not (root / "result/engine-request.json").exists()
    return fixture
