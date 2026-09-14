"""Disposable Git sources and fake provider for source and fresh-install integration tests."""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


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
        for name in ("automation.toml", "audits.json"):
            shutil.copy2(ROOT / "policy" / name, self.repo / "policy" / name)
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
        self.env = {**os.environ, "HOME": str(self.home), "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
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
