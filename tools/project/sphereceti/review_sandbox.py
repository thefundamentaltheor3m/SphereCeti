"""Credential-free Codex sandbox diagnostic for the local review engine.

Adapts TauCetiReview's `tauceti-review-check-sandbox` (runner/sandbox_check.py, added by
TauCetiReview #194 at 51149da792cd8b28aba617f118d1ae01aefbe501 and extended by #196 at
8cb4374133d429627c31d9835bfe6fc9d71771e9). TauCetiReview contributors, Apache-2.0.

The imported diagnostic runs in a fresh interpreter, like review_bridge.py, with the same
runtime variables a review passes to its engine and no provider key. It seeds no credential,
calls no model, and never contacts GitHub. A failed probe never relaxes the sandbox.
"""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import tempfile

from .local_review import ReviewError, engine_environment
from .review_resources import review_files

SANDBOX_UPSTREAM = "8cb4374133d429627c31d9835bfe6fc9d71771e9"

# runner/ uses flat sibling imports. Load it from the staged copy only, never from cwd.
BOOTSTRAP = r'''
import json, pathlib, sys
sys.path.insert(0, sys.argv[1])
import sandbox_check
report = sandbox_check.diagnose(pathlib.Path(sys.argv[2]), compare_path=sys.argv[3] == "1",
                                compare_tmpdir=sys.argv[4] == "1")
print(json.dumps(report))
'''


def add_parser(commands):
    p = commands.add_parser("review-check-sandbox",
                            help="diagnose Codex sandbox startup without credentials, inference, or GitHub")
    p.add_argument("--cwd", type=Path,
                   help="existing writable review workspace to probe; default: a fresh private "
                        "directory under the operator's review storage, removed afterwards")
    p.add_argument("--compare-path", action="store_true",
                   help="also probe the old empty-PATH environment to isolate launcher failures")
    p.add_argument("--compare-tmpdir", action="store_true",
                   help="also probe the system temporary directory to isolate bookkeeping failures")
    p.add_argument("--operator-config", type=Path, help="preferences only; selects review storage")
    return p


def check_sandbox(args, project, prefs) -> dict:
    if args.cwd is not None and not args.cwd.is_dir():
        raise ReviewError("--cwd must be an existing directory")
    storage = (Path(prefs.storage).expanduser().resolve() / project.repository.replace("/", "__")
               / "diagnostics")
    storage.mkdir(parents=True, exist_ok=True, mode=0o700)
    with tempfile.TemporaryDirectory(prefix="sandbox-check-", dir=storage) as scratch:
        scratch = Path(scratch)
        runner = scratch / "engine" / "runner"
        for name, body in review_files().items():
            if name.startswith("runner/"):
                target = scratch / "engine" / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(body)
        workspace = args.cwd.resolve() if args.cwd is not None else scratch / "workspace"
        workspace.mkdir(exist_ok=True)
        try:
            result = subprocess.run(
                [sys.executable, "-I", "-c", BOOTSTRAP, str(runner), str(workspace),
                 "1" if args.compare_path else "0", "1" if args.compare_tmpdir else "0"],
                env=engine_environment(["codex"], "subscription"), cwd=workspace,
                capture_output=True, text=True, timeout=180)
        except subprocess.TimeoutExpired as error:
            raise ReviewError("sandbox diagnostic timed out") from error
        if result.returncode:
            raise ReviewError("sandbox diagnostic could not start: " + result.stderr.strip()[-2000:])
        try:
            report = json.loads(result.stdout)
        except ValueError as error:
            raise ReviewError("sandbox diagnostic returned no report") from error
    if not isinstance(report, dict) or type(report.get("ok")) is not bool:
        raise ReviewError("sandbox diagnostic returned an invalid report")
    report["source"] = {"repository": "TauCetiProject/TauCetiReview", "commit": SANDBOX_UPSTREAM,
                        "path": "runner/sandbox_check.py"}
    report["workspace"] = "provided" if args.cwd is not None else "private_scratch"
    return report
