#!/usr/bin/env python3
"""Run the pinned TauCetiReview test scripts with no external calls or credentials.

The upstream scripts own their assertions and exit codes; unittest discovery would silently
skip their function-based checks. Use one fresh interpreter per script to isolate their mocks.
This audit hook detects accidental external calls in cooperative tests, not hostile Python.
"""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REVIEW = ROOT / "tools" / "review"

CHILD = r'''
from pathlib import Path
import runpy
import sys

sys.path.insert(0, str(Path(sys.argv[1]).parent))

blocked = []
class ExternalCall(BaseException):
    pass

def guard(event, args):
    if event.startswith(("subprocess.", "socket.", "os.exec", "os.spawn", "os.posix_spawn")) or event in (
        "os.system", "os.fork", "os.forkpty", "pty.spawn",
    ):
        blocked.append(event)
        raise ExternalCall("offline review tests forbid " + event)

sys.addaudithook(guard)
try:
    runpy.run_path(sys.argv[1], run_name="__main__")
finally:
    if blocked:
        raise SystemExit("external call attempted: " + ", ".join(blocked))
'''


def run_script(path: Path, *, upstream: bool = False) -> subprocess.CompletedProcess:
    with tempfile.TemporaryDirectory(prefix="sphereceti-review-test-") as scratch:
        if upstream:
            # Upstream tests inspect their own tree, including historical workflow examples.
            # Materialize those examples only here; they are never SphereCeti workflows.
            staged = Path(scratch) / "source"
            for directory in ("runner", "rubrics", "tests"):
                shutil.copytree(REVIEW / directory, staged / directory,
                                ignore=shutil.ignore_patterns("__pycache__"))
            shutil.copytree(REVIEW / "fixtures" / "workflows", staged / ".github" / "workflows")
            path = staged / "tests" / path.name
        return subprocess.run(
            [sys.executable, "-I", "-B", "-c", CHILD, str(path)],
            cwd=scratch,
            env={"HOME": scratch, "TMPDIR": scratch, "PATH": "/nonexistent", "LANG": "C.UTF-8"},
            capture_output=True, text=True, timeout=120,
        )


def main() -> int:
    scripts = sorted((REVIEW / "tests").glob("test_*.py"))
    if not scripts:
        raise SystemExit("missing upstream review tests")
    for path in scripts:
        result = run_script(path, upstream=True)
        if result.returncode:
            print(result.stdout)
            print(result.stderr, file=sys.stderr)
            raise SystemExit(f"failed: {path.name} ({result.returncode})")
        print(f"passed: {path.name}", flush=True)
    print(f"{len(scripts)} upstream test scripts passed; external calls forbidden")
    return 0


if __name__ == "__main__":
    sys.exit(main())
