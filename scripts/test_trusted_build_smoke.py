#!/usr/bin/env python3
"""CI-only integration smoke for proposed tooling; consumes this checkout's dependency cache.

Unprivileged CI may exercise proposed T. This produces no authoritative statuses and does
not approve T. The separate pull_request_target workflow selects T from approved main.
"""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
from sphereceti.gate import git, prepare
from sphereceti.sandbox import Sandbox, emit_candidate_output

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--toolchain', required=True, type=Path)
args = parser.parse_args()
head = git(ROOT, 'rev-parse', 'HEAD').decode().strip()
base = git(ROOT, 'rev-parse', 'HEAD^').decode().strip()
subprocess.run([sys.executable, '-I', str(ROOT / 'scripts/validate_dependencies.py')], check=True)
with tempfile.TemporaryDirectory(prefix='sphereceti-full-smoke-') as temp:
    candidate = Path(temp) / 'candidate'
    report = prepare(ROOT, head, base, head, candidate)
    assert report['config_attested']
    subprocess.run(['bash', str(ROOT / 'scripts/attest-pr-config.sh'), str(ROOT),
                    str(candidate), head, 'pull_request_target', '1', '0'], check=True)
    # CI has finished its ordinary build. Move, rather than duplicate, multi-GB dependencies.
    # No candidate root artifacts are copied; the temp tree and dependencies are then discarded.
    shutil.move(str(ROOT / '.lake/packages'), str(candidate / '.lake/packages'))
    result = Sandbox(ROOT, candidate, args.toolchain).build()
    emit_candidate_output(result.stdout + result.stderr)
    assert result.returncode == 0, f'full candidate smoke failed: {result.returncode}'
print('Full candidate smoke passed: raw immutable tree, attestation, staged D, and sandbox build.')
