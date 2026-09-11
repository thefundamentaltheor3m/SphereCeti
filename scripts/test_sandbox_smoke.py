#!/usr/bin/env python3
"""Required hosted positive sandbox test; never silently skips unavailable isolation."""
import argparse
import os
from pathlib import Path
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
from sphereceti.sandbox import Sandbox, emit_candidate_output

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--toolchain', required=True, type=Path)
args = parser.parse_args()
with tempfile.TemporaryDirectory(prefix='sphereceti-sandbox-smoke-') as temp:
    candidate = Path(temp) / 'candidate'
    candidate.mkdir()
    (candidate / '.lake').mkdir()
    (candidate / 'lean-toolchain').write_bytes((ROOT / 'lean-toolchain').read_bytes())
    (candidate / 'lakefile.toml').write_text('''name = "sandbox_smoke"
version = "0.0.0"
[[lean_lib]]
name = "SphereCeti"
[[lean_lib]]
name = "SphereCetiRoadmap"
''')
    (candidate / 'lake-manifest.json').write_text('{"version":"1.2.0","packagesDir":".lake/packages","packages":[],"name":"sandbox_smoke","lakeDir":".lake"}\n')
    (candidate / 'SphereCeti.lean').write_text('''-- A build-time fixture, not roadmap mathematics.
#eval do
  let token ← IO.getEnv "GH_TOKEN"
  if token.isSome then throw (IO.userError "credential entered sandbox")
  IO.FS.writeFile ".lake/lean-ran" "sandboxed"
''')
    (candidate / 'SphereCetiRoadmap.lean').write_text('-- Empty fixture roadmap.\n')
    # Neither this candidate helper nor any candidate Python is part of the trusted build.
    (candidate / 'scripts').mkdir()
    (candidate / 'scripts/sandbox-build.sh').write_text('exit 91\n')
    box = Sandbox(ROOT, candidate, args.toolchain)
    os.environ['GH_TOKEN'] = 'sandbox-smoke-host-secret'
    result = box.build()
    emit_candidate_output(result.stdout + result.stderr)
    assert result.returncode == 0, f'hosted sandbox build failed: {result.returncode}'
    assert (candidate / '.lake/lean-ran').read_text() == 'sandboxed'
print('Sandbox smoke passed: isolation probes and actual Lean candidate build.')
