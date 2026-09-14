#!/usr/bin/env python3
"""Mandatory hosted test: complete profiler on disposable, exact Lean revisions."""
import argparse
import json
import os
from pathlib import Path
import shutil
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
sys.path.insert(0, str(ROOT / 'tests'))
from sphereceti.profile_runner import run
from profiling_fixture import commit, fixture

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--toolchain', type=Path, required=True)
args = parser.parse_args()
with tempfile.TemporaryDirectory(prefix='sphereceti-profile-smoke-') as temp:
    root = Path(temp)
    repo = root / 'repo'
    base, head = fixture(repo)
    dependencies = root / 'dependencies'
    dependencies.mkdir()
    sentinel = dependencies / 'read-only-canary'
    sentinel.write_text('keep')
    # A source-time effect verifies isolation on prebuild AND direct re-elaboration.
    source = repo / 'SphereCeti/Basic.lean'
    source.write_text(source.read_text() + '''
#eval show IO Unit from do
  if (← IO.getEnv "GH_TOKEN").isSome then throw (IO.userError "credential leaked")
  let writable ← try
    IO.FS.writeFile ".lake/packages/read-only-canary" "changed"
    pure true
  catch _ => pure false
  if writable then throw (IO.userError "dependency write allowed")
  IO.FS.writeFile ".lake/ran" "yes"
''')
    head = commit(repo)
    os.environ['GH_TOKEN'] = 'host-only-profile-canary'
    report = run(repo, head, base, head, root / 'success', args.toolchain, dependencies)
    assert report['state'] == 'complete', json.dumps(report)
    assert len(report['samples']) == 2
    assert all(row['cpu_seconds'] >= 0 for row in report['samples'])
    assert sentinel.read_text() == 'keep'
    assert (root / 'success/head/.lake/ran').read_text() == 'yes'
    assert (root / 'success/report.md').is_file()
    source.write_text('this is intentionally invalid Lean\n')
    bad = commit(repo)
    report = run(repo, head, head, bad, root / 'failure', args.toolchain, dependencies)
    assert report['state'] == 'error'
    assert report['rows'][0]['errors'] == ['head: missing or failed measurement']
    assert not report['rows'][0]['flagged']
    # Exercise the real pinned TauCeti/Mathlib graph without copying multi-GB caches.
    # This must run before test_trusted_build_smoke.py moves the CI dependency tree.
    graph = root / 'graph'
    fixture(graph)
    for path in ('lakefile.toml', 'lake-manifest.json', 'SphereCeti.lean',
                 'SphereCetiRoadmap.lean', 'SphereCeti/Basic.lean'):
        shutil.copyfile(ROOT / path, graph / path)
    graph_base = commit(graph)
    source = graph / 'SphereCeti/Basic.lean'
    source.write_text(source.read_text() + '\n-- Disposable profiling comparison.\n')
    graph_head = commit(graph)
    report = run(graph, graph_head, graph_base, graph_head, root / 'pinned-graph',
                 args.toolchain, ROOT / '.lake/packages')
    assert report['state'] == 'complete', json.dumps(report)
    assert len(report['samples']) == 2
print('Profiling smoke passed: exact Lean revisions, host counters, read-only pinned graph, explicit failure.')
