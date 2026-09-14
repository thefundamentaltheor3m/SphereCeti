#!/usr/bin/env python3
"""Build audited documentation and a library-only native Lake staging bundle, without secrets.

Run under `lake env` so Lean's source parser sees the pinned dependency graph.
"""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from check_audits import audit
from check_modules import check
from publication import (PLATFORM, REPOSITORY, TOOLCHAIN, PublicationError, digest, json_bytes,
                         render_docs, revision, validate_staging, verify_bundle)


def run(args, **kw):
    return subprocess.check_output(args, cwd=ROOT, text=True, **kw).strip()


def clean_revision():
    sha = revision(run(['git', 'rev-parse', 'HEAD']))
    if run(['git', 'status', '--porcelain', '--untracked-files=all']):
        raise PublicationError('publication requires a clean committed source tree')
    if (ROOT / 'lean-toolchain').read_text() != TOOLCHAIN + '\n':
        raise PublicationError('toolchain differs from reviewed publication contract')
    return sha


def build(output: Path, source=False):
    sha = clean_revision()
    if output.exists() or output.is_symlink():
        raise PublicationError('output must be a fresh directory')
    if source:
        # Dependency caches remain pinned bootstrap inputs. The independently rebuilt scope is
        # every SphereCeti source, not Lean/Mathlib/TauCeti or every historical served artifact.
        for name in ('build', 'cache'):
            path = ROOT / '.lake' / name
            if path.is_symlink() or (path.exists() and any(path.iterdir())):
                raise PublicationError('source verification requires empty project build/cache directories')
    output.mkdir(parents=True)
    os.environ.update(LAKE_ARTIFACT_CACHE='true', LAKE_RESTORE_ARTIFACTS='false' if source else 'true',
                      LAKE_NO_CACHE='true', LAKE_CACHE_DIR=str(ROOT / '.lake/cache'))
    run([sys.executable, '-I', str(ROOT / 'scripts/validate_dependencies.py')])
    audit_path = ROOT / '.lake/publication-audit.json'
    audit(ROOT, ROOT / 'policy/audits.json', audit_path)
    modules = check(ROOT)['modules']
    report = json.loads(audit_path.read_text())
    config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    if any(config.get(k, False) for k in ('platformIndependent', 'fixedToolchain', 'bootstrap')):
        raise PublicationError('Lake scope changed; review publisher platform/toolchain contract')
    # Explicit library targets exclude roadmap admissions, audit tools, fixtures, dependencies,
    # native executables, and incidental outputs. --no-build prevents another elaboration here.
    targets = ['+' + m['name'] + ':olean' for m in modules if m['kind'] == 'library']
    mappings = ROOT / '.lake/publication-outputs.jsonl'
    run(['lake', 'build', '--no-build', *targets, '-o', str(mappings)])
    run(['lake', 'cache', 'stage', str(mappings), str(output / 'cache')])
    validate_staging(output / 'cache')
    dependencies = json.loads((ROOT / 'lake-manifest.json').read_text())
    render_docs(output / 'docs', sha, report, modules, dependencies)
    if clean_revision() != sha:
        raise PublicationError('source changed while building publication')
    run([sys.executable, '-I', str(ROOT / 'scripts/validate_dependencies.py')])
    files = {p.relative_to(output).as_posix(): digest(p.read_bytes())
             for folder in ('cache', 'docs') for p in (output / folder).rglob('*') if p.is_file()}
    (output / 'publication.json').write_bytes(json_bytes({
        'schema_version': 1, 'repository': REPOSITORY, 'source_revision': sha,
        'toolchain': TOOLCHAIN, 'platform': PLATFORM, 'files': files}))
    verify_bundle(output, sha)
    print(f'Built documentation and library cache for {sha}; source verification: {source}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--source', action='store_true')
    args = parser.parse_args()
    build(args.output.resolve(), args.source)
