#!/usr/bin/env python3
"""Data-only publication contracts adapted from pinned TauCeti Pages/cache operations.

TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
.github/workflows/{pages,publish-lake-cache,nightly-verify}.yml and
scripts/lake_cache_probe.py (Apache-2.0; TauCeti contributors).
No artifact is imported, executed, or extracted by this module.
"""
from __future__ import annotations

import argparse
import hashlib
import html
import json
from pathlib import Path
import re
import stat
import urllib.parse

REPOSITORY = 'thefundamentaltheor3m/SphereCeti'
TOOLCHAIN = 'leanprover/lean4:v4.34.0-rc1'
PLATFORM = 'x86_64-unknown-linux-gnu'
SHA = re.compile(r'[0-9a-f]{40}\Z')
HASH = re.compile(r'[0-9a-f]{16}\Z')
ARTIFACT = re.compile(r'[0-9a-f]{16}\.ltar\Z')
MAX_BYTES = 512 * 1024 * 1024


class PublicationError(ValueError):
    pass


def regular(path: Path, limit=MAX_BYTES) -> bytes:
    mode = path.lstat()
    if not stat.S_ISREG(mode.st_mode) or mode.st_nlink != 1 or mode.st_size > limit:
        raise PublicationError(f'expected bounded regular file: {path.name}')
    return path.read_bytes()


def revision(value):
    if not isinstance(value, str) or not SHA.fullmatch(value):
        raise PublicationError('expected exact lowercase Git revision')
    return value


def digest(data):
    return hashlib.sha256(data).hexdigest()


def json_bytes(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def marker(path):
    data = regular(path, 41)
    if len(data) != 41 or data[-1:] != b'\n':
        raise PublicationError('SOURCE_SHA must be exactly a revision plus newline')
    return revision(data[:-1].decode('ascii'))


def read_map(data):
    if len(data) > 8 * 1024 * 1024:
        raise PublicationError('oversized Lake map')
    lines = data.decode('utf-8').splitlines()
    if len(lines) < 2 or json.loads(lines[0]) != '2026-03-17':
        raise PublicationError('unsupported or empty pinned Lake map')
    inputs, outputs = set(), set()
    for line in lines[1:]:
        pair = json.loads(line)
        if (not isinstance(pair, list) or len(pair) != 2 or
                not isinstance(pair[0], str) or not HASH.fullmatch(pair[0]) or
                not isinstance(pair[1], str) or not ARTIFACT.fullmatch(pair[1]) or pair[0] in inputs):
            raise PublicationError('invalid or duplicate Lake output mapping')
        inputs.add(pair[0])
        outputs.add(pair[1])
    return outputs


def validate_staging(stage: Path):
    if stage.is_symlink() or not stage.is_dir():
        raise PublicationError('staging must be a real directory')
    data = regular(stage / 'outputs.jsonl', 8 * 1024 * 1024)
    names = read_map(data) | {'outputs.jsonl'}
    if {p.name for p in stage.iterdir()} != names:
        raise PublicationError('staging contains missing, extra, or nested entries')
    total, hashes = 0, {}
    for name in sorted(names):
        payload = regular(stage / name)
        total += len(payload)
        if total > MAX_BYTES:
            raise PublicationError('staging exceeds publication size limit')
        hashes[name] = digest(payload)
    return hashes


def endpoint(value):
    p = urllib.parse.urlsplit(value)
    if (p.scheme != 'https' or not p.hostname or p.username is not None or p.password is not None
            or p.query or p.fragment or any(c.isspace() or ord(c) < 32 for c in value)
            or any(part in ('.', '..') for part in urllib.parse.unquote(p.path).split('/'))):
        raise PublicationError('expected plain HTTPS storage endpoint')
    host = p.hostname.rstrip('.')
    if host == 'taucetiproject.org' or host.endswith('.taucetiproject.org'):
        raise PublicationError('SphereCeti uploads require its own storage authority')
    return value.rstrip('/')


def map_url(base, sha):
    return (f'{endpoint(base)}/{REPOSITORY}/pt/{PLATFORM}/tc/'
            f'{TOOLCHAIN.replace("/", "--").replace(":", "---")}/{revision(sha)}.jsonl')


def render_docs(destination: Path, sha: str, report: dict, inventory: list[dict], dependencies: dict):
    """Render the compiled inventory, never declarations inferred by parsing Lean source."""
    revision(sha)
    if report['verdict']['passed'] is not True:
        raise PublicationError('refusing documentation for failed audits')
    modules = {m['name']: m for m in inventory if m['kind'] in ('library', 'roadmap')}
    compiled = report['compiled']
    if {m['name'] for m in compiled['modules']} != modules.keys():
        raise PublicationError('compiled/source coverage mismatch')
    rows, seen = [], set()
    for d in compiled['declarations']:
        if d['moduleName'] not in modules or d['name'] in seen:
            raise PublicationError('foreign or duplicate compiled declaration')
        seen.add(d['name'])
        m = modules[d['moduleName']]
        section = 'targets' if m['kind'] == 'roadmap' else 'library'
        # Stable opaque anchors avoid collisions and HTML/URL injection in Lean names.
        anchor = 'd-' + digest(d['name'].encode())
        status = ('roadmap-target' if section == 'targets' else
                  'admission-dependent' if 'sorryAx' in d['axioms'] else 'audited-library-declaration')
        rows.append({**d, 'kind': m['kind'], 'status': status,
                     'url': f'{section}/index.html#{anchor}',
                     'source_url': f'https://github.com/{REPOSITORY}/blob/{sha}/{m["path"]}'})
    rows.sort(key=lambda d: d['name'])
    destination.mkdir(parents=True, exist_ok=False)
    (destination / 'SOURCE_SHA').write_text(sha + '\n')
    evidence = {'schema_version': 1, 'repository': REPOSITORY, 'source_revision': sha,
                'toolchain': TOOLCHAIN, 'dependencies': dependencies,
                'production_repository': 'thefundamentaltheor3m/Sphere-Packing-Lean',
                'production_evidence': False, 'audit_sha256': digest(json_bytes(report)),
                'declarations': rows}
    (destination / 'declarations.json').write_bytes(json_bytes(evidence))
    (destination / 'audit.json').write_bytes(json_bytes(report))
    def page(title, body):
        return ('<!doctype html><html lang="en"><meta charset="utf-8">'
                '<meta name="viewport" content="width=device-width"><title>' + html.escape(title) +
                '</title><body><main><h1>' + html.escape(title) + '</h1><p>Source: <a href="https://github.com/' +
                REPOSITORY + '/tree/' + sha + '">' + sha[:7] + '</a></p>' + body + '</main></body></html>\n')
    for section, title, label in [('library', 'Audited library declarations', 'Library inventory; this is not a claim of completed production proofs.'),
                                  ('targets', 'Roadmap targets', 'Proposed target signatures, including admitted declarations. These are not proved milestones.')]:
        (destination / section).mkdir()
        body = '<p>' + label + '</p><p><a href="../index.html">Overview</a></p><ul>'
        for d in rows:
            if d['url'].split('/')[0] != section:
                continue
            body += ('<li id="' + d['url'].split('#')[1] + '"><code>' + html.escape(d['name']) +
                     '</code> — ' + html.escape(d['status']) + '<br>Module: ' + html.escape(d['moduleName']) +
                     '; axioms: ' + html.escape(', '.join(d['axioms']) or 'none') +
                     ' · <a href="' + html.escape(d['source_url'], quote=True) + '">source</a></li>')
        (destination / section / 'index.html').write_text(page(title, body + '</ul>'))
    (destination / 'index.html').write_text(page('SphereCeti declaration reference',
        '<p>Compiled declaration and axiom inventory for the roadmap package. '
        'Production proofs live in Sphere-Packing-Lean. This reference provides names, axiom dependencies, '
        'and source links; it does not render full Lean types or replace doc-gen4.</p>'
        '<ul><li><a href="library/index.html">Audited library declarations</a></li>'
        '<li><a href="targets/index.html">Roadmap targets — not proof achievements</a></li></ul>'
        '<p><a href="declarations.json">Machine-readable evidence</a> · '
        '<a href="SOURCE_SHA">Documented revision</a> · <a href="audit.json">Compiled audit</a></p>'))
    return evidence


def verify_bundle(root, sha):
    """Check cross-job bytes; these hashes bind data, not proof of arbitrary producer execution."""
    revision(sha)
    if root.is_symlink() or {p.name for p in root.iterdir()} != {'docs', 'cache', 'publication.json'}:
        raise PublicationError('unexpected publication root entries')
    manifest = json.loads(regular(root / 'publication.json', 8 * 1024 * 1024))
    if (set(manifest) != {'schema_version', 'repository', 'source_revision', 'toolchain', 'platform', 'files'} or
            type(manifest['schema_version']) is not int or manifest['schema_version'] != 1 or
            manifest['repository'] != REPOSITORY or manifest['source_revision'] != sha or
            manifest['toolchain'] != TOOLCHAIN or manifest['platform'] != PLATFORM):
        raise PublicationError('publication identity mismatch')
    actual = {}
    for folder in ('docs', 'cache'):
        base = root / folder
        if base.is_symlink() or not base.is_dir():
            raise PublicationError('invalid publication folder')
        for path in base.rglob('*'):
            if path.is_symlink():
                raise PublicationError('symlink in publication bundle')
            if path.is_dir():
                continue
            actual[path.relative_to(root).as_posix()] = digest(regular(path))
    if actual != manifest['files']:
        raise PublicationError('publication bytes differ from manifest')
    expected_docs = {'SOURCE_SHA', 'index.html', 'library/index.html', 'targets/index.html', 'declarations.json', 'audit.json'}
    if {p.removeprefix('docs/') for p in actual if p.startswith('docs/')} != expected_docs:
        raise PublicationError('unexpected documentation paths')
    if marker(root / 'docs/SOURCE_SHA') != sha:
        raise PublicationError('documentation cursor differs from build revision')
    evidence = json.loads(regular(root / 'docs/declarations.json'))
    if evidence['source_revision'] != sha or evidence['repository'] != REPOSITORY or evidence['production_evidence'] is not False:
        raise PublicationError('invalid documentation evidence identity')
    validate_staging(root / 'cache')
    return manifest


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='command', required=True)
    v = sub.add_parser('verify'); v.add_argument('bundle', type=Path); v.add_argument('revision')
    c = sub.add_parser('endpoints'); c.add_argument('artifact'); c.add_argument('revision'); c.add_argument('public'); c.add_argument('sha')
    args = p.parse_args()
    if args.command == 'verify':
        verify_bundle(args.bundle, args.revision)
        print('publication bundle validated (data only)')
    else:
        endpoint(args.artifact); endpoint(args.revision)
        print(map_url(args.public, args.sha))


if __name__ == '__main__':
    main()
