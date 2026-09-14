"""Advisory exact-revision profiling, adapted from TauCeti (Apache-2.0).

TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5:
scripts/perf/{manifest,report}.py and .github/workflows/pr-profile.yml.
Credit: TauCeti contributors. SphereCeti uses Git trees, CPU-only local reports,
explicit missing-data errors, and separate library/roadmap labels.
"""
from __future__ import annotations

import hashlib
import html
import json
import math
from pathlib import Path
import re

from .config import parse_project
from .gate import CONFIG, GateError, blob, exact_commit, git, tree


def digest(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def plan(repo: Path, tooling: str, base: str, head: str) -> dict:
    for sha in (tooling, base, head):
        exact_commit(repo, sha)
    ancestors = git(repo, 'merge-base', '--all', base, head).decode().splitlines()
    if len(ancestors) != 1:
        raise GateError('profiling needs one unambiguous merge base')
    diff_base = ancestors[0]
    approved, before, after = (tree(repo, sha) for sha in (tooling, diff_base, head))
    profile = parse_project(blob(repo, approved['sphereceti.toml']).decode())
    required = ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain')
    for entries in (before, after):
        if any(path not in entries or path not in approved for path in required):
            raise GateError('missing pinned build configuration')
        if any(entries.get(path) != approved.get(path) for path in CONFIG):
            raise GateError('profiling requires identical approved configuration on both sides')
    changes = []
    for path in sorted(before.keys() | after.keys()):
        if before.get(path) == after.get(path):
            continue
        category = next((label for root, label in ((profile.library_root, 'library'),
                          (profile.roadmap_root, 'roadmap'))
                         if path == root + '.lean' or
                         (path.startswith(root + '/') and path.endswith('.lean'))), None)
        if category is None:
            continue
        # Restrict module syntax instead of interpolating untrusted paths into commands/reports.
        if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:/[A-Za-z_][A-Za-z0-9_]*)*\.lean', path):
            raise GateError(f'unsupported profiling module path: {path!r}')
        changes.append({'path': path, 'category': category,
                        'kind': 'added' if path not in before else 'removed' if path not in after else 'modified',
                        'base_blob': before[path].oid if path in before else None,
                        'head_blob': after[path].oid if path in after else None})
    if len(changes) > 32:
        raise GateError('profiling is limited to 32 changed modules per run')
    result = {'schema_version': 1, 'repository': profile.repository, 'tooling': tooling,
              'base': base, 'diff_base': diff_base, 'head': head,
              'dependency_digest': hashlib.sha256(blob(repo, approved['lake-manifest.json'])).hexdigest(),
              'lean': blob(repo, approved['lean-toolchain']).decode().strip(),
              'metric': 'cpu_seconds', 'changes': changes}
    result['plan_digest'] = digest(result)
    return result


def summarize(manifest: dict, samples: list[dict], run_id: str) -> dict:
    """Only successful, finite, same-run measurements can enter comparisons."""
    expected = {(entry['path'], side) for entry in manifest['changes']
                for side in ('base', 'head') if entry[side + '_blob'] is not None}
    indexed = {}
    for sample in samples:
        key = (sample.get('path'), sample.get('side'))
        if key not in expected or key in indexed:
            raise ValueError('unexpected or duplicate profile sample')
        if (sample.get('plan_digest') != manifest['plan_digest'] or sample.get('run_id') != run_id
                or sample.get('revision') != manifest['diff_base' if key[1] == 'base' else 'head']):
            raise ValueError('profile sample belongs to a different plan, revision, or run')
        indexed[key] = sample
    rows = []
    for entry in manifest['changes']:
        row = {**entry, 'base': None, 'head': None, 'flagged': False, 'errors': []}
        for side in ('base', 'head'):
            if entry[side + '_blob'] is None:
                continue
            sample = indexed.get((entry['path'], side))
            valid = sample is not None and sample.get('status') == 'ok' and sample.get('returncode') == 0
            valid = valid and all(type(sample.get(field)) in (int, float) and
                                  math.isfinite(sample[field]) and sample[field] >= 0
                                  for field in ('cpu_seconds', 'wall_seconds'))
            if not valid:
                row['errors'].append(f'{side}: missing or failed measurement')
            else:
                row[side] = {key: sample[key] for key in ('cpu_seconds', 'wall_seconds')}
        if not row['errors']:
            old, new = row['base'], row['head']
            if old is not None and new is not None:
                row['flagged'] = new['cpu_seconds'] >= 1.5 * old['cpu_seconds'] and new['cpu_seconds'] - old['cpu_seconds'] >= 30
            elif new is not None:
                row['flagged'] = new['cpu_seconds'] >= 150
        rows.append(row)
    return {'schema_version': 1, 'advisory': True, 'merge_authority': False,
            'state': 'error' if any(row['errors'] for row in rows) else 'complete' if rows else 'no_changes',
            'run_id': run_id, 'plan': manifest, 'samples': samples, 'rows': rows}


def markdown(report: dict) -> str:
    manifest = report['plan']
    out = ['# Advisory Lean profile', '',
           'Local CPU/wall-time measurements; these do not establish mathematical correctness or merge eligibility.',
           'Library and roadmap labels describe source location, not proof completion.', '',
           f"State: **{report['state']}**. Run: `{report['run_id']}`.", '']
    for key in ('tooling', 'base', 'diff_base', 'head'):
        sha = manifest[key]
        out.append(f"- {key}: [{sha[:7]}](https://github.com/{manifest['repository']}/commit/{sha})")
    out += ['', 'CPU flags: modified ≥1.5× AND +30s; added ≥150s. Flags are advisory.', '',
            '| Source | Kind | Base CPU / wall (s) | Head CPU / wall (s) | Result |',
            '|---|---|---:|---:|---|']
    for row in report['rows']:
        def value(side):
            item = row[side]
            return '—' if item is None else f"{item['cpu_seconds']:.2f} / {item['wall_seconds']:.2f}"
        result = '; '.join(row['errors']) or ('advisory flag' if row['flagged'] else 'measured')
        out.append(f"| `{html.escape(row['path'])}` ({row['category']}) | {row['kind']} | {value('base')} | {value('head')} | {result} |")
    if not report['rows']:
        out += ['', 'No changed library or roadmap Lean files in the exact Git diff.']
    out += ['', 'Each side uses its own prebuilt source environment. Timed direct Lean invocations',
            're-elaborate the source; they do not time cached Lake no-ops. CPU includes sandbox/Lake',
            'startup and is sensitive to the host and prepared dependencies. No cross-run comparison.', '']
    return '\n'.join(out)
