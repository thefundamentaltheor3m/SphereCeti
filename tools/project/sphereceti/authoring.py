# SPDX-License-Identifier: Apache-2.0
"""Provider-free, exact-revision handoffs for one bounded production task.

Local Git provenance does not establish repository identity, approved specification,
task readiness, or permission to execute or publish the proposed work.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re

from .config import local_path
from .gate import blob, git, tree
from .local_review import object_source


MAX_PATHS = 8
MAX_SOURCE_BYTES = 2 * 1024 * 1024
NOTICE = (
    "Local, unverified authoring proposal. Repository identities, source approval, prerequisites "
    "and task readiness have not been authenticated. This handoff does not authorize execution, "
    "publication or merging, and does not certify mathematical completion."
)


def add_parser(commands):
    author = commands.add_parser('author', help='prepare a provider-free local authoring handoff')
    actions = author.add_subparsers(dest='author_command', required=True)
    plan = actions.add_parser('plan', help='describe one bounded task without executing or publishing it')
    plan.add_argument('--roadmap-repo', type=Path, required=True)
    plan.add_argument('--roadmap', required=True, help='exact full roadmap commit')
    plan.add_argument('--implementation-repo', type=Path, required=True)
    plan.add_argument('--implementation', required=True, help='exact full production base commit')
    plan.add_argument('--reference', required=True, help='heading reference in the configured roadmap document')
    plan.add_argument('--task', required=True, help='one concise task proposed by the operator')
    plan.add_argument('--allow-path', action='append', required=True, help='explicit production .lean/.md file; at most eight')
    plan.add_argument('--max-changed-lines', type=int, default=200, help='proposed addition/deletion budget, 1–500')
    plan.add_argument('--time-limit-minutes', type=int, default=30, help='proposed work budget, 1–120')
    plan.add_argument('--output', type=Path, help='optional new directory for plan.json and brief.md')


def allowed_path(value):
    value = local_path(value, 'allowed path')
    path = PurePosixPath(value)
    if (str(path) != value or any(part.startswith('.') for part in path.parts)
            or any(part in {'lake-packages', 'node_modules', '__pycache__'} for part in path.parts)
            or not re.fullmatch(r'[A-Za-z0-9_/-]+\.(?:lean|md)', value)
            or path.name in {'AGENTS.md', 'lakefile.lean'}):
        raise ValueError('allowed paths must be explicit ordinary .lean/.md source files without hidden or reserved components')
    return value


def read_source(repo, entries, path):
    if path not in entries or entries[path].mode != '100644':
        raise ValueError(f'required source is not an ordinary non-executable file: {path}')
    entry = entries[path]
    size = int(git(repo, 'cat-file', '-s', entry.oid))
    if size > MAX_SOURCE_BYTES:
        raise ValueError('handoff source exceeds the 2 MiB per-file bound')
    raw = blob(repo, entry)
    return raw, {'path': path, 'git_blob': entry.oid, 'sha256': hashlib.sha256(raw).hexdigest(), 'bytes': len(raw)}


def section(document, reference, expected_document):
    prefix = expected_document + '#'
    if not reference.startswith(prefix) or not re.fullmatch(r'[a-z0-9][a-z0-9_-]{0,199}', reference[len(prefix):]):
        raise ValueError('reference must name a heading in the configured roadmap document')
    anchor = reference[len(prefix):]
    lines, headings, counts = document.splitlines(), [], {}
    fenced = None
    for index, line in enumerate(lines):
        fence = re.match(r'^ {0,3}(`{3,}|~{3,})(.*)$', line)
        if fenced:
            if (fence and fence[1][0] == fenced[0] and len(fence[1]) >= fenced[1]
                    and not fence[2].strip()):
                fenced = None
            continue
        if fence and (fence[1][0] == '~' or '`' not in fence[2]):
            fenced = (fence[1][0], len(fence[1]))
            continue
        match = re.match(r'^ {0,3}(#{1,6})\s+(.+?)\s*#*$', line)
        if not match:
            continue
        title = match[2]
        slug = re.sub(r'[^\w -]', '', title.lower()).replace(' ', '-')
        count = counts.get(slug, 0)
        counts[slug] = count + 1
        headings.append((index, len(match[1]), slug + (f'-{count}' if count else '')))
    matches = [h for h in headings if h[2] == anchor]
    if len(matches) != 1:
        raise ValueError('reference does not resolve to one roadmap heading')
    start, level, _ = matches[0]
    end = next((i for i, depth, _ in headings if i > start and depth <= level), len(lines))
    excerpt = '\n'.join(lines[start:end])
    return excerpt[:16000], len(excerpt) > 16000


def brief(report):
    # Indentation keeps supplied task text and source prose from creating active Markdown structure.
    payload = json.dumps(report, indent=2, ensure_ascii=True)
    return ('# Proposed production authoring handoff\n\n' + NOTICE + '\n\n'
            'Use your chosen external author tool with this exact source evidence and scope. '
            'Before doing work, independently establish source identity, approved specification, '
            'prerequisite completion and an isolated production checkout. Scope/time/line bounds '
            'are proposed limits; this exporter does not enforce an author process.\n\n'
            'Run the production repository\'s applicable build, proof/admission audits and focused '
            'checks before presenting a patch. Preserve the target statements and source attribution. '
            'A later authoring/publication adapter must independently validate the result.\n\n'
            + '\n'.join('    ' + line for line in payload.splitlines()) + '\n')


def run(args, project):
    if args.author_command != 'plan':
        raise ValueError('unsupported author command')
    if (not isinstance(args.task, str) or not 1 <= len(args.task) <= 2000
            or args.task.strip() != args.task or any(ord(c) < 32 or ord(c) == 127 for c in args.task)):
        raise ValueError('task must be one nonempty paragraph of at most 2000 characters')
    if not 1 <= args.max_changed_lines <= 500 or not 1 <= args.time_limit_minutes <= 120:
        raise ValueError('handoff bounds require 1–500 changed lines and 1–120 minutes')
    if not 1 <= len(args.allow_path) <= MAX_PATHS:
        raise ValueError('choose between one and eight explicit allowed paths')
    paths = sorted(allowed_path(p) for p in args.allow_path)
    if len(paths) != len(set(paths)):
        raise ValueError('duplicate allowed path')
    output = args.output.expanduser().absolute() if args.output else None
    if output and '..' in output.parts:
        raise ValueError('handoff output cannot use parent traversal')
    if output and (output.exists() or output.is_symlink()):
        raise ValueError('handoff output must be a new directory')
    if output and any(p.is_symlink() for p in output.parents):
        raise ValueError('handoff output cannot use symlinked parent directories')
    repos, source_roots = [], []
    for source, revision in ((args.roadmap_repo, args.roadmap), (args.implementation_repo, args.implementation)):
        source = source.expanduser().resolve()
        # Reject promisor stores as well as floating refs; no network fallback or checkout occurs.
        repo = object_source(source, source, '', [revision], True)
        repos.append(repo)
        source_roots.append(repo if git(repo, 'rev-parse', '--is-bare-repository').strip() == b'true'
                            else Path(git(repo, 'rev-parse', '--show-toplevel').decode().strip()).resolve())
    roadmap_repo, implementation_repo = repos
    if output and any(output == root or root in output.parents for root in source_roots):
        raise ValueError('handoff output must be outside both source repositories')
    roadmap_tree = tree(roadmap_repo, args.roadmap)
    implementation_tree = tree(implementation_repo, args.implementation)
    document, document_evidence = read_source(roadmap_repo, roadmap_tree, project.roadmap_document)
    _, targets_evidence = read_source(roadmap_repo, roadmap_tree, project.roadmap_targets)
    excerpt, truncated = section(document.decode('utf-8'), args.reference, project.roadmap_document)
    path_evidence = []
    for path in paths:
        if any(path.startswith(p + '/') or p.startswith(path + '/') for p in implementation_tree):
            raise ValueError('allowed path conflicts with an existing file or directory')
        if path in implementation_tree:
            _, evidence = read_source(implementation_repo, implementation_tree, path)
            path_evidence.append({**evidence, 'state': 'existing'})
        else:
            path_evidence.append({'path': path, 'state': 'new'})
    report = {
        'schema': 'sphereceti.author-plan/v1', 'state': 'proposed',
        'advisory_only': True, 'executable': False, 'publication_allowed': False,
        'merge_eligible': False, 'authority': 'local_unverified', 'notice': NOTICE,
        'repository': project.repository, 'destination': project.implementation_repository,
        'source_identity_verified': False, 'source_approval_verified': False,
        'prerequisites_verified': False, 'task': args.task, 'reference': args.reference,
        'roadmap': {'revision': args.roadmap, 'files': [document_evidence, targets_evidence]},
        'implementation': {'revision': args.implementation, 'files': path_evidence},
        'scope': {'allowed_paths': paths, 'max_files': len(paths),
                  'max_changed_lines': args.max_changed_lines, 'time_limit_minutes': args.time_limit_minutes,
                  'bounds_enforced': False},
        'roadmap_excerpt': excerpt, 'excerpt_truncated': truncated,
    }
    report['plan_digest'] = hashlib.sha256(json.dumps(report, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    if output:
        output.mkdir()  # Deliberately no exist_ok: concurrent exporters cannot overwrite a handoff.
        (output / 'plan.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
        (output / 'brief.md').write_text(brief(report), encoding='utf-8')
    return report
