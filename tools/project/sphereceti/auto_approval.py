"""Read-only decision: would SphereCeti automatically approve this proof PR, and why?

Nothing here reviews, approves, posts, merges, or calls a model provider. The decision reuses merge
observation's GET-only reader and evidence collection (`merge_observation.collect`), the trusted
run assessor (`merge_checks.assess_checks`), the scope gate (`gate.evaluate`), and the official
record reader (`review_records.assess_records`). It adds only the proof-topic path rule, the
library-root import rule, reviewer independence, and pull-request predicates that do not depend
on an existing GitHub approval, so it can run before GitHub considers the PR mergeable.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
from urllib.parse import quote

from .config import ConfigError, local_path
from .gate import CONFIG, GateError, blob, path_class, tree
from .local_review import RUBRICS
from .merge_checks import TOOLING_ATTESTATION, latest_statuses, timestamp
from .merge_observation import Reader, collect
from .review_records import RecordError, collect_records
from .worker_checks import HUMAN_SCOPE

ROOT_MODULE = 'SphereCeti.lean'
# One exported topic module per added line, in the library root's existing `public import` form.
ROOT_IMPORT = re.compile(r'public import (SphereCeti(?:\.[A-Z][A-Za-z0-9_]*)+)\n\Z')
FILE_LIMIT = 3000  # GitHub lists at most 3000 files for a pull request.
SCOPE_FAILURE = 'trusted-scope is not successful'
AUDIT_BINDING = ('trusted candidate: the approved pull_request_target workflow run attempt named by '
                 'trusted-build, whose candidate job ran the approved tooling\'s scripts/check_audits.py '
                 '(via scripts/sandbox-build.sh) on the exact head; run head_sha is the PR head, and the '
                 'trusted-build status attests the run\'s github.workflow_sha, which assess_checks requires '
                 'to equal the current approved main (#48)')
SPEC_DOCUMENTS = {'README.md', 'CONVENTIONS.md', 'MIGRATION.md', 'PROVENANCE.md', 'UPSTREAM.md',
                  'VALIDATION.md', 'AGENTS.md', 'CONTRIBUTING.md', 'INFRASTRUCTURE-PLAN.md',
                  'SphereCetiRoadmap.lean', 'sphereceti.toml'}
HUMAN_ROUTES = (
    ('roadmap specification', lambda p: p.startswith('SphereCetiRoadmap/') or p in SPEC_DOCUMENTS),
    ('dependencies', lambda p: p in CONFIG or p in ('uv.lock', 'pyproject.toml')),
    ('CI', lambda p: p.startswith('.github/')),
    ('review policy', lambda p: p.startswith(('policy/', 'tools/review/'))),
    ('merge machinery', lambda p: p.startswith(('tools/project/sphereceti/', 'scripts/'))),
    ('infrastructure', lambda p: p.startswith(('tests/', 'tools/', 'docs/'))),
    ('protected library module', lambda p: p.startswith('SphereCeti/') and path_class(p) == 'protected'),
)


def human_route(path):
    for name, matches in HUMAN_ROUTES:
        if matches(path):
            return f'{name} requires human approval'
    return 'outside the proof-topic allowlist'


def glob(pattern):
    """`*` and `?` stay within one path segment; `**` is a whole segment matching any depth."""
    if any(c in pattern for c in '[]{}!'):
        raise ConfigError('assumed proof paths support only *, ? and whole-segment **')
    out, parts = [], pattern.split('/')
    for i, part in enumerate(parts):
        last = i == len(parts) - 1
        if part == '**':
            out.append('.*' if last else '(?:[^/]+/)*')
            continue
        if '**' in part:
            raise ConfigError('** must be a whole path segment')
        out.append(''.join('[^/]*' if c == '*' else '[^/]' if c == '?' else re.escape(c) for c in part)
                   + ('' if last else '/'))
    return re.compile(''.join(out) + r'\Z')


def proof_paths(policy, assumed):
    """Effective allowlist: the approved policy's prefixes, or an explicitly hypothetical glob list."""
    if assumed:
        patterns = []
        for pattern in assumed:
            local_path(pattern, 'assumed proof path')
            if not pattern.startswith('SphereCeti/'):
                raise ConfigError('assumed proof paths must lie in the proof library SphereCeti/')
            patterns.append(pattern)
        regexes = [glob(p) for p in patterns]
        return {'source': 'assumed', 'hypothetical': True, 'patterns': patterns,
                'match': lambda path: any(r.fullmatch(path) for r in regexes)}
    prefixes = list(policy.mathematical_paths) if policy else []
    # The same prefix semantics as gate.evaluate's permitted().
    return {'source': 'policy', 'hypothetical': False, 'patterns': prefixes,
            'match': lambda path: any(path == p or path.startswith(p.rstrip('/') + '/') for p in prefixes)}


def pull_files(client, repository, pr):
    """The PR's complete changed-file list; pagination gaps or GitHub's file cap are errors."""
    pages = client.call(f'repos/{repository}/pulls/{pr["number"]}/files?per_page=100', paginate=True)
    if not isinstance(pages, list) or not pages or any(not isinstance(p, list) for p in pages):
        raise RecordError('incomplete PR file pages')
    files = [f for page in pages for f in page]
    expected = pr.get('changed_files')
    if type(expected) is not int or expected < 1 or expected >= FILE_LIMIT:
        raise RecordError('PR changed-file count is missing or at GitHub\'s listing limit; inventory may be truncated')
    if len(files) != expected:
        raise RecordError(f'PR file inventory is truncated or inconsistent ({len(files)} listed, {expected} changed)')
    names = set()
    for f in files:
        if (not isinstance(f, dict) or not isinstance(f.get('filename'), str) or not f['filename'] or
                not isinstance(f.get('status'), str) or f['filename'] in names or
                ('previous_filename' in f and f['previous_filename'] is not None and
                 not isinstance(f['previous_filename'], str))):
            raise RecordError('invalid or duplicate PR file entry')
        names.add(f['filename'])
    return files


def root_imports(repo, old, new, head_tree, allowed):
    """SphereCeti.lean may only gain `public import SphereCeti.<Topic>...` lines naming eligible modules.

    Every existing line must survive byte-for-byte and in order; nothing else may change.
    """
    if old is None or new is None:
        return 'the library root may only be modified, never added or removed', []
    if old.mode != '100644' or new.mode != '100644':
        return 'the library root must stay a regular non-executable file', []
    try:
        before = blob(repo, old).decode('utf-8').splitlines(keepends=True)
        after = blob(repo, new).decode('utf-8').splitlines(keepends=True)
    except UnicodeError:
        return 'the library root is not UTF-8 text', []
    added, kept = [], 0
    for line in after:
        if kept < len(before) and line == before[kept]:
            kept += 1
        else:
            added.append(line)
    if kept != len(before):
        return 'the library root change removes or edits existing lines', []
    modules = []
    for line in added:
        match = ROOT_IMPORT.fullmatch(line)
        if not match:
            return f'the library root change adds a non-import line: {line.rstrip()!r}', []
        module = match[1]
        path = module.replace('.', '/') + '.lean'
        if line in before or module in modules:
            return f'the library root imports {module} twice', []
        if path not in head_tree or not allowed(path):
            return f'the library root imports {module}, which is not an eligible proof module', []
        modules.append(module)
    if not modules:
        return 'the library root change adds no import', []
    return None, modules


def assess_paths(repo, files, scope, proof):
    """Requirement 1 from the API file list, cross-checked against the exact Git trees."""
    head_tree, base_tree = tree(repo, scope['head']), tree(repo, scope['diff_base'])
    allowed = lambda p: path_class(p) == 'library' and proof['match'](p)
    listed = {f['filename'] for f in files} | {f['previous_filename'] for f in files if f.get('previous_filename')}
    exact = {c['path'] for c in scope['changes']}
    eligible, ineligible, imports, problems = [], [], [], []
    if not proof['patterns']:
        problems.append('no proof-topic paths are approved (policy mathematical_paths is empty); '
                        'a hypothetical allowlist must be assumed explicitly')
    if listed != exact:
        problems.append('the GitHub file list differs from the exact Git diff: ' +
                        ', '.join(sorted(listed ^ exact)))
    if scope.get('config_attested') is not True:
        problems.append('candidate dependency configuration differs from approved main')
    for f in sorted(files, key=lambda f: f['filename']):
        path, status = f['filename'], f['status']
        if status not in ('added', 'modified'):
            reason = (f"renamed from {f.get('previous_filename')}; renames are not eligible" if status == 'renamed'
                      else f'{status} files are not eligible')
        elif path == ROOT_MODULE:
            reason, modules = root_imports(repo, base_tree.get(path), head_tree.get(path), head_tree, allowed)
            imports += modules
        elif not allowed(path):
            reason = human_route(path)
        elif path not in head_tree or head_tree[path].mode != '100644' or (
                path in base_tree and base_tree[path].mode != '100644') or (status == 'added') != (path not in base_tree):
            reason = 'not a regular non-executable file at both revisions, or its status disagrees with Git'
        else:
            reason = None
        (ineligible.append({'path': path, 'status': status, 'reason': reason}) if reason else eligible.append(path))
    return {'passed': not ineligible and not problems and bool(files), 'eligible': eligible,
            'ineligible': ineligible, 'problems': problems, 'root_imports': imports}


def main_update(client, repository, branch):
    """Diagnostic only: the latest push or merge that moved the default branch, or None."""
    ref = quote(f'refs/heads/{branch}', safe='')
    try:
        page = client.call(f'repos/{repository}/activity?ref={ref}&direction=desc&per_page=1')
    except RecordError:
        return None
    if (not isinstance(page, list) or len(page) != 1 or not isinstance(page[0], dict) or
            not isinstance(page[0].get('after'), str) or not isinstance(page[0].get('timestamp'), str)):
        return None
    return {k: page[0].get(k) for k in ('after', 'timestamp', 'activity_type')}


def run_after_main(run, update, current):
    """Diagnostic only: was the run created after main last moved to the current tooling?

    Timestamps never decide. The authority is the trusted-build attestation of github.workflow_sha,
    checked by assess_checks; this only helps explain a stale or missing attestation.
    """
    if not isinstance(run, dict) or not update:
        return None
    try:
        return update['after'] == current and timestamp(run.get('created_at')) > timestamp(update['timestamp'])
    except (ValueError, TypeError, RecordError):
        return None


def requirement(name, passed, summary, **evidence):
    status = 'not_assessed' if passed is None else 'pass' if passed else 'fail'
    return {'id': name, 'status': status, 'summary': summary, 'evidence': evidence}


def pull_request_state(pr, context, current):
    reasons = []
    if pr['state'] != 'open' or pr['merged'] is not False: reasons.append('PR is not open and unmerged')
    if pr['draft'] is not False: reasons.append('PR is a draft')
    if pr['base']['ref'] != 'main' or pr['base']['repo']['full_name'] != context['repository']:
        reasons.append('PR does not target main of this repository')
    if pr['base']['sha'] != current or context['base'] != current:
        reasons.append('PR base is not the current approved main; update the branch')
    if context.get('diff_base') != context['base']: reasons.append('PR is behind main; update the branch')
    if pr['head']['sha'] != context['head']: reasons.append('PR head moved during the decision')
    # Mergeability here is conflict state only. `blocked` (an approval or check still required)
    # and `unstable` are acceptable: the approval is what a bot would issue after this decision.
    if pr['mergeable'] is False or pr['mergeable_state'] == 'dirty': reasons.append('PR conflicts with main')
    elif pr['mergeable'] is not True or pr['mergeable_state'] in ('unknown', 'behind', 'draft'):
        reasons.append(f"GitHub mergeability is indeterminate ({pr['mergeable_state']}); retry")
    return reasons


def decide_approval(ev, paths, proof, *, comments):
    """One deterministic conjunction over collected evidence. It cannot authorize any action."""
    pr, current, policy = ev['pr'], ev['current'], ev['policy']
    scope, context, review, checks = ev['scope'], ev['context'], ev['review'], ev['checks']
    author = pr['user']['id']
    author_identity = f'user:{author}'
    requirements = []

    requirements.append(requirement(
        'paths', paths['passed'], 'every changed path is an eligible proof path or an allowed library-root import',
        allowlist=proof['patterns'], allowlist_source=proof['source'], eligible=paths['eligible'],
        ineligible=paths['ineligible'], problems=paths['problems'], root_imports=paths['root_imports'],
        root_rule=f'{ROOT_MODULE} may only add `public import SphereCeti.<Topic>...` lines naming eligible modules'))

    latest = latest_statuses(ev['statuses'])
    scope_status = latest.get('trusted-scope') or {}
    build_reasons = [r for r in checks['reasons'] if r != SCOPE_FAILURE]
    attestation = TOOLING_ATTESTATION.fullmatch((latest.get('trusted-build') or {}).get('description') or '')
    bound = [k for k in ('repository', 'head', 'base', 'tooling') if checks.get(k) != context.get(k)]
    bound += [f'scope {k}' for k in ('repository', 'head', 'base', 'diff_base', 'dependency_digest', 'tooling')
              if scope.get(k) != context.get(k)]
    accepted_scope = None
    if SCOPE_FAILURE in checks['reasons']:
        # The trusted gate applies the approved allowlist (empty today) and treats the library root as
        # protected. Its human_review verdict is replaced only by this decision's stricter path rule
        # over the same exact trees, and only where the assumed allowlist or root import explains it.
        if (scope_status.get('state') == 'failure' and scope_status.get('description') == HUMAN_SCOPE and
                scope.get('scope') == 'human_review' and paths['passed'] and
                (proof['hypothetical'] or ROOT_MODULE in [c['path'] for c in scope['changes']])):
            accepted_scope = ('human_review status replaced by the path requirement' +
                              (' under the hypothetical allowlist' if proof['hypothetical'] else
                               ' because the gate protects the library root'))
    trusted = not build_reasons and not bound and (SCOPE_FAILURE not in checks['reasons'] or accepted_scope is not None)
    statuses = {name: {k: s.get(k) for k in ('id', 'state', 'description', 'target_url')} for name, s in latest.items()}
    requirements.append(requirement(
        'trusted_checks', trusted, 'trusted-build succeeded and trusted-scope is present, both from the approved '
        'producer and one exact run attempt bound to this head and the current base',
        reasons=build_reasons + [f'mismatched {k}' for k in bound] +
        ([SCOPE_FAILURE] if SCOPE_FAILURE in checks['reasons'] and accepted_scope is None else []),
        statuses=statuses, trusted_scope=('success' if scope_status.get('state') == 'success' else accepted_scope or
                                          scope_status.get('state') or 'missing'), run=checks.get('run')))

    jobs = ev.get('jobs') or []
    candidate = [j for j in jobs if isinstance(j, dict) and j.get('name') == 'candidate']
    run = ev.get('run') or {}
    association = [p for p in run.get('pull_requests') or [] if isinstance(p, dict) and p.get('number') == pr['number']]
    requirements.append(requirement(
        'compiled_audit', not build_reasons and not bound,
        'the compiled audit (scripts/check_audits.py from approved tooling) passed on the exact head',
        binding=AUDIT_BINDING, reasons=build_reasons, run=checks.get('run'), workflow=run.get('path'),
        event=run.get('event'), run_head_sha=run.get('head_sha'),
        association_base_sha=((association[0].get('base') or {}).get('sha') if association else None),
        attested_tooling=attestation.group(1) if attestation else None, approved_tooling=current,
        diagnostic={'run_created_at': run.get('created_at'), 'main_update': ev.get('main_update'),
                    'run_created_after_main_moved': run_after_main(ev.get('run'), ev.get('main_update'), current),
                    'note': 'timestamps are diagnostic only; the attested tooling is the binding'},
        candidate_job={k: candidate[0].get(k) for k in ('id', 'conclusion', 'run_attempt')} if len(candidate) == 1 else None))

    assessed = 'selected_comments' in review
    by_id = {c.get('id'): c for c in comments}
    publishers = []
    for actor, cid in (review.get('selected_comments') or {}).items():
        user_id = ((by_id.get(cid) or {}).get('user') or {}).get('id')
        publishers.append({'identity': actor, 'comment_id': cid, 'user_id': user_id,
                           'is_author': actor == author_identity or user_id == author})
    head_records = sorted({cid for cid, (_, r) in collect_records(comments, context, policy).items()
                           if r['head'] == context['head'] and not r['advisory'] and r['completion'] == 'complete'})
    review_ok = (review.get('review_safe') is True and assessed and
                 all(review.get(k) == context.get(k) for k in ('repository', 'pr', 'head')))
    requirements.append(requirement(
        'official_review', review_ok if assessed else None,
        f'the official reader accepts a complete, non-advisory review of all {len(RUBRICS)} rubrics '
        'for this exact head and base from an authorized reviewer',
        reasons=review.get('reasons') or [], rubrics=list(RUBRICS), publishers=publishers,
        complete_authorized_records_for_head=head_records,
        **({} if assessed else {'skipped': 'review context is materialized only for path-eligible PRs'})))

    independent = [p for p in publishers if not p['is_author']]
    requirements.append(requirement(
        'independent_reviewer', (review_ok and bool(independent)) if assessed else None,
        'an accepted official review was published by someone other than the PR author',
        author=author_identity, publishers=publishers,
        reasons=[] if review_ok and independent else
        ['the PR author is the sole official reviewer'] if review_ok else ['no accepted official review']))

    pr_reasons = pull_request_state(pr, context, current)
    requirements.append(requirement(
        'pull_request', not pr_reasons, 'open, not draft, targets main, up to date with approved main, not conflicting',
        reasons=pr_reasons, state=pr['state'], draft=pr['draft'], base_ref=pr['base']['ref'],
        mergeable=pr['mergeable'], mergeable_state=pr['mergeable_state'], github_approval_required=False))

    requirements.append(requirement(
        'policy', bool(proof['patterns']), 'proof-topic allowlist from the approved policy or an explicit hypothesis',
        merging=policy.merging, mathematical_paths=list(policy.mathematical_paths),
        authorized_reviewers=list(policy.authorized_reviewers), hypothetical=proof['hypothetical'],
        assumed_proof_paths=proof['patterns'] if proof['hypothetical'] else None))
    return finish(ev, requirements, proof, author_identity, pr, publishers)


def finish(ev, requirements, proof, author_identity, pr, publishers):
    reasons = []
    for item in requirements:
        if item['status'] == 'fail':
            detail = item['evidence'].get('reasons') or item['evidence'].get('problems') or []
            detail = detail + [f"{p['path']}: {p['reason']}" for p in item['evidence'].get('ineligible', [])]
            reasons += [f"{item['id']}: {d}" for d in detail] or [f"{item['id']}: {item['summary']}"]
    scope = ev.get('scope') or {}
    note = 'Read-only decision; nothing was reviewed, approved, posted, or merged.'
    if proof['hypothetical']:
        note = ('HYPOTHETICAL: assumes proof paths ' + ', '.join(proof['patterns']) +
                '; the approved policy is unchanged. ' + note)
    return {'schema_version': 1, 'mode': 'auto_approval_decision', 'read_only': True,
            'repository': pr['base']['repo']['full_name'], 'pr': pr['number'],
            'would_approve': all(r['status'] == 'pass' for r in requirements),
            'hypothetical': proof['hypothetical'], 'assumed_proof_paths': proof['patterns'] if proof['hypothetical'] else None,
            'head': ev['refs']['head'], 'base': ev['refs']['base'], 'diff_base': scope.get('diff_base'),
            'tooling': ev['current'], 'author': {'identity': author_identity, 'login': pr['user'].get('login')},
            'review_publishers': publishers, 'audit_binding': AUDIT_BINDING, 'github_approval_required': False,
            'reasons': list(dict.fromkeys(reasons)), 'requirements': requirements, 'note': note}


def stopped(ev, proof, name, reason, **evidence):
    """A decidable 'no' before full evidence exists (missing approved policy, non-ordinary file)."""
    pr = ev['pr']
    requirements = [requirement(name, False, reason, reasons=[reason], **evidence)]
    requirements += [requirement(n, None, 'not assessed') for n in
                     ('paths', 'trusted_checks', 'compiled_audit', 'official_review', 'independent_reviewer',
                      'pull_request', 'policy') if n != name]
    return finish(ev, requirements, proof, f"user:{pr['user']['id']}", pr, [])


def auto_approval(args, project, *, client=None):
    assumed = list(args.assume_proof_paths or [])
    if assumed:
        proof_paths(None, assumed)  # Reject a malformed hypothesis before any read.
    client = client or Reader(project.repository)
    ev = {}

    def review_needed(scope, ev):
        ev['proof'] = proof_paths(ev['policy'], assumed)
        ev['files'] = pull_files(client, project.repository, ev['pr'])
        ev['paths'] = assess_paths(ev['repo'], ev['files'], scope, ev['proof'])
        return ev['paths']['passed']

    try:
        collect(args, project, client, assess_review=review_needed, evidence=ev)
    except GateError as error:
        # gate.tree rejects symlinks and submodules; that is an ineligible path, not an error.
        if 'non-ordinary source' not in str(error) or 'policy' not in ev:
            raise
        proof = proof_paths(ev['policy'], assumed)
        result = stopped(ev, proof, 'paths', str(error))
        client.revalidate()
        return digested(result)
    if ev['missing']:
        proof = proof_paths(None, assumed)
        result = stopped(ev, proof, 'policy', 'approved main lacks ' + ', '.join(ev['missing']))
        client.revalidate()
        return digested(result)
    comments = ev['comments'] if 'comments' in ev else client.comments(project.repository, args.pr)
    if isinstance(ev.get('run'), dict):
        ev['main_update'] = main_update(client, project.repository, project.default_branch)
    result = decide_approval(ev, ev['paths'], ev['proof'], comments=comments)
    result['check_policy_digest'] = ev['check_policy_digest']
    client.revalidate()
    return digested(result)


def digested(result):
    result['evidence_digest'] = hashlib.sha256(json.dumps(result, sort_keys=True).encode()).hexdigest()
    return result


def render(report):
    head = f"PR #{report['pr']}: would_approve = {str(report['would_approve']).lower()}"
    if report['hypothetical']:
        head += ' [HYPOTHETICAL: assumes proof paths ' + ', '.join(report['assumed_proof_paths']) + ']'
    lines = [head, f"head {report['head']}  base {report['base']}  tooling {report['tooling']}",
             f"author {report['author']['identity']}; official review publishers: " +
             (', '.join(p['identity'] + (' (author)' if p['is_author'] else '') for p in report['review_publishers'])
              or 'none')]
    for item in report['requirements']:
        lines.append(f"[{item['status']}] {item['id']}: {item['summary']}")
    lines += ['  - ' + r for r in report['reasons']]
    lines.append(report['note'])
    return '\n'.join(lines)


def add_parser(commands):
    p = commands.add_parser('auto-approve-check',
                            help='read-only: would SphereCeti automatically approve this proof PR, and why')
    p.add_argument('pr', type=int)
    p.add_argument('--assume-proof-paths', action='append', metavar='GLOB',
                   help='HYPOTHETICAL proof-topic allowlist for this report only (e.g. "SphereCeti/E8/**"); '
                        'never changes policy, and the output is marked hypothetical')
    p.add_argument('--json', action='store_true')
    p.add_argument('--source-repo', type=Path, help='fully materialized local Git objects; authority still comes from remote main')
    p.add_argument('--dependencies-dir', type=Path, help='optional existing pinned dependency Git stores')
    p.add_argument('--cache-dir', type=Path, default=Path('~/.cache/sphereceti/merge-observation'), help='source-only evidence cache')
    p.add_argument('--operator-config', type=Path, help='preferences only; cannot change approval policy')
