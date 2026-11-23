# SPDX-License-Identifier: Apache-2.0
"""Authenticate the human-review scope exception for advisory scheduling only.

The shared merge assessor remains authoritative for its existing provenance checks.
Its unsuccessful scope verdict is retained, never rewritten into a passing merge check.

Review readiness alone tolerates a trusted run that predates current main: its attested tooling
and the PR's recorded base need only be approved main commits (equal to or ancestors of current
main). A review runs with current tooling T and binds T itself, so the trusted run's tooling does
not change the review's authority. The merge side (merge_checks, auto_approval) still requires
both to equal current main.
"""
from urllib.parse import quote

from .merge_checks import TOOLING_ATTESTATION, assess_checks, latest_statuses, run_reference
from .review_records import RecordError
from .worker import WorkerError, commit, require


HUMAN_SCOPE = "Scope: human_review; no merge authorization"
SCOPE_FAILURE = 'trusted-scope is not successful'
STALE_TOOLING = 'trusted-build ran with tooling other than approved main; refresh the trusted run'
STALE_BASE = 'PR base is not approved main; update the PR and refresh the trusted run'
PREDATES_MAIN = 'trusted build predates main; refresh to merge'
NEEDS_REFRESH = 'awaits a refreshed trusted build'
# Failures that a fresh trusted run on current main resolves, not defects in the PR.
REFRESHABLE = {'trusted-build does not attest its tooling commit; refresh the trusted run'}


def approved_main(read, prefix, revision, current, cache):
    """Is `revision` current main or one of its ancestors? Unknown or unreadable means no."""
    if revision == current:
        return True
    key = (revision, current)
    if key not in cache:
        try:
            value = read(f'{prefix}/compare/{revision}...{current}')
            cache[key] = (isinstance(value, dict) and value.get('status') in ('ahead', 'identical') and
                          (value.get('merge_base_commit') or {}).get('sha') == revision)
        except WorkerError:
            cache[key] = False  # e.g. 404 for a SHA unknown to the repository
    return cache[key]


def human_review_scope(api, project, pr, scope_check, settings):
    """Bounded GETs; unconfigured producers cannot receive the exception.

    Returns False (not review-ready); {'accepted': True, 'note': None} for a run on current main;
    {'accepted': True, 'note': PREDATES_MAIN} for a run on the same head whose attested tooling and
    recorded base are older approved main commits; or {'accepted': False, 'note': NEEDS_REFRESH}
    when only a fresh trusted run is missing (an informational scheduling category).
    """
    if not settings['workflow_id'] or not settings['status_creator_ids']:
        return False
    head = commit(pr.get('headRefOid'), 'worker scope head')
    base = commit(pr.get('baseRefOid'), 'worker scope base')
    require(type(pr.get('number')) is int and pr['number'] > 0, 'invalid worker scope PR')

    def read(endpoint):
        return api.read(['api', '--hostname', 'github.com', '--method', 'GET', endpoint])

    prefix = f'repos/{project.repository}'
    statuses = read(f'{prefix}/commits/{head}/statuses?per_page=100')
    require(isinstance(statuses, list) and len(statuses) < 100,
            'truncated or incomplete worker status inventory')
    try:
        latest = latest_statuses(statuses)
        all_latest = {}
        for status in statuses:
            if status['id'] > all_latest.get(status['context'], {}).get('id', 0):
                all_latest[status['context']] = status
        if any(s.get('state') != 'success' for name, s in all_latest.items() if name != 'trusted-scope'):
            return False
        scope = latest.get('trusted-scope', {})
        if (scope.get('state') != 'failure' or scope.get('description') != HUMAN_SCOPE or
                scope_check.get('targetUrl') != scope.get('target_url')):
            return False
        refs = {run_reference(s.get('target_url'), project.repository) for s in latest.values()}
        if len(refs) != 1 or None in refs:
            return False
        rid, attempt = next(iter(refs))
        main = read(f'{prefix}/commits/{quote(project.default_branch, safe="")}')
        require(isinstance(main, dict), 'missing approved worker tooling revision')
        tooling = commit(main.get('sha'), 'approved worker tooling revision')
        run = read(f'{prefix}/actions/runs/{rid}')
        page = read(f'{prefix}/actions/runs/{rid}/attempts/{attempt}/jobs?per_page=100')
        require(isinstance(page, dict) and isinstance(page.get('jobs'), list) and
                type(page.get('total_count')) is int and page['total_count'] == len(page['jobs']) and
                len(page['jobs']) < 100, 'truncated or incomplete worker job inventory')
        jobs = page['jobs']
        require(all(isinstance(j, dict) and type(j.get('id')) is int and j['id'] > 0 for j in jobs) and
                len({j['id'] for j in jobs}) == len(jobs), 'invalid or duplicate worker jobs')
        context = {'repository': project.repository, 'pr': pr['number'], 'head': head,
                   'base': base, 'tooling': tooling,
                   'head_repository': (pr.get('headRepository') or {}).get('nameWithOwner')}
        reasons = assess_checks(statuses, run, jobs, context, settings)['reasons']
        if SCOPE_FAILURE not in reasons:
            return False
        cache = api.__dict__.setdefault('_approved_main', {}) if hasattr(api, '__dict__') else {}
        remaining, tolerated = set(reasons) - {SCOPE_FAILURE}, False
        if STALE_TOOLING in remaining:
            attested = TOOLING_ATTESTATION.fullmatch(latest['trusted-build'].get('description') or '')
            if attested is None or not approved_main(read, prefix, attested.group(1), tooling, cache):
                return False
            remaining.discard(STALE_TOOLING)
            tolerated = True
        if STALE_BASE in remaining:
            if not approved_main(read, prefix, base, tooling, cache):
                return False
            remaining.discard(STALE_BASE)
            tolerated = True
        if not remaining:
            return {'accepted': True, 'note': PREDATES_MAIN if tolerated else None}
        if remaining <= REFRESHABLE:
            return {'accepted': False, 'note': NEEDS_REFRESH}
        return False
    except (RecordError, ValueError, TypeError, KeyError, AttributeError) as error:
        raise WorkerError('incomplete worker scope provenance') from error
