# SPDX-License-Identifier: Apache-2.0
"""Authenticate the human-review scope exception for advisory scheduling only.

The shared merge assessor remains authoritative for its existing provenance checks.
Its unsuccessful scope verdict is retained, never rewritten into a passing merge check.
"""
from urllib.parse import quote

from .merge_checks import assess_checks, latest_statuses, run_reference
from .review_records import RecordError
from .worker import WorkerError, commit, require


HUMAN_SCOPE = "Scope: human_review; no merge authorization"


def human_review_scope(api, project, pr, scope_check, settings):
    """Bounded GETs; unconfigured producers cannot receive the exception."""
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
                   'base': base, 'tooling': tooling}
        verdict = assess_checks(statuses, run, jobs, context, settings)
        return verdict['reasons'] == ['trusted-scope is not successful']
    except (RecordError, ValueError, TypeError, KeyError, AttributeError) as error:
        raise WorkerError('incomplete worker scope provenance') from error
