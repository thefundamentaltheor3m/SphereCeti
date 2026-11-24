"""Authenticate #6/#8 build/scope statuses against their exact Actions run attempt.

Design adapted from TauCetiReview@afb424eda89e8ac96d9eb69f6a88972055a4cd1b
runner/merge_from_scoreboard.py (Apache-2.0, TauCetiReview contributors).
"""
from datetime import datetime
import re
import tomllib

from .config import fields, version
from .review_records import RecordError

WORKFLOW = '.github/workflows/pr-build.yml'
CONTEXTS = ('trusted-build', 'trusted-scope')
# pr-build.yml's status job publishes the commit whose workflow ran (github.workflow_sha) in the
# trusted-build description. A run's PR association reports the PR's current base, not the base when
# the run happened, so this attestation is what binds a run to its tooling. Newer runs also attest
# the pull_request_target event's PR number and base; the head is the status's own commit. That
# binding works for fork PRs, whose runs GitHub reports with an empty pull_requests association.
# A dispatched refresh (pr-build.yml on main, `workflow_dispatch`) says "refresh" instead of
# "build", and always carries the PR binding. Older readers do not match it, so they fail closed.
TOOLING_ATTESTATION = re.compile(r'Approved tooling (?:build|refresh): [a-z_]+; tooling ([0-9a-f]{40})'
                                 r'(?:; pr ([1-9][0-9]{0,8}); base ([0-9a-f]{40}))?')
REFRESH_PREFIX = 'Approved tooling refresh: '
# The trusted run builds and audits the PR head merged with the main commit whose workflow ran, and
# publishes that tested tree in a third status on the head (140 characters do not fit it in the
# trusted-build description). Main is the run's own workflow_sha, also attested as `tooling`.
MERGE_CONTEXT = 'trusted-merge'
MERGE_ATTESTATION = re.compile(r'Tested merge tree ([0-9a-f]{40}) with main ([0-9a-f]{40})')
MERGE_MISSING = 'trusted-merge is missing; rebuild the merge with current main'
MERGE_STALE = 'trusted-merge tested an older main; rebuild the merge with current main'
MERGE_MISMATCH = 'trusted-merge tested another tree than the merge of current main and the head'
MERGE_CONFLICT = 'the head does not merge cleanly with current main'


def refresh_title(pr, head):
    """pr-build.yml's run-name for a dispatched refresh, as the runs API reports it (display_title)."""
    return f'refresh #{pr} at {head}'


def parse_checks(text):
    value = tomllib.loads(text)
    fields(value, {'schema_version', 'workflow_id', 'status_creator_ids'}, 'merge checks')
    version(value, 'merge checks')
    ids = value['status_creator_ids']
    if (type(value['workflow_id']) is not int or value['workflow_id'] < 0 or
            not isinstance(ids, list) or any(type(i) is not int or i <= 0 for i in ids) or
            len(set(ids)) != len(ids)):
        raise RecordError('invalid trusted-check producer policy')
    return value


def timestamp(value):
    if not isinstance(value, str): raise RecordError('missing check timestamp')
    parsed = datetime.fromisoformat(value.replace('Z', '+00:00'))
    if parsed.tzinfo is None: raise RecordError('check timestamps must include a timezone')
    return parsed


def latest_statuses(statuses):
    if not isinstance(statuses, list): raise RecordError('incomplete status inventory')
    seen, latest = set(), {}
    for status in statuses:
        if (not isinstance(status, dict) or type(status.get('id')) is not int or
                status['id'] <= 0 or status['id'] in seen or not isinstance(status.get('context'), str)):
            raise RecordError('invalid or duplicate commit status')
        seen.add(status['id'])
        context = status['context']
        if context in (*CONTEXTS, MERGE_CONTEXT) and status['id'] > latest.get(context, {}).get('id', 0):
            latest[context] = status
    return latest


def run_reference(url, repository):
    # Explicit attempt links prevent old successful statuses from blessing a later rerun.
    match = re.fullmatch(re.escape(f'https://github.com/{repository}/actions/runs/') +
                         r'([1-9][0-9]*)/attempts/([1-9][0-9]*)', url or '')
    return tuple(map(int, match.groups())) if match else None


def assess_merge(statuses, context, expected_tree, settings):
    """The tested merge must be current main merged with this head, from the same trusted run.

    `expected_tree` is the tree of the head merged into current main, computed by the caller from
    Git objects (None when they conflict). The trusted run's other provenance checks (producer,
    exact run attempt, status job window) are assess_checks', which reads this status too.
    """
    latest = latest_statuses(statuses)
    status, build = latest.get(MERGE_CONTEXT), latest.get('trusted-build') or {}
    if expected_tree is None:
        return [MERGE_CONFLICT]
    if status is None:
        return [MERGE_MISSING]
    reasons = []
    attested = MERGE_ATTESTATION.fullmatch(status.get('description') or '')
    creator = status.get('creator') or {}
    if (creator.get('type') != 'Bot' or type(creator.get('id')) is not int or
            creator['id'] not in settings['status_creator_ids']):
        reasons.append('trusted-merge has an unapproved producer')
    if status.get('url') != f"https://api.github.com/repos/{context['repository']}/statuses/{context['head']}":
        reasons.append('trusted-merge has a wrong head/location')
    if run_reference(status.get('target_url'), context['repository']) != run_reference(
            build.get('target_url'), context['repository']):
        reasons.append('trusted-merge and trusted-build come from different run attempts')
    if attested is None:
        reasons.append('trusted-merge does not attest its tested tree')
    elif attested.group(2) != context['tooling']:
        reasons.append(MERGE_STALE)
    elif attested.group(1) != expected_tree:
        reasons.append(MERGE_MISMATCH)
    if status.get('state') != 'success':
        reasons.append('trusted-merge is not successful')
    return reasons


def refresh_binding(run, description, context):
    """Extra requirements for a dispatched refresh run; the shared checks still apply."""
    reasons = []
    attested = TOOLING_ATTESTATION.fullmatch(description)
    if run.get('head_branch') != 'main':
        reasons.append('refresh run was not dispatched on main')
    if run.get('display_title') != refresh_title(context['pr'], context['head']):
        reasons.append('refresh run-name does not name this PR and exact head')
    if not description.startswith(REFRESH_PREFIX) or attested is None or not attested.group(2):
        reasons.append('refresh run did not publish a refresh attestation with its PR binding')
    elif attested.group(1) != run.get('head_sha'):
        reasons.append('refresh attests tooling other than the dispatched main commit')
    # The run's creation after the head's last push is not readable for fork heads. The workflow
    # instead read the PR at its start and again before publishing and found this exact head and
    # base both times, so the head was current throughout the build (the race guard).
    return reasons


def assess_checks(statuses, run, jobs, context, settings):
    reasons = []
    latest = latest_statuses(statuses)
    if not settings['workflow_id'] or not settings['status_creator_ids']:
        reasons.append('trusted check producers are not configured')
    refs = []
    for name in CONTEXTS:
        status = latest.get(name)
        if status is None:
            reasons.append(f'missing {name}'); continue
        if status.get('state') != 'success': reasons.append(f'{name} is not successful')
        creator = status.get('creator') or {}
        if (creator.get('type') != 'Bot' or type(creator.get('id')) is not int or
                creator['id'] not in settings['status_creator_ids']):
            reasons.append(f'{name} has an unapproved producer')
        expected_url = f"https://api.github.com/repos/{context['repository']}/statuses/{context['head']}"
        if status.get('url') != expected_url: reasons.append(f'{name} has a wrong head/location')
        refs.append(run_reference(status.get('target_url'), context['repository']))
    if len(refs) != 2 or None in refs or len(set(refs)) != 1:
        reasons.append('build and scope do not identify one exact run attempt')
    elif not isinstance(run, dict):
        reasons.append('trusted workflow run is unavailable')
    else:
        rid, attempt = refs[0]
        description = (latest.get('trusted-build') or {}).get('description') or ''
        refresh = run.get('event') == 'workflow_dispatch'
        # GitHub reports a pull_request_target run's head_sha as the PR head, not the commit whose
        # workflow ran, so the run must name the exact PR head. The tooling is bound by the
        # trusted-build attestation checked below. The run's PR association reflects the PR's current
        # state, so its base proves only that the PR is up to date with approved main, not which
        # tooling an older run used.
        # A dispatched refresh instead runs main's own workflow: its head_sha is the dispatched main
        # commit, which must be the attested tooling. Its run-name names the PR and exact head; its
        # statuses live on that head commit; its attestation binds the PR number and base.
        expected = {'id': rid, 'run_attempt': attempt, 'workflow_id': settings['workflow_id'],
                    'path': WORKFLOW, 'event': 'workflow_dispatch' if refresh else 'pull_request_target',
                    'status': 'completed', 'conclusion': 'success',
                    'head_sha': context['tooling'] if refresh else context['head']}
        for key, value in expected.items():
            if run.get(key) != value or (type(value) is int and type(run.get(key)) is not int):
                reasons.append(f'trusted run has wrong {key}')
        if (run.get('repository') or {}).get('full_name') != context['repository']:
            reasons.append('trusted run belongs to another repository')
        if refresh:
            reasons += refresh_binding(run, description, context)
        elif description.startswith(REFRESH_PREFIX):
            reasons.append('a refresh attestation must come from a dispatched refresh run')
        associated = [] if refresh else run.get('pull_requests')
        mine = [p for p in associated if isinstance(p, dict) and type(p.get('number')) is int and
                p['number'] == context['pr']] if isinstance(associated, list) else []
        exact = any((p.get('head') or {}).get('sha') == context['head'] and
                    (p.get('base') or {}).get('sha') == context['base'] for p in mine)
        attested = TOOLING_ATTESTATION.fullmatch((latest.get('trusted-build') or {}).get('description') or '')
        if attested and attested.group(2):
            # The event's own PR binding; an association, when GitHub reports one, must agree.
            if int(attested.group(2)) != context['pr'] or attested.group(3) != context['base']:
                reasons.append('trusted-build attests another PR or base')
            if mine and not exact:
                reasons.append('trusted run PR association disagrees with the attested PR binding')
        elif not exact:
            # Older descriptions carry no PR binding: only the association can supply it.
            reasons.append('trusted run lacks the exact PR head/base association')
        if not refresh and (not context.get('head_repository') or
                (run.get('head_repository') or {}).get('full_name') != context['head_repository']):
            # A refresh runs from main; the exact head SHA, not a repository, binds its candidate.
            reasons.append('trusted run head repository differs from the PR head repository')
        if context['base'] != context['tooling']:
            reasons.append('PR base is not approved main; update the PR and refresh the trusted run')
        if not isinstance(jobs, list):
            reasons.append('trusted run jobs are unavailable')
        else:
            selected = {name: [j for j in jobs if isinstance(j, dict) and j.get('name') == name]
                        for name in ('candidate', 'status')}
            for name, matches in selected.items():
                if len(matches) != 1 or any(matches[0].get(k) != v or
                        (type(v) is int and type(matches[0].get(k)) is not int) for k, v in
                        {'run_id':rid, 'run_attempt':attempt, 'status':'completed', 'conclusion':'success'}.items()):
                    reasons.append(f'trusted {name} job is not complete in this attempt')
            if len(selected['status']) == 1:
                job = selected['status'][0]
                try:
                    start, end = timestamp(job.get('started_at')), timestamp(job.get('completed_at'))
                    if any(not start <= timestamp(s.get('created_at')) <= end for s in latest.values()):
                        reasons.append('status was not published during this attempt')
                except (ValueError, TypeError):
                    reasons.append('invalid status/job timestamp')
    build = latest.get('trusted-build')
    if build is not None:
        attested = TOOLING_ATTESTATION.fullmatch(build.get('description') or '')
        if attested is None:
            reasons.append('trusted-build does not attest its tooling commit; refresh the trusted run')
        elif attested.group(1) != context['tooling']:
            reasons.append('trusted-build ran with tooling other than approved main; refresh the trusted run')
    return {'passed': not reasons, 'reasons': reasons,
            **{k:context[k] for k in ('repository','head','base','tooling')},
            'status_ids': {k:v['id'] for k,v in latest.items()},
            'run': list(refs[0]) if refs and refs[0] else None}
