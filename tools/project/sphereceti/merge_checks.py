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
        if context in CONTEXTS and status['id'] > latest.get(context, {}).get('id', 0):
            latest[context] = status
    return latest


def run_reference(url, repository):
    # Explicit attempt links prevent old successful statuses from blessing a later rerun.
    match = re.fullmatch(re.escape(f'https://github.com/{repository}/actions/runs/') +
                         r'([1-9][0-9]*)/attempts/([1-9][0-9]*)', url or '')
    return tuple(map(int, match.groups())) if match else None


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
        expected = {'id': rid, 'run_attempt': attempt, 'workflow_id': settings['workflow_id'],
                    'path': WORKFLOW, 'event': 'pull_request_target', 'status': 'completed',
                    'conclusion': 'success', 'head_sha': context['tooling']}
        for key, value in expected.items():
            if run.get(key) != value or (type(value) is int and type(run.get(key)) is not int):
                reasons.append(f'trusted run has wrong {key}')
        if (run.get('repository') or {}).get('full_name') != context['repository']:
            reasons.append('trusted run belongs to another repository')
        associated = run.get('pull_requests')
        if not isinstance(associated, list) or not any(
                isinstance(p, dict) and type(p.get('number')) is int and p['number'] == context['pr'] and
                (p.get('head') or {}).get('sha') == context['head'] and
                (p.get('base') or {}).get('sha') == context['base'] for p in associated):
            reasons.append('trusted run lacks the exact PR head/base association')
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
    return {'passed': not reasons, 'reasons': reasons,
            **{k:context[k] for k in ('repository','head','base','tooling')},
            'status_ids': {k:v['id'] for k,v in latest.items()},
            'run': list(refs[0]) if refs and refs[0] else None}
