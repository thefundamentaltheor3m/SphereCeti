"""Lifecycle diagnostics adapted from TauCeti contributors (Apache-2.0).

TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5:
scripts/pr_status/{labels,conflicts,stuck_alerts}.py and scripts/housekeeping.py.
Use SphereCeti's shared observation instead of parsing TauCeti scoreboards.
"""
from datetime import datetime, timezone
import hashlib
import json
import re
import tomllib

from .config import fields, version
from .merge_checks import timestamp
from .review_records import RecordError

LABELS = {'human_review': 'sphereceti:human-review', 'blocked': 'sphereceti:blocked',
          'eligible': 'sphereceti:observed-eligible'}
CONFLICT = 'sphereceti:conflict'
MANAGED = frozenset([*LABELS.values(), CONFLICT])
HOLD = {'keep', 'hold', 'wip', 'human', 'do-not-close', 'blocked'}
RED = {'failure', 'timed_out', 'action_required', 'startup_failure'}
SHA = re.compile(r'[0-9a-f]{40}\Z')


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def parse_settings(text):
    data = tomllib.loads(text)
    fields(data, {'schema_version', 'labels_enabled', 'writer_user_id', 'stuck_hours',
                  'housekeeping_hours'}, 'lifecycle')
    version(data, 'lifecycle')
    if (type(data['labels_enabled']) is not bool or type(data['writer_user_id']) is not int
            or data['writer_user_id'] < 0):
        raise RecordError('invalid lifecycle publication policy')
    for name in ('stuck_hours', 'housekeeping_hours'):
        if type(data[name]) is not int or not 1 <= data[name] <= 8760:
            raise RecordError('lifecycle age thresholds must be 1..8760 hours')
    return data


def pr_plan(pr, observation, current, settings, *, now=None):
    """Pure metadata plan; never supplies review or merge authority."""
    now = now or datetime.now(timezone.utc)
    if (pr.get('state') not in ('open', 'closed') or type(pr.get('merged')) is not bool
            or type(pr.get('draft')) is not bool or type(pr.get('number')) is not int
            or pr['number'] <= 0 or 'auto_merge' not in pr):
        raise RecordError('incomplete lifecycle fields')
    for sha in (current, pr['head']['sha'], pr['base']['sha']):
        if not isinstance(sha, str) or not SHA.fullmatch(sha):
            raise RecordError('invalid lifecycle revision')
    labels = pr.get('labels')
    if (not isinstance(labels, list) or any(not isinstance(label, str) for label in labels)
            or len(labels) != len(set(labels))):
        raise RecordError('incomplete or duplicate labels')
    age = (now - timestamp(pr['updated_at'])).total_seconds() / 3600
    if age < 0:
        raise RecordError('PR activity is in the future')
    present = set(labels) & MANAGED
    result = {'pr': pr['number'], 'head': pr['head']['sha'], 'base': pr['base']['sha'],
              'main': current, 'state': 'observed', 'conflict': 'unknown', 'alerts': [],
              'recommendations': [], 'add': [], 'remove': [], 'merge_allowed': False}
    terminal = pr['state'] == 'closed' or pr['merged']
    held = bool({name.lower() for name in labels} & HOLD)
    if not terminal and (held or pr['draft'] or pr['auto_merge'] is not None or pr['base']['ref'] != 'main'):
        result['state'] = 'human_managed'
        return result
    if terminal:
        result.update(state='merged' if pr['merged'] else 'closed', remove=sorted(present))
        return result
    if observation is None:
        raise RecordError('shared merge observation is unavailable')
    expected = {'pr': pr['number'], 'head': pr['head']['sha'], 'base': pr['base']['sha'],
                'tooling': current, 'repository': pr['base']['repo']['full_name']}
    if any(observation.get(k) != v for k, v in expected.items()):
        raise RecordError('lifecycle observation belongs to different revisions or repository')
    state = observation.get('eligibility')
    if state not in LABELS or observation.get('merge_allowed') is not False:
        raise RecordError('invalid shared observation')
    result['observation'] = state
    result['observation_digest'] = digest(observation)
    desired = {LABELS[state]}
    # Conflict is independent of review/CI state. Unknown preserves existing conflict label.
    if pr.get('mergeable') is False:
        result['conflict'] = 'conflicting'
        desired.add(CONFLICT)
    elif pr.get('mergeable') is True:
        result['conflict'] = 'clear'
    elif pr.get('mergeable') is None:
        if CONFLICT in present:
            desired.add(CONFLICT)
        result['state'] = 'unknown'
    else:
        raise RecordError('invalid mergeability')
    if state == 'eligible' and age >= settings['stuck_hours']:
        result['alerts'].append('eligible_now_but_quiet')
    if state == 'blocked' and age >= settings['housekeeping_hours']:
        result['recommendations'].append('human_review_of_quiet_blocked_pr')
    result.update(add=sorted(desired - present), remove=sorted(present - desired))
    return result


def main_health(tip, workflow, runs, repository):
    """Most recent conclusive push run; cancellation/pending never clears an older failure."""
    if not isinstance(tip, str) or not SHA.fullmatch(tip):
        raise RecordError('invalid main revision')
    if (not isinstance(workflow, dict) or type(workflow.get('id')) is not int or workflow['id'] <= 0
            or workflow.get('path') != '.github/workflows/ci.yml'
            or not isinstance(workflow.get('state'), str)):
        raise RecordError('invalid main CI workflow identity')
    if not isinstance(runs, list) or len(runs) > 30:
        raise RecordError('invalid bounded main CI window')
    seen = set()
    for row in runs:
        if (not isinstance(row, dict) or type(row.get('id')) is not int or row['id'] <= 0 or row['id'] in seen
                or row.get('workflow_id') != workflow['id'] or row.get('head_branch') != 'main'
                or row.get('event') != 'push' or row.get('path') != workflow['path']
                or not isinstance(row.get('repository'), dict)
                or (row.get('repository') or {}).get('full_name') != repository
                or not isinstance(row.get('head_sha'), str) or not SHA.fullmatch(row['head_sha'])
                or row.get('status') not in ('queued', 'in_progress', 'completed', 'waiting', 'pending', 'requested')):
            raise RecordError('incomplete or misbound main CI run')
        timestamp(row['created_at'])
        seen.add(row['id'])
    conclusive = sorted((r for r in runs if r['status'] == 'completed' and
                         r.get('conclusion') in RED | {'success'}),
                        key=lambda r: (timestamp(r['created_at']), r['id']), reverse=True)
    last = conclusive[0] if conclusive else None
    return {'main': tip, 'workflow_id': workflow['id'], 'workflow_state': workflow['state'],
            'state': 'disabled' if workflow['state'] != 'active' else
                     'unknown' if last is None else 'red' if last['conclusion'] in RED else
                     'green' if last['head_sha'] == tip else 'pending_tip',
            'last_conclusive': None if last is None else {k: last[k] for k in
                                                        ('id', 'head_sha', 'conclusion', 'created_at')},
            'current_tip_passed': last is not None and last['head_sha'] == tip and last['conclusion'] == 'success',
            'window': len(runs), 'merge_allowed': False}
