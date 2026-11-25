"""Halt the merge controller after an unexpected refusal, until a maintainer acknowledges it.

Decision 3 on #100. When GitHub refuses a merge PUT for any reason other than the expected stale
combination (`rejected_unexpected`), the controller opens a halt issue with its own job token. The
issue is authored by github-actions[bot] and carries a machine-readable marker. Every applying run,
scheduled or dispatched, reads those issues and refuses to act while any halt is unacknowledged.

The acknowledgement is a maintainer action. It is an unedited comment on the halt issue whose first
line is `/sphereceti acknowledge-halt`, posted after the halt by a human whose identity is in policy
authorized_reviewers and whose association is OWNER, MEMBER or COLLABORATOR. Closing the issue
alone does not acknowledge it, and the bot can never acknowledge its own halt.
"""
from __future__ import annotations

import json
import re
from urllib.parse import quote

from .review_records import RecordError

MARKER = '<!--sphereceti-merge-halt:v1 '
TITLE = 'Merge controller halted after an unexpected refusal'
ACKNOWLEDGE = '/sphereceti acknowledge-halt'
BOT_LOGIN = 'github-actions[bot]'
BOT_ID = 41898282  # github-actions[bot], the job token's identity (verified with the trusted statuses)
MAINTAINERS = ('OWNER', 'MEMBER', 'COLLABORATOR')


def issue(run, pr, head, refusal):
    """The exact halt issue the job token may create: fixed title, marker first, no free-form input."""
    if (type(run) is not int or run <= 0 or type(pr) is not int or pr <= 0 or
            not isinstance(head, str) or not re.fullmatch(r'[0-9a-f]{40}', head) or not isinstance(refusal, dict)):
        raise RecordError('invalid halt record')
    status = str(refusal.get('status', ''))
    message = str(refusal.get('message', ''))[:200]
    if not re.fullmatch(r'4[0-9]{2}', status):
        raise RecordError('invalid halt refusal')
    marker = {'run': run, 'pr': pr, 'head': head, 'status': status}
    body = (MARKER + json.dumps(marker, sort_keys=True) + '-->\n\n'
            f'The merge controller stopped: GitHub refused the merge of #{pr} at `{head}` with HTTP {status}, '
            'which is not the expected stale-combination refusal. Scheduled and dispatched controller runs '
            'refuse to act until a maintainer acknowledges this.\n\n'
            f'GitHub said: `{message.replace("`", "")}`\n\n'
            f'To acknowledge after investigating, comment `{ACKNOWLEDGE}` on this issue.')
    return {'title': TITLE, 'body': body}


def marker(item):
    """The halt marker of a bot-authored issue, or None."""
    body = item.get('body') if isinstance(item, dict) else None
    user = (item.get('user') or {}) if isinstance(item, dict) else {}
    if (not isinstance(body, str) or not body.startswith(MARKER) or user.get('id') != BOT_ID or
            user.get('type') != 'Bot' or 'pull_request' in item):
        return None
    try:
        value = json.loads(body[len(MARKER):body.index('-->')])
    except ValueError:
        return None
    return value if isinstance(value, dict) else None


def acknowledged(halt, comments, maintainers):
    """The acknowledging comment, or None. Fail closed on anything unexpected."""
    for c in sorted(comments, key=lambda c: c.get('id', 0)):
        user, body = c.get('user') or {}, c.get('body')
        if (isinstance(body, str) and body.strip().splitlines()[:1] == [ACKNOWLEDGE] and
                user.get('type') == 'User' and f"user:{user.get('id')}" in maintainers and
                c.get('author_association') in MAINTAINERS and c.get('created_at') == c.get('updated_at') and
                isinstance(c.get('created_at'), str) and c['created_at'] > halt.get('created_at', '')):
            return {'comment': c.get('id'), 'by': f"user:{user['id']}", 'at': c['created_at']}
    return None


def assess(issues, comments_of, maintainers):
    """Every halt issue with its acknowledgement; `halted` lists those not yet acknowledged."""
    halts = []
    for item in sorted(issues, key=lambda i: i.get('number', 0)):
        found = marker(item)
        if found is None:
            continue
        ack = acknowledged(item, comments_of(item['number']), maintainers)
        halts.append({'issue': item['number'], 'run': found.get('run'), 'pr': found.get('pr'),
                      'head': found.get('head'), 'status': found.get('status'), 'acknowledged': ack})
    return {'halts': halts, 'halted': [h for h in halts if h['acknowledged'] is None]}


def read(client, repository, maintainers):
    """GET-only: bot-authored issues in any state, then the comments of each halt issue."""
    pages = client.call(f'repos/{repository}/issues?creator={quote(BOT_LOGIN, safe="")}&state=all&per_page=100',
                        paginate=True)
    if not isinstance(pages, list) or not pages or any(not isinstance(p, list) for p in pages):
        raise RecordError('incomplete halt inventory')

    def comments_of(number):
        found = client.call(f'repos/{repository}/issues/{number}/comments?per_page=100', paginate=True)
        if not isinstance(found, list) or not found or any(not isinstance(p, list) for p in found):
            raise RecordError('incomplete halt acknowledgement inventory')
        return [c for p in found for c in p]
    return assess([i for p in pages for i in p], comments_of, maintainers)


def reason(halted):
    first = halted[0]
    return (f"merge controller halted by an unexpected refusal (HTTP {first['status']}, #{first['pr']}, run "
            f"{first['run']}); a maintainer acknowledges with `{ACKNOWLEDGE}` on issue #{first['issue']}"
            + (f' and {len(halted) - 1} more' if len(halted) > 1 else ''))
