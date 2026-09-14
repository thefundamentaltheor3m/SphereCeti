# SPDX-License-Identifier: Apache-2.0
"""Independent append-only, API-identified cooperative review leases.

These reduce duplicate effort; they are not a distributed mutex or merge authority.
"""
from __future__ import annotations

from datetime import datetime, timedelta, timezone
import json
import re
import uuid

from .review_records import identity, intact
from .worker import WorkerError, commit, fields, require, timestamp
from .worker_cli import load_json

MARKER = '<!--sphereceti-worker-lease:v1 '
TTL = 300
BINDINGS = ('repository', 'pr', 'head', 'base', 'tooling')


def utcnow():
    return datetime.now(timezone.utc).replace(microsecond=0)


def stamp(value):
    return value.strftime('%Y-%m-%dT%H:%M:%SZ')


def encode(data):
    return MARKER + json.dumps(data, sort_keys=True, separators=(',', ':')) + '-->'


def parse(comment, repository, pr, allowed):
    require(isinstance(comment, dict), 'missing lease comment')
    body = comment.get('body')
    if not isinstance(body, str) or not body.startswith(MARKER) or identity(comment) not in allowed:
        return None
    require(intact(comment, repository, pr), 'edited or misplaced authorized lease; coordination is unknown')
    require(len(body) < 4000 and body.endswith('-->'), 'invalid lease envelope')
    data = load_json(body[len(MARKER):-3])
    fields(data, {*BINDINGS, 'stage', 'owner', 'worker', 'claim', 'sequence', 'previous', 'kind', 'expires'}, 'lease')
    require(data['repository'] == repository and type(data['pr']) is int and data['pr'] == pr,
            'wrong lease destination')
    for key in ('head', 'base', 'tooling'):
        commit(data[key], key)
    require(data['stage'] == 'review' and data['owner'] == identity(comment), 'lease identity mismatch')
    for key in ('worker', 'claim'):
        require(isinstance(data[key], str) and re.fullmatch(r'[a-zA-Z0-9_-]{1,64}', data[key]) is not None,
                'invalid lease identity')
    require(type(data['sequence']) is int and 0 <= data['sequence'] < 1000, 'invalid lease sequence')
    require(data['previous'] is None or (type(data['previous']) is int and data['previous'] > 0),
            'invalid lease predecessor')
    require(data['kind'] in ('acquire', 'renew', 'release'), 'invalid lease event')
    created, expires = timestamp(comment['created_at']), timestamp(data['expires'])
    require(-30 <= (expires - created).total_seconds() <= TTL + 30, 'lease lifetime exceeds bound')
    if data['kind'] != 'release':
        require(expires > created, 'lease already expired when created')
    return {**data, 'comment_id': comment['id'], 'created': created, 'expiry': expires}


def active_claims(comments, context, allowed, now):
    require(isinstance(comments, list), 'missing lease observation')
    require(all(isinstance(c, dict) and type(c.get('id')) is int and c['id'] > 0 for c in comments),
            'incomplete comment observation')
    require(len({c['id'] for c in comments}) == len(comments), 'duplicate comment observation')
    chains = {}
    for comment in sorted(comments, key=lambda c: c['id']):
        event = parse(comment, context['repository'], context['pr'], allowed)
        if event is None:
            continue
        require(event['created'] <= now + timedelta(seconds=30), 'future lease observation')
        if any(event[k] != context[k] for k in BINDINGS):
            continue
        key = (event['owner'], event['claim'])
        prior = chains.get(key)
        if prior is None:
            require(event['kind'] == 'acquire' and event['sequence'] == 0 and event['previous'] is None,
                    'lease history is incomplete')
            event['root'] = event['comment_id']
        else:
            require(event['kind'] != 'acquire' and prior['kind'] != 'release' and
                    event['previous'] == prior['comment_id'] and event['sequence'] == prior['sequence'] + 1 and
                    event['worker'] == prior['worker'] and event['created'] >= prior['created'],
                    'lease history fork or identity change')
            require(event['kind'] == 'release' or event['created'] < prior['expiry'],
                    'expired lease cannot be renewed')
            event['root'] = prior['root']
        chains[key] = event
    return sorted((event for event in chains.values() if event['kind'] != 'release' and event['expiry'] > now),
                  key=lambda event: event['root'])


class Lease:
    def __init__(self, api, context, allowed, owner, worker, *, now=utcnow):
        self.api, self.context, self.allowed = api, {k: context[k] for k in BINDINGS}, allowed
        self.owner, self.worker, self.now = owner, worker, now
        require(owner in allowed, 'worker identity is not authorized by approved policy')
        require(isinstance(worker, str) and re.fullmatch(r'[a-zA-Z0-9_-]{1,64}', worker) is not None,
                'worker ID must contain 1–64 letters, digits, underscores or hyphens')
        self.claim = uuid.uuid4().hex
        self.last = None

    def observe(self):
        comments = self.api.comments(self.context['repository'], self.context['pr'])
        return active_claims(comments, self.context, self.allowed, self.now())

    def append(self, kind):
        now = self.now()
        data = {**self.context, 'stage': 'review', 'owner': self.owner, 'worker': self.worker,
                'claim': self.claim, 'sequence': self.last['sequence'] + 1 if self.last else 0,
                'previous': self.last['comment_id'] if self.last else None, 'kind': kind,
                'expires': stamp(now if kind == 'release' else now + timedelta(seconds=TTL))}
        body = encode(data)
        posted = self.api.call(f"repos/{self.context['repository']}/issues/{self.context['pr']}/comments",
                               payload={'body': body})
        require(isinstance(posted, dict) and type(posted.get('id')) is int and posted['id'] > 0,
                'lease publication is unconfirmed; do not retry or dispatch')
        seen = self.api.call(f"repos/{self.context['repository']}/issues/comments/{posted['id']}")
        require(isinstance(seen, dict) and seen.get('id') == posted['id'] and seen.get('body') == body,
                'lease readback mismatch; do not dispatch')
        event = parse(seen, self.context['repository'], self.context['pr'], self.allowed)
        require(event is not None and event['owner'] == self.owner, 'lease publisher changed')
        self.last = event
        return event

    def acquire(self):
        if self.observe():
            return False
        self.append('acquire')
        # Concurrent claimants converge on the earliest API comment, not client clocks.
        claims = self.observe()
        if not claims or claims[0]['claim'] != self.claim or claims[0]['owner'] != self.owner:
            self.release()
            return False
        return True

    def check(self):
        require(self.last is not None, 'no confirmed lease')
        claims = self.observe()
        require(bool(claims) and claims[0]['claim'] == self.claim and claims[0]['owner'] == self.owner,
                'lease expired, lost or released; stop work')
        require(claims[0]['comment_id'] == self.last['comment_id'], 'another process changed this lease')
        if (self.last['expiry'] - self.now()).total_seconds() <= 120:
            self.append('renew')
            claims = self.observe()
            require(bool(claims) and claims[0]['claim'] == self.claim and claims[0]['owner'] == self.owner and
                    claims[0]['comment_id'] == self.last['comment_id'], 'lease renewal lost; stop work')

    def release(self):
        if self.last is not None and self.last['kind'] != 'release':
            self.append('release')
