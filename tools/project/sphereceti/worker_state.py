# SPDX-License-Identifier: Apache-2.0
"""Explicit append-only operational receipts on an already initialized reviews branch.

This independently authored journal is a cache of run outcomes, not live review authority.
"""
from __future__ import annotations

import base64
import hashlib
import json
import re

from .worker import commit, require
from .worker_cli import load_json

ANCHOR = 'sphereceti-state.json'
SCHEMA = 'sphereceti.worker-state/v1'


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True)


def expected_anchor(project):
    return {'schema': SCHEMA, 'repository': project.repository, 'branch': 'reviews'}


def blob(api, repository, oid):
    commit(oid, 'blob')
    value = api.call(f'repos/{repository}/git/blobs/{oid}')
    require(isinstance(value, dict) and value.get('encoding') == 'base64' and
            type(value.get('size')) is int and 0 <= value['size'] <= 100000 and isinstance(value.get('content'), str),
            'invalid state blob')
    try:
        raw = base64.b64decode(''.join(value['content'].split()), validate=True)
    except (ValueError, KeyError, TypeError) as error:
        from .worker import WorkerError
        raise WorkerError('invalid state blob encoding') from error
    require(len(raw) == value['size'], 'state blob length mismatch')
    require(hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == oid,
            'state blob object mismatch')
    return raw


def state_tree(api, project):
    repo = project.repository
    ref = api.call(f'repos/{repo}/git/ref/heads/reviews')
    require(isinstance(ref, dict) and ref.get('ref') == 'refs/heads/reviews' and
            isinstance(ref.get('object'), dict) and ref['object'].get('type') == 'commit', 'reviews branch must be initialized explicitly')
    head = commit(ref['object']['sha'], 'state head')
    tree = api.call(f'repos/{repo}/git/trees/{head}?recursive=1')
    require(isinstance(tree, dict) and tree.get('truncated') is False and isinstance(tree.get('tree'), list),
            'state tree is truncated or unavailable')
    commit(tree.get('sha'), 'state tree')
    entries = {}
    for entry in tree['tree']:
        require(isinstance(entry, dict) and isinstance(entry.get('path'), str), 'invalid state entry')
        name = entry['path']
        require(name not in entries, 'duplicate state path')
        if name == 'runs':
            require(entry.get('type') == 'tree' and entry.get('mode') == '040000', 'invalid runs directory')
        else:
            require(name == ANCHOR or re.fullmatch(r'runs/[0-9a-f]{64}\.json', name) is not None,
                    'unexpected content on reviews branch')
            require(entry.get('type') == 'blob' and entry.get('mode') == '100644', 'invalid state file mode')
        commit(entry.get('sha'), 'state entry')
        entries[name] = entry
    require(ANCHOR in entries, 'reviews branch anchor is missing; initialization is a separate operator action')
    require(load_json(blob(api, repo, entries[ANCHOR]['sha']).decode()) == expected_anchor(project),
            'reviews branch anchor does not match this repository/schema')
    return head, tree['sha'], entries


def publish_state(api, project, policy, receipt, revalidate):
    require(policy.review_generation and policy.posting, 'operational state publication is disabled')
    require(project.reviews_branch == 'reviews' and project.default_branch != 'reviews' and
            project.archive_branch != 'reviews', 'operational state destination is not isolated')
    require(receipt.get('repository') == project.repository and type(receipt.get('pr')) is int and receipt['pr'] > 0,
            'wrong state receipt destination')
    require(receipt.get('state') in ('complete', 'partial', 'error') and receipt.get('executed') is True,
            'state publication requires an executed review receipt')
    for name in ('head', 'base', 'tooling'):
        commit(receipt.get(name), name)
    # Whitelist public facts. No local paths, provider text, credentials, prompts or budgets.
    event = {key: receipt[key] for key in ('repository', 'pr', 'head', 'base', 'tooling', 'state')}
    coordination = receipt['coordination']
    require(isinstance(coordination, dict) and isinstance(coordination.get('owner'), str) and
            re.fullmatch(r'user:[1-9][0-9]*', coordination['owner']) is not None and
            isinstance(coordination.get('claim'), str) and re.fullmatch(r'[0-9a-f]{32}', coordination['claim']) is not None and
            type(coordination.get('lease_comment')) is int and coordination['lease_comment'] > 0,
            'state receipt lacks confirmed coordination identity')
    user = api.call('user')
    require(isinstance(user, dict) and user.get('type') == 'User' and
            type(user.get('id')) is int and f"user:{user['id']}" == coordination['owner'] and
            coordination['owner'] in policy.authorized_reviewers, 'state publisher identity changed or is unauthorized')
    event.update(schema=SCHEMA, authority='operational-only',
                 owner=coordination['owner'], claim=coordination['claim'], lease_comment=coordination['lease_comment'])
    encoded = canonical(event).encode()
    path = 'runs/' + hashlib.sha256(encoded).hexdigest() + '.json'
    revalidate()
    head, tree, entries = state_tree(api, project)
    if path in entries:
        require(blob(api, project.repository, entries[path]['sha']) == encoded, 'immutable state collision')
        return {'state': 'confirmed', 'path': path, 'commit': head, 'adopted': True}
    repo = project.repository
    created = api.call(f'repos/{repo}/git/blobs', payload={'content': encoded.decode(), 'encoding': 'utf-8'})
    require(isinstance(created, dict), 'missing created blob')
    oid = commit(created.get('sha'), 'new state blob')
    require(oid == hashlib.sha1(b'blob ' + str(len(encoded)).encode() + b'\0' + encoded).hexdigest(),
            'created state blob mismatch')
    created = api.call(f'repos/{repo}/git/trees', payload={'base_tree': tree,
                      'tree': [{'path': path, 'mode': '100644', 'type': 'blob', 'sha': oid}]})
    require(isinstance(created, dict), 'missing created tree')
    new_tree = commit(created.get('sha'), 'new state tree')
    created = api.call(f'repos/{repo}/git/commits', payload={'message': 'Record SphereCeti worker outcome',
                                                        'tree': new_tree, 'parents': [head]})
    require(isinstance(created, dict), 'missing created commit')
    new_head = commit(created.get('sha'), 'new state commit')
    revalidate()
    latest = api.call(f'repos/{repo}/git/ref/heads/reviews')
    require(isinstance(latest, dict) and isinstance(latest.get('object'), dict) and latest['object'].get('sha') == head, 'reviews branch advanced; rerun explicit sync')
    # Git rejects a non-fast-forward race. No branch creation or forced replacement.
    api.call(f'repos/{repo}/git/refs/heads/reviews', payload={'sha': new_head, 'force': False}, method='PATCH')
    confirmed, _, files = state_tree(api, project)
    require(confirmed == new_head and path in files and blob(api, repo, files[path]['sha']) == encoded,
            'state publication readback is unconfirmed')
    return {'state': 'confirmed', 'path': path, 'commit': confirmed, 'adopted': False}


def sync_receipt(args, project, policy):
    """Explicitly retry one local receipt; never run a provider or create a branch."""
    from urllib.parse import quote
    from .config import resource_text, parse_policy, parse_project
    from .review_post import GitHub
    from .worker_cli import read_json
    from .worker_leases import parse as parse_lease
    require(policy.review_generation and policy.posting, 'operational state publication is disabled')
    receipt = read_json(args.receipt)
    require(isinstance(receipt, dict) and receipt.get('schema') == 'sphereceti.worker-round/v1',
            'unsupported worker receipt')
    api = GitHub()
    def refresh():
        main = api.call(f'repos/{project.repository}/commits/{quote(project.default_branch, safe="")}')
        require(isinstance(main, dict), 'approved main unavailable')
        revision = commit(main.get('sha'), 'approved main')
        for source, resource in (('sphereceti.toml', 'sphereceti.toml'),
                                 ('policy/automation.toml', 'automation.toml')):
            remote = api.call(f'repos/{project.repository}/contents/{source}?ref={revision}')
            require(isinstance(remote, dict) and remote.get('type') == 'file', 'approved policy unavailable')
            raw = blob(api, project.repository, remote.get('sha'))
            require(raw == resource_text(resource).encode(), 'installed identity/policy differs from approved main')
            require((parse_policy(raw.decode()) == policy if source.startswith('policy/') else
                     parse_project(raw.decode()) == project), 'effective identity/policy differs from approved main')
        coordination = receipt.get('coordination')
        require(isinstance(coordination, dict) and type(coordination.get('lease_comment')) is int and
                coordination['lease_comment'] > 0, 'receipt lacks a confirmed lease')
        pr = receipt.get('pr')
        require(type(pr) is int and pr > 0 and receipt.get('repository') == project.repository,
                'wrong receipt destination')
        comment = api.call(f"repos/{project.repository}/issues/comments/{coordination['lease_comment']}")
        event = parse_lease(comment, project.repository, pr, policy.authorized_reviewers)
        require(event is not None and event['kind'] == 'acquire' and
                all(event[key] == receipt.get(key) for key in ('head','base','tooling')) and
                event['claim'] == coordination.get('claim') and event['owner'] == coordination.get('owner'),
                'receipt does not match its API-authenticated acquisition')
        latest = api.call(f'repos/{project.repository}/commits/{quote(project.default_branch, safe="")}')
        require(isinstance(latest, dict) and latest.get('sha') == revision, 'approved policy advanced during state checks')
    publication = publish_state(api, project, policy, receipt, refresh)
    return {'schema': 'sphereceti.worker-round/v1', 'state': 'synced', 'executed': False,
            'state_publication': publication}
