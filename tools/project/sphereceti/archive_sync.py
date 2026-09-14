"""Append-only sync with confirmed readback, adapted from pinned TauCetiReview runner/archive.py.

TauCetiProject/TauCetiReview@afb424eda89e8ac96d9eb69f6a88972055a4cd1b,
Apache-2.0, TauCetiReview contributors. GitHub transport uses tree objects, never checkout code.
"""
from __future__ import annotations

import base64
import hashlib
import json
import subprocess
import tomllib

from .archive_store import (ArchiveError, MAX_FILE, MAX_FILES, MAX_TOTAL, locked,
                            require, snapshot, validate)
from .config import fields, parse_policy, parse_project, resource_text, version
from .review_resources import tooling_files


def parse_archive_policy(text):
    policy = tomllib.loads(text)
    fields(policy, {'schema_version', 'enabled', 'publish_text'}, 'archive policy')
    version(policy, 'archive policy')
    require(all(type(policy[k]) is bool for k in ('enabled', 'publish_text')), 'invalid archive switches')
    return policy


def sync(store, repository, transport):
    """Snapshot without draining; retry fresh parents; drain only exact confirmed bytes.

    The local journal remains durable after a successful sync. A failed/ambiguous remote
    operation never authorizes deletion. New concurrently queued files stay in the outbox.
    """
    with locked(store):
        files = snapshot(store / 'outbox') if (store / 'outbox').exists() else {}
        validate(files, repository)
    if not files:
        return {'state': 'empty', 'files': 0}
    for attempt in range(3):
        parent, remote = transport.fetch()
        validate(remote, repository, anchored=True)
        for name, body in files.items():
            require(name not in remote or remote[name] == body, 'immutable remote path collision')
        additions = {n: b for n, b in files.items() if n not in remote}
        validate({**remote, **additions}, repository, anchored=True)
        if additions:
            try:
                transport.append(parent, additions)
            except ArchiveError:
                # A timeout may have committed successfully; only readback decides.
                pass
        _, confirmed = transport.fetch()
        validate(confirmed, repository, anchored=True)
        if all(confirmed.get(n) == b for n, b in files.items()):
            with locked(store):
                current = snapshot(store / 'outbox')
                validate(current, repository)
                for name, body in files.items():
                    require(name not in current or current[name] == body, 'outbox changed during sync')
                remaining = {n: b for n, b in current.items() if n not in files}
                # A concurrent enqueue may reuse a blob in this batch. Keep it until every
                # pending referencing record has been confirmed, even though it is remote.
                for name, body in list(remaining.items()):
                    if name.startswith('records/'):
                        key = json.loads(body)['text_blob']
                        if key:
                            path = f'blobs/{key[:2]}/{key}.gz'
                            remaining[path] = current[path]
                validate(remaining, repository)
                for name in files.keys() - remaining.keys():
                    (store / 'outbox' / name).unlink(missing_ok=True)
            return {'state': 'confirmed', 'files': len(files), 'attempts': attempt + 1}
    raise ArchiveError('archive sync did not confirm after three attempts; outbox retained')


def git_hash(body):
    return hashlib.sha1(b'blob ' + str(len(body)).encode() + b'\0' + body).hexdigest()


def oid(value):
    import re
    require(isinstance(value, str) and re.fullmatch(r'[0-9a-f]{40}', value), 'invalid Git object ID')
    return value


class GitHubArchive:
    """Fixed same-repository branch, approved installed code/policy, non-force ref update."""
    def __init__(self, project, *, call=None):
        require(project.default_branch == 'main' and project.archive_branch == 'review-data'
                and project.reviews_branch == 'reviews', 'unsupported source/state branch layout')
        self.project = project
        self.prefix = f'repos/{project.repository}/git/'
        self.call = call or self.api
        self.tree_ids = {}
        self.with_text = False

    @staticmethod
    def api(endpoint, *, payload=None, method=None):
        command = ['gh', 'api', '--hostname', 'github.com', endpoint]
        if payload is not None:
            command += ['--method', method or 'POST', '--input', '-']
        try:
            result = subprocess.run(command, input=json.dumps(payload) if payload is not None else None,
                                    text=True, capture_output=True, timeout=60)
        except (OSError, subprocess.SubprocessError) as error:
            raise ArchiveError('archive API operation unavailable; outbox retained') from error
        require(result.returncode == 0 and len(result.stdout) <= 8 * MAX_FILE,
                'archive API operation unconfirmed; outbox retained')
        try:
            return json.loads(result.stdout)
        except ValueError as error:
            raise ArchiveError('invalid archive API response') from error

    def tree(self, branch):
        ref = self.call(self.prefix + 'ref/heads/' + branch)
        require(isinstance(ref, dict) and ref.get('ref') == 'refs/heads/' + branch
                and isinstance(ref.get('object'), dict) and ref['object'].get('type') == 'commit', 'invalid branch reference')
        revision = oid(ref['object'].get('sha'))
        commit = self.call(self.prefix + 'commits/' + revision)
        require(isinstance(commit, dict) and isinstance(commit.get('tree'), dict), 'invalid commit response')
        tree_id = oid(commit['tree'].get('sha'))
        data = self.call(self.prefix + 'trees/' + tree_id + '?recursive=1')
        require(isinstance(data, dict) and data.get('truncated') is False and isinstance(data.get('tree'), list)
                and len(data['tree']) <= 10000, 'incomplete or oversized Git tree')
        entries = {}
        for entry in data['tree']:
            require(isinstance(entry, dict) and isinstance(entry.get('path'), str), 'invalid tree entry')
            name = entry['path']
            require(name not in entries, 'duplicate Git path')
            require(name and not name.startswith('/') and all(p not in ('', '.', '..') for p in name.split('/'))
                    and '\\' not in name, 'invalid Git path')
            entries[name] = entry
        self.tree_ids[revision] = tree_id
        return revision, entries

    def blob(self, entry):
        require(entry.get('type') == 'blob' and entry.get('mode') == '100644'
                and type(entry.get('size')) is int and 0 <= entry['size'] <= MAX_FILE, 'invalid archive file mode/size')
        sha = oid(entry.get('sha'))
        data = self.call(self.prefix + 'blobs/' + sha)
        require(isinstance(data, dict) and data.get('encoding') == 'base64'
                and isinstance(data.get('content'), str), 'invalid blob response')
        try:
            body = base64.b64decode(data['content'].replace('\n', ''), validate=True)
        except ValueError as error:
            raise ArchiveError('invalid encoded Git blob') from error
        require(len(body) == entry['size'] and git_hash(body) == sha, 'Git blob integrity mismatch')
        return body

    def authorize(self):
        """Authority comes from exact remote main; cwd/candidate/operator policy cannot enable writes."""
        _, entries = self.tree('main')
        installed = tooling_files()
        for name, body in installed.items():
            entry = entries.get(name, {})
            require(entry.get('type') == 'blob' and entry.get('mode') == '100644'
                    and entry.get('sha') == git_hash(body), 'installed archive tooling does not match approved main')
        require(parse_project(resource_text('sphereceti.toml')) == self.project, 'archive project identity mismatch')
        policy = parse_archive_policy(resource_text('archive.toml'))
        require(policy['enabled'] and parse_policy(resource_text('automation.toml')).posting,
                'archive publication is disabled by approved main policy')
        require(not self.with_text or policy['publish_text'], 'text publication is disabled by approved main policy')

    def fetch(self):
        revision, entries = self.tree('review-data')
        files = {}
        total = 0
        directories = {name.rsplit('/', depth)[0] for name, e in entries.items()
                       if e.get('type') != 'tree' for depth in range(1, name.count('/') + 1)}
        for name, entry in entries.items():
            if entry.get('type') == 'tree':
                require(entry.get('mode') == '040000' and name in directories, 'unexpected archive directory')
                continue
            total += entry.get('size', MAX_TOTAL + 1) if type(entry.get('size')) is int else MAX_TOTAL + 1
            require(len(files) < MAX_FILES and total <= MAX_TOTAL, 'remote archive inventory limit exceeded')
            files[name] = self.blob(entry)
        validate(files, self.project.repository, anchored=True)
        return revision, files

    def append(self, parent, additions):
        self.with_text = any(n.startswith('blobs/') or
                             (n.startswith('records/') and json.loads(b)['text_blob'] is not None)
                             for n, b in additions.items())
        self.authorize()
        entries = []
        for name, body in sorted(additions.items()):
            result = self.call(self.prefix + 'blobs', payload={
                'encoding': 'base64', 'content': base64.b64encode(body).decode()})
            require(isinstance(result, dict) and result.get('sha') == git_hash(body), 'created Git blob mismatch')
            entries.append({'path': name, 'type': 'blob', 'mode': '100644', 'sha': result['sha']})
        tree = self.call(self.prefix + 'trees', payload={'base_tree': self.tree_ids[parent], 'tree': entries})
        require(isinstance(tree, dict), 'invalid created tree')
        commit = self.call(self.prefix + 'commits', payload={
            'message': 'Archive SphereCeti review evidence', 'tree': oid(tree.get('sha')), 'parents': [parent]})
        require(isinstance(commit, dict), 'invalid created commit')
        revision = oid(commit.get('sha'))
        self.authorize()  # Policy/tooling may change while blobs are uploaded.
        self.call(self.prefix + 'refs/heads/review-data', method='PATCH',
                  payload={'sha': revision, 'force': False})
