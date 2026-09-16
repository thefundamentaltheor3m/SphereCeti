"""Real disposable Git object store behind the archive's GitHub API seam; no network."""
from contextlib import ExitStack
import base64
import json
import os
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
from sphereceti import archive_sync
from sphereceti.archive_store import ArchiveError, SCHEMA, encode
from sphereceti.config import parse_project, resource_text
from sphereceti.review_resources import tooling_files

REPO = 'thefundamentaltheor3m/SphereCeti'


def enabled_resource(name):
    value = resource_text(name)
    if name == 'archive.toml':
        value = value.replace('enabled = false', 'enabled = true')
    if name == 'automation.toml':
        value = value.replace('posting = false', 'posting = true')
    return value


def enabled(*, text=False):
    def policy(name):
        value = enabled_resource(name)
        return value.replace('publish_text = false', 'publish_text = true') if text and name == 'archive.toml' else value
    stack = ExitStack()
    stack.enter_context(patch('sphereceti.archive_sync.resource_text', side_effect=policy))
    stack.enter_context(patch('sphereceti.review_resources.resource_text', side_effect=policy))
    return stack


class GitAPI:
    def __init__(self, root):
        self.repo = root / 'objects.git'
        self.env = {**os.environ, 'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': '/dev/null',
                    'GIT_AUTHOR_NAME': 'Archive fixture', 'GIT_AUTHOR_EMAIL': 'fixture@example.invalid',
                    'GIT_COMMITTER_NAME': 'Archive fixture', 'GIT_COMMITTER_EMAIL': 'fixture@example.invalid',
                    'GIT_INDEX_FILE': str(root / 'index')}
        subprocess.run(['git', 'init', '--bare', '-q', str(self.repo)], check=True, env=self.env)
        self.calls = []
        self.before_update = None
        self.after_update = None
        self.outage = False
        self.commit_branch('main', tooling_files())
        self.commit_branch('review-data', {'ARCHIVE.json': encode({'schema': SCHEMA,
                           'repository': REPO, 'branch': 'review-data'})})
        self.transport = archive_sync.GitHubArchive(parse_project(resource_text('sphereceti.toml')), call=self)

    def git(self, *args, data=None):
        p = subprocess.run(['git', '--git-dir', str(self.repo), *args], input=data,
                           capture_output=True, env=self.env)
        if p.returncode:
            raise ArchiveError('fixture Git operation failed')
        return p.stdout

    def tree(self, files, base=None):
        self.git('read-tree', base or '--empty')
        for path, body in files.items():
            sha = self.git('hash-object', '-w', '--stdin', data=body).decode().strip()
            self.git('update-index', '--add', '--cacheinfo', '100644', sha, path)
        return self.git('write-tree').decode().strip()

    def commit_branch(self, branch, files, parent=None):
        tree = self.tree(files, parent)
        sha = self.git('commit-tree', tree, *(['-p', parent] if parent else []), data=b'fixture\n').decode().strip()
        self.git('update-ref', 'refs/heads/' + branch, sha)
        return sha

    def __call__(self, endpoint, *, payload=None, method=None):
        self.calls.append((endpoint, payload, method))
        if self.outage:
            raise ArchiveError('fixture outage')
        prefix = f'repos/{REPO}/git/'
        assert endpoint.startswith(prefix)
        path = endpoint[len(prefix):]
        if path.startswith('ref/heads/'):
            ref = 'refs/heads/' + path.removeprefix('ref/heads/')
            return {'ref': ref, 'object': {'type': 'commit', 'sha': self.git('rev-parse', ref).decode().strip()}}
        if path.startswith('commits/'):
            return {'tree': {'sha': self.git('rev-parse', path[8:] + '^{tree}').decode().strip()}}
        if path.startswith('trees/'):
            revision = path[6:].split('?')[0]
            entries = []
            for line in self.git('ls-tree', '-r', '-z', '-l', revision).split(b'\0'):
                if line:
                    meta, name = line.split(b'\t')
                    mode, kind, sha, size = meta.split()
                    entries.append({'path': name.decode(), 'mode': mode.decode(), 'type': kind.decode(),
                                    'sha': sha.decode(), 'size': int(size)})
            return {'truncated': False, 'tree': entries}
        if path.startswith('blobs/'):
            return {'encoding': 'base64', 'content': base64.b64encode(self.git('cat-file', 'blob', path[6:])).decode()}
        if path == 'blobs':
            return {'sha': self.git('hash-object', '-w', '--stdin', data=base64.b64decode(payload['content'])).decode().strip()}
        if path == 'trees':
            self.git('read-tree', payload['base_tree'])
            for entry in payload['tree']:
                self.git('update-index', '--add', '--cacheinfo', entry['mode'], entry['sha'], entry['path'])
            return {'sha': self.git('write-tree').decode().strip()}
        if path == 'commits':
            assert len(payload['parents']) == 1
            return {'sha': self.git('commit-tree', payload['tree'], '-p', payload['parents'][0],
                                   data=payload['message'].encode()).decode().strip()}
        if path == 'refs/heads/review-data':
            assert method == 'PATCH' and payload['force'] is False
            if self.before_update:
                self.before_update()
            current = self.git('rev-parse', 'refs/heads/review-data').decode().strip()
            self.git('merge-base', '--is-ancestor', current, payload['sha'])
            self.git('update-ref', 'refs/heads/review-data', payload['sha'], current)
            if self.after_update:
                self.after_update()
            return {'object': {'sha': payload['sha']}}
        raise AssertionError(path)


def installed_archive_smoke(executable, fixture):
    root = fixture.root
    command = [str(executable), 'archive', 'preview', '--operator-config', str(fixture.operator), '--json']
    preview = subprocess.run(command, cwd=fixture.foreign, env=fixture.env, capture_output=True, text=True, check=True)
    assert json.loads(preview.stdout)['records'] == 1, preview.stdout
    command[2] = 'rebuild'
    command += ['--output', str(root / 'archive.sqlite')]
    subprocess.run(command, cwd=fixture.foreign, env=fixture.env, capture_output=True, text=True, check=True)
    command = [str(executable), 'archive', 'sync', '--apply', '--operator-config', str(fixture.operator)]
    denied = subprocess.run(command, cwd=fixture.foreign, env=fixture.env, capture_output=True, text=True)
    assert denied.returncode == 2 and 'no network request' in denied.stderr, denied.stderr
