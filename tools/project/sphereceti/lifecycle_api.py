"""Fresh lifecycle observations and a disabled, label-only publication boundary.

TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
scripts/pr_status/{core,labels,conflicts,stuck_alerts}.py (Apache-2.0).
"""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
from types import SimpleNamespace
from urllib.parse import quote

from .config import parse_policy, parse_project, resource_text
from .gate import blob, tree
from .lifecycle import MANAGED, digest, main_health, parse_settings, pr_plan
from .local_review import object_source
from .merge_observation import Reader, observe, pull
from .review_records import RecordError
from .review_resources import tooling_files


def pages(value):
    if not isinstance(value, list) or not value or any(not isinstance(p, list) for p in value):
        raise RecordError('incomplete lifecycle pagination')
    rows = [row for page in value for row in page]
    if len(rows) > 1000:
        raise RecordError('lifecycle inventory exceeds 1000 entries')
    return rows


class LabelWriter:
    """The private token can reach only identity GET and four fixed label names."""
    def __init__(self, repository, token):
        self.repository, self.token = repository, token

    def request(self, endpoint, method='GET', payload=None):
        env = {name: os.environ[name] for name in ('PATH', 'HOME') if name in os.environ}
        env.update(GH_TOKEN=self.token, GH_PROMPT_DISABLED='1')
        command = ['gh', 'api', '--hostname', 'github.com', endpoint, '--method', method]
        if payload is not None:
            command += ['--input', '-']
        try:
            result = subprocess.run(command, env=env, input=json.dumps(payload) if payload else None,
                                    capture_output=True, text=True, timeout=60)
            if result.returncode:
                raise RecordError('label request unconfirmed')
            return json.loads(result.stdout) if result.stdout.strip() else None
        except (OSError, ValueError, subprocess.SubprocessError) as error:
            raise RecordError('label request unconfirmed') from error

    def identity(self):
        return self.request('user')

    def change(self, number, action, label):
        if type(number) is not int or number <= 0 or label not in MANAGED or action not in ('add', 'remove'):
            raise RecordError('unsupported lifecycle mutation')
        endpoint = f'repos/{self.repository}/issues/{number}/labels'
        return (self.request(endpoint, 'POST', {'labels': [label]}) if action == 'add' else
                self.request(endpoint + '/' + quote(label, safe=''), 'DELETE'))


class Backend:
    def __init__(self, args, project, writer):
        self.args, self.project, self.writer = args, project, writer
        self.now = datetime.now(timezone.utc)

    def setup(self, applying=False):
        client = Reader(self.project.repository)
        current = client.call(f'repos/{self.project.repository}/commits/main')['sha']
        from .lifecycle import SHA
        if not isinstance(current, str) or not SHA.fullmatch(current):
            raise RecordError('invalid approved main revision')
        cache = self.args.cache_dir.expanduser().absolute()
        cache.mkdir(parents=True, exist_ok=True)
        repo = object_source(self.args.source_repo, cache / 'SphereCeti.git',
                             f'https://github.com/{self.project.repository}', [current], False)
        approved = tree(repo, current)
        required = ('sphereceti.toml', 'policy/automation.toml', 'policy/lifecycle.toml')
        missing = [p for p in required if p not in approved]
        result = {'main': current, 'ready': False, 'settings': parse_settings(resource_text('lifecycle.toml')),
                  'reasons': ['approved main lacks ' + p for p in missing]}
        if not missing:
            project = parse_project(blob(repo, approved['sphereceti.toml']).decode())
            if project != self.project:
                raise RecordError('approved lifecycle project differs from installed project')
            policy = parse_policy(blob(repo, approved['policy/automation.toml']).decode())
            settings = parse_settings(blob(repo, approved['policy/lifecycle.toml']).decode())
            result['settings'] = settings
            if not settings['labels_enabled'] or not policy.posting:
                result['reasons'].append('label publication is disabled by approved policy')
            if not settings['writer_user_id']:
                result['reasons'].append('label writer identity is not configured')
            files = tooling_files()
            if any(p not in approved or blob(repo, approved[p]) != body for p, body in files.items()):
                result['reasons'].append('installed tooling/resources differ from approved main')
            if applying and not result['reasons']:
                if self.writer is None:
                    raise RecordError('missing SPHERECETI_MAINTENANCE_TOKEN')
                actor = self.writer.identity()
                if (not isinstance(actor, dict) or type(actor.get('id')) is not int
                        or actor['id'] != settings['writer_user_id'] or actor.get('type') != 'User'
                        or actor.get('site_admin') is not False):
                    raise RecordError('unexpected label writer identity')
                for name in sorted(MANAGED):
                    label = client.call(f'repos/{self.project.repository}/labels/{quote(name, safe="")}')
                    if label.get('name') != name:
                        raise RecordError('managed labels must be preconfigured')
            result['ready'] = not result['reasons']
        client.revalidate()
        return result

    def labels(self, number, client=None):
        client = client or Reader(self.project.repository)
        rows = pages(client.call(f'repos/{self.project.repository}/issues/{number}/labels?per_page=100', paginate=True))
        names = [r['name'] for r in rows]
        if any(not isinstance(n, str) for n in names) or len(set(names)) != len(names):
            raise RecordError('invalid label inventory')
        return names

    def snapshot(self, number, setup):
        client = Reader(self.project.repository)
        pr = pull(client, self.project, number)
        pr['labels'] = self.labels(number, client)
        # Human-held/draft/terminal/stack PRs do not need a review environment.
        from .lifecycle import HOLD
        skipped = (pr['state'] != 'open' or pr['merged'] or pr['draft'] or
                   bool(set(n.lower() for n in pr['labels']) & HOLD) or
                   pr.get('auto_merge') is not None or pr['base']['ref'] != 'main')
        observation = None if skipped else observe(SimpleNamespace(**{**vars(self.args), 'pr': number}),
                                                   self.project, client=client)
        result = pr_plan(pr, observation, setup['main'], setup['settings'], now=self.now)
        # Refresh all reads, including the PR and complete labels, before returning a plan.
        client.revalidate()
        return result

    def queue(self):
        client = Reader(self.project.repository)
        rows = pages(client.call(f'repos/{self.project.repository}/pulls?state=open&per_page=100', paginate=True))
        numbers = [r['number'] for r in rows]
        if (len(numbers) > 50 or any(type(n) is not int or n <= 0 for n in numbers)
                or len(numbers) != len(set(numbers))):
            raise RecordError('invalid, duplicate, or oversized lifecycle queue (maximum 50 PRs)')
        return sorted(numbers)

    def health(self):
        client = Reader(self.project.repository)
        prefix = f'repos/{self.project.repository}'
        tip = client.call(prefix + '/commits/main')['sha']
        workflow = client.call(prefix + '/actions/workflows/ci.yml')
        value = client.call(prefix + '/actions/workflows/ci.yml/runs?branch=main&event=push&per_page=30')
        if (not isinstance(value, dict) or type(value.get('total_count')) is not int
                or not isinstance(value.get('workflow_runs'), list)
                or len(value['workflow_runs']) != min(30, value['total_count'])):
            raise RecordError('incomplete main CI run window')
        result = main_health(tip, workflow, value['workflow_runs'], self.project.repository)
        client.revalidate()
        return result

    def change(self, number, action, name):
        return self.writer.change(number, action, name)


def reconcile(backend, numbers=None, *, applying=False):
    setup = backend.setup(applying)
    result = {'schema_version': 1, 'mode': 'apply' if applying else 'preview', 'setup': setup,
              'state': 'complete', 'results': [], 'merge_allowed': False}
    # The stop switches are evaluated BEFORE enumerating PRs or taking mutation decisions.
    if applying and not setup['ready']:
        result['state'] = 'disabled'
        return result
    for number in backend.queue() if numbers is None else numbers:
        try:
            first = backend.snapshot(number, setup)
            if not applying or first['state'] in ('human_managed', 'unknown'):
                result['results'].append(first)
                if first['state'] == 'unknown': result['state'] = 'error'
                continue
            # Remove obsolete status first, add on the next invocation. One write globally
            # bounds races and ambiguous responses; repeated fresh invocations converge.
            action = 'remove' if first['remove'] else 'add'
            names = first[action]
            if not names:
                result['results'].append(first)
                continue
            fresh_setup = backend.setup(True)
            if fresh_setup != setup or backend.snapshot(number, fresh_setup) != first:
                raise RecordError('lifecycle evidence changed; revalidation required')
            name = names[0]
            confirmed = False
            try:
                backend.change(number, action, name)
            except RecordError:
                pass  # A timeout may have applied. Never blindly retry a label write.
            try:
                labels = backend.labels(number)
                confirmed = (name in labels) == (action == 'add')
            except (RecordError, OSError, ValueError, KeyError, TypeError):
                pass
            result['results'].append({**first, 'publication': {'action': action, 'label': name,
                                      'state': 'observed' if confirmed else 'unconfirmed'}})
            result['state'] = 'error' if not confirmed or result['state'] == 'error' else 'reconcile_again'
            return result
        except (RecordError, OSError, ValueError, KeyError, TypeError) as error:
            result['results'].append({'pr': number, 'state': 'error', 'reason': str(error)})
            result['state'] = 'error'
    return result


def run(args, project):
    token = os.environ.pop('SPHERECETI_MAINTENANCE_TOKEN', None)
    if args.pr is not None and args.pr <= 0:
        raise RecordError('PR number must be positive')
    if args.health_only and args.apply_labels:
        raise RecordError('health-only cannot apply labels')
    writer = LabelWriter(project.repository, token) if token and args.apply_labels else None
    backend = Backend(args, project, writer)
    if args.health_only:
        health = backend.health()
        return {'schema_version': 1, 'state': 'error' if health['state'] == 'unknown' else 'complete',
                'main_health': health, 'merge_allowed': False}
    report = reconcile(backend, [args.pr] if args.pr is not None else None, applying=args.apply_labels)
    if not args.apply_labels:
        try:
            report['main_health'] = backend.health()
            if report['main_health']['state'] == 'unknown': report['state'] = 'error'
        except (RecordError, OSError, ValueError, KeyError, TypeError) as error:
            report['main_health'] = {'state': 'error', 'reason': str(error)}
            report['state'] = 'error'
    report['report_digest'] = digest(report)
    return report


def add_parser(commands):
    p = commands.add_parser('maintenance', help='lifecycle diagnostics and disabled label reconciliation')
    group = p.add_mutually_exclusive_group(required=True)
    group.add_argument('--pr', type=int)
    group.add_argument('--sweep', action='store_true')
    group.add_argument('--health-only', action='store_true')
    p.add_argument('--apply-labels', action='store_true', help='requires both approved publication switches')
    p.add_argument('--json', action='store_true')
    p.add_argument('--source-repo', type=Path)
    p.add_argument('--dependencies-dir', type=Path)
    p.add_argument('--cache-dir', type=Path, default=Path('~/.cache/sphereceti/lifecycle'))
    p.add_argument('--operator-config', type=Path)
