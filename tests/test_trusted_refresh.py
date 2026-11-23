# SPDX-License-Identifier: Apache-2.0
"""Stale build versus stale review, and the dispatched trusted refresh (pr-build.yml on main).

Classification runs the real auto-approval decision over disposable Git (test_auto_approval's
Harness). The dispatched-run binding uses #84's shared evidence fixture. The workflow's resolve and
publish scripts are extracted from pr-build.yml and run with fake gh/git, so their race and length
guards are tested as shell, not as prose.
"""
from copy import deepcopy
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import textwrap
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
from sphereceti.config import parse_policy
from sphereceti.merge_checks import TOOLING_ATTESTATION, assess_checks, refresh_title
from sphereceti.merge_controller import Backend, Writer, classify, reconcile
from sphereceti.review_post import GitHub
from sphereceti.review_records import RecordError
from review_fixture import git
from test_merge_observation import evidence
from test_review_records import REPO

WORKFLOW_TEXT = (ROOT / '.github/workflows/pr-build.yml').read_text()
OTHER = 'trusted-build attests another PR or base'
M = '3' * 40


class DispatchedBindingTests(unittest.TestCase):
    """assess_checks accepts a refresh only with its whole binding."""

    def setUp(self):
        self.context, _, _, self.pr, self.settings, self.statuses, self.run, self.jobs = evidence()
        self.tooling, self.head = self.context['tooling'], self.context['head']

    def refresh(self, *, description=None, statuses=None, context=None, **run_change):
        statuses = deepcopy(statuses or self.statuses)
        statuses[0]['description'] = description or (
            f'Approved tooling refresh: success; tooling {self.tooling}; pr 1; base {self.context["base"]}')
        run = {**deepcopy(self.run), 'event': 'workflow_dispatch', 'head_sha': self.tooling, 'head_branch': 'main',
               'display_title': refresh_title(1, self.head), 'pull_requests': [],
               'head_repository': {'full_name': REPO}, **run_change}
        bound = {**self.context, 'head_repository': 'fork/SphereCeti', **(context or {})}
        return assess_checks(statuses, run, self.jobs, bound, self.settings)['reasons']

    def test_a_dispatched_run_binding_is_accepted_when_everything_matches(self):
        # The fork's head repository is irrelevant: the exact head SHA binds the candidate.
        self.assertEqual(self.refresh(), [])
        self.assertEqual(len(self.refresh(description=None)), 0)
        longest = f"Approved tooling refresh: success; tooling {'a'*40}; pr 9999; base {'b'*40}"
        self.assertLessEqual(len(longest), 140)
        self.assertTrue(TOOLING_ATTESTATION.fullmatch(longest))

    def test_wrong_pr_input_head_workflow_or_commit_is_refused(self):
        title = 'refresh run-name does not name this PR and exact head'
        cases = {
            'another PR in the run-name': (dict(display_title=refresh_title(2, self.head)), title),
            'another head in the run-name': (dict(display_title=refresh_title(1, '9' * 40)), title),
            'another PR attested': (dict(description=f'Approved tooling refresh: success; tooling {self.tooling}; '
                                                     f'pr 2; base {self.tooling}'), OTHER),
            'another workflow file': (dict(path='.github/workflows/ci.yml'), 'trusted run has wrong path'),
            'another workflow id': (dict(workflow_id=72), 'trusted run has wrong workflow_id'),
            'dispatched on a branch commit': (dict(head_sha='8' * 40), 'trusted run has wrong head_sha'),
            'dispatched on another branch': (dict(head_branch='feature'), 'refresh run was not dispatched on main'),
            'no refresh attestation': (dict(description=f'Approved tooling build: success; tooling {self.tooling}; '
                                                       f'pr 1; base {self.tooling}'),
                                       'refresh run did not publish a refresh attestation with its PR binding'),
            'tooling other than the run': (dict(description=f"Approved tooling refresh: success; tooling {'e'*40}; "
                                                            f'pr 1; base {self.tooling}'),
                                           'refresh attests tooling other than the dispatched main commit'),
        }
        for name, (kwargs, reason) in cases.items():
            with self.subTest(name):
                self.assertIn(reason, self.refresh(**kwargs))
        other_commit = deepcopy(self.statuses)
        for status in other_commit:
            status['url'] = status['url'].rsplit('/', 1)[0] + '/' + '9' * 40
        self.assertIn('trusted-build has a wrong head/location', self.refresh(statuses=other_commit))
        # A refresh attestation never qualifies on a pull_request_target run.
        statuses = deepcopy(self.statuses)
        statuses[0]['description'] = f'Approved tooling refresh: success; tooling {self.tooling}; pr 1; base {self.tooling}'
        reasons = assess_checks(statuses, self.run, self.jobs, {**self.context, 'head_repository': REPO},
                                self.settings)['reasons']
        self.assertIn('a refresh attestation must come from a dispatched refresh run', reasons)

    def test_head_or_base_change_during_the_refresh_never_qualifies(self):
        # Head changed: the PR now has another head, so the refresh's run-name and commit name the old one.
        moved = self.refresh(context={'head': '9' * 40})
        self.assertIn('refresh run-name does not name this PR and exact head', moved)
        self.assertIn('trusted-build has a wrong head/location', moved)
        # Base changed: the attested base is not the PR's base now.
        self.assertIn(OTHER, self.refresh(description=f'Approved tooling refresh: success; tooling {self.tooling}; '
                                                      f"pr 1; base {'7'*40}"))
        # Main moved after the refresh: its tooling is no longer approved main.
        self.assertIn('trusted-build ran with tooling other than approved main; refresh the trusted run',
                      self.refresh(context={'tooling': '6' * 40, 'base': '6' * 40}))

    def test_older_readers_fail_closed_on_a_refresh_attestation(self):
        before = re.compile(r'Approved tooling build: [a-z_]+; tooling ([0-9a-f]{40})'
                            r'(?:; pr ([1-9][0-9]{0,8}); base ([0-9a-f]{40}))?')
        self.assertIsNone(before.fullmatch(f"Approved tooling refresh: success; tooling {'a'*40}; pr 1; base {'b'*40}"))


class RecordingWriter(Writer):
    def __init__(self, on_merge=None):
        super().__init__(REPO, 'ghs_fixturejobtoken')
        self.requests, self.on_merge = [], on_merge

    def run(self, command, payload, env):
        self.requests.append((command[4], command[6] if '--method' in command else 'GET', payload))
        assert env['GH_TOKEN'] == self._token and 'SPHERECETI_MERGE_TOKEN' not in env
        if command[4].endswith('/merge') and self.on_merge: self.on_merge()
        stdout = '' if command[4].endswith('/dispatches') else json.dumps({'merged': True, 'sha': M})
        return subprocess.CompletedProcess(command, 0, stdout, '')


class ClassificationTests(unittest.TestCase):
    """Per-PR actions from the real decision, and the gated single refresh dispatch."""

    def setUp(self):
        from test_auto_approval import REVIEWER, Harness
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        # merging = true exists only in this fixture's approved policy; the repository keeps false.
        self.h = Harness(Path(self.tmp.name), policy_paths=('SphereCeti/E8',), merging=True,
                         approving_reviewers=(f'user:{REVIEWER}',))
        self.reviewer = REVIEWER
        self.reviews = [{'id': 1, 'user': {'id': REVIEWER, 'type': 'User'}, 'state': 'APPROVED',
                         'commit_id': self.h.head, 'author_association': 'COLLABORATOR'}]
        respond = self.h.respond

        def github(endpoint, **kwargs):
            if endpoint == f'repos/{REPO}/pulls/1/reviews?per_page=100':
                return [deepcopy(self.reviews)]
            return respond(endpoint, **kwargs)
        self.github = github

    def backend(self, ready=True):
        h = self.h
        writer = RecordingWriter(lambda: h.pr.update(merged=True, state='closed', merge_commit_sha=M))
        args = SimpleNamespace(cache_dir=Path(self.tmp.name) / 'cache', source_repo=h.repo, dependencies_dir=None)
        backend = Backend(args, h.project, writer)
        policy = parse_policy(git(h.repo, 'show', f'{h.tooling}:policy/automation.toml') + '\n')
        setup = {'ready': ready, 'merging_requested': ready, 'executor_verified': ready, 'tooling': h.tooling}
        backend.activation = SimpleNamespace(policy=policy, checks={'workflow_id': 358051984},
                                             inspect=lambda **kw: dict(setup), refresh=lambda: None)
        return backend, writer

    def reconcile(self, numbers=(1,), *, applying=True, ready=True):
        backend, writer = self.backend(ready)
        with patch.object(GitHub, 'call', side_effect=self.github), \
                patch('sphereceti.merge_observation.prepare', side_effect=self.h.prepared):
            return reconcile(backend, lambda: list(numbers), applying=applying), writer

    def stale_build(self):
        build = next(s for s in self.h.statuses if s['context'] == 'trusted-build')
        build['description'] = f"Approved tooling build: success; tooling {'e'*40}"

    def move_main(self):
        """Main advances to a new commit M2; the PR's base.sha (GitHub's snapshot) stays at T."""
        tree = git(self.h.repo, 'rev-parse', f'{self.h.tooling}^{{tree}}')
        self.h.current = git(self.h.repo, 'commit-tree', tree, '-p', self.h.tooling, '-m', 'main moves')

    def test_current_pr_takes_the_unchanged_merge_path(self):
        result, writer = self.reconcile()
        self.assertEqual(result['results'][0]['state'], 'merged')
        self.assertEqual([r[:2] for r in writer.requests], [(f'repos/{REPO}/pulls/1/merge', 'PUT')])

    def test_stale_build_only_dispatches_one_refresh_for_that_pr(self):
        self.stale_build()
        result, writer = self.reconcile(numbers=(1, 1))  # A duplicate in one run is not dispatched twice.
        first, second = result['results']
        self.assertEqual((first['action'], first['state']), ('refresh_build', 'refresh_dispatched'))
        self.assertEqual(first['reasons'], ['trusted-build ran with tooling other than approved main; refresh the trusted run'])
        self.assertEqual((second['state'], second['note']), ('would_dispatch_refresh', 'would dispatch refresh for #1'))
        self.assertEqual(writer.requests, [(f'repos/{REPO}/actions/workflows/358051984/dispatches', 'POST',
                                            {'ref': 'main', 'inputs': {'pr': '1', 'head': self.h.head}})])
        self.assertEqual(result['refreshes_dispatched'], [1]);self.assertFalse(result['merge_attempted'])

    def test_switches_off_only_report(self):
        self.stale_build()
        preview, writer = self.reconcile(applying=False, ready=False)
        self.assertEqual(preview['state'], 'disabled')
        self.assertEqual(preview['results'][0]['note'], 'would dispatch refresh for #1')
        applied, writer2 = self.reconcile(applying=True, ready=False)
        self.assertEqual((applied['state'], applied['results']), ('disabled', []))
        self.assertEqual(writer.requests + writer2.requests, [])

    def test_stale_review_base_needs_review_even_with_an_unchanged_diff(self):
        self.move_main()  # Same PR, same diff, same review record; only main moved.
        result, writer = self.reconcile()
        item = result['results'][0]
        self.assertEqual(item['state'], 'needs_review')
        self.assertIn(f'the PR base {self.h.tooling[:12]} that a review binds is not current main {self.h.current[:12]}',
                      item['reasons'])
        self.assertEqual(writer.requests, [])

    def test_no_review_needs_review(self):
        self.h.comments = []
        result, writer = self.reconcile()
        self.assertEqual(result['results'][0]['state'], 'needs_review')
        self.assertIn('no accepted official review for the current head', result['results'][0]['reasons'])
        self.assertEqual(writer.requests, [])

    def test_stale_build_without_formal_approval_is_blocked_not_refreshed(self):
        self.stale_build()
        self.reviews = []
        result, writer = self.reconcile()
        item = result['results'][0]
        self.assertEqual(item['state'], 'blocked');self.assertIn('the trusted build is also stale', item['reasons'])
        self.assertEqual(writer.requests, [])

    def test_a_real_build_failure_or_misbinding_is_not_refreshed(self):
        build = next(s for s in self.h.statuses if s['context'] == 'trusted-build')
        build['state'] = 'failure'
        self.stale_build()
        result, writer = self.reconcile()
        self.assertEqual(result['results'][0]['state'], 'blocked');self.assertEqual(writer.requests, [])


def requirement(name, status='pass', **evidence):
    return {'id': name, 'status': status, 'summary': name, 'evidence': evidence}


class ClassifyUnitTests(unittest.TestCase):
    """Edge cases of the rule without Git: another PR's attestation and human-route paths."""

    def decision(self, **changes):
        T, H = '1' * 40, '2' * 40
        req = {n: requirement(n) for n in ('paths', 'trusted_checks', 'compiled_audit', 'official_review',
                                             'independent_reviewer', 'pull_request', 'policy')}
        for name, value in changes.items():
            req[name] = value
        return {'pr': 1, 'tooling': T, 'base': T, 'diff_base': T, 'head': H, 'hypothetical': False,
                'would_approve': all(r['status'] == 'pass' for r in req.values()),
                'reasons': [f'{n}: x' for n, r in req.items() if r['status'] != 'pass'], 'requirements': list(req.values())}

    def test_another_prs_attestation_is_a_misbinding(self):
        build = {'description': f"Approved tooling build: success; tooling {'1'*40}; pr 2; base {'1'*40}"}
        checks = requirement('trusted_checks', 'fail', reasons=[OTHER], statuses={'trusted-build': build})
        audit = requirement('compiled_audit', 'fail', reasons=[OTHER])
        action, _ = classify(self.decision(trusted_checks=checks, compiled_audit=audit), {'reasons': []})
        self.assertEqual(action, 'blocked')
        build['description'] = build['description'].replace('pr 2', 'pr 1')
        self.assertEqual(classify(self.decision(trusted_checks=checks, compiled_audit=audit), {'reasons': []})[0],
                         'refresh_build')

    def test_human_route_and_behind_prs(self):
        self.assertEqual(classify(self.decision(paths=requirement('paths', 'fail')), {'reasons': []})[0], 'blocked')
        behind = self.decision();behind['diff_base'] = '0' * 40
        action, reasons = classify(behind, {'reasons': []})
        self.assertEqual(action, 'needs_review');self.assertIn('the PR must contain current main', reasons[0])
        self.assertEqual(classify(self.decision(), {'reasons': ['no qualifying approval: x']})[0], 'blocked')
        self.assertEqual(classify(self.decision(), {'reasons': []}), ('merge', []))


class DispatchTransportTests(unittest.TestCase):
    def test_the_job_token_may_dispatch_only_one_exact_refresh(self):
        writer = RecordingWriter()
        writer.dispatch_refresh(358051984, 7, 'b' * 40)
        self.assertEqual(writer.requests, [(f'repos/{REPO}/actions/workflows/358051984/dispatches', 'POST',
                                            {'ref': 'main', 'inputs': {'pr': '7', 'head': 'b' * 40}})])
        endpoint = f'repos/{REPO}/actions/workflows/358051984/dispatches'
        for payload in ({'ref': 'feature', 'inputs': {'pr': '7', 'head': 'b' * 40}},
                        {'ref': 'main', 'inputs': {'pr': '7', 'head': 'HEAD'}},
                        {'ref': 'main', 'inputs': {'pr': '0', 'head': 'b' * 40}},
                        {'ref': 'main', 'inputs': {'pr': '7', 'head': 'b' * 40, 'extra': 'x'}},
                        {'ref': 'main', 'inputs': {'pr': '7', 'head': 'b' * 40}, 'return_run_details': True}, None):
            with self.subTest(payload=payload), self.assertRaises(RecordError):
                writer.call(endpoint, payload)
        for bad in (f'repos/{REPO}/actions/workflows/pr-build.yml/dispatches', f'repos/other/repo/actions/workflows/1/dispatches'):
            with self.assertRaises(RecordError):
                writer.call(bad, {'ref': 'main', 'inputs': {'pr': '7', 'head': 'b' * 40}})
        with self.assertRaises(RecordError):
            writer.dispatch_refresh(0, 7, 'b' * 40)
        self.assertEqual(len(writer.requests), 1)

    def test_merge_doctor_reports_one_prs_action_read_only(self):
        import sphereceti.merge_controller as controller
        class Stub:
            def __init__(self, args, project, writer): self.writer = writer
            def setup(self, applying, *, verify_executor=False): return {'ready': False, 'reasons': ['off']}
            def observation(self, number):
                return {'action': 'refresh_build', 'head': 'b' * 40, 'base': 'a' * 40, 'reasons': ['stale']}
            def dispatch_refresh(self, *a): raise AssertionError('merge-doctor never dispatches')
        with tempfile.TemporaryDirectory() as t, patch.object(controller, 'Backend', Stub):
            args = SimpleNamespace(command='merge-doctor', executor=False, pr=7, cache_dir=Path(t))
            report = controller.run(args, SimpleNamespace(repository=REPO))
        self.assertEqual(report['candidate'], {'pr': 7, 'state': 'refresh_build', 'action': 'refresh_build',
                                               'head': 'b' * 40, 'base': 'a' * 40, 'reasons': ['stale'],
                                               'note': 'would dispatch refresh for #7'})
        self.assertIn('#7: refresh_build (would dispatch refresh for #7)', controller.render(report))

    def test_text_output_names_each_action(self):
        from sphereceti.merge_controller import render
        report = {'mode': 'preview', 'state': 'disabled', 'note': 'switches are off',
                  'setup': {'ready': False, 'reasons': ['global merging switch is off']},
                  'results': [{'pr': 1, 'state': 'would_dispatch_refresh', 'note': 'would dispatch refresh for #1',
                               'reasons': ['trusted-build ran with tooling other than approved main']},
                              {'pr': 2, 'state': 'needs_review', 'reasons': ['no accepted official review']}]}
        text = render(report)
        for line in ('merge-control (preview): disabled', '#1: would_dispatch_refresh (would dispatch refresh for #1)',
                     '#2: needs_review', '    - no accepted official review', '  - global merging switch is off'):
            self.assertIn(line, text)


def step_script(name):
    """The `run: |` block of the named step in pr-build.yml, dedented."""
    lines = WORKFLOW_TEXT.splitlines()
    start = next(i for i, line in enumerate(lines) if line.strip() == f'- name: {name}')
    run = next(i for i in range(start, len(lines)) if lines[i].strip() == 'run: |')
    indent = len(lines[run]) - len(lines[run].lstrip())
    body = []
    for line in lines[run + 1:]:
        if line.strip() and len(line) - len(line.lstrip()) <= indent:
            break
        body.append(line)
    return textwrap.dedent('\n'.join(body)) + '\n'


FAKE_GH = r'''#!{python}
import json, os, re, sys
state = json.load(open(os.environ['FAKE_STATE']))
args = sys.argv[1:]
with open(os.environ['FAKE_LOG'], 'a') as log: log.write(json.dumps(['gh'] + args) + '\n')
assert args[0] == 'api'
endpoint = args[1].removeprefix('repos/' + os.environ['GH_REPO'] + '/')
if '-f' in args:
    print('{{}}'); sys.exit(0)
value = state[endpoint]
expr = args[args.index('--jq') + 1]
def path(obj, dotted):
    for part in dotted.strip('.').split('.'):
        obj = obj.get(part) if isinstance(obj, dict) else None
    return obj
if expr == '.sha': print(value['sha']); sys.exit(0)
fields = re.fullmatch(r'\[(.*)\] \| @tsv', expr).group(1).split(', ')
out = []
for field in fields:
    m = re.fullmatch(r'\((\S+) // ""\)', field)
    out.append(str(path(value, m.group(1) if m else field) or ''))
print('\t'.join(out))
'''
RECORD = '#!/bin/sh\necho "$(basename "$0") $*" >> "$FAKE_LOG"\n'
FAKE_GIT = RECORD + 'if [ "$1" = -C ]; then shift 2; fi\nif [ "$1" = rev-parse ]; then echo "${3%^{commit\\}}"; fi\n'


class WorkflowScriptTests(unittest.TestCase):
    """The refresh's resolve and publish steps, run as shell against fake gh/git."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        for name, text in (('gh', FAKE_GH.format(python=sys.executable)), ('git', FAKE_GIT),
                           ('python3', RECORD), ('bash', RECORD)):
            (self.bin / name).write_text(text)
            (self.bin / name).chmod(0o755)
        self.T, self.H = 'a' * 40, 'b' * 40
        self.pr = {'number': 7, 'state': 'open', 'head': {'sha': self.H, 'repo': {'full_name': 'fork/SphereCeti'}},
                   'base': {'sha': self.T, 'ref': 'main', 'repo': {'full_name': REPO}}}
        self.main = {'sha': self.T}

    def run_step(self, name, env):
        state = {f"pulls/{self.pr['number']}": self.pr, 'commits/main': self.main}
        (self.root / 'state.json').write_text(json.dumps(state))
        log = self.root / 'log'
        log.write_text('')
        full = {'PATH': f'{self.bin}:/usr/bin:/bin', 'FAKE_STATE': str(self.root / 'state.json'),
                'FAKE_LOG': str(log), 'GH_REPO': REPO, 'GH_TOKEN': 'fixture', 'GITHUB_OUTPUT': str(self.root / 'out'),
                'RUNNER_TEMP': str(self.root), **env}
        done = subprocess.run(['/bin/bash', '-c', step_script(name)], env=full, capture_output=True, text=True,
                              cwd=self.root, timeout=60)
        calls = [line for line in log.read_text().splitlines() if line]
        return done, calls

    def publish(self, **env):
        base = {'EVENT': 'workflow_dispatch', 'HEAD_SHA': self.H, 'PR_NUMBER': '7', 'BASE_SHA': self.T,
                'TOOLING_SHA': self.T, 'BUILD_RESULT': 'success', 'SCOPE': 'mathematical',
                'RUN_URL': f'https://github.com/{REPO}/actions/runs/1/attempts/1'}
        done, calls = self.run_step('Publish separate build and scope verdicts for exact H', {**base, **env})
        posts = [json.loads(c) for c in calls if c.startswith('[') and '-f' in json.loads(c)]
        return done, posts, calls

    def test_refresh_publishes_its_binding_when_nothing_moved(self):
        done, posts, _ = self.publish()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertEqual(len(posts), 2)
        description = next(a for a in posts[0] if a.startswith('description='))[len('description='):]
        self.assertEqual(description, f'Approved tooling refresh: success; tooling {self.T}; pr 7; base {self.T}')
        self.assertTrue(posts[0][2].endswith(f'/statuses/{self.H}'))  # On the PR head commit.

    def test_end_of_run_race_guard_publishes_nothing(self):
        cases = {'head moved': lambda: self.pr['head'].update(sha='c' * 40),
                 'base moved': lambda: self.pr['base'].update(sha='d' * 40),
                 'main moved': lambda: self.main.update(sha='e' * 40),
                 'PR closed': lambda: self.pr.update(state='closed')}
        for name, change in cases.items():
            with self.subTest(name):
                self.setUp()
                change()
                done, posts, _ = self.publish()
                self.assertNotEqual(done.returncode, 0);self.assertEqual(posts, [])
                self.assertIn('refresh not published', done.stdout + done.stderr)
        self.setUp()
        done, posts, _ = self.publish(BASE_SHA='')  # The resolve step refused: no base output.
        self.assertNotEqual(done.returncode, 0);self.assertEqual(posts, [])

    def test_description_length_guard(self):
        # A 9-digit PR and a `cancelled` result overflow GitHub's 140 characters: nothing is published.
        for event in ('workflow_dispatch', 'pull_request_target'):
            with self.subTest(event):
                self.setUp()
                self.pr['number'] = 123456789
                done, posts, _ = self.publish(EVENT=event, PR_NUMBER='123456789', BUILD_RESULT='cancelled')
                self.assertNotEqual(done.returncode, 0);self.assertEqual(posts, [])
                self.assertIn('limit 140', done.stdout + done.stderr)

    def test_pull_request_target_path_reads_no_pr_and_keeps_its_attestation(self):
        done, posts, calls = self.publish(EVENT='pull_request_target')
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertFalse([c for c in calls if 'pulls/' in c or 'commits/main' in c])
        description = next(a for a in posts[0] if a.startswith('description='))[len('description='):]
        self.assertTrue(description.startswith('Approved tooling build: success;'))

    def resolve(self, **env):
        base = {'EVENT': 'workflow_dispatch', 'GITHUB_REF': 'refs/heads/main', 'TOOLING_SHA': self.T,
                'INPUT_PR': '7', 'INPUT_HEAD': self.H, 'EVENT_BASE': '', 'EVENT_HEAD': ''}
        return self.run_step('Resolve the complete immutable candidate tree', {**base, **env})

    def test_resolve_fetches_the_exact_head_from_the_head_repository(self):
        done, calls = self.resolve()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn(f'git -C gate fetch --no-tags https://github.com/fork/SphereCeti.git {self.H}', calls)
        self.assertIn(f'git -C gate fetch --no-tags origin {self.T}', calls)
        self.assertEqual((self.root / 'out').read_text(), f'base={self.T}\nhead={self.H}\n')
        self.assertTrue(any(c.startswith('bash gate/scripts/attest-pr-config.sh gate candidate ' + self.H +
                                         ' workflow_dispatch 1 0') for c in calls))

    def test_resolve_refuses_before_fetching_anything(self):
        cases = {'head already moved': ({}, lambda: self.pr['head'].update(sha='c' * 40)),
                 'base is not this main': ({}, lambda: self.pr['base'].update(sha='d' * 40)),
                 'closed': ({}, lambda: self.pr.update(state='closed')),
                 'another base branch': ({}, lambda: self.pr['base'].update(ref='develop')),
                 'not on main': ({'GITHUB_REF': 'refs/heads/feature'}, lambda: None),
                 'bad pr input': ({'INPUT_PR': '7; rm -rf /'}, lambda: None),
                 'bad head input': ({'INPUT_HEAD': 'HEAD'}, lambda: None)}
        for name, (env, change) in cases.items():
            with self.subTest(name):
                self.setUp()
                change()
                done, calls = self.resolve(**env)
                self.assertNotEqual(done.returncode, 0)
                self.assertFalse([c for c in calls if c.startswith('git ')], calls)

    def test_pull_request_target_resolution_is_unchanged(self):
        done, calls = self.resolve(EVENT='pull_request_target', EVENT_BASE=self.T, EVENT_HEAD=self.H,
                                   INPUT_PR='', INPUT_HEAD='', GITHUB_REF='refs/pull/7/merge')
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertFalse([c for c in calls if c.startswith('[')])  # No API read.
        self.assertIn(f'git -C gate fetch --no-tags origin {self.H}', calls)

    def test_workflow_shape(self):
        self.assertIn("format('refresh #{0} at {1}', inputs.pr, inputs.head)", WORKFLOW_TEXT)
        self.assertIn("group: trusted-candidate-${{ github.event.pull_request.number || inputs.pr }}", WORKFLOW_TEXT)
        self.assertIn("if: github.event_name == 'pull_request_target' || github.ref == 'refs/heads/main'", WORKFLOW_TEXT)
        self.assertEqual(WORKFLOW_TEXT.count('statuses: write'), 1)  # Still only the status job.
        for name in ('Resolve the complete immutable candidate tree', 'Publish separate build and scope verdicts for exact H'):
            self.assertNotIn('${{', step_script(name))  # Inputs reach shell only through env.
        self.assertIsNone(re.search(r'\$\{\{ *(github\.event\.pull_request\.(title|body|head\.ref)|inputs\.\w+ *\}\}.*\n *run)',
                                    WORKFLOW_TEXT))


if __name__ == '__main__':
    unittest.main()
