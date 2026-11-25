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
from sphereceti.merge_checks import (MERGE_CONFLICT, MERGE_MISMATCH, MERGE_MISSING, MERGE_STALE,
                                     TOOLING_ATTESTATION, assess_checks, assess_merge, refresh_title)
from sphereceti.merge_controller import Backend, Writer, classify, reconcile
from sphereceti.review_post import GitHub
from sphereceti.review_records import RecordError
from review_fixture import commit, git
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
        self.reviewer, self.enforced = REVIEWER, True
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
        setup = {'ready': ready, 'merging_requested': ready, 'executor_verified': ready, 'tooling': h.tooling,
                 'protection': {'tested_tree_enforced': self.enforced}}
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

    def move_main(self, files=None):
        """Main advances to M2 (a child of T) changing `files`; the PR head and its base.sha snapshot stay."""
        if not files:
            tree = git(self.h.repo, 'rev-parse', f'{self.h.tooling}^{{tree}}')
            self.h.current = git(self.h.repo, 'commit-tree', tree, '-p', self.h.tooling, '-m', 'main moves')
            return
        git(self.h.repo, 'checkout', '-q', '--detach', self.h.tooling)
        for name, text in files.items():
            path = self.h.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(path.read_text() + text if path.exists() else text)
        self.h.current = commit(self.h.repo)
        git(self.h.repo, 'checkout', '-q', 'proof/e8')

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

    def test_same_head_with_a_changed_review_input_needs_review(self):
        for name, text, category in (('README.md', '\nA clarified specification.\n', 'specification'),
                                     ('SphereCetiRoadmap/Suggested.lean', '-- new target\n', 'specification'),
                                     ('lake-manifest.json', '\n', 'dependencies'),
                                     ('policy/automation.toml', '# reviewed policy note\n', 'policy'),
                                     ('tools/review/rubric.md', 'stricter\n', 'review tooling'),
                                     ('SphereCeti/E8/Basic.lean', '-- main changed a library module\n', 'library')):
            with self.subTest(name):
                self.setUp()
                self.move_main({name: text})
                result, writer = self.reconcile()
                item = result['results'][0]
                self.assertEqual(item['state'], 'needs_review', item)
                self.assertIn(f'{category} changed on main since the review: {name}', item['reasons'])
                self.assertEqual(item['review_inputs']['changed_inputs'], {category: [name]})
                self.assertEqual(writer.requests, [])

    def test_library_root_only_main_change_needs_review_and_is_measured(self):
        # Another proof landed: main only added its import line to the shared library root.
        self.move_main({'SphereCeti.lean': 'public import SphereCeti.Other\n'})
        result, writer = self.reconcile()
        item = result['results'][0]
        self.assertEqual(item['state'], 'needs_review')
        self.assertIn('measurement: only SphereCeti.lean changed on main since the review; '
                      'it still forces re-review for now', item['reasons'])
        self.assertEqual(item['review_inputs']['changed_inputs'], {'library root': ['SphereCeti.lean']})
        self.assertTrue(item['review_inputs']['library_root_only'])
        self.assertTrue(item['review_inputs']['change_identical'])
        self.assertEqual(writer.requests, [])

    def test_main_advancing_after_the_build_needs_a_rebuild_and_never_merges(self):
        # Main moved with no review input changed: the review stays valid (option 2), but the tested
        # merge used the old main and the head does not contain the new one, so nothing merges.
        self.move_main({'docs/infrastructure/notes.md': 'unrelated\n'})
        result, writer = self.reconcile()
        item = result['results'][0]
        self.assertEqual(item['state'], 'needs_update', item)
        self.assertEqual(writer.requests, []);self.assertFalse(result['merge_attempted'])
        self.move_main()  # The same with an empty main commit.
        self.assertEqual(self.reconcile()[0]['results'][0]['state'], 'needs_update')

    def test_executor_refuses_without_enforcement(self):
        self.enforced = False
        result, writer = self.reconcile()
        self.assertEqual(result['state'], 'refused')
        self.assertIn('the merge API pins only the head', result['results'][0]['reason'])
        self.assertEqual(writer.requests, []);self.assertFalse(result['merge_attempted'])

    def test_decisive_main_advances_between_the_final_check_and_the_put_and_github_refuses(self):
        """The actual race. (1) The controller finishes its final eligibility check, the last refresh,
        with main at T and the head containing it. (2) Only then does another PR land on main.
        (3) The executor sends its one head-pinned PUT. (4) The fake GitHub applies the ruleset's
        server-side strict check at merge time and refuses."""
        h = self.h
        tested = git(h.repo, 'rev-parse', f'{h.head}^{{tree}}')
        server = {'main': h.tooling, 'events': []}
        # Start from a PR that otherwise fully qualifies: in scope, a current review, a qualifying
        # formal approval and a passing merged-tree build, so a refusal can only be the race.
        preview, _ = self.reconcile(applying=False)
        self.assertEqual(preview['results'][0]['state'], 'would_merge')

        def land_another_pr():
            git(h.repo, 'checkout', '-q', '--detach', h.tooling)
            (h.repo / 'SphereCeti/E8/Basic.lean').write_text('module\n-- another proof landed\n')
            server['main'] = h.current = commit(h.repo)  # GitHub's main moves; later reads see it.
            git(h.repo, 'checkout', '-q', 'proof/e8')

        def github_merge(strict):
            """GitHub's merge of the pinned head against its main at the moment of the PUT."""
            if strict and git(h.repo, 'merge-base', server['main'], h.head) != server['main']:
                return None  # 405: the head branch is not up to date with the base branch.
            return git(h.repo, 'merge-tree', '--write-tree', server['main'], h.head)

        class StrictGitHub(RecordingWriter):
            def run(writer, command, payload, env):
                writer.requests.append((command[4], command[6] if '--method' in command else 'GET', payload))
                server['events'].append(('put', server['main']))
                if github_merge(strict=True) is None:
                    return subprocess.CompletedProcess(command, 1, '', 'gh: Head branch is not up to date with the base branch (HTTP 405)')
                h.pr.update(merged=True, state='closed', merge_commit_sha=M)
                return subprocess.CompletedProcess(command, 0, json.dumps({'merged': True, 'sha': M}), '')

        backend, _ = self.backend()
        backend.writer = writer = StrictGitHub()

        def final_check_then_main_advances():
            server['events'].append(('final check done', server['main']))
            land_another_pr()  # Strictly after the controller's last read, before its PUT.
        backend.activation.refresh = final_check_then_main_advances
        with patch.object(GitHub, 'call', side_effect=self.github), \
                patch('sphereceti.merge_observation.prepare', side_effect=self.h.prepared):
            result = reconcile(backend, lambda: [1], applying=True)
        advanced = server['main']
        self.assertEqual(server['events'], [('final check done', h.tooling), ('put', advanced)])
        # Exactly one head-pinned PUT by the executor's identity, refused; nothing landed; no retry.
        self.assertEqual(writer.requests, [(f'repos/{REPO}/pulls/1/merge', 'PUT', {'sha': h.head, 'merge_method': 'squash'})])
        item = result['results'][0]
        self.assertEqual((result['state'], item['state'], item['merge_commit']), ('rejected', 'rejected_stale', None))
        self.assertEqual(item['refusal'], {'status': '405', 'message': 'Head branch is not up to date with the base branch'})
        self.assertIn('the next run re-evaluates', item['reason'])
        # The PR is still open, and main (reread after the refusal) does not contain its change.
        self.assertEqual((h.pr['state'], h.pr['merged']), ('open', False))
        self.assertEqual(item['main_after'], advanced)
        self.assertEqual(git(h.repo, 'ls-tree', advanced, 'SphereCeti/E8/Lattice.lean'), '')
        # Without strict, the same PUT would have landed a tree nobody tested.
        self.assertNotEqual(github_merge(strict=False), tested)
        # The next run reads the new main and does not attempt the stale combination again.
        h.current = advanced
        again, writer2 = self.reconcile()
        self.assertNotIn(again['results'][0]['state'], ('merged', 'rejected_by_github'))
        self.assertEqual(writer2.requests, [])

    def test_an_unexpected_refusal_stops_and_reports_without_retrying(self):
        # Neither a permissions 403 nor an unrelated missing approval tests the race: stop and report.
        # The run id is fixed: the halt record names it, and CI's GITHUB_RUN_ID must not change the test.
        from sphereceti import controller_halt
        for status, message in (('403', 'Resource not accessible by integration'),
                                ('405', 'At least 1 approving review is required by reviewers with write access.')):
            for halt_accepted in (True, False):
                with self.subTest(status=status, halt_accepted=halt_accepted), \
                        patch.dict(os.environ, {'GITHUB_RUN_ID': '100'}):
                    self.setUp()

                    class Refusing(RecordingWriter):
                        def run(writer, command, payload, env):
                            writer.requests.append((command[4], command[6] if '--method' in command else 'GET', payload))
                            if command[4].endswith('/issues') and halt_accepted:
                                return subprocess.CompletedProcess(command, 0, '{"number": 31}', '')
                            return subprocess.CompletedProcess(command, 1, '', f'gh: {message} (HTTP {status})')
                    backend, _ = self.backend()
                    backend.writer = writer = Refusing()
                    with patch.object(GitHub, 'call', side_effect=self.github), \
                            patch('sphereceti.merge_observation.prepare', side_effect=self.h.prepared):
                        result = reconcile(backend, lambda: [1, 1], applying=True)
                    item = result['results'][0]
                    self.assertEqual((result['state'], item['state']), ('stopped', 'rejected_unexpected'))
                    self.assertEqual(item['refusal'], {'status': status, 'message': message})
                    self.assertIn('stops and reports', item['reason'])
                    # Exactly one merge PUT, never retried, and one halt issue (decision 3).
                    merges = [r for r in writer.requests if r[0].endswith('/merge')]
                    halts = [r for r in writer.requests if r[0].endswith('/issues')]
                    self.assertEqual([r[:2] for r in merges], [(f'repos/{REPO}/pulls/1/merge', 'PUT')])
                    self.assertEqual([(r[1], r[2]['title']) for r in halts], [('POST', controller_halt.TITLE)])
                    self.assertEqual(len(writer.requests), 2);self.assertEqual(len(result['results']), 1)
                    if halt_accepted:
                        self.assertEqual(item['halt_issue'], 31)
                    else:
                        self.assertIsNone(item['halt_issue']);self.assertIn(f'HTTP {status}', item['halt_error'])
                    self.assertEqual((self.h.pr['state'], self.h.pr['merged']), ('open', False))

    def test_only_a_definite_refusal_with_nothing_landed_is_reported_as_rejected(self):
        writer = RecordingWriter()
        writer.run = lambda command, payload, env: subprocess.CompletedProcess(command, 1, '', 'gh: Not Found (HTTP 404)')
        with self.assertRaises(RecordError) as error:
            writer.merge(1, 'b' * 40)
        self.assertEqual(str(error.exception), 'GitHub refused the request (HTTP 404): Not Found')
        writer.run = lambda command, payload, env: subprocess.CompletedProcess(command, 1, '', 'connection reset')
        with self.assertRaises(RecordError) as error:
            writer.merge(1, 'b' * 40)
        self.assertIn('unconfirmed', str(error.exception))

    def test_executor_refuses_a_head_that_is_not_the_tested_tree(self):
        from test_merge_controller import FakeBackend
        for change in ({'head_tree': '6' * 40}, {'tested_tree': None}):
            with self.subTest(change=change):
                backend = FakeBackend();backend.decision.update(change)
                result = reconcile(backend, lambda: [1], applying=True)
                self.assertEqual((result['state'], backend.puts), ('refused', []))
        backend = FakeBackend();backend.activation['protection'] = {'tested_tree_enforced': False}
        self.assertEqual(reconcile(backend, lambda: [1], applying=True)['state'], 'refused')
        self.assertEqual(backend.puts, [])

    def test_a_tampered_tested_tree_is_refused_not_refreshed(self):
        merge = next(s for s in self.h.statuses if s['context'] == 'trusted-merge')
        merge['description'] = f"Tested merge tree {'9'*40} with main {self.h.tooling}"
        result, writer = self.reconcile()
        self.assertEqual(result['results'][0]['state'], 'blocked')
        self.assertTrue(any(MERGE_MISMATCH in r for r in result['results'][0]['reasons']))
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
                                             'independent_reviewer', 'pull_request', 'policy', 'review_inputs')}
        for name, value in changes.items():
            req[name] = value
        req.setdefault('review_inputs', requirement('review_inputs'))
        return {'pr': 1, 'tooling': T, 'base': T, 'diff_base': T, 'head': H, 'hypothetical': False,
                'merge': {'main': T, 'tree': '4' * 40, 'head_tree': '4' * 40, 'head_contains_main': True},
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

    def test_human_route_behind_and_stale_merge(self):
        self.assertEqual(classify(self.decision(paths=requirement('paths', 'fail')), {'reasons': []})[0], 'blocked')
        behind = self.decision();behind['merge']['head_contains_main'] = False
        self.assertEqual(classify(behind, {'reasons': []})[0], 'needs_update')
        conflict = self.decision();conflict['merge']['tree'] = None
        self.assertEqual(classify(conflict, {'reasons': []})[0], 'blocked')
        inputs = requirement('review_inputs', 'fail', reasons=['library root changed on main since the review: SphereCeti.lean'],
                             library_root_only=True)
        action, reasons = classify(self.decision(review_inputs=inputs), {'reasons': []})
        self.assertEqual(action, 'needs_review');self.assertTrue(reasons[-1].startswith('measurement:'))
        for reason in (MERGE_STALE, MERGE_MISSING):  # Main advanced after the build: rebuild the merge.
            stale = self.decision(trusted_checks=requirement('trusted_checks', 'fail', reasons=[reason]),
                                  compiled_audit=requirement('compiled_audit', 'fail', reasons=[reason]))
            self.assertEqual(classify(stale, {'reasons': []}), ('refresh_build', [reason]))
        mismatch = self.decision(trusted_checks=requirement('trusted_checks', 'fail', reasons=[MERGE_MISMATCH]))
        self.assertEqual(classify(mismatch, {'reasons': []})[0], 'blocked')
        self.assertEqual(classify(self.decision(), {'reasons': ['no qualifying approval: x']})[0], 'blocked')
        self.assertEqual(classify(self.decision(), {'reasons': []}), ('merge', []))


class MergeAttestationTests(unittest.TestCase):
    """The tested merge tree binding: current main merged with this head, from the same trusted run."""

    def setUp(self):
        self.context, _, _, _, self.settings, self.statuses, _, _ = evidence()
        self.tree = '4' * 40
        self.statuses.append({'id': 3, 'context': 'trusted-merge', 'state': 'success', 'creator': {'id': 42, 'type': 'Bot'},
                              'description': f"Tested merge tree {self.tree} with main {self.context['tooling']}",
                              'url': self.statuses[0]['url'], 'target_url': self.statuses[0]['target_url'],
                              'created_at': self.statuses[0]['created_at']})

    def reasons(self, expected=None, **change):
        statuses = deepcopy(self.statuses)
        statuses[-1].update(change)
        return assess_merge(statuses, self.context, self.tree if expected is None else expected, self.settings)

    def test_binding_is_accepted_and_every_mismatch_refused(self):
        self.assertEqual(self.reasons(), [])
        self.assertEqual(self.reasons(expected='5' * 40), [MERGE_MISMATCH])
        self.assertEqual(self.reasons(description=f"Tested merge tree {self.tree} with main {'6'*40}"), [MERGE_STALE])
        self.assertEqual(assess_merge(self.statuses, self.context, None, self.settings), [MERGE_CONFLICT])
        self.assertEqual(assess_merge(self.statuses[:-1], self.context, self.tree, self.settings), [MERGE_MISSING])
        for change, reason in ((dict(state='failure'), 'trusted-merge is not successful'),
                               (dict(creator={'id': 8, 'type': 'Bot'}), 'trusted-merge has an unapproved producer'),
                               (dict(url=self.statuses[0]['url'][:-40] + '9' * 40), 'trusted-merge has a wrong head/location'),
                               (dict(target_url=f'https://github.com/{REPO}/actions/runs/101/attempts/1'),
                                'trusted-merge and trusted-build come from different run attempts'),
                               (dict(description='Tested merge'), 'trusted-merge does not attest its tested tree')):
            with self.subTest(reason):
                self.assertIn(reason, self.reasons(**change))
        longest = f"Tested merge tree {'a'*40} with main {'b'*40}"
        self.assertLessEqual(len(longest), 140)


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


class MergeSettingTests(unittest.TestCase):
    """The squash setting: the squash-only ruleset is the authority when the repository flag is hidden."""

    def test_ruleset_authority_and_visible_repository_flag(self):
        from sphereceti.merge_activation import merge_setting
        ruleset = {'source': 'ruleset', 'squash_only': True}
        # Run 45274799597: the read-only job token's repository response has no merge settings.
        self.assertEqual(merge_setting({'full_name': REPO}, REPO, ruleset)['findings'],
                         ['repository merge settings are not visible to this token; the ruleset\'s '
                          'allowed_merge_methods ["squash"] is the authority'])
        self.assertEqual(merge_setting({'full_name': REPO}, REPO, ruleset)['missing'], [])
        self.assertEqual(merge_setting({'full_name': REPO, 'allow_squash_merge': True}, REPO, ruleset)['verified'],
                         ['repository allows squash merges'])
        # A visible disabled flag still fails; hidden without a squash-only ruleset fails closed.
        self.assertEqual(merge_setting({'full_name': REPO, 'allow_squash_merge': False}, REPO, ruleset)['missing'],
                         ['repository does not allow squash merges'])
        for protection in ({'source': 'ruleset', 'squash_only': False}, {'source': 'classic'}):
            self.assertTrue(merge_setting({'full_name': REPO}, REPO, protection)['missing'])
        self.assertEqual(merge_setting({'full_name': 'other/repo'}, REPO, ruleset)['missing'],
                         ['repository identity is incompatible'])

    def test_only_exactly_squash_is_squash_only(self):
        from sphereceti.merge_activation import rulesets
        from ruleset_fixture import live
        from test_merge_controller import UNCONFIGURED
        branch, effective, listing, detail = live()
        self.assertTrue(rulesets(effective[0], listing[0], detail, REPO, UNCONFIGURED)['squash_only'])
        for methods in (['squash', 'merge'], ['merge'], None):
            changed = deepcopy(detail)
            rule = next(r for r in changed['rules'] if r['type'] == 'pull_request')
            if methods is None: del rule['parameters']['allowed_merge_methods']
            else: rule['parameters']['allowed_merge_methods'] = methods
            eff = [{**r, 'ruleset_source_type': 'Repository', 'ruleset_source': REPO, 'ruleset_id': changed['id']}
                   for r in changed['rules']]
            with self.subTest(methods=methods):
                self.assertFalse(rulesets(eff, listing[0], changed, REPO, UNCONFIGURED)['squash_only'])


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
FAKE_GIT = RECORD + '''if [ "$1" = -C ]; then shift 2; fi
case "$1" in
  rev-parse) echo "${3%^{commit\\}}" ;;
  merge-tree) echo "${FAKE_MERGE_TREE:-eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee}"
              if [ -n "${FAKE_MERGE_CONFLICT:-}" ]; then echo "CONFLICT (content): f"; exit 1; fi ;;
  commit-tree) echo ffffffffffffffffffffffffffffffffffffffff ;;
esac
'''


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
                'TOOLING_SHA': self.T, 'BUILD_RESULT': 'success', 'SCOPE': 'mathematical', 'MERGE_TREE': 'e' * 40,
                'RUN_URL': f'https://github.com/{REPO}/actions/runs/1/attempts/1'}
        done, calls = self.run_step('Publish separate build and scope verdicts for exact H', {**base, **env})
        posts = [json.loads(c) for c in calls if c.startswith('[') and '-f' in json.loads(c)]
        return done, posts, calls

    def test_refresh_publishes_its_binding_when_nothing_moved(self):
        done, posts, _ = self.publish()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertEqual(len(posts), 3)
        fields = [{a.split('=', 1)[0]: a.split('=', 1)[1] for a in post if '=' in a} for post in posts]
        self.assertEqual(fields[0]['description'], f'Approved tooling refresh: success; tooling {self.T}; pr 7; base {self.T}')
        self.assertEqual((fields[2]['context'], fields[2]['state'], fields[2]['description']),
                         ('trusted-merge', 'success', f"Tested merge tree {'e'*40} with main {self.T}"))
        self.assertTrue(all(post[2].endswith(f'/statuses/{self.H}') for post in posts))  # On the PR head commit.
        # Without a tested merge (the candidate stopped first), trusted-merge cannot qualify.
        done, posts, _ = self.publish(MERGE_TREE='', BUILD_RESULT='failure')
        merge = {a.split('=', 1)[0]: a.split('=', 1)[1] for a in posts[2] if '=' in a}
        self.assertEqual((merge['state'], merge['description']), ('failure', f'No tested merge with main {self.T}'))

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
        self.assertIn(f'git -C gate merge-tree --write-tree {self.T} {self.H}', calls)
        merge = 'f' * 40
        self.assertEqual((self.root / 'out').read_text(),
                         f"base={self.T}\nhead={self.H}\nmerge_tree={'e'*40}\ncandidate={merge}\n")
        # The gate and the attestation take the merge commit: the build is of what would land.
        self.assertTrue(any(c.startswith('python3 -I gate/scripts/trusted_gate.py') and f'--base {self.T} --head {merge}' in c
                            for c in calls), calls)
        self.assertTrue(any(c.startswith(f'bash gate/scripts/attest-pr-config.sh gate candidate {merge} workflow_dispatch 1 0')
                            for c in calls))

    def test_a_lagging_base_snapshot_still_builds_the_merge_and_a_conflict_builds_nothing(self):
        self.pr['base']['sha'] = 'd' * 40  # GitHub's base.sha snapshot lags main.
        done, calls = self.resolve()
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        self.assertIn(f'git -C gate merge-tree --write-tree {self.T} {self.H}', calls)
        self.setUp()
        done, calls = self.resolve(FAKE_MERGE_CONFLICT='1')
        self.assertNotEqual(done.returncode, 0)
        self.assertIn('does not merge cleanly with main', done.stdout + done.stderr)
        self.assertFalse([c for c in calls if c.startswith(('python3', 'bash'))])

    def test_resolve_refuses_before_fetching_anything(self):
        cases = {'head already moved': ({}, lambda: self.pr['head'].update(sha='c' * 40)),
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
