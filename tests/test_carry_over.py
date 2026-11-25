# SPDX-License-Identifier: Apache-2.0
"""Carrying a review and a formal approval over to "Update branch" heads (decision 2 on #100).

A real Git repository supplies main, a PR head H1 and update-branch merges. The same rule runs on
Git objects (the decision) and on a GET-only GitHub API served from that repository (selection, the
queue, record inspection and the controller's approval check), and both must agree.
"""
from datetime import timedelta
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools/project'))
from sphereceti.carry_over import ApiSource, GitSource, carry, describe
from sphereceti.config import OperatorPreferences, parse_policy
from sphereceti.local_review import RUBRICS
from sphereceti.merge_controller import formal_approval
from sphereceti.review_queue import queue
from sphereceti.review_records import BINDINGS, RecordError, make_record
from sphereceti.review_select import reviewed
from review_fixture import automation_policy, commit, git, init
from test_review_queue import SurveyAPI, stamp
from test_worker import PROJECT, gh_pr

REPO = PROJECT.repository
REVIEWER, AUTHOR = 7, 99


class Repo:
    """main M0 -> M1 (unrelated docs change); PR H1 off M0; H2 = Update branch (H1, M1)."""

    def __init__(self, root):
        self.path = root / 'repo'
        init(self.path)
        for name, text in {'README.md': 'spec\n', 'SphereCeti.lean': 'public import SphereCeti.Basic\n',
                           'SphereCeti/E8/Basic.lean': 'module\n-- a\n-- b\n-- c\n-- d\n-- e\n',
                           'policy/automation.toml': '# policy\n', 'tools/review/rubric.md': 'rubric\n',
                           'docs/infrastructure/notes.md': 'notes\n', 'tests/test_x.py': '# test\n'}.items():
            self.write(name, text)
        git(self.path, 'branch', '-M', 'main')
        self.m0 = commit(self.path)
        git(self.path, 'checkout', '-qb', 'pr')
        self.write('SphereCeti/E8/Lattice.lean', 'module\ntheorem e8 : True := trivial\n')
        self.write('SphereCeti/E8/Basic.lean', 'module\n-- a PR\n-- b\n-- c\n-- d\n-- e\n')
        self.h1 = commit(self.path)
        self.m1 = self.main_commit({'docs/infrastructure/notes.md': 'notes, revised\n'})
        self.h2 = self.update(self.h1, self.m1)

    def write(self, name, text):
        path = self.path / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def main_commit(self, files, parent=None):
        """A new commit on main (first-parent history), changing `files`."""
        git(self.path, 'checkout', '-q', 'main')
        for name, text in files.items():
            self.write(name, text)
        sha = commit(self.path)
        git(self.path, 'checkout', '-q', 'pr')
        return sha

    def update(self, head, main_commit, *, extra=None):
        """GitHub's "Update branch": a merge commit with parents (head, main_commit)."""
        tree = git(self.path, 'merge-tree', '--write-tree', main_commit, head).split()[0]
        if extra:
            git(self.path, 'checkout', '-q', '--detach', head)
            git(self.path, 'read-tree', tree)
            for name, text in extra.items():
                self.write(name, text)
                git(self.path, 'update-index', '--add', name)
            tree = git(self.path, 'write-tree')
            git(self.path, 'checkout', '-qf', 'pr')
        return git(self.path, 'commit-tree', tree, '-p', head, '-p', main_commit, '-m', 'Merge main into pr')

    def side_commit(self):
        """A commit on another branch, never on main's first-parent history."""
        git(self.path, 'checkout', '-q', '-b', 'side', self.m0)
        self.write('SphereCeti/E8/Side.lean', 'module\n')
        sha = commit(self.path)
        git(self.path, 'checkout', '-q', 'pr')
        return sha

    def main(self):
        return git(self.path, 'rev-parse', 'main')


class RepoAPI:
    """GET-only GitHub API answers computed from the repository; any write or unknown read fails."""

    def __init__(self, repo, comments=None):
        self.repo, self.records, self.calls = repo, comments or {}, []

    def comments(self, repository, number):
        return self.records.get(number, [])

    def call(self, endpoint, **kwargs):
        assert not kwargs.get('payload'), 'carry-over never writes'
        self.calls.append(endpoint)
        prefix = f'repos/{REPO}/'
        path = endpoint.removeprefix(prefix)
        if path.startswith('git/commits/'):
            sha = path.split('/')[-1]
            parents = git(self.repo.path, 'rev-list', '--parents', '-n', '1', sha).split()[1:]
            return {'sha': sha, 'parents': [{'sha': p} for p in parents],
                    'tree': {'sha': git(self.repo.path, 'rev-parse', f'{sha}^{{tree}}')}}
        if path.startswith('git/trees/') and path.endswith('?recursive=1'):
            tree = path.split('/')[2].split('?')[0]
            entries = []
            for line in git(self.repo.path, 'ls-tree', '-r', tree).splitlines():
                meta, name = line.split('\t')
                mode, kind, sha = meta.split()
                entries.append({'path': name, 'mode': mode, 'type': kind, 'sha': sha})
            return {'sha': tree, 'truncated': False, 'tree': entries}
        if path.startswith('compare/'):
            a, b = path.removeprefix('compare/').split('...')
            base = git(self.repo.path, 'merge-base', a, b)
            ahead = int(git(self.repo.path, 'rev-list', '--count', f'{a}..{b}'))
            behind = int(git(self.repo.path, 'rev-list', '--count', f'{b}..{a}'))
            status = 'identical' if not ahead and not behind else 'ahead' if not behind else 'behind' if not ahead else 'diverged'
            return {'merge_base_commit': {'sha': base}, 'status': status, 'ahead_by': ahead, 'behind_by': behind}
        if path == 'commits/main':
            return {'sha': self.repo.main()}
        raise RecordError('unexpected read')


def record_comment(number, head, base, tooling, *, cid=10, actor=REVIEWER, login='maintainer', verdicts=None):
    result = {k: 'a' * 64 for k in BINDINGS}
    result.update(repository=REPO, pr=number, tooling=tooling, head=head, base=base, diff_base=base,
                  completion='complete', execution_mode='commit', tooling_approved=True,
                  installed_tooling_matches_T=True, missing_context=[], config_differences=[],
                  verdicts={r: 'approve' for r in RUBRICS} | (verdicts or {}), reviews={})
    _, body = make_record(result)
    return {'id': cid, 'body': body, 'user': {'type': 'User', 'id': actor, 'login': login},
            'created_at': '2026-11-24T10:00:00Z', 'updated_at': '2026-11-24T10:00:00Z',
            'issue_url': f'https://api.github.com/repos/{REPO}/issues/{number}'}


class CarryOverRuleTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.r = Repo(Path(self.tmp.name))

    def both(self, h1, h2, main=None, revisions=None):
        """The rule from Git objects and from the GET-only API, which must agree exactly."""
        main = main or self.r.main()
        found = carry(GitSource(self.r.path), h1, h2, main, revisions or [self.r.m0])
        self.assertEqual(carry(ApiSource(RepoAPI(self.r), REPO), h1, h2, main, revisions or [self.r.m0]), found)
        return found

    def test_update_branch_with_an_identical_change_carries_over(self):
        found = self.both(self.r.h1, self.r.h2)
        self.assertTrue(found['carried'], found)
        self.assertEqual(found['via'], [{'merge': self.r.h2, 'main': self.r.m1}])
        self.assertEqual(found['unrelated_changes'], ['docs/infrastructure/notes.md'])
        self.assertEqual(describe(found), f'current (carried over from {self.r.h1[:7]} via update-branch)')

    def test_chained_update_merges_carry_over(self):
        m2 = self.r.main_commit({'tests/test_x.py': '# test, revised\n'})
        h3 = self.r.update(self.r.h2, m2)
        found = self.both(self.r.h1, h3)
        self.assertTrue(found['carried'], found)
        self.assertEqual([v['main'] for v in found['via']], [m2, self.r.m1])
        self.assertEqual(describe(found), f'current (carried over from {self.r.h1[:7]} via update-branch, 2 merges)')

    def test_a_conflict_resolution_or_extra_change_in_the_merge_does_not(self):
        # Main changed a file the PR changes (a different line, so it merges cleanly): the change differs.
        m2 = self.r.main_commit({'SphereCeti/E8/Basic.lean': 'module\n-- a\n-- b\n-- c\n-- d\n-- e main\n'})
        found = self.both(self.r.h1, self.r.update(self.r.h2, m2))
        self.assertFalse(found['carried'])
        self.assertIn("the PR's own change differs after the update", found['reason'])
        self.assertIn('SphereCeti/E8/Basic.lean', found['reason'])
        # A merge commit that resolves or adds anything beyond main's tree is not an update merge.
        for extra in ({'SphereCeti/E8/Lattice.lean': 'module\ntheorem e8 : True := by trivial\n'},
                      {'SphereCeti/E8/Sneaky.lean': 'module\n'}):
            with self.subTest(extra=list(extra)):
                found = self.both(self.r.h1, self.r.update(self.r.h1, self.r.m1, extra=extra))
                self.assertFalse(found['carried']);self.assertIn(list(extra)[0], found['reason'])

    def test_a_merge_of_a_non_main_branch_or_a_new_commit_does_not(self):
        side = self.r.side_commit()
        found = self.both(self.r.h1, self.r.update(self.r.h1, side))
        self.assertFalse(found['carried'])
        self.assertIn(f"merges {side[:12]}, which is not on main's first-parent history", found['reason'])
        git(self.r.path, 'checkout', '-q', '--detach', self.r.h2)
        self.r.write('SphereCeti/E8/Lattice.lean', 'module\ntheorem e8 : True := by trivial\n')
        pushed = commit(self.r.path)
        found = self.both(self.r.h1, pushed)
        self.assertFalse(found['carried']);self.assertIn('is not an update-branch merge (1 parent)', found['reason'])
        found = self.both(self.r.h2, self.r.h1)  # Backwards is never an update.
        self.assertFalse(found['carried'])

    def test_a_review_input_change_on_main_does_not(self):
        for name, category in (('README.md', 'specification'), ('policy/automation.toml', 'policy'),
                               ('tools/review/rubric.md', 'review tooling'), ('SphereCeti/E8/Other.lean', 'library')):
            with self.subTest(name):
                self.setUp()  # A fresh repository: only this input changes on main.
                m2 = self.r.main_commit({name: 'changed on main\n'})
                found = self.both(self.r.h1, self.r.update(self.r.h2, m2))
                self.assertFalse(found['carried'])
                self.assertEqual(found['changed_inputs'], {category: [name]})
                self.assertIn(f'review inputs changed on main since the review: {category}: {name}', found['reason'])

    def test_a_library_root_only_change_does_not_and_is_measured(self):
        m2 = self.r.main_commit({'SphereCeti.lean': 'public import SphereCeti.Basic\npublic import SphereCeti.Other\n'})
        found = self.both(self.r.h1, self.r.update(self.r.h2, m2))
        self.assertFalse(found['carried']);self.assertTrue(found['library_root_only'])
        self.assertIn('measurement: only SphereCeti.lean changed', found['reason'])

    def test_unreadable_or_truncated_evidence_never_carries(self):
        class Truncated(RepoAPI):
            def call(self, endpoint, **kwargs):
                value = super().call(endpoint, **kwargs)
                if '/git/trees/' in endpoint:
                    value['truncated'] = True
                return value
        found = carry(ApiSource(Truncated(self.r), REPO), self.r.h1, self.r.h2, self.r.main(), [self.r.m0])
        self.assertFalse(found['carried']);self.assertIn('incomplete', found['reason'])
        self.assertFalse(carry(GitSource(self.r.path), self.r.h1, self.r.h2, self.r.main(), [])['carried'])


class FormalApprovalCarryTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.r = Repo(Path(self.tmp.name))

    def approval(self, approver, author, head=None, commit=None):
        head = head or self.r.h2
        review = {'id': 1, 'user': {'id': approver, 'type': 'User'}, 'state': 'APPROVED',
                  'commit_id': commit or self.r.h1, 'author_association': 'COLLABORATOR'}
        source = ApiSource(RepoAPI(self.r), REPO)
        carried = lambda older: carry(source, older, head, self.r.main(), [self.r.m0])
        return formal_approval([review], f'user:{author}', head, (f'user:{approver}',), carried)

    def test_an_approval_on_the_reviewed_head_carries_over(self):
        found = self.approval(REVIEWER, AUTHOR)
        self.assertEqual(found['reasons'], [])
        self.assertEqual(found['qualifying'], [{'identity': f'user:{REVIEWER}', 'review_id': 1, 'commit_id': self.r.h2,
                                                'carried_from': self.r.h1, 'carried_via': [self.r.h2]}])

    def test_an_author_self_approval_never_carries(self):
        found = self.approval(REVIEWER, REVIEWER)
        self.assertEqual(found['qualifying'], []);self.assertIn(f'user:{REVIEWER} is the PR author', found['reasons'][0])

    def test_an_approval_that_does_not_carry_names_why(self):
        m2 = self.r.main_commit({'README.md': 'spec, revised\n'})
        found = self.approval(REVIEWER, AUTHOR, head=self.r.update(self.r.h2, m2))
        self.assertEqual(found['qualifying'], [])
        self.assertIn('review inputs changed on main since the review: specification: README.md', found['reasons'][0])


class SelectionAndQueueTests(unittest.TestCase):
    """Bare review and `sphereceti reviews` do not ask for a fresh review of an update-branch head."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.r = Repo(Path(self.tmp.name))
        self.policy = parse_policy(automation_policy(authorized_reviewers=[f'user:{REVIEWER}']))
        self.storage = Path(self.tmp.name) / 'storage'
        self.storage.mkdir()

    def selection_state(self, head, actor='someone'):
        api = RepoAPI(self.r, {3: [record_comment(3, self.r.h1, self.r.m0, self.r.m0)]})
        pr = {'number': 3, 'head': head, 'base': self.r.m1}
        return reviewed(api, api.comments(REPO, 3), REPO, pr, actor, self.policy, self.storage)

    def test_selection_shows_carried_over_and_skips_the_pr(self):
        self.assertEqual(self.selection_state(self.r.h2), (
            'reviewed', f'already has an accepted review (user:{REVIEWER}); '
                        f'current (carried over from {self.r.h1[:7]} via update-branch)'))
        self.assertEqual(self.selection_state(self.r.h2, actor='maintainer'), (
            'reviewed_by_you', f'you already reviewed this change; current (carried over from {self.r.h1[:7]} via update-branch)'))
        # A spec change on main since the review: a fresh review is needed again.
        m2 = self.r.main_commit({'README.md': 'spec, revised\n'})
        self.assertIsNone(self.selection_state(self.r.update(self.r.h2, m2)))

    def test_queue_lists_a_carried_over_review_as_done_not_revised(self):
        prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=str(self.storage))
        api = RepoAPI(self.r, {3: [record_comment(3, self.r.h1, self.r.m0, self.r.m0, login='yvonne')]})
        policy = parse_policy(automation_policy(authorized_reviewers=[f'user:{REVIEWER}']))
        prs = [gh_pr(3, author={'login': 'bob'}, headRefOid=self.r.h2, baseRefOid=self.r.m1, updatedAt=stamp(timedelta(hours=1)))]
        report = queue(PROJECT, policy, prefs, api=SurveyAPI(prs, actor='yvonne'), client=api)
        self.assertEqual(report['sections']['revised'], [])
        self.assertEqual(report['done'], [{'pr': 3, 'head': self.r.h2, 'code': 'reviewed_by_you', 'reason':
                                           f'you already reviewed this change; current (carried over from '
                                           f'{self.r.h1[:7]} via update-branch)'}])
        # With an extra change in the merge, it is a revision to re-review.
        extra = self.r.update(self.r.h1, self.r.m1, extra={'SphereCeti/E8/Sneaky.lean': 'module\n'})
        prs = [gh_pr(3, author={'login': 'bob'}, headRefOid=extra, baseRefOid=self.r.m1, updatedAt=stamp(timedelta(hours=1)))]
        report = queue(PROJECT, policy, prefs, api=SurveyAPI(prs, actor='yvonne'), client=api)
        self.assertEqual([e['pr'] for e in report['sections']['revised']], [3])

    def test_queue_keeps_your_change_request_waiting_on_the_author(self):
        prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=str(self.storage))
        changes = record_comment(3, self.r.h1, self.r.m0, self.r.m0, login='yvonne',
                                 verdicts={'naming': 'request_changes'})
        api = RepoAPI(self.r, {3: [changes]})
        prs = [gh_pr(3, author={'login': 'bob'}, headRefOid=self.r.h2, baseRefOid=self.r.m1, updatedAt=stamp(timedelta(hours=1)))]
        report = queue(PROJECT, self.policy, prefs, api=SurveyAPI(prs, actor='yvonne'), client=api)
        [waiting] = report['sections']['waiting_on_author']
        self.assertEqual(waiting['reason'], 'you requested changes (naming); no new change; '
                                            f'current (carried over from {self.r.h1[:7]} via update-branch)')


class DecisionCarryTests(unittest.TestCase):
    """End to end: the real decision and controller, after an update-branch merge of the reviewed head."""

    def setUp(self):
        from test_auto_approval import REVIEWER as HARNESS_REVIEWER, Harness
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        h = self.h = Harness(Path(self.tmp.name), policy_paths=('SphereCeti/E8',), merging=True,
                             approving_reviewers=(f'user:{HARNESS_REVIEWER}',))
        self.reviewer, self.h1 = HARNESS_REVIEWER, h.head
        # Main moves with an unrelated change; "Update branch" merges it into the reviewed head.
        git(h.repo, 'checkout', '-q', '--detach', h.tooling)
        (h.repo / 'docs/infrastructure').mkdir(parents=True, exist_ok=True)
        (h.repo / 'docs/infrastructure/notes.md').write_text('unrelated\n')
        m1 = commit(h.repo)
        git(h.repo, 'checkout', '-q', 'proof/e8')
        tree = git(h.repo, 'merge-tree', '--write-tree', m1, self.h1).split()[0]
        h2 = git(h.repo, 'commit-tree', tree, '-p', self.h1, '-p', m1, '-m', 'Merge main into proof/e8')
        self.update(m1, h2)
        self.reviews = [{'id': 1, 'user': {'id': self.reviewer, 'type': 'User'}, 'state': 'APPROVED',
                         'commit_id': self.h1, 'author_association': 'COLLABORATOR'}]

    def update(self, main, head):
        """GitHub's view after the update: new head, base.sha re-snapshotted to the merged main."""
        h = self.h
        h.current, h.head, h.base = main, head, main
        h.pr['head']['sha'], h.pr['base']['sha'] = head, main
        names = {'A': 'added', 'M': 'modified'}
        h.files = [{'sha': '0' * 40, 'filename': line.split('\t')[1], 'status': names[line[0]],
                    'additions': 1, 'deletions': 0, 'changes': 1}
                   for line in git(h.repo, 'diff', '--name-status', main, head).splitlines()]
        h.pr['changed_files'] = len(h.files)
        build = f'Approved tooling build: success; tooling {main}; pr 1; base {main}'
        for status in h.statuses:
            status['url'] = f'https://api.github.com/repos/{REPO}/statuses/{head}'
            if status['context'] == 'trusted-build': status['description'] = build
            if status['context'] == 'trusted-merge':
                status['description'] = f"Tested merge tree {git(h.repo, 'rev-parse', head + '^{tree}')} with main {main}"
        h.run.update(head_sha=head)
        h.run['pull_requests'][0]['head']['sha'], h.run['pull_requests'][0]['base']['sha'] = head, main
        for job in h.jobs: job['head_sha'] = head
        h.activity[0]['after'] = main

    def github(self, endpoint, **kwargs):
        shim = type('Shim', (), {'path': self.h.repo, 'main': lambda _: self.h.current})()
        path = endpoint.removeprefix(f'repos/{REPO}/')
        if path.startswith(('git/commits/', 'git/trees/')) or (path.startswith('compare/') and '...' in path):
            return RepoAPI(shim).call(endpoint)
        if path == 'pulls/1/reviews?per_page=100':
            return [list(self.reviews)]
        return self.h.respond(endpoint, **kwargs)

    def prepared(self, args, project, refs, *rest):
        # The context a review of refs['head'] binds now; a record matches only its own head and base.
        return {**self.h.context, 'head': refs['head'], 'base': refs['base'], 'tooling': refs['tooling'],
                'diff_base': git(self.h.repo, 'merge-base', refs['base'], refs['head'])}

    def run_controller(self):
        from unittest.mock import patch
        from types import SimpleNamespace
        from sphereceti.merge_controller import Backend, reconcile
        from sphereceti.review_post import GitHub
        from test_merge_controller import FakeWriter
        h = self.h
        def merged(payload):
            h.pr.update(merged=True, state='closed', merge_commit_sha='3' * 40)
            return {'merged': True, 'sha': '3' * 40}
        writer = FakeWriter(on_put=merged)
        backend = Backend(SimpleNamespace(cache_dir=Path(self.tmp.name) / 'cache', source_repo=h.repo,
                                          dependencies_dir=None), h.project, writer)
        policy = parse_policy(git(h.repo, 'show', f'{h.tooling}:policy/automation.toml') + '\n')
        ready = {'ready': True, 'merging_requested': True, 'executor_verified': True, 'tooling': h.current,
                 'protection': {'tested_tree_enforced': True}}
        backend.activation = SimpleNamespace(policy=policy, inspect=lambda **kw: dict(ready), refresh=lambda: None)
        with patch.object(GitHub, 'call', side_effect=self.github), \
                patch('sphereceti.merge_observation.prepare', side_effect=self.prepared):
            return reconcile(backend, lambda: [1], applying=True), writer, backend

    def test_review_and_approval_carry_over_and_the_update_head_merges(self):
        result, writer, _ = self.run_controller()
        self.assertEqual(result['results'][0]['state'], 'merged', result)
        self.assertEqual(writer.requests, [(f'repos/{REPO}/pulls/1/merge', {'sha': self.h.head, 'merge_method': 'squash'})])

    def test_the_decision_reports_the_carried_review(self):
        from unittest.mock import patch
        from types import SimpleNamespace
        from sphereceti.auto_approval import auto_approval
        from sphereceti.merge_observation import Reader
        from sphereceti.review_post import GitHub
        args = SimpleNamespace(pr=1, assume_proof_paths=None, cache_dir=Path(self.tmp.name) / 'c',
                               source_repo=self.h.repo, dependencies_dir=None)
        with patch.object(GitHub, 'call', side_effect=self.github), \
                patch('sphereceti.merge_observation.prepare', side_effect=self.prepared):
            report = auto_approval(args, self.h.project, client=Reader(REPO))
        self.assertTrue(report['would_approve'], report['reasons'])
        review = next(r for r in report['requirements'] if r['id'] == 'official_review')['evidence']
        inputs = next(r for r in report['requirements'] if r['id'] == 'review_inputs')['evidence']
        self.assertEqual(review['carried_from'], self.h1)
        self.assertEqual((inputs['carried_from'], inputs['carried_via'], inputs['change_identical']),
                         (self.h1, [self.h.head], True))
        self.assertEqual(inputs['unrelated_changes'], ['docs/infrastructure/notes.md'])

    def test_an_extra_change_in_the_update_merge_needs_review_and_a_fresh_approval(self):
        h = self.h
        m1 = h.current
        git(h.repo, 'checkout', '-q', '--detach', self.h1)
        git(h.repo, 'merge', '-q', '--no-ff', '--no-edit', m1)
        (h.repo / 'SphereCeti/E8/Sneaky.lean').write_text('module\n')
        git(h.repo, 'add', '.')
        git(h.repo, 'commit', '-q', '--amend', '--no-edit')
        sneaky = git(h.repo, 'rev-parse', 'HEAD')
        git(h.repo, 'checkout', '-q', 'proof/e8')
        self.update(m1, sneaky)
        result, writer, _ = self.run_controller()
        self.assertEqual(result['results'][0]['state'], 'needs_review')
        self.assertEqual(writer.requests, [])


if __name__ == '__main__':
    unittest.main()
