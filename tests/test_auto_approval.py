"""Read-only auto-approval decision over real Git trees and GitHub-shaped GET responses.

The fakes follow responses read from thefundamentaltheor3m/SphereCeti on 2026-11-23 (PR #47's
trusted run 45184402931): a pull_request_target run whose head_sha is the PR head, whose PR
association base.sha is the tooling, a candidate/status job pair, statuses linking the run
attempt, and docs-cache jobs that GitHub reports as skipped on pull requests.
"""
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools/project'))
from sphereceti.auto_approval import auto_approval, glob, proof_paths, pull_files
from sphereceti.config import ConfigError, parse_policy, parse_project, resource_text
from sphereceti.merge_checks import WORKFLOW
from sphereceti.merge_observation import Reader
from sphereceti.review_post import GitHub
from sphereceti.review_records import RecordError
from sphereceti.worker_checks import HUMAN_SCOPE
from review_fixture import ROOT, automation_policy, commit, git, init
from test_review_records import REPO, comment, result

RUN, AUTHOR, REVIEWER, OTHER = 45184402931, 99, 7, 8
TOPIC = ('SphereCeti/E8/**',)
CHECKS = 'schema_version = 1\nworkflow_id = 358051984\nstatus_creator_ids = [41898282]\n'
BOT = {'login': 'github-actions[bot]', 'id': 41898282, 'type': 'Bot'}


def proof(repo):
    # A proof PR adds only its own module; the SphereCeti.* glob builds it without a root import.
    (repo / 'SphereCeti/E8/Lattice.lean').write_text('module\n\n-- proof\ntheorem e8 : True := trivial\n')


def export_from_root(repo):
    root = repo / 'SphereCeti.lean'
    root.write_text(root.read_text().replace('public import SphereCeti.Basic\n',
                                             'public import SphereCeti.Basic\npublic import SphereCeti.E8.Lattice\n'))


class Harness:
    """One disposable repository: approved main T, a PR head H, and GitHub's view of both."""

    def __init__(self, root, change=proof, *, policy_paths=(), merging=False, approving_reviewers=()):
        self.root, self.repo = root, root / 'repo'
        init(self.repo)
        for name in ('sphereceti.toml', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'SphereCeti.lean',
                     'SphereCeti/Basic.lean', 'README.md', '.github/workflows/ci.yml'):
            (self.repo / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, self.repo / name)
        (self.repo / 'SphereCetiRoadmap').mkdir()
        (self.repo / 'SphereCetiRoadmap/Suggested.lean').write_text('module\n')
        (self.repo / 'SphereCeti/E8').mkdir()
        (self.repo / 'SphereCeti/E8/Basic.lean').write_text('module\n')
        (self.repo / 'policy').mkdir()
        (self.repo / 'policy/automation.toml').write_text(automation_policy(
            review_generation=True, posting=True, merging=merging, mathematical_paths=policy_paths,
            authorized_reviewers=(f'user:{REVIEWER}', f'user:{OTHER}')) +
            (f'approving_reviewers = {json.dumps(list(approving_reviewers))}\n' if approving_reviewers else ''))
        (self.repo / 'policy/merge-checks.toml').write_text(CHECKS)
        (self.repo / 'scripts').mkdir()
        (self.repo / 'scripts/check_audits.py').write_text('# approved\n')
        (self.repo / 'tools/review').mkdir(parents=True)
        (self.repo / 'tools/review/rubric.md').write_text('approved\n')
        self.tooling = commit(self.repo)
        git(self.repo, 'checkout', '-qb', 'proof/e8')
        # A change may commit itself (a gitlink cannot survive `git add .` without a checkout).
        self.head = git(self.repo, 'rev-parse', 'HEAD') if change(self.repo) else commit(self.repo)
        self.current = self.base = self.tooling
        project = parse_project(resource_text('sphereceti.toml'))
        self.project = project
        repo_ref = {'id': 1346330495, 'name': 'SphereCeti', 'url': f'https://api.github.com/repos/{REPO}'}
        self.pr = {'number': 1, 'state': 'open', 'merged': False, 'draft': False, 'mergeable': True,
                   'mergeable_state': 'blocked', 'auto_merge': None, 'title': 'Prove E8 lattice facts', 'body': None,
                   'user': {'login': 'contributor', 'id': AUTHOR, 'type': 'User'},
                   'head': {'sha': self.head, 'ref': 'proof/e8', 'repo': {'full_name': REPO}},
                   'base': {'sha': self.base, 'ref': 'main', 'repo': {'full_name': REPO}},
                   'changed_files': 0}
        self.files = self.github_files()
        self.pr['changed_files'] = len(self.files)
        mathematical = bool(policy_paths)
        url = f'https://github.com/{REPO}/actions/runs/{RUN}/attempts/1'
        self.statuses = [
            {'id': 59656456951, 'context': 'trusted-scope', 'state': 'success' if mathematical else 'failure',
             'description': ('Scope: mathematical; no merge authorization' if mathematical else HUMAN_SCOPE),
             'target_url': url, 'creator': BOT, 'created_at': '2026-11-23T13:32:19Z',
             'url': f'https://api.github.com/repos/{REPO}/statuses/{self.head}'},
            {'id': 59656455717, 'context': 'trusted-build', 'state': 'success',
             'description': f'Approved tooling build: success; tooling {self.tooling}', 'target_url': url, 'creator': BOT,
             'created_at': '2026-11-23T13:32:19Z', 'url': f'https://api.github.com/repos/{REPO}/statuses/{self.head}'}]
        # The trusted run's tested merge: the head merged into main (here main is the head's parent).
        self.statuses.append(
            {'id': 59656456952, 'context': 'trusted-merge', 'state': 'success',
             'description': f"Tested merge tree {git(self.repo, 'rev-parse', self.head + '^{tree}')} with main {self.tooling}",
             'target_url': url, 'creator': BOT, 'created_at': '2026-11-23T13:32:20Z',
             'url': f'https://api.github.com/repos/{REPO}/statuses/{self.head}'})
        self.run = {'id': RUN, 'run_attempt': 1, 'workflow_id': 358051984, 'path': WORKFLOW,
                    'event': 'pull_request_target', 'status': 'completed', 'conclusion': 'success',
                    'head_sha': self.head, 'head_branch': 'proof/e8', 'repository': {'full_name': REPO},
                    'head_repository': {'full_name': REPO},
                    'created_at': '2026-11-23T13:29:15Z', 'run_started_at': '2026-11-23T13:29:15Z',
                    'pull_requests': [{'id': 5454040028, 'number': 1, 'url': f'https://api.github.com/repos/{REPO}/pulls/1',
                                       'head': {'ref': 'proof/e8', 'sha': self.head, 'repo': repo_ref},
                                       'base': {'ref': 'main', 'sha': self.tooling, 'repo': repo_ref}}]}
        self.jobs = [{'id': 137726147771, 'name': 'candidate', 'run_id': RUN, 'run_attempt': 1, 'head_sha': self.head,
                      'status': 'completed', 'conclusion': 'success',
                      'started_at': '2026-11-23T13:29:22Z', 'completed_at': '2026-11-23T13:32:10Z'},
                     {'id': 137727780321, 'name': 'status', 'run_id': RUN, 'run_attempt': 1, 'head_sha': self.head,
                      'status': 'completed', 'conclusion': 'success',
                      'started_at': '2026-11-23T13:32:13Z', 'completed_at': '2026-11-23T13:32:22Z'}]
        # Main-only docs-cache jobs that GitHub reports as skipped; no approval decision reads them.
        self.check_runs = {'total_count': 2, 'check_runs': [
            {'id': 1, 'name': 'deploy-pages', 'status': 'completed', 'conclusion': 'skipped', 'head_sha': self.head},
            {'id': 2, 'name': 'publish-cache', 'status': 'completed', 'conclusion': 'skipped', 'head_sha': self.head}]}
        # Repository activity: the merge that last moved main, before the trusted run was created.
        self.activity = [{'id': 51507619776, 'before': 'd' * 40, 'after': self.tooling, 'ref': 'refs/heads/main',
                          'timestamp': '2026-11-23T13:10:09Z', 'activity_type': 'pr_merge'}]
        self.context = result()
        self.context.update(repository=REPO, pr=1, tooling=self.tooling, head=self.head, base=self.base,
                            diff_base=self.tooling, dependency_digest=hashlib.sha256(
                                (self.repo / 'lake-manifest.json').read_bytes()).hexdigest())
        self.comments = [comment(self.context, actor=REVIEWER)[0]]
        self.calls = []

    def github_files(self):
        out = git(self.repo, 'diff', '--name-status', '-M', self.tooling, self.head)
        names = {'A': 'added', 'M': 'modified', 'D': 'removed', 'R': 'renamed', 'T': 'changed'}
        files = []
        for line in out.splitlines():
            status, *paths = line.split('\t')
            entry = {'sha': '0' * 40, 'filename': paths[-1], 'status': names[status[0]],
                     'additions': 1, 'deletions': 0, 'changes': 1}
            if status[0] == 'R':
                entry['previous_filename'] = paths[0]
            files.append(entry)
        return files

    def respond(self, endpoint, *, payload=None, paginate=False, method=None):
        assert payload is None and method is None, 'GET only'
        self.calls.append(endpoint)
        prefix = f'repos/{REPO}/'
        if endpoint.startswith(prefix + 'compare/'):
            # The record's tooling is an ancestor of the advanced main (GitHub's compare shape).
            revision = endpoint.removeprefix(prefix + 'compare/').split('...')[0]
            return {'status': 'ahead', 'merge_base_commit': {'sha': revision}}
        table = {
            'pulls/1': self.pr,
            'commits/main': {'sha': self.current},
            'pulls/1/files?per_page=100': [self.files[i:i + 100] for i in range(0, max(len(self.files), 1), 100)],
            'issues/1/comments?per_page=100': [self.comments],
            f'commits/{self.head}/statuses?per_page=100': [self.statuses],
            f'actions/runs/{RUN}': self.run,
            f'actions/runs/{RUN}/attempts/1/jobs?per_page=100': [{'total_count': len(self.jobs), 'jobs': self.jobs}],
            f'commits/{self.head}/check-runs?per_page=100': self.check_runs,
            'activity?ref=refs%2Fheads%2Fmain&direction=desc&per_page=1': self.activity,
        }
        return deepcopy(table[endpoint.removeprefix(prefix)])

    def prepared(self, *args, **kwargs):
        # Review-context digests are exercised by test_review_records; this fixture's main cannot
        # contain the installed package, so the installed-tooling comparison is supplied here.
        return deepcopy(self.context)

    def decide(self, assume=TOPIC):
        args = SimpleNamespace(pr=1, assume_proof_paths=list(assume) if assume else None,
                               cache_dir=self.root / 'cache', source_repo=self.repo, dependencies_dir=None)
        with patch.object(GitHub, 'call', side_effect=self.respond), \
                patch('sphereceti.merge_observation.prepare', side_effect=self.prepared):
            return auto_approval(args, self.project, client=Reader(REPO))


def status(report):
    return {r['id']: r['status'] for r in report['requirements']}


def failed(report):
    return {r['id'] for r in report['requirements'] if r['status'] != 'pass'}


class AutoApprovalTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.count = 0

    def harness(self, change=proof, **kwargs):
        self.count += 1
        root = Path(self.tmp.name) / str(self.count)
        root.mkdir()
        return Harness(root, change, **kwargs)

    def test_eligible_proof_pr_is_approved_without_any_github_approval(self):
        h = self.harness()
        report = h.decide()
        self.assertTrue(report['would_approve'], json.dumps(report, indent=2))
        self.assertEqual(set(status(report).values()), {'pass'})
        self.assertTrue(report['hypothetical'])
        self.assertEqual(report['assumed_proof_paths'], list(TOPIC))
        self.assertTrue(report['note'].startswith('HYPOTHETICAL'))
        self.assertFalse(report['github_approval_required'])
        self.assertEqual(report['pr'], 1)
        self.assertEqual((report['head'], report['base'], report['tooling']), (h.head, h.tooling, h.tooling))
        self.assertEqual(report['author']['identity'], f'user:{AUTHOR}')
        self.assertEqual(report['review_publishers'][0]['identity'], f'user:{REVIEWER}')
        paths = report['requirements'][0]['evidence']
        self.assertEqual(paths['eligible'], ['SphereCeti/E8/Lattice.lean'])
        self.assertNotIn('root_imports', paths)
        self.assertIn('never edit SphereCeti.lean', paths['root_rule'])
        trusted = report['requirements'][1]['evidence']
        self.assertIn('hypothetical allowlist', trusted['trusted_scope'])
        audit = report['requirements'][2]['evidence']
        self.assertEqual((audit['run'], audit['run_head_sha'], audit['association_base_sha']),
                         ([RUN, 1], h.head, h.tooling))
        self.assertEqual(audit['candidate_job']['conclusion'], 'success')
        self.assertEqual((audit['attested_tooling'], audit['approved_tooling']), (h.tooling, h.tooling))
        self.assertTrue(audit['diagnostic']['run_created_after_main_moved'])
        # No GitHub review, merge, or check-run endpoint is consulted, and every read is a GET.
        self.assertFalse(any('reviews' in c or 'merge' in c or 'check-runs' in c for c in h.calls))
        self.assertEqual(report['requirements'][5]['evidence']['mergeable_state'], 'blocked')

    def test_mergeable_states_that_await_approval_or_checks_remain_decidable(self):
        for state in ('blocked', 'unstable', 'clean', 'has_hooks'):
            with self.subTest(state=state):
                h = self.harness(); h.pr['mergeable_state'] = state
                self.assertTrue(h.decide()['would_approve'])

    def test_non_topic_and_human_paths_are_listed(self):
        cases = {
            'SphereCeti/Sphere/Packing.lean': 'outside the proof-topic allowlist',
            'SphereCeti/Basic.lean': 'protected library module',
            'README.md': 'roadmap specification',
            'SphereCetiRoadmap/Suggested.lean': 'roadmap specification',
            '.github/workflows/ci.yml': 'CI',
            'policy/automation.toml': 'review policy',
            'tools/review/rubric.md': 'review policy',
            'lakefile.toml': 'dependencies',
            'lean-toolchain': 'dependencies',
            'scripts/check_audits.py': 'merge machinery',
            'tools/project/sphereceti/gate.py': 'merge machinery',
        }
        for path, route in cases.items():
            with self.subTest(path=path):
                def change(repo, path=path):
                    proof(repo)
                    target = repo / path
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text((target.read_text() if target.exists() else '') + '\n-- changed\n')
                report = self.harness(change).decide()
                self.assertFalse(report['would_approve'])
                ineligible = report['requirements'][0]['evidence']['ineligible']
                self.assertEqual([p['path'] for p in ineligible], [path])
                self.assertIn(route, ineligible[0]['reason'])
                self.assertIn(f'paths: {path}: {ineligible[0]["reason"]}', report['reasons'])
                self.assertEqual(status(report)['official_review'], 'not_assessed')

    def test_any_library_root_edit_is_routed_to_human_review(self):
        # Proof PRs no longer edit the root, so even the formerly allowed export is protected again.
        edits = {
            'export with the proof': lambda repo: (proof(repo), export_from_root(repo)),
            'export alone': lambda repo: (repo / 'SphereCeti.lean').write_text(
                (repo / 'SphereCeti.lean').read_text().replace(
                    'public import SphereCeti.Basic\n', 'public import SphereCeti.Basic\npublic import SphereCeti.E8.Basic\n')),
            'sorted reorder': lambda repo: (proof(repo), (repo / 'SphereCeti.lean').write_text(
                (repo / 'SphereCeti.lean').read_text().replace(
                    'public import SphereCeti.Basic\n', '\npublic import SphereCeti.Basic\n'))),
            'non-import line': lambda repo: (proof(repo), (repo / 'SphereCeti.lean').write_text(
                (repo / 'SphereCeti.lean').read_text() + 'theorem sneaky : True := trivial\n')),
        }
        for name, change in edits.items():
            for policy_paths in ((), ('SphereCeti/E8',)):
                with self.subTest(name=name, policy=policy_paths):
                    # The change applies its edits and returns None, so the harness commits it.
                    h = self.harness(lambda repo, change=change: change(repo) and None, policy_paths=policy_paths)
                    report = h.decide(assume=None) if policy_paths else h.decide()
                    self.assertFalse(report['would_approve'])
                    ineligible = report['requirements'][0]['evidence']['ineligible']
                    self.assertEqual([p['path'] for p in ineligible], ['SphereCeti.lean'])
                    self.assertEqual(ineligible[0]['reason'], 'library root requires human approval')

    def test_renames_deletions_symlinks_and_submodules_are_ineligible(self):
        def rename(repo):
            git(repo, 'mv', 'SphereCeti/E8/Basic.lean', 'SphereCeti/E8/Renamed.lean')
        def delete(repo):
            (repo / 'SphereCeti/E8/Basic.lean').unlink()
        for change, word in ((rename, 'renamed'), (delete, 'removed')):
            with self.subTest(word=word):
                report = self.harness(change).decide()
                self.assertFalse(report['would_approve'])
                self.assertIn(word, report['requirements'][0]['evidence']['ineligible'][0]['reason'])
        def symlink(repo):
            os.symlink('Basic.lean', repo / 'SphereCeti/E8/Link.lean')
        def submodule(repo):
            git(repo, 'update-index', '--add', '--cacheinfo', f'160000,{"1" * 40},SphereCeti/E8/Sub')
            git(repo, 'commit', '-qm', 'submodule')
            return True
        for change, path in ((symlink, 'SphereCeti/E8/Link.lean'), (submodule, 'SphereCeti/E8/Sub')):
            with self.subTest(path=path):
                report = self.harness(change).decide()
                self.assertFalse(report['would_approve'])
                self.assertEqual(status(report)['paths'], 'fail')
                self.assertIn(path, report['reasons'][0])

    def test_github_file_list_must_match_exact_git_diff(self):
        def two_modules(repo):
            proof(repo)
            (repo / 'SphereCeti/E8/Shell.lean').write_text('module\n')
        h = self.harness(two_modules)
        h.files = h.files[:1]; h.pr['changed_files'] = 1
        report = h.decide()
        self.assertFalse(report['would_approve'])
        self.assertIn('differs from the exact Git diff', report['requirements'][0]['evidence']['problems'][0])

    def test_truncated_or_capped_file_lists_are_errors(self):
        for change in ({'changed_files': 3}, {'changed_files': 3000}, {'changed_files': None}):
            with self.subTest(change=change):
                h = self.harness(); h.pr.update(change)
                with self.assertRaises(RecordError):
                    h.decide()
        client = Reader(REPO)
        for pages in ([], {}, [None], [[{'filename': 'a', 'status': 'added'}], [{'filename': 'a', 'status': 'added'}]]):
            with patch.object(GitHub, 'call', return_value=pages), self.assertRaises(RecordError):
                pull_files(client, REPO, {'number': 1, 'changed_files': 2 if len(pages) == 2 else 1})

    def test_author_as_sole_official_reviewer_is_refused(self):
        h = self.harness(); h.pr['user']['id'] = REVIEWER
        report = h.decide()
        self.assertFalse(report['would_approve'])
        self.assertEqual(status(report)['official_review'], 'pass')
        self.assertEqual(failed(report), {'independent_reviewer'})
        self.assertIn('independent_reviewer: the PR author is the sole official reviewer', report['reasons'])
        self.assertTrue(report['review_publishers'][0]['is_author'])
        # A second, independent complete approval for the same exact evidence satisfies independence.
        h.comments.append(comment(h.context, number=11, actor=OTHER)[0])
        self.assertTrue(h.decide()['would_approve'])

    def test_incomplete_advisory_unauthorized_or_stale_reviews_are_refused(self):
        h = self.harness()
        cases = [{'completion': 'partial'}, {'execution_mode': 'shadow'}, {'missing_context': ['roadmap']},
                 {'head': '4' * 40}, {'base': '4' * 40}, {'diff_base': '4' * 40},
                 {'verdicts': {**h.context['verdicts'], 'correctness': 'request_changes'}}]
        for change in cases:
            with self.subTest(change=change):
                h.comments = [comment({**h.context, **change}, actor=REVIEWER)[0]]
                report = h.decide()
                self.assertFalse(report['would_approve'])
                self.assertIn('official_review', failed(report))
        h.comments = [comment(h.context, actor=900)[0]]
        self.assertIn('official_review: no complete authorized review', h.decide()['reasons'])
        h.comments = []
        self.assertFalse(h.decide()['would_approve'])

    def test_stale_head_or_base_and_pull_request_state_are_refused(self):
        cases =[({'state': 'closed'}, 'not open'), ({'merged': True}, 'not open'), ({'draft': True}, 'draft'),
                 ({'mergeable': False, 'mergeable_state': 'dirty'}, 'conflicts'),
                 ({'mergeable': None, 'mergeable_state': 'unknown'}, 'indeterminate')]
        for change, word in cases:
            with self.subTest(change=change):
                h = self.harness(); h.pr.update(change)
                report = h.decide()
                self.assertFalse(report['would_approve'])
                self.assertTrue(any(word in r for r in report['requirements'][5]['evidence']['reasons']), report['reasons'])
        h = self.harness(); h.pr['base'] = {**h.pr['base'], 'ref': 'stack'}
        self.assertIn('pull_request', failed(h.decide()))
        # Main advanced past the trusted build: the tested merge is stale, so build and audit fail.
        # Option 2: GitHub's base.sha snapshot is never compared with main, and the review stays valid
        # because the change is the same and main changed no review input.
        h = self.harness()
        h.current = git(h.repo, 'commit-tree', f'{h.tooling}^{{tree}}', '-p', h.tooling, '-m', 'main advanced')
        report = h.decide()
        self.assertFalse(report['would_approve'])
        self.assertEqual(failed(report), {'trusted_checks', 'compiled_audit'})
        self.assertIn('trusted_checks: trusted-merge tested an older main; rebuild the merge with current main',
                      report['reasons'])
        self.assertFalse(report['merge']['head_contains_main'])

    def test_failed_or_missing_trusted_build_or_audit_is_refused(self):
        def build(h, **change): h.statuses[1].update(change)
        cases = {
            'failed build status': lambda h: build(h, state='failure'),
            'missing build status': lambda h: h.statuses.pop(1),
            'missing scope status': lambda h: h.statuses.pop(0),
            'foreign producer': lambda h: build(h, creator={'id': 8, 'type': 'Bot'}),
            'failed candidate job': lambda h: h.jobs[0].update(conclusion='failure'),
            'failed run': lambda h: h.run.update(conclusion='failure'),
            'run for another head': lambda h: h.run.update(head_sha='6' * 40),
            'untrusted workflow': lambda h: h.run.update(path='.github/workflows/ci.yml', event='pull_request'),
            'association with old base': lambda h: h.run['pull_requests'][0]['base'].update(sha='7' * 40),
            'scope failure for another reason': lambda h: h.statuses[0].update(description='Scope: other'),
        }
        for name, change in cases.items():
            with self.subTest(name=name):
                h = self.harness(); change(h)
                report = h.decide()
                self.assertFalse(report['would_approve'])
                self.assertIn('trusted_checks', failed(report))
                if name != 'scope failure for another reason':
                    self.assertIn('compiled_audit', failed(report))

    def test_old_run_with_unchanged_head_is_refused_by_its_attested_tooling(self):
        # The head is unchanged and current with main, but its trusted run predates main's move to
        # the current tooling. GitHub reports the run's PR association with the live base, so base
        # equality cannot reveal that; the #48 attestation of github.workflow_sha does.
        old = '9' * 40
        cases = {'attests old tooling': f'Approved tooling build: success; tooling {old}',
                 'predates the attestation': 'Approved tooling build: success'}
        for name, description in cases.items():
            with self.subTest(name=name):
                h = self.harness()
                h.statuses[1]['description'] = description
                h.activity[0].update(timestamp='2026-11-23T13:40:49Z')  # main moved after the run
                report = h.decide()
                self.assertFalse(report['would_approve'])
                self.assertEqual(failed(report), {'trusted_checks', 'compiled_audit'})
                audit = report['requirements'][2]['evidence']
                self.assertEqual(audit['association_base_sha'], h.tooling)
                self.assertEqual(audit['attested_tooling'], old if 'old' in name else None)
                self.assertFalse(audit['diagnostic']['run_created_after_main_moved'])
                self.assertTrue(any(('tooling other than approved main' if 'old' in name else
                                     'does not attest its tooling') in r for r in audit['reasons']), audit['reasons'])

    def test_timestamps_are_diagnostic_only(self):
        # A run that looks stale by timestamps but attests the current tooling is accepted, and an
        # unavailable or malformed activity response leaves the decision unchanged.
        for name, change in {'run predates main': lambda h: h.activity[0].update(timestamp='2026-11-23T13:40:49Z'),
                             'activity names another commit': lambda h: h.activity[0].update(after='8' * 40),
                             'activity unavailable': lambda h: setattr(h, 'activity', [])}.items():
            with self.subTest(name=name):
                h = self.harness(); change(h)
                report = h.decide()
                self.assertTrue(report['would_approve'], report['reasons'])
                self.assertIn(report['requirements'][2]['evidence']['diagnostic']['run_created_after_main_moved'],
                              (False, None))

    def test_real_empty_policy_is_reported_and_never_assumed(self):
        h = self.harness()
        report = h.decide(assume=None)
        self.assertFalse(report['would_approve'])
        self.assertFalse(report['hypothetical'])
        self.assertIsNone(report['assumed_proof_paths'])
        self.assertFalse(report['note'].startswith('HYPOTHETICAL'))
        self.assertEqual(status(report)['policy'], 'fail')
        self.assertIn('mathematical_paths is empty', report['requirements'][0]['evidence']['problems'][0])
        policy = next(r for r in report['requirements'] if r['id'] == 'policy')['evidence']
        self.assertEqual((policy['merging'], policy['mathematical_paths']), (False, []))

    def test_future_approved_policy_needs_no_hypothesis(self):
        def topic_only(repo):
            (repo / 'SphereCeti/E8/Lattice.lean').write_text('module\n')
        h = self.harness(topic_only, policy_paths=('SphereCeti/E8',))
        report = h.decide(assume=None)
        self.assertTrue(report['would_approve'], report['reasons'])
        self.assertFalse(report['hypothetical'])
        self.assertEqual(report['requirements'][1]['evidence']['trusted_scope'], 'success')
        # Without the hypothesis, a human_review trusted scope for a topic-only PR is not overridden.
        h.statuses[0].update(state='failure', description=HUMAN_SCOPE)
        self.assertIn('trusted_checks: trusted-scope is not successful', h.decide(assume=None)['reasons'])

    def test_shipped_policy_admits_module_only_prs_in_any_topic(self):
        shipped = parse_policy((ROOT / 'policy/automation.toml').read_text()).mathematical_paths
        self.assertEqual(shipped, ('SphereCeti/',))

        def new_topic(repo):
            (repo / 'SphereCeti/NumberTheory').mkdir(exist_ok=True)
            (repo / 'SphereCeti/NumberTheory/Foo.lean').write_text('module\n\n-- proof\n')

        for name, change in (('NumberTheory, a new topic', new_topic), ('E8', proof)):
            with self.subTest(topic=name):
                report = self.harness(change, policy_paths=shipped).decide(assume=None)
                self.assertTrue(report['would_approve'], report['reasons'])
                self.assertFalse(report['hypothetical'])
                self.assertEqual(status(report)['paths'], 'pass')

        def write(path, text='module\n'):
            def change(repo):
                new_topic(repo)
                (repo / path).parent.mkdir(parents=True, exist_ok=True)
                (repo / path).write_text(text)
            return change
        root = (ROOT / 'SphereCeti.lean').read_text()
        cases = {'SphereCeti.lean': (write('SphereCeti.lean', root + 'public import SphereCeti.NumberTheory.Foo\n'),
                                     'library root requires human approval'),
                 'SphereCeti/Basic.lean': (write('SphereCeti/Basic.lean', 'module\n-- changed\n'),
                                           'protected library module requires human approval'),
                 'SphereCeti/Pinned.lean': (write('SphereCeti/Pinned.lean'),
                                            'protected library module requires human approval'),
                 'SphereCeti/Suggested.lean': (write('SphereCeti/Suggested.lean'),
                                               'protected library module requires human approval'),
                 'SphereCetiExtra/Foo.lean': (write('SphereCetiExtra/Foo.lean'), 'outside the proof-topic allowlist')}
        for path, (change, reason) in cases.items():
            with self.subTest(path=path):
                report = self.harness(change, policy_paths=shipped).decide(assume=None)
                self.assertFalse(report['would_approve'])
                ineligible = report['requirements'][0]['evidence']['ineligible']
                self.assertEqual([(p['path'], p['reason']) for p in ineligible], [(path, reason)])

    def test_hypothetical_allowlist_globs_are_narrow(self):
        topic = glob('SphereCeti/E8/**')
        self.assertTrue(topic.fullmatch('SphereCeti/E8/A.lean'))
        self.assertTrue(topic.fullmatch('SphereCeti/E8/x/B.lean'))
        self.assertFalse(topic.fullmatch('SphereCeti/E80/A.lean'))
        lean = glob('SphereCeti/**/*.lean')
        self.assertTrue(lean.fullmatch('SphereCeti/E8/x/B.lean'))
        self.assertFalse(lean.fullmatch('SphereCeti/E8/notes.md'))
        for bad in ('README.md', '**', '../SphereCeti/x', 'SphereCeti/a**', 'SphereCeti/[ab].lean', 'SphereCeti/x y'):
            with self.subTest(bad=bad), self.assertRaises(ConfigError):
                proof_paths(None, [bad])


class AutoApprovalCliTests(unittest.TestCase):
    def test_cli_reports_hypothetical_ineligible_decision_with_get_only_reads(self):
        from merge_fixture import MergeFixture
        with tempfile.TemporaryDirectory() as tmp:
            f = MergeFixture(Path(tmp))
            # Extend the GET-only fake with the PR file list GitHub returns for this README change.
            fake = f.bin / 'gh'
            fake.write_text(fake.read_text().replace(
                "elif endpoint==f'repos/{repo}/commits/main'",
                "elif endpoint==f'repos/{repo}/pulls/1/files?per_page=100':out=[[{'filename':'README.md','status':'modified'}]]\n"
                "elif endpoint==f'repos/{repo}/commits/main'").replace(
                "'state':'open'", "'changed_files':1,'state':'open'"))
            command = f.command()
            command[command.index('merge-observe')] = 'auto-approve-check'
            run = subprocess.run([*command, '--assume-proof-paths', 'SphereCeti/E8/**'], cwd=f.foreign, env=f.env,
                                 capture_output=True, text=True, timeout=120)
            self.assertEqual(run.returncode, 0, run.stderr)
            report = json.loads(run.stdout)
            self.assertFalse(report['would_approve'])
            self.assertTrue(report['hypothetical'])
            self.assertEqual(report['requirements'][0]['evidence']['ineligible'][0]['path'], 'README.md')
            calls = f.api()['calls']
            self.assertFalse(any('--method' in c or '--input' in c for c in calls))
            self.assertFalse(f.calls())  # no provider
            text = subprocess.run([*command[:-1], '--assume-proof-paths', 'SphereCeti/E8/**'], cwd=f.foreign,
                                  env=f.env, capture_output=True, text=True, timeout=120)
            self.assertEqual(text.returncode, 0, text.stderr)
            self.assertIn('would_approve = false [HYPOTHETICAL', text.stdout)
            bad = subprocess.run([*command, '--assume-proof-paths', 'README.md'], cwd=f.foreign, env=f.env,
                                 capture_output=True, text=True, timeout=120)
            self.assertEqual(bad.returncode, 2)


if __name__ == '__main__':
    unittest.main()
