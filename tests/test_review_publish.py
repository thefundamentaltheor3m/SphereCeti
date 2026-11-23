"""Publishing a saved review run: fake providers and a fake GitHub executable, no network."""
import json
import os
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools/project'))
from review_fixture import automation_policy, commit, git
from review_post_fixture import PostingFixture


class SavedRunPublicationTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-publish-test-')
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.f = PostingFixture(self.root)
        review = self.f.run(extra=('--no-post',))
        self.assertEqual(review.returncode, 0, review.stderr)
        self.run_dir = self.root / 'result'
        self.record = json.loads((self.run_dir / 'record.json').read_text())
        self.provider_calls = len(self.f.calls())
        self.assertEqual(self.provider_calls, 10)
        self.assertEqual(self.f.posts(), 0)

    def tearDown(self):
        self.assertEqual(len(self.f.calls()), self.provider_calls, 'review-publish must never call a provider')

    def publish(self, *extra, run=None):
        r = self.f.publish(run or self.run_dir, *extra)
        return r, (json.loads(r.stdout) if r.stdout.strip() else None)

    def refused(self, fragment):
        r, report = self.publish()
        self.assertEqual(r.returncode, 2, r.stderr)
        self.assertEqual(report['state'], 'refused')
        self.assertTrue(any(fragment in reason for reason in report['reasons']), report['reasons'])
        self.assertEqual(self.f.posts(), 0)
        return report

    def test_saved_run_publishes_once_with_readback(self):
        r, report = self.publish()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(report['state'], 'published')
        self.assertEqual(report['publication']['state'], 'confirmed')
        self.assertTrue(report['publication']['authorized'])
        self.assertEqual(report['identity'], 'user:7')
        self.assertFalse(report['merge_eligible'])
        comments = self.f.api()['comments']
        self.assertEqual(len(comments), 1)
        self.assertEqual(comments[0]['body'], (self.run_dir / 'record.md').read_text())
        self.assertEqual(self.f.posts(), 1)
        self.assertTrue(any(c[0] == f'repos/thefundamentaltheor3m/SphereCeti/issues/comments/{comments[0]["id"]}'
                            for c in self.f.api()['calls']), 'readback')
        saved = json.loads((self.run_dir / 'result.json').read_text())
        self.assertEqual(saved['publication']['comment_id'], comments[0]['id'])
        self.assertEqual(saved['publication']['via'], 'review-publish')
        self.assertEqual(saved['archive']['state'], 'queued')
        again, report = self.publish()
        self.assertEqual(again.returncode, 2)
        self.assertIn('already published as comment', report['reasons'][0])
        self.assertEqual(self.f.posts(), 1)

    def test_existing_comment_with_this_record_means_nothing_is_written(self):
        body = (self.run_dir / 'record.md').read_text()
        self.f.update(comments=[{'id': 150, 'body': body, 'user': {'id': 7, 'type': 'User'},
                                 'issue_url': 'https://api.github.com/repos/thefundamentaltheor3m/SphereCeti/issues/1',
                                 'created_at': '2026-09-11T00:00:00Z', 'updated_at': '2026-09-11T00:00:00Z'}])
        before = (self.run_dir / 'result.json').read_bytes()
        r, report = self.publish()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(report['state'], 'already_published')
        self.assertEqual(report['comment_id'], 150)
        self.assertTrue(report['intact'])
        self.assertEqual(self.f.posts(), 0)
        self.assertEqual((self.run_dir / 'result.json').read_bytes(), before)

    def test_head_moved_is_refused_as_not_current(self):
        self.f.update(head=self.f.tooling)
        self.refused('cannot be published as current')

    def test_base_moved_is_refused(self):
        self.f.update(base=self.f.head)
        self.refused('the PR base moved')

    def test_closed_pr_is_refused(self):
        self.f.update(state='closed')
        self.refused('PR #1 is closed')

    def test_policy_that_no_longer_permits_posting_is_refused(self):
        git(self.f.repo, 'checkout', '-q', self.f.tooling)
        (self.f.repo / 'policy/automation.toml').write_text(automation_policy(authorized_reviewers=('user:7',)))
        self.f.update(tooling=commit(self.f.repo), base=self.f.tooling)  # main moves on; the PR base does not
        report = self.refused('posting is disabled by approved repository policy')
        self.assertIn('the approved policy changed since the review', report['reasons'])

    def test_changed_approved_context_is_refused(self):
        git(self.f.repo, 'checkout', '-q', self.f.tooling)
        (self.f.repo / 'CONVENTIONS.md').write_text('APPROVED SENTINEL changed conventions\n')
        self.f.update(tooling=commit(self.f.repo), base=self.f.tooling)
        self.refused('the approved review context changed since the review')

    def test_installed_tooling_mismatch_is_refused(self):
        from sphereceti import review_publish
        from sphereceti.config import parse_operator
        real = review_publish.prepare

        def other_tooling(*args, **kwargs):
            return {**real(*args, **kwargs), 'installed_tooling_digest': 'f' * 64}
        args = SimpleNamespace(run=str(self.run_dir), latest=None, source_repo=self.f.repo,
                               dependencies_dir=self.f.deps)
        prefs = parse_operator(self.f.operator.read_text())
        env = {k: v for k, v in self.f.env.items() if k in ('PATH', 'GH_TOKEN', 'HOME')}
        with patch.dict(os.environ, env), patch.object(review_publish, 'prepare', side_effect=other_tooling), \
                patch('sphereceti.local_review.execute', side_effect=AssertionError('provider')), \
                patch('sphereceti.local_review.invoke_bridge', side_effect=AssertionError('provider')):
            from sphereceti.config import parse_project, resource_text
            with self.assertRaises(review_publish.PublishRefused) as refusal:
                review_publish.publish_saved(args, parse_project(resource_text('sphereceti.toml')), prefs)
        self.assertEqual(refusal.exception.reasons, ['the installed tooling changed since the review'])
        self.assertEqual(self.f.posts(), 0)

    def test_different_gh_identity_is_refused(self):
        saved = json.loads((self.run_dir / 'result.json').read_text())
        saved['poster_identity'] = 'user:7'
        (self.run_dir / 'result.json').write_text(json.dumps(saved))
        self.f.update(user_id=8)
        self.refused('the run belongs to user:7; gh is authenticated as user:8')

    def test_ambiguous_post_is_not_retried_and_a_rerun_reconciles(self):
        self.f.update(post_fail='after')
        r, report = self.publish()
        self.assertEqual(r.returncode, 2, r.stderr)
        self.assertEqual(report['state'], 'unconfirmed')
        self.assertEqual(self.f.posts(), 1)
        saved = json.loads((self.run_dir / 'result.json').read_text())
        self.assertEqual(saved['publication']['state'], 'unconfirmed')
        self.assertEqual(saved['publication']['identity'], 'user:7')
        text = self.f.publish(self.run_dir)
        self.assertEqual(json.loads(text.stdout)['state'], 'already_published')
        self.assertEqual(self.f.posts(), 1)

    def test_lost_post_without_a_comment_publishes_on_the_next_run(self):
        self.f.update(post_fail='before')
        r, _ = self.publish()
        self.assertEqual(r.returncode, 2)
        self.f.update(post_fail=None)
        r, report = self.publish()
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(report['state'], 'published')
        self.assertEqual(len(self.f.api()['comments']), 1)
        self.assertEqual(self.f.posts(), 2)

    def test_latest_selects_the_newest_run_for_the_pr(self):
        review = self.f.run(output='second', extra=('--no-post',))
        self.assertEqual(review.returncode, 0, review.stderr)
        self.provider_calls = len(self.f.calls())
        runs = self.root / 'state/thefundamentaltheor3m__SphereCeti/runs'
        for name, directory in (('a' * 32, self.run_dir), ('b' * 32, self.root / 'second')):
            (runs / name).parent.mkdir(parents=True, exist_ok=True)
            directory.rename(runs / name)
        r = self.f.publish(['--latest', '1'])
        report = json.loads(r.stdout)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(report['run'], str(runs / ('b' * 32)))

    def test_text_output_names_the_comment(self):
        command = [a for a in self.f.publish_command(self.run_dir) if a != '--json']
        import subprocess
        r = subprocess.run(command, cwd=self.f.foreign, env=self.f.env, capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn('Published the saved review of #1', r.stdout)
        self.assertIn('#issuecomment-100 (authorized reviewer).', r.stdout)
        self.assertIn('No review was run again.', r.stdout)


class InterruptedPostTests(unittest.TestCase):
    def test_interrupted_post_is_published_without_another_review(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-publish-test-')
        self.addCleanup(temp.cleanup)
        f = PostingFixture(Path(temp.name))
        f.update(post_fail='before')
        review = f.run(extra=('--post',))
        self.assertEqual(review.returncode, 2, review.stderr)
        run = Path(temp.name) / 'result'
        saved = json.loads((run / 'result.json').read_text())
        self.assertEqual(saved['publication']['state'], 'unconfirmed')
        self.assertEqual((saved['poster_identity'], saved['contest_inputs']), ('user:7', 'github'))
        self.assertEqual(len(f.calls()), 10)
        f.update(post_fail=None)
        r = f.publish(run)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertEqual(json.loads(r.stdout)['state'], 'published')
        self.assertEqual(len(f.api()['comments']), 1)
        self.assertEqual(len(f.calls()), 10)


class SavedRunEligibilityTests(unittest.TestCase):
    """Runs that `review --post` could not have published stay local."""
    def check(self, change, fragment):
        from sphereceti.review_publish import eligibility
        record = {'execution_mode': 'commit', 'completion': 'complete',
                  'contests_through': {'correctness': 0}}
        result = {'source_mode': 'github', 'tooling_approved': True, 'contest_inputs': 'none'}
        for target, key, value in change:
            (record if target == 'record' else result)[key] = value
        reasons = eligibility(result, record)
        self.assertTrue(any(fragment in r for r in reasons), reasons)

    def test_ineligible_runs(self):
        cases = ((('result', 'source_mode', 'local_unverified'),), 'local sources'),\
                ((('result', 'tooling_approved', False),), 'prospective'),\
                ((('record', 'execution_mode', 'shadow'),), 'shadow runs are never published'),\
                ((('record', 'execution_mode', 'reply'),), 'reply runs are never published'),\
                ((('record', 'completion', 'error'),), 'completion is error'),\
                ((('result', 'contest_inputs', 'local'),), 'local reply inputs'),\
                ((('result', 'contest_inputs', None), ('record', 'contests_through', {'correctness': 5})),
                 'predates recorded contest provenance'),\
                ((('result', 'publication', {'state': 'confirmed', 'comment_id': 3}),), 'already published')
        for change, fragment in cases:
            with self.subTest(fragment=fragment):
                self.check(change, fragment)

    def test_partial_and_no_post_runs_are_eligible(self):
        from sphereceti.review_publish import eligibility
        for completion in ('complete', 'partial'):
            self.assertEqual(eligibility({'source_mode': 'github', 'tooling_approved': True, 'contest_inputs': 'none'},
                                         {'execution_mode': 'manual', 'completion': completion,
                                          'contests_through': {'correctness': 0}}), [])


if __name__ == '__main__':
    unittest.main()
