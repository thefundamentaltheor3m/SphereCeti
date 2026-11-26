# SPDX-License-Identifier: Apache-2.0
"""Advisory contributor review claims: post, confirm, yield or proceed, and edit on finish."""
from argparse import Namespace
from datetime import timedelta
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences, parse_project, resource_text
from sphereceti.local_review import RUBRICS, ReviewError
from sphereceti.review_claims import (MARKER, TTL, ClaimRefused, ClaimYielded, live, note, parse,
                                      render, run_claimed)
from sphereceti.review_records import RecordError, assess_records
from sphereceti.review_select import run_bare
from sphereceti import worker_leases
from sphereceti.worker_leases import stamp, utcnow
from test_review_select import POLICY, BareReviewHarness
from test_worker import FakeAPI, gh_pr

PROJECT = parse_project(resource_text('sphereceti.toml'))
REPO = PROJECT.repository
HEAD, BASE = 'a' * 40, 'b' * 40
USERS = {7: 'yvonne', 9: 'alice', 11: 'bob'}


def claim_comment(cid, *, user=9, actor=None, head=HEAD, state='in_progress', age=timedelta(0),
                  ttl=TTL, pr=1, login=None):
    now = utcnow() - age
    data = {'repository': REPO, 'pr': pr, 'head': head, 'base': BASE, 'actor': actor or f'user:{user}',
            'login': login or USERS[user], 'claim': f'{cid:032x}', 'started_at': stamp(now),
            'expires_at': stamp(now + timedelta(seconds=ttl)), 'state': state,
            'detail': None if state == 'in_progress' else 'x'}
    return {'id': cid, 'body': render(data), 'user': {'id': user, 'type': 'User', 'login': USERS[user]},
            'issue_url': f'https://api.github.com/repos/{REPO}/issues/{pr}',
            'created_at': stamp(now), 'updated_at': stamp(now)}


class FakeGitHub:
    """Shared comment store; one client per GitHub identity."""

    def __init__(self):
        self.store, self.next_id, self.calls = {}, 100, []
        self.fail_patch = self.truncated = False
        self.on_post = self.after_post = None
        self.stale_reads = 0

    def client(self, user):
        return Client(self, user)


class Client:
    def __init__(self, hub, user):
        self.hub, self.user = hub, user

    def comments(self, repository, pr):
        if self.hub.truncated:
            raise RecordError('incomplete comments response')
        comments = json.loads(json.dumps(self.hub.store.get(pr, [])))
        if self.hub.stale_reads and comments:
            self.hub.stale_reads -= 1  # a read that began before the newest comment landed
            comments = comments[:-1]
        return comments

    def call(self, endpoint, *, payload=None, paginate=False, method=None):
        hub = self.hub
        hub.calls.append((self.user, method or ('POST' if payload else 'GET'), endpoint))
        if endpoint == 'user':
            return {'login': USERS[self.user], 'id': self.user, 'type': 'User'}
        if endpoint.startswith(f'repos/{REPO}/issues/comments/'):
            cid = int(endpoint.rsplit('/', 1)[1])
            comment = next(c for cs in hub.store.values() for c in cs if c['id'] == cid)
            if method == 'PATCH':
                if hub.fail_patch:
                    raise RecordError('GitHub operation failed; publication is unconfirmed')
                comment.update(body=payload['body'], updated_at=stamp(utcnow()))
            return dict(comment)
        if payload is not None:
            pr = int(endpoint.split('/')[-2])
            if hub.on_post:
                hook, hub.on_post = hub.on_post, None
                hook()
            now = stamp(utcnow())
            comment = {'id': hub.next_id, 'body': payload['body'], 'created_at': now, 'updated_at': now,
                       'user': {'id': self.user, 'type': 'User', 'login': USERS[self.user]},
                       'issue_url': f'https://api.github.com/repos/{REPO}/issues/{pr}'}
            hub.next_id += 1
            hub.store.setdefault(pr, []).append(comment)
            if hub.after_post:
                hook, hub.after_post = hub.after_post, None
                hook()
            return dict(comment)
        raise AssertionError(endpoint)


def arguments(**updates):
    values = dict(post=True, no_post=False, dry_run=False, read_records=False, force_claim=False,
                  output=None, pr=1)
    values.update(updates)
    return Namespace(**values)


class FakeReview:
    """Stands in for run_review: the guard wraps provider work, as in the real adapter."""

    def __init__(self, client, *, fail=None, completion='complete', head=HEAD):
        self.client, self.fail, self.completion, self.head = client, fail, completion, head
        self.model_calls = 0

    def __call__(self, args, project, prefs, guard):
        report = {'repository': REPO, 'pr': args.pr, 'head': self.head, 'base': BASE}
        with guard(args, report, POLICY, self.client):
            self.model_calls += 1
            if self.fail:
                raise self.fail
            published = ({'state': 'confirmed', 'comment_id': 555} if args.post else None)
        return {**report, 'completion': self.completion, 'stop_reason': None,
                **({'publication': published} if published else {})}


def bodies(hub, pr=1):
    return [c['body'] for c in hub.store.get(pr, [])]


class ClaimTest(unittest.TestCase):
    def setUp(self):
        self.hub = FakeGitHub()
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-claims-')
        self.addCleanup(temp.cleanup)
        self.prefs = OperatorPreferences(budget_usd=5, storage=temp.name)

    def review(self, user=7, **kwargs):
        run = FakeReview(self.hub.client(user), **{k: v for k, v in kwargs.items() if k in ('fail', 'completion')})
        args = arguments(**{k: v for k, v in kwargs.items() if k not in ('fail', 'completion')})
        return run, run_claimed(args, PROJECT, self.prefs, run=run)

    def test_claim_is_posted_on_start_and_edited_to_finished(self):
        seen = []
        hub = self.hub

        class Watch(FakeReview):
            def __call__(inner, args, project, prefs, guard):
                report = {'repository': REPO, 'pr': 1, 'head': HEAD, 'base': BASE}
                with guard(args, report, POLICY, inner.client):
                    seen.extend(bodies(hub))
                return {**report, 'completion': 'complete', 'publication': {'state': 'confirmed', 'comment_id': 555}}
        result = run_claimed(arguments(provider="codex", codex_model="gpt-6.1-sol"), PROJECT, self.prefs, run=Watch(hub.client(7)))
        [started] = seen
        self.assertTrue(started.startswith(MARKER))
        self.assertIn('Selected model: codex/gpt-6.1-sol · Estimated usage cost: pending', started)
        data = json.loads(started[len(MARKER):started.index('-->')])
        self.assertEqual({k: data[k] for k in ('repository', 'pr', 'head', 'base', 'actor', 'state')},
                         {'repository': REPO, 'pr': 1, 'head': HEAD, 'base': BASE, 'actor': 'user:7',
                          'state': 'in_progress'})
        self.assertRegex(started, r'\nReviewing aaaaaaa now · `yvonne` '
                                  r'\(started \d\d:\d\d UTC, expires \d\d:\d\d UTC\)\n')
        self.assertNotIn('@yvonne', started)  # a code login, not a mention
        self.assertEqual((utcnow().fromisoformat(data['expires_at'].replace('Z', '+00:00')) -
                          utcnow().fromisoformat(data['started_at'].replace('Z', '+00:00'))).total_seconds(), 1800)
        [final] = bodies(hub)  # edited in place, never a second comment
        self.assertIn(f'finished: https://github.com/{REPO}/pull/1#issuecomment-555', final)
        self.assertIn('Estimated usage cost: unavailable', final)  # no receipts in this fixture
        self.assertEqual(result['claim']['state'], 'finished')
        self.assertEqual(note(result['claim']), f'Claim https://github.com/{REPO}/pull/1#issuecomment-100 marked finished.')

    def test_failure_interrupt_and_partial_runs_abandon_the_claim(self):
        for index, fail in enumerate((ReviewError('provider failed'), KeyboardInterrupt())):
            with self.subTest(fail=fail), self.assertRaises(type(fail)):
                self.review(pr=index + 1, fail=fail)
        self.assertIn('abandoned (review failed: provider failed)', bodies(self.hub, 1)[0])
        self.assertIn('abandoned (interrupted)', bodies(self.hub, 2)[0])
        _, result = self.review(pr=3, completion='partial')
        self.assertIn('abandoned (review partial; partial record https://', bodies(self.hub, 3)[0])
        self.assertEqual(result['claim']['state'], 'abandoned')

    def test_no_claim_without_posting(self):
        for updates in ({'post': False, 'no_post': True}, {'post': False, 'dry_run': True}):
            run, result = self.review(**updates)
            self.assertEqual(run.model_calls, 1)
            self.assertNotIn('claim', result)
        self.assertEqual(self.hub.calls, [])

    def test_two_simultaneous_claims_exactly_one_proceeds(self):
        # Both check before either claim is visible; A's comment lands first, then B posts and
        # confirms before A confirms. B sees A's earlier comment and yields; A proceeds.
        later = FakeReview(self.hub.client(9))
        outcome = {}

        def b_runs():
            self.hub.stale_reads = 1
            try:
                run_claimed(arguments(), PROJECT, self.prefs, run=later)
            except ClaimYielded as error:
                outcome['b'] = error
        self.hub.after_post = b_runs
        first, result = self.review()
        self.assertEqual((first.model_calls, later.model_calls), (1, 0))
        self.assertEqual(str(outcome['b']), 'PR #1: yielded to @yvonne, whose claim is earlier; nothing was spent')
        a, b = bodies(self.hub)
        self.assertIn('finished:', a)
        self.assertIn('Review of aaaaaaa by `alice` yielded to `yvonne`.', b)

    def test_earlier_foreign_claim_posted_during_ours_makes_us_yield(self):
        self.hub.on_post = lambda: self.hub.store.setdefault(1, []).append(claim_comment(50))
        with self.assertRaises(ClaimYielded):
            self.review()
        own = bodies(self.hub)[-1]
        self.assertIn('yielded to `alice`', own)

    def test_expired_old_head_forged_and_finished_claims_are_ignored(self):
        self.hub.store[1] = [claim_comment(10, age=timedelta(minutes=31)),          # expired
                             claim_comment(11, head='9' * 40),                         # old head
                             claim_comment(12, actor='user:11', login='bob'),         # author 9 != actor
                             claim_comment(13, state='finished'),                     # no longer live
                             claim_comment(14, ttl=TTL * 10)]                          # beyond one run
        run, result = self.review()
        self.assertEqual(run.model_calls, 1)
        self.assertEqual(result['claim']['state'], 'finished')
        self.assertEqual(live(self.hub.store[1], {'repository': REPO, 'pr': 1, 'head': HEAD}, utcnow()), [])

    def test_explicit_review_with_a_live_foreign_claim_is_refused_unless_forced(self):
        self.hub.store[1] = [claim_comment(10, age=timedelta(minutes=18))]
        with self.assertRaises(ClaimRefused) as refused:
            self.review()
        self.assertEqual(str(refused.exception), 'PR #1: review in progress by @alice, 12 min left; '
                                                 'rerun with --force-claim to review anyway')
        self.assertEqual(len(self.hub.store[1]), 1)
        run, result = self.review(force_claim=True)
        self.assertEqual(run.model_calls, 1)
        self.assertEqual(result['claim']['state'], 'finished')

    def test_own_live_claim_is_refreshed_in_place(self):
        self.hub.store[1] = [claim_comment(10, user=7, age=timedelta(minutes=20))]
        _, result = self.review()
        self.assertEqual(len(self.hub.store[1]), 1)
        self.assertEqual(result['claim']['comment_id'], 10)
        self.assertFalse(any(method == 'POST' for _, method, _ in self.hub.calls))

    def test_truncated_comments_fail_closed_before_any_write_or_spend(self):
        self.hub.truncated = True
        run = FakeReview(self.hub.client(7))
        with self.assertRaises(RecordError):
            run_claimed(arguments(), PROJECT, self.prefs, run=run)
        self.assertEqual(run.model_calls, 0)
        self.assertEqual(self.hub.store, {})
        with self.assertRaises(RecordError):
            live([{'id': 1}, {'id': 1}], {'repository': REPO, 'pr': 1, 'head': HEAD}, utcnow())

    def test_failed_finish_edit_is_reported(self):
        hub = self.hub

        class Run(FakeReview):
            def __call__(inner, args, project, prefs, guard):
                report = {'repository': REPO, 'pr': 1, 'head': HEAD, 'base': BASE}
                with guard(args, report, POLICY, inner.client):
                    hub.fail_patch = True
                return {**report, 'completion': 'complete', 'publication': {'state': 'confirmed', 'comment_id': 555}}
        result = run_claimed(arguments(), PROJECT, self.prefs, run=Run(hub.client(7)))
        self.assertEqual(result['claim']['edit'], 'failed')
        self.assertRegex(note(result['claim']), r'^Claim comment 100 could not be marked finished \(GitHub operation '
                                                r'failed; publication is unconfirmed\); it expires on its own at '
                                                r'\d\d:\d\d UTC\.$')
        self.assertIn('Reviewing aaaaaaa now', bodies(hub)[0])

    def test_a_budget_too_small_for_the_first_rubric_posts_no_claim(self):
        ledger = Path(self.prefs.storage) / REPO.replace('/', '__') / 'engine' / 'ledger.json'
        ledger.parent.mkdir(parents=True)
        ledger.write_text(json.dumps({'days': {utcnow().strftime('%Y-%m-%d'): 4.5}, 'prs': {}}))

        class BudgetStop(FakeReview):
            def __call__(inner, args, project, prefs, guard):
                report = {'repository': REPO, 'pr': 1, 'head': HEAD, 'base': BASE}
                with guard(args, report, POLICY, inner.client):
                    pass  # the engine stops before its first rubric: no provider call
                return {**report, 'completion': 'partial', 'stop_reason': 'daily_budget', 'finished_rubrics': [],
                        'requested_rubrics': list(RUBRICS), 'not_posted': 'daily review budget reached'}
        result = run_claimed(arguments(budget_usd=5.0, max_call_cost=1.0), PROJECT, self.prefs,
                             run=BudgetStop(self.hub.client(7)))
        self.assertEqual(self.hub.store, {})       # the PR stays silent
        self.assertEqual(self.hub.calls, [])       # not even the identity or comment reads
        self.assertNotIn('claim', result)
        self.assertEqual(result['stop_reason'], 'daily_budget')
        # Exactly the engine's rule: one more reservation within the budget still fits.
        self.assertIsNotNone(run_claimed(arguments(budget_usd=5.5, max_call_cost=1.0), PROJECT, self.prefs,
                                         run=FakeReview(self.hub.client(7)))['claim'])

    def test_a_mid_review_budget_stop_pauses_the_claim_with_counts(self):
        class MidStop(FakeReview):
            def __call__(inner, args, project, prefs, guard):
                report = {'repository': REPO, 'pr': 1, 'head': HEAD, 'base': BASE}
                with guard(args, report, POLICY, inner.client):
                    inner.model_calls += 4
                return {**report, 'completion': 'partial', 'stop_reason': 'daily_budget',
                        'finished_rubrics': list(RUBRICS[:4]), 'requested_rubrics': list(RUBRICS)}
        result = run_claimed(arguments(), PROJECT, self.prefs, run=MidStop(self.hub.client(7)))
        [body] = bodies(self.hub)
        self.assertIn('\nReview paused · 4 of 10 rubrics completed (daily budget reached)\n', body)
        self.assertEqual(result['claim']['state'], 'paused')
        data = json.loads(body[len(MARKER):body.index('-->')])
        self.assertEqual(data['state'], 'paused')
        self.assertIsNotNone(parse(self.hub.store[1][0], REPO, 1))  # the marker stays valid
        self.assertEqual(live(self.hub.store[1], {'repository': REPO, 'pr': 1, 'head': HEAD}, utcnow()), [])

    def test_markers_keep_claims_and_official_leases_apart(self):
        claim = claim_comment(10)
        lease = dict(claim, id=11, body=worker_leases.encode({'kind': 'acquire'}))
        self.assertIsNone(worker_leases.parse(claim, REPO, 1, {'user:9'}))
        self.assertIsNone(parse(lease, REPO, 1))
        context = {'repository': REPO, 'pr': 1, 'head': HEAD, 'tooling_approved': True,
                   'installed_tooling_matches_T': True, 'missing_context': [], 'config_differences': []}
        self.assertEqual(assess_records([claim], context, POLICY, lambda rev: True, 1)['selected_comments'], {})


class BareClaimTest(unittest.TestCase):
    def setUp(self):
        self.hub = FakeGitHub()

    def queue(self):
        return [gh_pr(1, author={'login': 'bob'}, updatedAt='2020-01-01T00:00:00Z'),
                gh_pr(2, author={'login': 'bob'}, updatedAt='2020-02-01T00:00:00Z')]

    def bare(self, client, run, **updates):
        args = arguments(pr=None, local_sources=False, shadow=None, replies_json=None, head=None, base=None,
                         description_file=None, reply_file=None, reply_rubric=None, mode='commit',
                         post_default=True, **updates)
        api = FakeAPI([{'login': 'yvonne'}, self.queue()])
        return run_bare(args, PROJECT, POLICY, OperatorPreferences(budget_usd=5, storage='/nonexistent'), api=api,
                        client=client, run=run)

    def test_bare_review_skips_a_live_foreign_claim_and_picks_the_next(self):
        self.hub.store[1] = [claim_comment(10, age=timedelta(minutes=18))]
        client = self.hub.client(7)
        selection = self.bare(client, FakeReview(client))
        self.assertEqual(selection['selected']['pr'], 2)
        self.assertIn({'pr': 1, 'head': HEAD, 'code': 'claimed',
                       'reason': 'review in progress by @alice, 12 min left', 'note': None}, selection['skipped'])

    def test_lost_race_moves_on_to_the_next_candidate(self):
        client = self.hub.client(7)
        self.hub.on_post = lambda: self.hub.store.setdefault(1, []).append(claim_comment(50))
        run = FakeReview(client)
        selection = self.bare(client, run)
        self.assertEqual(selection['selected']['pr'], 2)
        self.assertEqual(run.model_calls, 1)
        self.assertIn({'pr': 1, 'head': HEAD, 'code': 'claimed', 'reason': 'review in progress by @alice (yielded)'},
                      selection['skipped'])
        self.assertIn('yielded to `alice`', bodies(self.hub)[-1])

    def test_forced_bare_review_ignores_claims(self):
        self.hub.store[1] = [claim_comment(10)]
        client = self.hub.client(7)
        self.assertEqual(self.bare(client, FakeReview(client), force_claim=True)['selected']['pr'], 1)


class ClaimCliTest(BareReviewHarness):
    def seed_claim(self, number=47):
        comment = claim_comment(10, pr=number, head=self.fixture.head, age=timedelta(minutes=18))
        data = json.loads(comment['body'][len(MARKER):comment['body'].index('-->')])
        data['base'] = self.fixture.tooling
        comment['body'] = render(data)
        (self.fixture.bin / 'gh-comments.json').write_text(json.dumps({str(number): [comment]}))

    def test_default_codex_model_and_usage_cost_are_visible(self):
        self.enable_posting()
        self.fixture.codex_subscription()
        run = self.run_cli('--provider', 'codex', '--auth', 'subscription', pr=47)
        self.assertEqual(run.returncode, 0, run.stderr)
        [comment] = self.claims()
        # Each fake Codex rubric reports tokens priced at $0.058 for the default model.
        self.assertIn('Models used: codex/gpt-6.1-sol · Estimated usage cost: $0.58', comment['body'])

    def test_unknown_usage_never_displays_a_zero_cost(self):
        self.enable_posting()
        self.fixture.codex_subscription()
        (self.fixture.bin / 'codex-no-usage').touch()
        run = self.run_cli('--provider', 'codex', '--auth', 'subscription', pr=47)
        [comment] = self.claims()
        self.assertIn('codex/gpt-6.1-sol · Estimated usage cost: unavailable', comment['body'])
        self.assertNotIn('$0.00', comment['body'])

    def test_explicit_review_is_refused_then_forced(self):
        self.enable_posting()
        self.seed_claim()
        refused = self.run_cli(pr=47)
        self.assertEqual(refused.returncode, 2)
        # Progress lines (evidence preparation) precede the refusal on stderr.
        self.assertEqual(refused.stderr.strip().splitlines()[-1],
                         'sphereceti: PR #47: review in progress by @alice, 12 min left; '
                         'rerun with --force-claim to review anyway')
        self.assertFalse(self.fixture.calls())
        self.assertEqual(self.writes(), [])
        forced = self.run_cli('--force-claim', pr=47, output='forced')
        self.assertEqual(forced.returncode, 0, forced.stderr)
        self.assertEqual(len(self.fixture.calls()), 10)
        self.assertIn('finished: https://github.com/', self.claims()[-1]['body'])
        self.assertIn(f"Claim https://github.com/{REPO}/pull/47#issuecomment-{self.claims()[-1]['id']} "
                      'marked finished.', forced.stdout.splitlines())

    def test_bare_review_skips_the_claimed_pr_and_no_claim_on_dry_run(self):
        self.enable_posting()
        self.seed_claim()
        result = json.loads(self.run_cli('--dry-run', '--json').stdout)
        self.assertEqual(result['selected']['pr'], 50)
        self.assertIn({'pr': 47, 'head': self.fixture.head, 'code': 'claimed',
                       'reason': 'review in progress by @alice, 12 min left', 'note': None}, result['skipped'])
        self.assertEqual(self.writes(), [])
        no_post = self.run_cli('--no-post', output='local')
        self.assertEqual(no_post.returncode, 0, no_post.stderr)
        self.assertEqual(self.writes(), [])
        self.assertEqual(len(self.claims(50)), 0)


if __name__ == '__main__':
    unittest.main()


class BatchClaimTest(unittest.TestCase):
    """Batch items go through run_claimed exactly as bare review does."""

    def test_a_claimed_pr_is_skipped_and_the_next_item_posts_its_own_claim(self):
        from test_review_queue import SurveyAPI, pr as queue_pr
        from sphereceti.local_review import RUBRICS
        from sphereceti.review_queue import run_batch
        hub = FakeGitHub()
        client = hub.client(7)
        api = SurveyAPI([queue_pr(2, ago=timedelta(hours=3)), queue_pr(3)], actor='yvonne')
        runs = []

        def run(args, project, prefs, guard):
            report = {'repository': REPO, 'pr': args.pr, 'head': HEAD, 'base': BASE, 'output': f'/runs/r{args.pr}'}
            if args.pr == 2:  # another contributor claims #2 after the survey, before this review starts
                hub.store[2] = [claim_comment(10, pr=2, age=timedelta(minutes=18))]
            with guard(args, report, POLICY, client):
                runs.append(args.pr)
            return {**report, 'completion': 'complete', 'requested_rubrics': list(RUBRICS), 'stop_reason': None,
                    'verdicts': {r: 'approve' for r in RUBRICS}, 'engine_exit_code': 0,
                    'publication': {'state': 'confirmed', 'comment_id': 900, 'authorized': False}}
        args = Namespace(new=True, revised=False, all=False, limit=2, dry_run=False, post=True, no_post=False,
                         post_default=True, output=None, budget_usd=None, max_call_cost=1.0, provider=None,
                         codex_model=None, claude_model=None, kiro_model=None, local_sources=False,
                         read_records=False, shadow=None, replies_json=None, head=None, base=None,
                         description_file=None, reply_file=None, reply_rubric=None, mode='commit', pr=None,
                         force_claim=False)
        result = run_batch(args, PROJECT, POLICY, OperatorPreferences(budget_usd=5, storage='/nonexistent'), api=api,
                           client=client, run=run)
        self.assertEqual(runs, [3])
        self.assertEqual(result['skipped'][0]['pr'], 2)
        self.assertTrue(result['skipped'][0]['reason'].startswith('review in progress by @alice'))
        [claim] = [c for c in hub.store[3] if c['body'].startswith(MARKER)]
        self.assertIn('finished: https://github.com/', claim['body'])
