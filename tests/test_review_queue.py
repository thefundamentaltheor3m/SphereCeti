# SPDX-License-Identifier: Apache-2.0
"""`sphereceti reviews` and bounded `review --new/--revised/--all --limit N` batches, offline."""
from argparse import Namespace
from datetime import datetime, timedelta, timezone
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences, parse_policy
from sphereceti.local_review import RUBRICS, ReviewError
from sphereceti.review_queue import BATCH_SCHEMA, SCHEMA, queue, render, run_batch, section_items
from sphereceti.review_records import CONTEST, RecordError, make_record
from sphereceti.worker import WorkerError
from review_fixture import ROOT, ReviewFixture, automation_policy
from test_review_select import FAKE_GH
from test_worker import PROJECT, gh_pr

REPO = PROJECT.repository
POLICY = parse_policy(automation_policy(authorized_reviewers=['user:2009342']))
ME = 'yvonne'
OLD, HEAD, BASE = 'c' * 40, 'a' * 40, 'b' * 40


def stamp(ago=timedelta(0)):
    return (datetime.now(timezone.utc) - ago).strftime('%Y-%m-%dT%H:%M:%SZ')


def record(cid, pr, head=HEAD, verdicts=None, login=ME, completion='complete'):
    result = {'repository': REPO, 'pr': pr, 'head': head, 'base': BASE, 'diff_base': BASE,
              'tooling': 'd' * 40, 'completion': completion, 'execution_mode': 'commit',
              'tooling_approved': True, 'installed_tooling_matches_T': False, 'missing_context': [],
              'config_differences': [], 'verdicts': {r: 'approve' for r in RUBRICS} | (verdicts or {}),
              'reviews': {}, **{k: 'e' * 64 for k in ('dependency_digest', 'engine_digest',
                                                      'effective_rubrics_digest', 'installed_tooling_digest',
                                                      'policy_digest', 'review_context_digest',
                                                      'description_digest')}}
    _, rendered = make_record(result)
    return comment(cid, pr, rendered, login)


def comment(cid, pr, body, login, user_id=7):
    return {'id': cid, 'body': body, 'user': {'id': user_id, 'type': 'User', 'login': login},
            'issue_url': f'https://api.github.com/repos/{REPO}/issues/{pr}',
            'created_at': '2026-11-20T10:00:00Z', 'updated_at': '2026-11-20T10:00:00Z'}


class SurveyAPI:
    """gh reads by argument, so every survey sees the queue as it is now."""

    def __init__(self, prs, actor=ME):
        self.prs, self.actor, self.surveys, self.fail_after = prs, actor, 0, None

    def read(self, args):
        if args[-1] == 'user':
            return {'login': self.actor}
        if args[:2] == ['pr', 'list']:
            self.surveys += 1
            if self.fail_after is not None and self.surveys > self.fail_after:
                raise WorkerError('GitHub survey failed; queue is unknown (no fallback)')
            return list(self.prs)
        raise AssertionError(args)


class Client:
    def __init__(self, comments=None, compare=None):
        self.records, self.compare, self.calls = comments or {}, compare or {}, []

    def comments(self, repository, pr):
        return self.records.get(pr, [])

    def call(self, endpoint, **kwargs):
        self.calls.append(endpoint)
        assert not kwargs.get('payload'), 'the queue never writes'
        if '/compare/' in endpoint:
            value = self.compare.get(endpoint.rsplit('/', 1)[1])
            if value is None:
                raise RecordError('GitHub operation failed')
            return value
        raise RecordError('unexpected read')


def pr(number, author='bob', head=HEAD, ago=timedelta(hours=1), **updates):
    return gh_pr(number, author={'login': author}, headRefOid=head, baseRefOid=BASE, updatedAt=stamp(ago),
                 **updates)


FAILED = [{'__typename': 'CheckRun', 'status': 'COMPLETED', 'conclusion': 'FAILURE'}]


class QueueTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-queue-')
        self.addCleanup(temp.cleanup)
        self.prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=temp.name)

    def classify(self, prs, comments=None, compare=None):
        return queue(PROJECT, POLICY, self.prefs, api=SurveyAPI(prs), client=Client(comments, compare))

    def test_sections_revised_with_author_reply_new_waiting_and_not_ready(self):
        prs = [pr(1, ME), pr(2, ago=timedelta(hours=2)), pr(3, ago=timedelta(hours=1)),
               pr(4, 'carol', statusCheckRollup=FAILED), pr(5, isDraft=True), pr(6, statusCheckRollup=FAILED),
               pr(7), pr(8, mergeable='UNKNOWN')]
        comments = {
            3: [record(10, 3, head=OLD), comment(11, 3, 'Fixed the naming, thanks.', 'bob'),
                comment(12, 3, CONTEST + '{"comment":10}-->\nplease reconsider', 'bob')],
            4: [record(20, 4, verdicts={'attribution': 'request_changes', 'naming': 'block'})],
            7: [record(30, 7)],
        }
        report = self.classify(prs, comments, {f'{OLD}...{HEAD}': {'status': 'ahead', 'ahead_by': 2}})
        sections = report['sections']
        self.assertEqual([e['pr'] for e in sections['revised']], [3])
        self.assertEqual(sections['revised'][0]['reason'],
                         'revised ccccccc → aaaaaaa, 2 commits; author replied 1×; 1 contest')
        self.assertEqual((sections['revised'][0]['previous_head'], sections['revised'][0]['commits_since'],
                          sections['revised'][0]['author_replies'], sections['revised'][0]['contests']),
                         (OLD, 2, 1, 1))
        self.assertEqual([e['pr'] for e in sections['new']], [2])
        self.assertEqual(sections['new'][0]['reason'], 'ready; no review by you')
        self.assertEqual([e['pr'] for e in sections['waiting_on_author']], [4])
        self.assertEqual(sections['waiting_on_author'][0]['reason'],
                         'you blocked (attribution, naming); no new head')
        self.assertEqual(sections['waiting_on_author'][0]['rubrics'], ['attribution', 'naming'])
        self.assertEqual({i['pr']: i['code'] for i in sections['not_ready']},
                         {1: 'yours', 5: 'draft', 6: 'not_ready', 8: 'awaiting_github'})
        self.assertEqual(report['done'], [{'pr': 7, 'head': HEAD, 'code': 'reviewed_by_you',
                                           'reason': 'you already published a complete review of this head'}])
        self.assertEqual(report['not_ready_summary'],
                         "No PR is ready with current evidence: 1 open PR awaits GitHub's mergeability check; "
                         '1 is yours; #6 is not ready (CI failed); #5 is a draft.')

    def test_an_author_reply_on_the_unchanged_head_lands_in_author_replied(self):
        findings = {'scope': 'request_changes'}
        prs = [pr(69, 'carol'), pr(70, 'carol')]
        reply = comment(41, 69, 'The scope is intended: see the roadmap entry.', 'carol')
        reply['html_url'] = f'https://github.com/{REPO}/pull/69#issuecomment-41'
        comments = {69: [record(40, 69, verdicts=findings), reply],
                    70: [record(50, 70, verdicts=findings), comment(51, 70, 'Thanks!', 'zed')]}
        report = self.classify(prs, comments)
        [replied] = report['sections']['author_replied']
        self.assertEqual(replied['pr'], 69)
        self.assertEqual(replied['reason'], f'you requested changes (scope); author replied 1×: '
                                            f'https://github.com/{REPO}/pull/69#issuecomment-41')
        self.assertEqual(replied['reply_url'], f'https://github.com/{REPO}/pull/69#issuecomment-41')
        # Neither a revision nor a response from the author: still waiting on the author.
        self.assertEqual([e['pr'] for e in report['sections']['waiting_on_author']], [70])
        # Follow-ups come first: revised, then author replied, then new.
        both = self.classify([pr(2, ago=timedelta(days=9)), pr(3), pr(69, 'carol')],
                             {3: [record(10, 3, head=OLD)], 69: comments[69]},
                             {f'{OLD}...{HEAD}': {'status': 'ahead', 'ahead_by': 1}})
        self.assertEqual([(e['pr'], e['section']) for e in section_items(both, 'all')],
                         [(3, 'revised'), (69, 'author_replied'), (2, 'new')])
        self.assertEqual([e['pr'] for e in section_items(both, 'revised')], [3, 69])

    def test_a_revised_pr_awaiting_ci_is_shown_as_your_follow_up(self):
        # #69's live shape: reviewed at 99e8687, the author replied and pushed; CI is pending.
        pending = [{'__typename': 'CheckRun', 'status': 'IN_PROGRESS', 'conclusion': None}]
        comments = {69: [record(40, 69, head=OLD, verdicts={'scope': 'request_changes'}),
                         comment(41, 69, 'All three findings are addressed.', 'carol')]}
        report = self.classify([pr(69, 'carol', statusCheckRollup=pending)], comments)
        self.assertEqual(report['sections']['not_ready'][0]['code'], 'awaiting_ci')
        self.assertEqual(report['follow_ups_not_ready'], [{
            'pr': 69, 'head': HEAD, 'reason': 'awaits CI (pending); revised ccccccc → aaaaaaa; author replied 1×'}])
        self.assertIn('Your follow-ups, not ready yet: #69 awaits CI (pending); revised ccccccc → aaaaaaa; '
                      'author replied 1×', render(report))

    def test_revised_ranks_first_and_rewritten_history_is_reported(self):
        prs = [pr(2, ago=timedelta(days=3)), pr(3, ago=timedelta(minutes=5))]
        report = self.classify(prs, {3: [record(10, 3, head=OLD)]})   # compare 404: force-pushed
        self.assertEqual([e['pr'] for e in section_items(report, 'all')], [3, 2])
        revised = report['sections']['revised'][0]
        self.assertIsNone(revised['commits_since'])
        self.assertEqual(revised['reason'], 'revised ccccccc → aaaaaaa; the reviewed head is no longer in the '
                                            'history (force-pushed)')

    def test_other_reviewers_and_edited_records_do_not_make_a_pr_yours_to_follow_up(self):
        edited = record(10, 3, head=OLD)
        edited['updated_at'] = '2026-11-21T00:00:00Z'
        report = self.classify([pr(3)], {3: [edited, record(11, 3, head=OLD, login='zed')]})
        self.assertEqual([e['pr'] for e in report['sections']['new']], [3])
        self.assertEqual(report['sections']['revised'], [])

    def test_render_and_json_shape(self):
        report = self.classify([pr(2, title='A' * 80)])
        self.assertEqual(set(report), {'schema', 'repository', 'actor', 'observed_at', 'order', 'sections',
                                       'done', 'follow_ups_not_ready', 'main', 'not_ready_summary'})
        self.assertEqual(report['schema'], SCHEMA)
        self.assertEqual(set(report['sections']), {'revised', 'author_replied', 'new', 'waiting_on_author',
                                                   'not_ready'})
        self.assertEqual(set(report['sections']['new'][0]), {'section', 'pr', 'author', 'title', 'head', 'base',
                                                             'updated_at', 'waiting_seconds', 'reason', 'note'})
        text = render(report)
        self.assertIn('Revised since your review (0): none', text)
        self.assertIn(f'  #2 bob "{"A" * 57}..." aaaaaaa: ready; no review by you; waiting 1h', text)

    def test_lookup_failures_raise_instead_of_guessing(self):
        api = SurveyAPI([pr(2)])
        api.fail_after = 0
        with self.assertRaises(WorkerError):
            queue(PROJECT, POLICY, self.prefs, api=api, client=Client())

        class Broken(Client):
            def comments(self, repository, pr):
                return None
        with self.assertRaises(RecordError):
            queue(PROJECT, POLICY, self.prefs, api=SurveyAPI([pr(2)]), client=Broken())


class FakeRun:
    """run_review's shape: evidence for the live head, the guard, then a result."""

    def __init__(self, api, fail=None, moved=None):
        self.api, self.fail, self.moved, self.calls = api, fail or {}, moved or {}, []

    def __call__(self, args, project, prefs, guard):
        live = next(p for p in self.api.prs if p['number'] == args.pr)
        head = self.moved.get(args.pr, live['headRefOid'])
        report = {'repository': REPO, 'pr': args.pr, 'head': head, 'base': BASE, 'output': f'/runs/run-{args.pr}'}
        with guard(args, report, POLICY, None):
            self.calls.append(args.pr)
        verdicts = {r: 'approve' for r in RUBRICS}
        result = {**report, 'completion': 'complete', 'requested_rubrics': list(RUBRICS), 'verdicts': verdicts,
                  'stop_reason': None, 'engine_exit_code': 0}
        result.update(self.fail.get(args.pr, {}))
        return result


class BatchTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-batch-')
        self.addCleanup(temp.cleanup)
        self.storage = Path(temp.name)
        self.prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=temp.name)
        self.lines = []

    def batch(self, api, run, client=None, **flags):
        values = dict(new=False, revised=False, all=False, limit=None, dry_run=False, post=False, no_post=True,
                      post_default=True, output=None, budget_usd=None, max_call_cost=1.0, provider=None,
                      codex_model=None, claude_model=None, kiro_model=None, local_sources=False,
                      read_records=False, shadow=None, replies_json=None, head=None, base=None,
                      description_file=None, reply_file=None, reply_rubric=None, mode='commit', pr=None)
        values.update(flags)
        return run_batch(Namespace(**values), PROJECT, POLICY, self.prefs, api=api, client=client or Client(),
                         announce=self.lines.append, run=run)

    def test_limit_is_respected_and_each_item_re_surveys(self):
        api = SurveyAPI([pr(2, ago=timedelta(hours=3)), pr(3, ago=timedelta(hours=2)), pr(4)])
        run = FakeRun(api)
        result = self.batch(api, run, new=True, limit=2)
        self.assertEqual(run.calls, [2, 3])
        self.assertEqual(api.surveys, 2)
        self.assertEqual((result['reviewed'], result['stopped']), (2, 'limit of 2 reached'))
        self.assertEqual(self.lines[0], '[1/2] #2 bob aaaaaaa: ready; no review by you')
        self.assertTrue(any(line.startswith('Review #2: head aaaaaaa') for line in self.lines))
        self.assertTrue(any(line.startswith('10/10 approve') for line in self.lines))
        self.assertEqual(result['line'], 'Batch (new): 2 reviewed, 0 posted, 0 skipped; stopped: limit of 2 reached.')

    def test_a_limit_of_five_gives_five_distinct_prs(self):
        api = SurveyAPI([pr(n, ago=timedelta(hours=10 - n)) for n in range(2, 8)])
        run = FakeRun(api)
        result = self.batch(api, run, new=True, limit=5)
        self.assertEqual(run.calls, [2, 3, 4, 5, 6])
        self.assertEqual(len(set(run.calls)), 5)
        self.assertEqual(result['lines'], [f'  #{n}: approved' for n in (2, 3, 4, 5, 6)])

    def test_a_head_moving_mid_run_is_reported_and_not_re_reviewed(self):
        api = SurveyAPI([pr(2, ago=timedelta(hours=3)), pr(3)])

        class Moving(FakeRun):
            def __call__(inner, args, project, prefs, guard):
                FakeRun.__call__(inner, args, project, prefs, guard)
                if args.pr == 2:  # a push lands while #2 is being reviewed; the publish check sees it
                    api.prs[0] = pr(2, head='9' * 40, ago=timedelta(hours=3))
                    raise ReviewError('review evidence or posting policy changed; rerun before posting')
                return FakeRun.__call__(inner, args, project, prefs, guard)
        run = Moving(api)
        result = self.batch(api, run, new=True, limit=5)
        self.assertEqual(sorted(set(run.calls)), [2, 3])
        self.assertEqual(run.calls.count(2), 1)  # the new revision waits for a later invocation
        self.assertEqual(result['lines'][0], '  #2: head moved during the review; new revision left for a later run')
        self.assertEqual(result['stopped'], 'no more PRs in this section')

    def test_a_block_or_requested_changes_continues_the_batch(self):
        api = SurveyAPI([pr(2, ago=timedelta(hours=3)), pr(3, ago=timedelta(hours=2)), pr(4)])
        blocked = {r: 'absent' for r in RUBRICS} | {RUBRICS[0]: 'approve', 'reuse': 'block'}
        run = FakeRun(api, fail={2: {'completion': 'partial', 'verdicts': blocked},
                                 3: {'verdicts': {r: 'approve' for r in RUBRICS} | {'naming': 'request_changes'}}})
        result = self.batch(api, run, new=True, limit=3)
        self.assertEqual(run.calls, [2, 3, 4])
        self.assertEqual(result['lines'], ['  #2: blocked (reuse)', '  #3: changes (naming)', '  #4: approved'])
        self.assertEqual(result['stopped'], 'limit of 3 reached')

    def test_requested_changes_then_later_approvals_are_reported_in_full_and_the_batch_continues(self):
        # The engine ends a round, not the batch runner: here correctness requested changes and the
        # nine later rubrics still ran and approved. The whole round is reported; the next PR starts.
        api = SurveyAPI([pr(2, ago=timedelta(hours=3)), pr(3)])
        mixed = {r: 'approve' for r in RUBRICS} | {'correctness': 'request_changes'}
        run = FakeRun(api, fail={2: {'verdicts': mixed}})
        result = self.batch(api, run, new=True, limit=2)
        self.assertEqual(run.calls, [2, 3])
        first = result['items'][0]
        self.assertEqual(first['outcome'], 'changes (correctness)')
        self.assertEqual((first['summary']['reviewed'], first['summary']['total'], first['summary']['stop']),
                         (10, 10, None))
        self.assertTrue(first['summary']['line'].startswith('10/10 reviewed · changes requested: correctness'))
        self.assertEqual(result['stopped'], 'limit of 2 reached')

    def test_each_execution_failure_stops_the_batch_and_names_the_untouched(self):
        partial = {r: 'absent' for r in RUBRICS} | {RUBRICS[0]: 'approve'}
        failures = {
            'unknown usage': ({'completion': 'partial', 'stop_reason': 'usage_unknown', 'verdicts': partial},
                              '#2: usage unknown'),
            'budget exhausted': ({'completion': 'partial', 'verdicts': partial}, '#2: budget exhausted'),
            'provider failure': ({'completion': 'error', 'engine_exit_code': 3,
                                  'verdicts': {r: 'absent' for r in RUBRICS}}, 'provider failure on #2'),
        }
        for name, (failure, stop) in failures.items():
            with self.subTest(name):
                api = SurveyAPI([pr(n, ago=timedelta(hours=10 - n)) for n in (2, 3, 4)])
                run = FakeRun(api, fail={2: failure})
                result = self.batch(api, run, new=True, limit=3)
                self.assertEqual(run.calls, [2])
                self.assertTrue(result['stopped'].startswith(stop), result['stopped'])
                self.assertEqual(result['untouched'], [3, 4])
                self.assertEqual(result['lines'][-2:], ['  #3: untouched', '  #4: untouched'])
        api = SurveyAPI([pr(n, ago=timedelta(hours=10 - n)) for n in (2, 3, 4)])

        class Unconfirmed(FakeRun):
            def __call__(inner, args, project, prefs, guard):
                FakeRun.__call__(inner, args, project, prefs, guard)
                raise RecordError('GitHub operation failed; publication is unconfirmed')
        run = Unconfirmed(api)
        result = self.batch(api, run, new=True, limit=3)
        self.assertEqual(run.calls, [2])
        self.assertTrue(result['stopped'].startswith('#2: publication unconfirmed'))
        self.assertEqual((result['untouched'], result['items'][0]['outcome']), ([3, 4], 'publication unconfirmed'))

    def test_default_limit_is_one_and_the_cap_is_ten(self):
        api = SurveyAPI([pr(2), pr(3)])
        run = FakeRun(api)
        self.assertEqual(self.batch(api, run, new=True)['reviewed'], 1)
        with self.assertRaises(ReviewError):
            self.batch(api, run, new=True, limit=11)

    def test_provider_failure_stops_with_no_further_calls(self):
        api = SurveyAPI([pr(2, ago=timedelta(hours=3)), pr(3)])
        run = FakeRun(api, fail={2: {'completion': 'error', 'engine_exit_code': 3,
                                     'verdicts': {r: 'absent' for r in RUBRICS}}})
        result = self.batch(api, run, new=True, limit=5)
        self.assertEqual(run.calls, [2])
        self.assertTrue(result['stopped'].startswith('provider failure on #2'))
        self.assertTrue(result['failed'])
        usage = FakeRun(api, fail={2: {'stop_reason': 'usage_unknown', 'completion': 'partial'}})
        self.assertEqual(self.batch(api, usage, new=True, limit=5)['stopped'], '#2: usage unknown')
        self.assertEqual(usage.calls, [2])

    def test_a_pr_that_moved_or_became_ineligible_is_skipped(self):
        api = SurveyAPI([pr(2, ago=timedelta(hours=3)), pr(3, ago=timedelta(hours=2)), pr(4)])
        class Shrinking(FakeRun):
            def __call__(inner, args, project, prefs, guard):
                result = FakeRun.__call__(inner, args, project, prefs, guard)
                api.prs[2] = pr(4, isDraft=True)  # #4 turns into a draft mid-batch
                return result
        result = self.batch(api, Shrinking(api, moved={2: '9' * 40}), new=True, limit=3)
        self.assertEqual(result['skipped'], [{'pr': 2, 'head': HEAD, 'reason': 'moved before review'},
                                             {'pr': 4, 'head': None, 'reason': 'is a draft'}])
        self.assertEqual([i['pr'] for i in result['items']], [3])
        self.assertEqual(result['stopped'], 'no more PRs in this section')

    def test_revised_first_with_all_and_revised_only(self):
        api = SurveyAPI([pr(2, ago=timedelta(days=2)), pr(3)])
        client = Client({3: [record(10, 3, head=OLD)]}, {f'{OLD}...{HEAD}': {'status': 'ahead', 'ahead_by': 1}})
        run = FakeRun(api)
        result = self.batch(api, run, client=client, all=True, limit=2)
        self.assertEqual(run.calls, [3, 2])
        self.assertEqual([i['section'] for i in result['items']], ['revised', 'new'])
        run = FakeRun(api)
        self.assertEqual(self.batch(api, run, client=client, revised=True, limit=5)['reviewed'], 1)
        self.assertEqual(run.calls, [3])

    def test_lookup_failure_and_budget_stop_before_any_spend(self):
        api = SurveyAPI([pr(2, ago=timedelta(hours=3)), pr(3)])
        api.fail_after = 1
        run = FakeRun(api)
        result = self.batch(api, run, new=True, limit=3)
        self.assertEqual(run.calls, [2])
        self.assertTrue(result['lookup_failed'])
        self.assertTrue(result['stopped'].startswith('GitHub lookup failed'))
        ledger = self.storage / REPO.replace('/', '__') / 'engine' / 'ledger.json'
        ledger.parent.mkdir(parents=True)
        ledger.write_text(json.dumps({'days': {datetime.now(timezone.utc).strftime('%Y-%m-%d'): 4.5}, 'prs': {}}))
        api = SurveyAPI([pr(2)])
        run = FakeRun(api)
        result = self.batch(api, run, new=True, limit=3)
        self.assertEqual((result['stopped'], result['untouched']), ('daily budget exhausted', [2]))
        self.assertEqual(run.calls, [])

    def test_batch_json_shape(self):
        api = SurveyAPI([pr(2)])
        result = self.batch(api, FakeRun(api), new=True, limit=1)
        self.assertEqual(set(result), {'schema', 'section', 'limit', 'repository', 'items', 'skipped', 'untouched',
                                       'reviewed', 'posted', 'stopped', 'line', 'lines', 'lookup_failed', 'failed'})
        self.assertEqual(result['schema'], BATCH_SCHEMA)
        self.assertEqual(set(result['items'][0]), {'pr', 'head', 'section', 'outcome', 'output', 'completion',
                                                   'posting', 'posted', 'plan', 'summary'})
        self.assertEqual(result['lines'], ['  #2: approved'])


class QueueCliTest(unittest.TestCase):
    """The real CLI with a fake gh: `reviews --json`, a failed lookup, and flag validation."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-queue-cli-')
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.fixture = ReviewFixture(self.root)
        gh = self.fixture.bin / 'gh'
        gh.write_text(f'#!{sys.executable}\n' + FAKE_GH)
        gh.chmod(0o755)
        item = dict(number=47, title='Change 47', author={'login': 'bob'}, headRefOid=self.fixture.head,
                    baseRefOid=self.fixture.tooling, updatedAt='2026-01-01T00:00:00Z', state='OPEN',
                    isDraft=False, mergeable='MERGEABLE',
                    statusCheckRollup=[{'__typename': 'CheckRun', 'status': 'COMPLETED', 'conclusion': 'SUCCESS'}],
                    headRepository={'nameWithOwner': REPO})
        self.table = {'user': {'login': ME}, 'pr list': [item], 'poster_id': 7, 'accept_posts': False}
        (self.fixture.bin / 'gh.json').write_text(json.dumps(self.table))

    def run_cli(self, *args):
        launcher = [sys.executable, '-c', f'import sys; sys.path.insert(0, {str(ROOT / "tools/project")!r}); '
                    'from sphereceti.cli import main; sys.exit(main())']
        return subprocess.run([*launcher, *args, '--operator-config', str(self.fixture.operator)],
                              cwd=self.fixture.foreign, env=self.fixture.env, capture_output=True, text=True,
                              timeout=120)

    def test_reviews_json_and_a_failed_lookup_exits_two(self):
        process = self.run_cli('reviews', '--json')
        self.assertEqual(process.returncode, 0, process.stderr)
        report = json.loads(process.stdout)
        self.assertEqual((report['schema'], report['actor']), (SCHEMA, ME))
        self.assertEqual([e['pr'] for e in report['sections']['new']], [47])
        text = self.run_cli('reviews')
        self.assertIn('New to you (1):', text.stdout)
        del self.table['pr list']
        (self.fixture.bin / 'gh.json').write_text(json.dumps(self.table))
        failed = self.run_cli('reviews')
        self.assertEqual(failed.returncode, 2)
        self.assertIn('queue is unknown', failed.stderr)
        self.assertEqual(failed.stdout, '')

    def test_batch_flags_are_validated(self):
        for args in (('review', '47', '--new'), ('review', '--limit', '2')):
            with self.subTest(args=args):
                process = self.run_cli(*args)
                self.assertEqual(process.returncode, 2)
                self.assertIn('--limit needs one of them', process.stderr)
        both = self.run_cli('review', '--new', '--revised')
        self.assertEqual(both.returncode, 2)
        self.assertIn('not allowed with argument', both.stderr)


if __name__ == '__main__':
    unittest.main()
