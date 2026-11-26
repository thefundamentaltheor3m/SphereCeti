# SPDX-License-Identifier: Apache-2.0
"""An opted-in maintainer's all-green review submits one formal APPROVE, and only then."""
from dataclasses import replace
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import ConfigError, OperatorPreferences, parse_policy, parse_project, resource_text
from sphereceti.local_review import RUBRICS
from sphereceti.review_approval import ANNOUNCE, Approval, note
from sphereceti.review_claims import run_claimed
from sphereceti.review_records import RecordError, make_record
from sphereceti.worker_leases import stamp, utcnow
from review_fixture import automation_policy
from test_review_claims import Client, FakeGitHub, arguments

PROJECT = parse_project(resource_text('sphereceti.toml'))
REPO = PROJECT.repository
HEAD, BASE, TOOLING = 'a' * 40, 'b' * 40, 'c' * 40
ME, AUTHOR = 7, 11
SEVEN = (2009342, 56166236, 64404030, 29959226, 49933279, 117926300, 6530144)  # shipped approvers
POLICY = parse_policy(automation_policy(posting=True, authorized_reviewers=[f'user:{ME}', 'user:9']))
APPROVING = replace(POLICY, approving=True, approving_reviewers=(f'user:{ME}',))
DIGESTS = ('dependency_digest', 'engine_digest', 'effective_rubrics_digest', 'installed_tooling_digest',
           'policy_digest', 'review_context_digest', 'description_digest')


class ApprovalHub(FakeGitHub):
    def __init__(self):
        super().__init__()
        self.author, self.head = AUTHOR, HEAD
        self.reviews, self.fail_review_post, self.events = [], False, []

    def client(self, user):
        return ApprovalClient(self, user)


class ApprovalClient(Client):
    def comments(self, repository, pr):
        self.hub.events.append('comments')
        return super().comments(repository, pr)

    def approved_revision(self, repository, revision, current):
        return revision == current

    def call(self, endpoint, *, payload=None, paginate=False, method=None):
        hub = self.hub
        if endpoint == f'repos/{REPO}/pulls/1':
            hub.calls.append((self.user, 'GET', endpoint))
            return {'number': 1, 'user': {'id': hub.author}, 'head': {'sha': hub.head}, 'base': {'sha': BASE}}
        if endpoint == f'repos/{REPO}/pulls/1/reviews?per_page=100':
            hub.calls.append((self.user, 'GET', endpoint))
            assert paginate
            return [list(hub.reviews)]
        if endpoint == f'repos/{REPO}/pulls/1/reviews':
            hub.calls.append((self.user, 'POST', endpoint, payload))
            hub.events.append('approve')
            if hub.fail_review_post:
                raise RecordError('GitHub operation failed; publication is unconfirmed')
            review = {'id': 900 + len(hub.reviews), 'user': {'id': self.user}, 'state': payload['event'] + 'D',
                      'commit_id': payload['commit_id'], 'body': payload['body'],
                      'html_url': f'https://github.com/{REPO}/pull/1#pullrequestreview-{900 + len(hub.reviews)}'}
            hub.reviews.append(review)
            return review
        return super().call(endpoint, payload=payload, paginate=paginate, method=method)


def report():
    return {'repository': REPO, 'pr': 1, 'head': HEAD, 'base': BASE, 'diff_base': BASE, 'tooling': TOOLING,
            'tooling_approved': True, 'installed_tooling_matches_T': True, 'missing_context': [],
            'config_differences': [], **{k: 'e' * 64 for k in DIGESTS}}


class FakeReview:
    """run_review's shape: guard around provider work, then the record is posted and confirmed."""

    def __init__(self, hub, policy, *, verdict='approve', publish=True, tamper=False):
        self.hub, self.policy, self.verdict, self.publish, self.tamper = hub, policy, verdict, publish, tamper
        self.client = hub.client(ME)

    def __call__(self, args, project, prefs, guard):
        base = report()
        with guard(args, base, self.policy, self.client):
            self.hub.events.append('model')
        result = {**base, 'completion': 'complete', 'execution_mode': 'commit', 'stop_reason': None,
                  'verdicts': {r: 'approve' for r in RUBRICS} | ({'naming': self.verdict}), 'reviews': {}}
        if args.post and self.publish:
            _, rendered = make_record(result)
            now = stamp(utcnow())
            comment = {'id': self.hub.next_id, 'body': rendered, 'created_at': now,
                       'updated_at': stamp(utcnow()) if not self.tamper else '2000-01-01T00:00:00Z',
                       'user': {'id': ME, 'type': 'User', 'login': 'yvonne'},
                       'issue_url': f'https://api.github.com/repos/{REPO}/issues/1'}
            self.hub.next_id += 1
            self.hub.store.setdefault(1, []).append(comment)
            result['publication'] = {'state': 'confirmed', 'comment_id': comment['id'], 'identity': f'user:{ME}',
                                     'authorized': True}
        return result


def would_approve(**updates):
    calls = []

    def decide(args, project):
        calls.append(args.pr)
        return {'would_approve': True, 'hypothetical': False, 'head': HEAD, 'base': BASE, 'reasons': [], **updates}
    decide.calls = calls
    return decide


class ApprovalTest(unittest.TestCase):
    def setUp(self):
        self.hub = ApprovalHub()
        self.lines = []
        import tempfile
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-approval-')
        self.addCleanup(temp.cleanup)
        self.storage = temp.name

    def tearDown(self):
        # The CLI never merges: no merge endpoint is ever called, in any scenario.
        self.assertFalse([c for c in self.hub.calls if 'merge' in c[2]])

    def review(self, policy=APPROVING, decide=None, **updates):
        self.decide = decide or would_approve()
        flags = {k: updates.pop(k) for k in ('verdict', 'publish', 'tamper') if k in updates}
        args = arguments(**updates)
        args.source_repo = args.dependencies_dir = None
        approval = Approval(PROJECT, announce=self.lines.append, decide=self.decide)
        # A budget that fits the first rubric, so the claim is posted (an empty ledger in a temp store).
        prefs = OperatorPreferences(budget_usd=5, storage=self.storage)
        return run_claimed(args, PROJECT, prefs, run=FakeReview(self.hub, policy, **flags),
                           approval=approval)

    def approvals(self):
        return [c for c in self.hub.calls if c[1] == 'POST' and c[2].endswith('/pulls/1/reviews')]

    def test_opted_in_maintainer_submits_exactly_one_approve_after_readback(self):
        result = self.review()
        [post] = self.approvals()
        self.assertEqual(post[3]['event'], 'APPROVE')
        self.assertEqual(post[3]['commit_id'], HEAD)
        self.assertIn(f'https://github.com/{REPO}/pull/1#issuecomment-', post[3]['body'])
        self.assertEqual(result['approval']['state'], 'submitted')
        self.assertEqual(note(result['approval']),
                         f'Approval: submitted https://github.com/{REPO}/pull/1#pullrequestreview-900')
        self.assertEqual(self.lines, [ANNOUNCE])
        # The line precedes inference; the readback precedes the decision, which precedes the POST.
        events = self.hub.events
        self.assertLess(events.index('model'), events.index('approve'))
        self.assertEqual(self.decide.calls, [1])
        self.assertEqual(result['claim']['state'], 'finished')

    def test_no_approve_posts_findings_without_approval(self):
        result = self.review(no_approve=True)
        self.assertEqual(self.approvals(), [])
        self.assertIn('publication', result)
        self.assertEqual(note(result['approval']), 'Approval: not submitted: --no-approve')
        self.assertEqual(self.lines, [])

    def test_not_opted_in_approving_off_or_shipped_policy_never_approve(self):
        shipped = parse_policy(resource_text('automation.toml'))
        # Activated: every authorized reviewer opted in on 2026-11-25; anyone else is never approved.
        self.assertEqual((shipped.approving, shipped.approving_reviewers),
                         (True, tuple(f'user:{i}' for i in SEVEN)))
        for policy, reason in ((replace(APPROVING, approving_reviewers=('user:9',)), 'not opted in'),
                               (replace(APPROVING, approving=False), 'approving is off'),
                               (replace(shipped, authorized_reviewers=(f'user:{ME}',)), 'not opted in')):
            with self.subTest(reason=reason):
                result = self.review(policy=policy)
                self.assertIn(reason, result['approval']['reason'])
        self.assertEqual(self.approvals(), [])
        self.assertEqual(self.lines, [])

    def test_the_pr_author_is_refused(self):
        self.hub.author = ME
        result = self.review()
        self.assertEqual(result['approval']['reason'], 'you are the PR author')
        self.assertEqual((self.approvals(), self.lines), ([], []))

    def test_a_non_approving_rubric_gives_no_approval(self):
        result = self.review(verdict='request_changes')
        self.assertEqual(result['approval']['reason'], 'not all rubrics approve (naming)')
        self.assertEqual(self.approvals(), [])
        self.assertEqual(self.decide.calls, [])

    def test_a_refusing_decision_gives_no_approval_with_its_reasons(self):
        reasons = ['paths: SphereCeti/Other/X.lean: outside the proof-topic allowlist',
                   'compiled_audit: trusted-build tooling attestation is stale']
        result = self.review(decide=would_approve(would_approve=False, reasons=reasons))
        self.assertEqual(result['approval']['decision_reasons'], reasons)
        self.assertEqual(note(result['approval']), 'Approval: not submitted: the auto-approval decision refused ('
                         + '; '.join(reasons) + ')')
        hypothetical = self.review(decide=would_approve(hypothetical=True))
        other_head = self.review(decide=would_approve(head='9' * 40))
        for refused in (hypothetical, other_head):
            self.assertEqual(refused['approval']['reason'], 'the auto-approval decision refused')
        self.assertEqual(self.approvals(), [])

    def test_failed_or_mismatched_readback_gives_no_approval(self):
        edited = self.review(tamper=True)  # the record comment reads back edited
        self.assertIn('readback did not accept', edited['approval']['reason'])
        missing = self.review(publish=False)  # the record was not published
        self.assertEqual(missing['approval']['reason'], 'the review record was not posted under your identity')
        self.hub.head = '9' * 40  # the PR moved after the review
        moved = self.review()
        self.assertIn(moved['approval']['reason'], ('the PR head or base moved after the review',))
        self.assertEqual(self.approvals(), [])

    def test_an_existing_approval_is_idempotent(self):
        self.hub.reviews.append({'id': 800, 'user': {'id': ME}, 'state': 'APPROVED', 'commit_id': HEAD,
                                 'html_url': 'https://github.com/x#pullrequestreview-800'})
        result = self.review()
        self.assertEqual(result['approval']['state'], 'existing')
        self.assertEqual(self.approvals(), [])
        self.assertIn('you already approved this head', note(result['approval']))

    def test_an_unanswered_author_contest_on_your_earlier_record_blocks_approval(self):
        # #107: an author contest on your earlier record must be answered by your new record before
        # the official reader accepts it; this all-green record leaves it unanswered.
        from test_author_contests import finding, plain
        self.hub.store[1] = [finding(50, actor=ME),
                             plain(60, '/sphereceti contest generality\nThe finding does not apply.',
                                   actor=AUTHOR)]
        result = self.review()
        self.assertEqual(result['approval']['state'], 'not_submitted')
        self.assertIn('unanswered contest on generality', result['approval']['reason'])
        self.assertEqual(self.approvals(), [])

    def test_a_later_change_request_by_you_supersedes_an_older_approve(self):
        # As the merge controller reads it, your latest decisive review is your current state.
        self.hub.reviews += [{'id': 800, 'user': {'id': ME}, 'state': 'APPROVED', 'commit_id': HEAD},
                             {'id': 801, 'user': {'id': ME}, 'state': 'CHANGES_REQUESTED', 'commit_id': HEAD},
                             {'id': 802, 'user': {'id': ME}, 'state': 'COMMENTED', 'commit_id': HEAD}]
        result = self.review()
        self.assertEqual(result['approval']['state'], 'submitted')
        [post] = self.approvals()
        self.assertEqual((post[3]['event'], post[3]['commit_id']), ('APPROVE', HEAD))

    def test_an_ambiguous_approval_post_is_never_retried(self):
        self.hub.fail_review_post = True
        result = self.review()
        self.assertEqual(len(self.approvals()), 1)
        self.assertTrue(result['approval']['reason'].startswith('approval submission is unconfirmed'))

    def test_dry_run_and_no_post_have_no_line_and_no_approval(self):
        dry = self.review(post=False, dry_run=True)
        self.assertNotIn('approval', dry)
        local = self.review(post=False, no_post=True)
        self.assertEqual(local['approval']['reason'], 'the review record is not being posted')
        self.assertEqual((self.lines, self.approvals()), ([], []))


class PolicyTest(unittest.TestCase):
    def test_approving_fields_are_optional_validated_and_shipped_off(self):
        base = automation_policy(posting=True, authorized_reviewers=['user:7'])
        policy = parse_policy(base)
        self.assertEqual((policy.approving, policy.approving_reviewers), (False, ()))
        enabled = parse_policy(base + 'approving = true\napproving_reviewers = ["user:7"]\n')
        self.assertEqual((enabled.approving, enabled.approving_reviewers), (True, ('user:7',)))
        for extra in ('approving_reviewers = ["user:8"]\n', 'approving_reviewers = ["app:7"]\n',
                      'approving_reviewers = ["user:7", "user:7"]\n', 'approving = "yes"\n',
                      'approving_reviewer = []\n'):
            with self.subTest(extra=extra), self.assertRaises(ConfigError):
                parse_policy(base + extra)
        shipped = (Path(__file__).resolve().parents[1] / 'policy/automation.toml').read_text()
        self.assertIn('approving = true\n', shipped)
        expected = 'approving_reviewers = [' + ', '.join(f'"user:{i}"' for i in SEVEN) + ']\n'
        self.assertIn(expected, shipped)



class BatchApprovalTest(unittest.TestCase):
    def test_batch_items_go_through_the_same_approval_as_review_n(self):
        from argparse import Namespace
        from datetime import timedelta
        import tempfile
        from sphereceti.review_queue import run_batch
        from test_review_queue import SurveyAPI, pr
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-batch-approve-')
        self.addCleanup(temp.cleanup)
        hub, lines = ApprovalHub(), []
        api = SurveyAPI([pr(1, 'bob', ago=timedelta(hours=1))], actor='yvonne')
        args = Namespace(new=True, revised=False, all=False, limit=1, dry_run=False, post=True, no_post=False,
                         post_default=True, output=None, budget_usd=None, max_call_cost=1.0, provider=None,
                         codex_model=None, claude_model=None, kiro_model=None, local_sources=False,
                         read_records=False, shadow=None, replies_json=None, head=None, base=None,
                         description_file=None, reply_file=None, reply_rubric=None, mode='commit', pr=None,
                         force_claim=False, no_approve=False, source_repo=None, dependencies_dir=None)
        decide = would_approve()
        result = run_batch(args, PROJECT, APPROVING, OperatorPreferences(storage=temp.name), api=api,
                           client=hub.client(ME), announce=lines.append, run=FakeReview(hub, APPROVING),
                           approval=lambda: Approval(PROJECT, announce=lines.append, decide=decide))
        [item] = result['items']
        self.assertEqual(item['approval']['state'], 'submitted')
        self.assertTrue(item['outcome'].endswith('; approval submitted'))
        self.assertIn(ANNOUNCE, lines)
        self.assertEqual(len([c for c in hub.calls if c[1] == 'POST' and c[2].endswith('/pulls/1/reviews')]), 1)
        self.assertFalse([c for c in hub.calls if 'merge' in c[2]])

    def test_bare_stack_aware_selection_goes_through_approval_too(self):
        from argparse import Namespace
        from datetime import timedelta
        import tempfile
        from sphereceti.review_select import run_bare
        from test_review_queue import SurveyAPI, pr
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-bare-approve-')
        self.addCleanup(temp.cleanup)
        hub, lines = ApprovalHub(), []
        # #1 is a stack root; its child #2 waits on it, so bare selection picks #1.
        api = SurveyAPI([pr(1, 'bob', ago=timedelta(hours=1), baseRefName='main', headRefName='root'),
                         pr(2, 'bob', ago=timedelta(hours=2), baseRefName='root', headRefName='child')],
                        actor='yvonne')
        args = Namespace(dry_run=False, post=True, no_post=False, post_default=True, output=None, budget_usd=None,
                         max_call_cost=1.0, provider=None, codex_model=None, claude_model=None, kiro_model=None,
                         local_sources=False, read_records=False, shadow=None, replies_json=None, head=None, base=None,
                         description_file=None, reply_file=None, reply_rubric=None, mode='commit', pr=None,
                         force_claim=False, no_approve=False, source_repo=None, dependencies_dir=None)
        selection = run_bare(args, PROJECT, APPROVING, OperatorPreferences(budget_usd=5, storage=temp.name),
                             api=api, client=hub.client(ME), announce=lines.append, run=FakeReview(hub, APPROVING),
                             approval=lambda: Approval(PROJECT, announce=lines.append, decide=would_approve()))
        self.assertEqual(selection['selected']['pr'], 1)
        self.assertIn(('waiting_on_parent', 2), [(s['code'], s['pr']) for s in selection['skipped']])
        self.assertEqual(selection['approval']['state'], 'submitted')
        self.assertIn(ANNOUNCE, lines)


if __name__ == '__main__':
    unittest.main()
