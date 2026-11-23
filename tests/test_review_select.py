# SPDX-License-Identifier: Apache-2.0
"""Bare `sphereceti review`: choosing the one PR a contributor can help with, offline."""
from argparse import Namespace
from datetime import datetime, timedelta, timezone
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences, parse_policy
from sphereceti.local_review import RUBRICS, ReviewError
from sphereceti.review_records import CONTEST, make_record
from sphereceti.review_select import check_arguments, rationale, select, waiting
from sphereceti.worker import WorkerError
from review_fixture import ROOT, ReviewFixture, automation_policy, commit, git
from test_worker import FakeAPI, PROJECT, gh_pr
from test_worker_checks import POLICY as CHECKS, evidence

REPO = PROJECT.repository
MAINTAINER = 2009342
POLICY = parse_policy(automation_policy(authorized_reviewers=[f'user:{MAINTAINER}']))


def stamp(ago=timedelta(0)):
    return (datetime.now(timezone.utc) - ago).strftime('%Y-%m-%dT%H:%M:%SZ')


def record_comment(cid, pr, head='a'*40, base='b'*40, *, user_id=MAINTAINER, login='maintainer',
                   advisory=False, completion='complete'):
    result = {'repository': REPO, 'pr': pr, 'head': head, 'base': base, 'diff_base': base,
              'tooling': 'c'*40, 'completion': completion, 'execution_mode': 'commit',
              'tooling_approved': not advisory, 'installed_tooling_matches_T': True,
              'missing_context': [], 'config_differences': [],
              'verdicts': {r: 'approve' for r in RUBRICS}, 'reviews': {},
              **{k: 'e'*64 for k in ('dependency_digest', 'engine_digest', 'effective_rubrics_digest',
                                     'installed_tooling_digest', 'policy_digest', 'review_context_digest',
                                     'description_digest')}}
    record, rendered = make_record(result)
    return {'id': cid, 'body': rendered, 'user': {'id': user_id, 'type': 'User', 'login': login},
            'issue_url': f'https://api.github.com/repos/{REPO}/issues/{pr}',
            'created_at': '2026-09-12T11:00:00Z', 'updated_at': '2026-09-12T11:00:00Z'}, record


class FakeClient:
    def __init__(self, comments=None, pulls=None):
        self.records, self.pulls, self.calls = comments or {}, pulls or {}, []

    def comments(self, repository, pr):
        self.calls.append(('comments', pr))
        return self.records.get(pr, [])

    def call(self, endpoint, **kwargs):
        self.calls.append(('call', endpoint))
        assert not kwargs.get('payload'), 'selection never writes'
        return self.pulls[endpoint]


class SelectionTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-select-')
        self.addCleanup(temp.cleanup)
        self.storage = Path(temp.name)
        self.prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=str(self.storage))

    def choose(self, raw, actor='alice', client=None, extra=()):
        api = FakeAPI([{'login': actor}, raw, *extra])
        return select(PROJECT, POLICY, self.prefs, api=api, client=client or FakeClient())

    def local_run(self, pr, head='a'*40, base='b'*40, completion='complete'):
        _, record = record_comment(1, pr, head, base, completion=completion)
        run = self.storage / REPO.replace('/', '__') / 'runs' / f'run{pr}'
        run.mkdir(parents=True)
        (run / 'record.json').write_text(json.dumps(record))
        return run

    def test_bare_review_picks_the_oldest_eligible_pr_and_explains_every_skip(self):
        accepted, _ = record_comment(10, 6)
        mine, _ = record_comment(11, 7, user_id=99, login='Alice', advisory=True)
        self.local_run(8)
        self.local_run(9, head='f'*40)  # a different head does not count as reviewed
        raw = [gh_pr(1, author={'login': 'ALICE'}),
               gh_pr(2, author={'login': 'bob'}, isDraft=True),
               gh_pr(3, author={'login': 'bob'}, statusCheckRollup=[
                   {'__typename': 'CheckRun', 'status': 'COMPLETED', 'conclusion': 'FAILURE'}]),
               gh_pr(4, author={'login': 'bob'}, mergeable='CONFLICTING'),
               gh_pr(5, author={'login': 'bob'}, updatedAt=stamp(timedelta(hours=1))),
               gh_pr(6, author={'login': 'bob'}, updatedAt='2020-01-01T00:00:00Z'),
               gh_pr(7, author={'login': 'bob'}, updatedAt='2020-01-01T00:00:00Z'),
               gh_pr(8, author={'login': 'bob'}, updatedAt='2020-01-01T00:00:00Z'),
               gh_pr(9, author={'login': 'carol'}, updatedAt=stamp(timedelta(hours=5)))]
        client = FakeClient({6: [accepted], 7: [mine]})
        result = self.choose(raw, client=client)
        self.assertEqual(result['state'], 'selected')
        self.assertEqual(result['selected']['pr'], 9)          # waiting 5h beats #5's 1h
        self.assertEqual([c['pr'] for c in result['candidates']], [9, 5])
        codes = {item['pr']: item['code'] for item in result['skipped']}
        self.assertEqual(codes, {1: 'yours', 2: 'draft', 3: 'not_ready', 4: 'not_ready',
                                 6: 'reviewed', 7: 'reviewed_by_you', 8: 'reviewed_by_you'})
        reasons = {item['pr']: item['reason'] for item in result['skipped']}
        self.assertEqual(reasons[3], 'is not ready (CI failed)')
        self.assertEqual(reasons[4], 'is not ready (conflicting)')
        self.assertEqual(reasons[6], f'already has an accepted review of this head (user:{MAINTAINER})')
        self.assertIn('locally', reasons[8])
        # Only ready, foreign PRs have their review records read; nothing is written.
        self.assertEqual(sorted(n for kind, n in client.calls if kind == 'comments'), [5, 6, 7, 8, 9])

    def test_tie_break_is_updated_at_then_lowest_number(self):
        same = stamp(timedelta(hours=2))
        result = self.choose([gh_pr(12, author={'login': 'bob'}, updatedAt=same),
                              gh_pr(11, author={'login': 'bob'}, updatedAt=same)])
        self.assertEqual(result['selected']['pr'], 11)
        self.assertEqual(result['waiting_since'], 'updatedAt')

    def test_unauthorized_or_incomplete_records_and_other_heads_still_need_review(self):
        stranger, _ = record_comment(10, 1, user_id=4242, login='stranger')
        partial, _ = record_comment(11, 1, completion='partial')
        old_head, _ = record_comment(12, 1, head='9'*40)
        other_base, _ = record_comment(13, 1, base='8'*40)
        self.local_run(1, completion='partial')
        result = self.choose([gh_pr(1, author={'login': 'bob'})],
                             client=FakeClient({1: [stranger, partial, old_head, other_base]}))
        self.assertEqual(result['selected']['pr'], 1)

    def test_unresolved_contest_reopens_an_accepted_review(self):
        accepted, record = record_comment(10, 1)
        contest = {'id': 20, 'user': {'id': 77, 'type': 'User', 'login': 'bob'},
                   'body': CONTEST + json.dumps({'comment': 10, 'record': record['record_id'],
                                                 'rubric': 'correctness'}) + '-->\nPlease reconsider.',
                   'issue_url': accepted['issue_url'], 'created_at': 'x', 'updated_at': 'x'}
        client = FakeClient({1: [accepted, contest]}, {f'repos/{REPO}/pulls/1': {'user': {'id': 77}}})
        self.assertEqual(self.choose([gh_pr(1, author={'login': 'bob'})], client=client)['selected']['pr'], 1)
        client = FakeClient({1: [accepted]})
        self.assertIsNone(self.choose([gh_pr(1, author={'login': 'bob'})], client=client)['selected'])

    def test_rationale_line(self):
        result = self.choose([gh_pr(50, author={'login': 'bob'}, headRefOid='8cdec1b' + 'a'*33,
                                    updatedAt=stamp(timedelta(hours=3, minutes=5)))])
        self.assertEqual(rationale(result),
                         'Reviewing #50 (head 8cdec1b): ready, not yours, no current review; waiting 3h.')
        self.assertTrue(rationale(result, dry_run=True).startswith('Previewing #50 (head 8cdec1b)'))
        self.assertEqual([waiting(s) for s in (5, 60, 7200, 3 * 86400)], ['<1m', '1m', '2h', '3d'])

    def test_nothing_qualifies_says_why(self):
        raw = [gh_pr(50, author={'login': 'alice'}),
               gh_pr(41, author={'login': 'bob'}, statusCheckRollup=[
                   {'__typename': 'CheckRun', 'status': 'COMPLETED', 'conclusion': 'FAILURE'}])]
        result = self.choose(raw)
        self.assertEqual(result['state'], 'nothing_to_review')
        self.assertIsNone(result['selected'])
        self.assertEqual(rationale(result),
                         'No PRs need your review: #50 is yours; #41 is not ready (CI failed).')
        self.assertEqual(rationale(self.choose([])), 'No PRs need your review: the open queue is empty.')

    def test_unknown_queue_or_records_is_an_error_not_an_empty_choice(self):
        with self.assertRaises(WorkerError):
            select(PROJECT, POLICY, self.prefs, api=FakeAPI([{'login': 'alice'}, WorkerError('down')]),
                   client=FakeClient())

        class Broken(FakeClient):
            def comments(self, repository, pr):
                return None
        with self.assertRaises(ValueError):
            self.choose([gh_pr(1, author={'login': 'bob'})], client=Broken())

    def test_proof_pr_like_50_is_yours_for_its_author_and_ready_for_others(self):
        # PR #50's shape: a proof under SphereCeti/Contour/ whose CI passes except the
        # authenticated human-review scope status, which the worker's readiness accepts.
        raw, responses = evidence()
        raw = {**raw, 'number': 1, 'author': {'login': 'xavier'}, 'title': 'Prove the contour deformation'}
        with patch('sphereceti.config.resource_text', return_value=CHECKS):
            as_author = self.choose([raw], actor='xavier', extra=responses)
            as_other = self.choose([raw], actor='yvonne', extra=responses)
        self.assertEqual(as_author['skipped'], [{'pr': 1, 'head': 'a'*40, 'code': 'yours', 'reason': 'is yours',
                                                'note': None}])
        self.assertEqual(rationale(as_author), 'No PRs need your review: #1 is yours.')
        self.assertEqual(as_other['selected']['pr'], 1)
        self.assertEqual(as_other['selected']['ci'], 'failed')
        self.assertIn('ready (human-review scope), not yours', rationale(as_other))
        # Before the trusted scope check reports, the same PR is not ready for anyone.
        pending = {**raw, 'statusCheckRollup': [{'__typename': 'CheckRun', 'status': 'IN_PROGRESS',
                                                 'conclusion': None}]}
        self.assertEqual(self.choose([pending], actor='yvonne')['skipped'][0]['code'], 'awaiting_ci')

    def predates_main(self, number=1, author='xavier'):
        # The same evidence after main moved from b... to e...: the run's tooling and the PR base are
        # an older approved main (one compare), so the PR is review-ready with a note.
        raw, responses = evidence()
        responses[1] = {'sha': 'e'*40}
        responses.append({'status': 'ahead', 'merge_base_commit': {'sha': 'b'*40}})
        return {**raw, 'number': number, 'author': {'login': author}}, responses

    def test_older_trusted_build_is_ready_with_a_refresh_note(self):
        raw, responses = self.predates_main()
        with patch('sphereceti.config.resource_text', return_value=CHECKS):
            other = self.choose([raw], actor='yvonne', extra=responses)
            raw, responses = self.predates_main()
            author = self.choose([raw], actor='xavier', extra=responses)
        self.assertEqual(other['selected']['note'], 'trusted build predates main; refresh to merge')
        self.assertIn('ready (human-review scope; trusted build predates main; refresh to merge), not yours',
                      rationale(other))
        # Information only: a PR skipped for another reason keeps its reason, with the note beside it.
        self.assertEqual(author['skipped'][0]['reason'], 'is yours (trusted build predates main; refresh to merge)')
        self.assertEqual(author['skipped'][0]['code'], 'yours')

    def test_stale_or_pending_evidence_is_summarized_apart_from_real_failures(self):
        stale, responses = evidence()
        stale = {**stale, 'number': 60, 'author': {'login': 'bob'}}
        responses[0][0]['description'] = 'Approved tooling build: success'  # pre-attestation build
        responses[2]['pull_requests'][0]['number'] = 60
        stale2, responses2 = evidence()
        stale2 = {**stale2, 'number': 61, 'author': {'login': 'carol'}}
        responses2[0][0]['description'] = 'Approved tooling build: success'
        responses2[2]['pull_requests'][0]['number'] = 61
        pending = gh_pr(62, author={'login': 'bob'}, statusCheckRollup=[
            {'__typename': 'CheckRun', 'status': 'IN_PROGRESS', 'conclusion': None}])
        failed = gh_pr(41, author={'login': 'bob'}, statusCheckRollup=[
            {'__typename': 'CheckRun', 'status': 'COMPLETED', 'conclusion': 'FAILURE'}])
        mine = gh_pr(50, author={'login': 'alice'})
        client = FakeClient(pulls={f'repos/{REPO}/commits/main': {'sha': '5db3655' + 'f'*33}})
        with patch('sphereceti.config.resource_text', return_value=CHECKS):
            result = self.choose([stale, stale2, pending, failed, mine], client=client,
                                 extra=[*responses, *responses2])
        codes = {i['pr']: i['code'] for i in result['skipped']}
        self.assertEqual(codes, {60: 'awaiting_refresh', 61: 'awaiting_refresh', 62: 'awaiting_ci',
                                 41: 'not_ready', 50: 'yours'})
        self.assertEqual(rationale(result), 'No PR is ready with current evidence: 2 open PRs await a refreshed '
                         'trusted build (main moved to 5db3655); 1 open PR awaits CI; 1 is yours; '
                         '#41 is not ready (CI failed).')

    def test_pr_specific_inputs_need_an_explicit_number(self):
        base = dict(local_sources=False, read_records=False, shadow=None, replies_json=None, head=None,
                    base=None, description_file=None, reply_file=None, reply_rubric=None, mode='commit')
        check_arguments(Namespace(**base))
        for key, value in (('local_sources', True), ('read_records', True), ('shadow', 'x'),
                           ('head', 'a'*40), ('mode', 'reply')):
            with self.subTest(key=key), self.assertRaises(ReviewError):
                check_arguments(Namespace(**{**base, key: value}))


FAKE_GH = r'''
import datetime, json, pathlib, sys
now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
root = pathlib.Path(__file__).parent
args = sys.argv[1:]
with (root / "gh-calls.jsonl").open("a") as f:
    f.write(json.dumps(args) + "\n")
table = json.loads((root / "gh.json").read_text())
state_path = root / "gh-comments.json"
comments = json.loads(state_path.read_text()) if state_path.exists() else {}
if args[:2] == ["pr", "list"]:
    key = "pr list"
else:
    assert args[0] == "api"
    key = next(a for a in args[1:] if a == "user" or a.startswith("repos/"))
repo = "thefundamentaltheor3m/SphereCeti"
if "--input" in args and args[-3:-2] == ["PATCH"] and table.get("accept_posts"):
    value = next(c for cs in comments.values() for c in cs if c["id"] == int(key.split("/")[-1]))
    value.update(body=json.load(sys.stdin)["body"], updated_at=now)
    state_path.write_text(json.dumps(comments))
elif "--input" in args:
    if not table.get("accept_posts") or args[-4:] != ["--method", "POST", "--input", "-"]:
        sys.exit(3)  # an unexpected write
    number = key.split("/")[-2]
    for racer in table.get("race", {}).pop(number, []):  # another contributor posts at the same moment
        comments.setdefault(number, []).append({**racer, "id": 100 + sum(map(len, comments.values())),
                                                "created_at": now, "updated_at": now})
    (root / "gh.json").write_text(json.dumps(table))
    value = {"id": 100 + sum(map(len, comments.values())), "body": json.load(sys.stdin)["body"],
             "user": {"id": table["poster_id"], "type": "User", "login": table["user"]["login"]},
             "issue_url": f"https://api.github.com/repos/{repo}/issues/{number}",
             "created_at": now, "updated_at": now}
    comments.setdefault(number, []).append(value)
    state_path.write_text(json.dumps(comments))
elif key.startswith(f"repos/{repo}/issues/comments/"):
    value = next(c for cs in comments.values() for c in cs if c["id"] == int(key.split("/")[-1]))
elif key.endswith("/comments?per_page=100"):
    value = comments.get(key.split("/")[-2], [])
elif key in table:
    value = table[key]
else:
    sys.exit(1)
print(json.dumps([value] if "--paginate" in args else value))
'''


class BareReviewHarness(unittest.TestCase):
    """The CLI end to end: fake gh, fake provider, exact disposable Git evidence."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-bare-review-')
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.fixture = ReviewFixture(self.root)
        gh = self.fixture.bin / 'gh'
        gh.write_text(f'#!{sys.executable}\n' + FAKE_GH)
        gh.chmod(0o755)
        self.build_table()

    def build_table(self, *, accept_posts=False):
        f = self.fixture

        def pr(number, author, **updates):
            value = dict(number=number, title=f'Change {number}', author={'login': author},
                         headRefOid=f.head, baseRefOid=f.tooling, updatedAt='2026-01-01T00:00:00Z',
                         state='OPEN', isDraft=False, mergeable='MERGEABLE',
                         statusCheckRollup=[{'__typename': 'CheckRun', 'status': 'COMPLETED',
                                             'conclusion': 'SUCCESS'}])
            value.update(updates)
            return value
        self.queue = [pr(50, 'xavier', updatedAt='2026-03-01T00:00:00Z'),
                      pr(49, 'bob', isDraft=True), pr(48, 'bob', mergeable='CONFLICTING'),
                      pr(47, 'bob', updatedAt='2026-02-01T00:00:00Z')]
        self.table = {'user': {'login': 'yvonne', 'id': 7, 'type': 'User'}, 'pr list': self.queue, 'poster_id': 7,
                      'accept_posts': accept_posts, f'repos/{REPO}/commits/main': {'sha': f.tooling}}
        for item in self.queue:
            n = item['number']
            self.table[f'repos/{REPO}/pulls/{n}'] = {
                'number': n, 'title': item['title'], 'body': 'untrusted', 'user': {'id': 7},
                'head': {'sha': f.head}, 'base': {'sha': f.tooling, 'repo': {'full_name': REPO}}}
        self.write_table()

    def enable_posting(self, reviewers=('user:7',)):
        """Approved main's policy permits posting; the fake GitHub accepts comments."""
        f = self.fixture
        git(f.repo, 'checkout', '-q', f.tooling)
        (f.repo / 'policy/automation.toml').write_text(
            automation_policy(posting=True, authorized_reviewers=reviewers))
        f.tooling = commit(f.repo)
        (f.repo / 'README.md').write_text('PROPOSED SENTINEL roadmap')
        f.head = commit(f.repo)
        self.build_table(accept_posts=True)

    def comments(self, number):
        path = self.fixture.bin / 'gh-comments.json'
        return json.loads(path.read_text()).get(str(number), []) if path.exists() else []

    def records(self, number=47):
        return [c for c in self.comments(number) if c['body'].startswith('<!--sphereceti-review:v1 ')]

    def claims(self, number=47):
        return [c for c in self.comments(number) if c['body'].startswith('<!--sphereceti-review-claim:v1 ')]

    def writes(self):
        return [call for call in self.gh_calls() if '--input' in call]

    def write_table(self):
        (self.fixture.bin / 'gh.json').write_text(json.dumps(self.table))

    def gh_calls(self):
        path = self.fixture.bin / 'gh-calls.jsonl'
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def run_cli(self, *args, pr=None, output='result'):
        f = self.fixture
        launcher = [sys.executable, '-c', f'import sys; sys.path.insert(0, {str(ROOT / "tools/project")!r}); '
                    'from sphereceti.cli import main; sys.exit(main())']
        command = [*launcher, 'review', *([str(pr)] if pr else []), '--source-repo', str(f.repo),
                   '--dependencies-dir', str(f.deps), '--operator-config', str(f.operator),
                   '--auth', 'api', '--output', str(self.root / output), *args]
        return subprocess.run(command, cwd=f.foreign, env=f.env, capture_output=True, text=True, timeout=120)



class BareReviewCliTest(BareReviewHarness):
    def test_dry_run_selects_without_a_model_call_or_write_and_reports_json(self):
        process = self.run_cli('--dry-run', '--json')
        self.assertEqual(process.returncode, 0, process.stderr)
        result = json.loads(process.stdout)
        self.assertEqual(set(result), {'schema', 'state', 'repository', 'actor', 'observed_at', 'priority',
                                       'waiting_since', 'selected', 'candidates', 'skipped',
                                       'rationale', 'posting', 'approval', 'plan', 'summary', 'review', 'main'})
        self.assertEqual(result['schema'], 'sphereceti.review-selection/v1')
        self.assertEqual((result['state'], result['actor']), ('selected', 'yvonne'))
        self.assertEqual(result['selected']['pr'], 47)  # older than #50
        self.assertEqual([c['pr'] for c in result['candidates']], [47, 50])
        self.assertEqual([(s['pr'], s['code']) for s in result['skipped']], [(49, 'draft'), (48, 'not_ready')])
        self.assertTrue(result['rationale'].startswith(f'Previewing #47 (head {self.fixture.head[:7]}): ready'))
        self.assertTrue(result['rationale'].endswith('; nothing will be posted.'))
        self.assertEqual(result['posting'], 'Not posted: dry run.')
        self.assertEqual(result['review']['completion'], 'dry_run')
        self.assertTrue(result['plan']['line'].startswith(f'Review #47: head {self.fixture.head[:7]}, base '))
        self.assertEqual(result['plan']['posting'], 'dry run: no model call, nothing posted')
        self.assertEqual((result['summary']['line'], result['summary']['next_action']),
                         ('dry run · not posted: dry run', 'run again without --dry-run to review'))
        self.assertEqual((result['review']['pr'], result['review']['head']), (47, self.fixture.head))
        self.assertFalse(self.fixture.calls())
        self.assertFalse((self.root / 'result/record.json').exists())
        self.assertEqual(self.writes(), [])

    def test_full_review_prints_one_line_then_verdicts_and_record(self):
        # Approved policy disables posting: the default keeps the record local and says why.
        process = self.run_cli()
        self.assertEqual(process.returncode, 0, process.stderr)
        lines = process.stdout.splitlines()
        self.assertRegex(lines[0], r'^Reviewing #47 \(head [0-9a-f]{7}\): ready, not yours, '
                                   r'no current review; waiting \d+d; will post if policy permits\.$')
        self.assertRegex(lines[1], r'^Review #47: head [0-9a-f]{7}, base [0-9a-f]{7} · claude claude-[a-z0-9.-]+ · '
                                   r'will not post \(approved policy disables posting\)$')
        self.assertEqual(lines[2], 'Local advisory review #47: complete')
        for rubric in RUBRICS:
            self.assertIn(f'  {rubric.ljust(max(map(len, RUBRICS)))}  approve', lines)
        self.assertIn(f'Record: {self.root}/result/record.md (machine-readable: record.json)', lines)
        self.assertEqual(lines[-5:], ['Not posted: posting is disabled by approved repository policy.',
                                      'Approval: not submitted: the review record is not being posted',
                                      'This command does not authorize merging.',
                                      '10/10 approve · not posted: posting is disabled by approved repository policy',
                                      'Next: none: every rubric approves; the record stays local '
                                      '(posting is disabled by approved repository policy)'])
        self.assertEqual(len(self.fixture.calls()), 10)
        self.assertEqual(self.writes(), [])
        # The contributor's local record now counts as their review of this exact head.
        again = self.run_cli('--dry-run', '--json', output='again')
        result = json.loads(again.stdout)
        self.assertEqual(result['selected']['pr'], 50)
        self.assertIn((47, 'reviewed_by_you'), [(s['pr'], s['code']) for s in result['skipped']])

    def test_bare_review_posts_by_default_and_then_counts_as_yours(self):
        self.enable_posting()
        process = self.run_cli()
        self.assertEqual(process.returncode, 0, process.stderr)
        lines = process.stdout.splitlines()
        self.assertTrue(lines[0].endswith('; will post if policy permits.'))
        self.assertIn(f'Posted: https://github.com/{REPO}/pull/47#issuecomment-101 (authorized reviewer).', lines)
        self.assertEqual(len(self.records()), 1)
        [claim] = self.claims()
        self.assertIn('finished: https://github.com/', claim['body'])
        # Remove the local copies: the published record alone marks #47 as reviewed by you.
        for path in (self.root / 'state').rglob('record.json'):
            path.unlink()
        for path in (self.root / 'state').rglob('journal/records/*.json'):
            path.unlink()
        (self.root / 'result/record.json').unlink()
        again = json.loads(self.run_cli('--dry-run', '--json', output='again').stdout)
        self.assertIn({'pr': 47, 'head': self.fixture.head, 'code': 'reviewed_by_you',
                       'reason': 'you already published a complete review of this head', 'note': None},
                      again['skipped'])
        self.assertEqual(again['selected']['pr'], 50)

    def test_unauthorized_contributor_posts_an_advisory_record(self):
        self.enable_posting(reviewers=('user:1',))
        process = self.run_cli()
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertIn(f'Posted: https://github.com/{REPO}/pull/47#issuecomment-101 '
                      '(advisory: user:7 is not an authorized reviewer).', process.stdout.splitlines())

    def test_no_post_and_dry_run_never_write(self):
        self.enable_posting()
        process = self.run_cli('--no-post')
        self.assertEqual(process.returncode, 0, process.stderr)
        lines = process.stdout.splitlines()
        self.assertTrue(lines[0].endswith('; will not post (--no-post).'))
        self.assertIn('Not posted: --no-post.', lines)
        dry = self.run_cli('--dry-run', output='dry')
        self.assertEqual(dry.returncode, 0, dry.stderr)
        self.assertIn('Not posted: dry run.', dry.stdout.splitlines())
        self.assertEqual(self.writes(), [])
        both = self.run_cli('--post', '--no-post', output='both')
        self.assertEqual(both.returncode, 2)
        self.assertIn('not allowed with argument', both.stderr)

    def test_nothing_to_review_exits_zero_with_reasons(self):
        self.table['user'] = {'login': 'Bob'}
        self.queue[0]['author'] = {'login': 'bob'}
        self.write_table()
        process = self.run_cli('--dry-run')
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(process.stdout.strip(), 'No PRs need your review: #50 is yours; #49 is yours; '
                                                 '#48 is yours; #47 is yours.')
        self.assertFalse(self.fixture.calls())
        process = self.run_cli('--json')
        self.assertEqual(json.loads(process.stdout)['state'], 'nothing_to_review')
        self.assertIsNone(json.loads(process.stdout)['review'])

    def test_unknown_queue_exits_two(self):
        del self.table['pr list']
        self.write_table()
        process = self.run_cli('--dry-run')
        self.assertEqual(process.returncode, 2)
        self.assertIn('queue is unknown', process.stderr)
        self.assertEqual(process.stdout, '')

    def test_head_moving_after_selection_stops_before_the_provider(self):
        self.enable_posting()
        moved = self.queue[3] | {'headRefOid': 'f'*40}
        self.table['pr list'] = [moved]
        self.write_table()
        process = self.run_cli()
        self.assertEqual(process.returncode, 2)
        self.assertIn('changed since it was selected', process.stderr)
        self.assertFalse(self.fixture.calls())
        self.assertEqual(self.writes(), [])

    def test_explicit_review_number_skips_selection(self):
        process = self.run_cli('--dry-run', '--json', pr=50)
        self.assertEqual(process.returncode, 0, process.stderr)
        report = json.loads(process.stdout)
        self.assertNotIn('schema', report)
        self.assertEqual((report['pr'], report['completion']), (50, 'dry_run'))
        endpoints = [call[-1] for call in self.gh_calls()]
        self.assertEqual(endpoints, [f'repos/{REPO}/pulls/50', f'repos/{REPO}/commits/main'])
        process = self.run_cli('--dry-run', pr=50, output='text')
        self.assertRegex(process.stdout, r'^Review #50: head [0-9a-f]{7}, base [0-9a-f]{7} · claude [^·]+ · '
                                         r'dry run: no model call, nothing posted\nLocal advisory review #50: dry_run\n')
        self.assertIn('Not posted: dry run.', process.stdout.splitlines())

    def test_pr_specific_flags_are_refused_before_github(self):
        process = self.run_cli('--read-records')
        self.assertEqual(process.returncode, 2)
        self.assertIn('requires an explicit PR number', process.stderr)
        self.assertEqual(self.gh_calls(), [])


if __name__ == '__main__':
    unittest.main()
