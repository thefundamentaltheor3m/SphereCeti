# SPDX-License-Identifier: Apache-2.0
"""The fast queue decides exactly as the per-PR REST queue: bulk vs REST, parallel vs sequential,
cached vs fresh, and across PRs that change between runs. Failures still fail closed."""
from copy import deepcopy
from datetime import timedelta
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences
from sphereceti.review_queue import queue, render
from sphereceti.review_records import CONTEST, RecordError
from sphereceti.review_select import select
from sphereceti.worker import WorkerError
from sphereceti.worker_cli import GitHub, rate_limit_reason, survey
from bulk_fixture import graphql_page
from test_review_queue import BASE, HEAD, ME, OLD, POLICY, PROJECT, REPO, comment, pr, record
from test_worker_checks import POLICY as CHECKS, evidence

SCOPE_HEAD = 'a' * 40


class Hub:
    """One fixture world served three ways: `gh pr list` + REST comments, or the bulk GraphQL
    query; scope provenance by endpoint (so concurrent reads get the right answer)."""

    def __init__(self, prs, comments=None, compare=None, scope=None):
        self.prs, self.comments, self.compare = prs, comments or {}, compare or {}
        self.scope = scope or {}
        self.calls, self.lock = [], threading.Lock()

    def log(self, kind):
        with self.lock:
            self.calls.append(kind)


class SurveyReader:
    def __init__(self, hub, *, bulk=False, concurrent=False, page=20, limit=100):
        self.hub, self.bulk, self.concurrent, self.page, self.limit = hub, bulk, concurrent, page, limit
        self.queue_comments, self.scope_cache = {}, None

    def read(self, args, limit=None):
        hub = self.hub
        if args[:2] == ['api', 'graphql']:
            hub.log('graphql')
            fields = dict(a.split('=', 1) for a in args if '=' in a and not a.startswith('query='))
            return graphql_page(hub.prs, hub.comments, ME, fields.get('cursor'), self.page, self.limit)
        if args[-1] == 'user':
            hub.log('user')
            return {'login': ME}
        if args[:2] == ['pr', 'list']:
            hub.log('pr list')
            return deepcopy(hub.prs)
        endpoint = args[-1]
        hub.log('scope ' + endpoint.split('/', 3)[-1].split('?')[0])
        if endpoint in hub.scope:
            value = hub.scope[endpoint]
            if isinstance(value, Exception):
                raise value
            return deepcopy(value)
        raise WorkerError('GitHub survey failed; queue is unknown (no fallback)')


class RestClient:
    def __init__(self, hub, *, concurrent=False):
        self.hub, self.concurrent = hub, concurrent

    def comments(self, repository, number):
        self.hub.log(f'comments {number}')
        return deepcopy(self.hub.comments.get(number, []))

    def call(self, endpoint, **kwargs):
        assert not kwargs.get('payload') and not kwargs.get('method'), 'the queue never writes'
        self.hub.log(endpoint.split('/')[3] if endpoint.startswith('repos/') else endpoint)
        if '/compare/' in endpoint:
            value = self.hub.compare.get(endpoint.rsplit('/', 1)[1])
            if value is None:
                raise RecordError('GitHub operation failed')
            return deepcopy(value)
        if '/actions/runs?head_sha=' in endpoint:
            return [{'total_count': 0, 'workflow_runs': []}]
        if '/pulls?state=closed&head=' in endpoint:
            return [[{'merged_at': '2026-11-01T00:00:00Z'}]]
        raise RecordError('unexpected read ' + endpoint)


def scope_world():
    """#9: a human-review-scope PR whose trusted run must be authenticated (four GETs)."""
    raw, responses = evidence()
    statuses, main, run, jobs = responses
    prefix = f'repos/{PROJECT.repository}'
    scope = {f'{prefix}/commits/{SCOPE_HEAD}/statuses?per_page=100': statuses, f'{prefix}/commits/main': main,
             f'{prefix}/actions/runs/100': run, f'{prefix}/actions/runs/100/attempts/1/jobs?per_page=100': jobs}
    raw = {**raw, 'number': 9, 'author': {'login': 'dave'}, 'title': 'Scope', 'headRefName': 'scope',
           'updatedAt': pr(9)['updatedAt']}
    run['pull_requests'][0]['number'] = 9
    return raw, scope


def world():
    raw, scope = scope_world()
    prs = [pr(1, ME), pr(2, ago=timedelta(hours=2)), pr(3, ago=timedelta(hours=1)),
           pr(4, 'carol', statusCheckRollup=[{'__typename': 'CheckRun', 'status': 'COMPLETED',
                                              'conclusion': 'FAILURE'}]),
           pr(5, isDraft=True), pr(7), pr(8, mergeable='UNKNOWN'),
           pr(10, baseRefName='branch-3'), pr(11, baseRefName='gone-branch'), raw]
    comments = {
        3: [record(10, 3, head=OLD), comment(11, 3, 'Fixed the naming, thanks.', 'bob'),
            comment(12, 3, CONTEST + '{"comment":10}-->\nplease reconsider', 'bob')],
        4: [record(20, 4, verdicts={'attribution': 'request_changes', 'naming': 'block'})],
        7: [record(30, 7)],
    }
    prs[2]['headRefName'] = 'branch-3'
    return Hub(prs, comments, {f'{OLD}...{HEAD}': {'status': 'ahead', 'ahead_by': 2, 'merge_base_commit': {}}},
               scope)


def stable(report):
    """The listing without the observation clock (each run observes a moment later)."""
    text = json.dumps(report, sort_keys=False)
    report = json.loads(text)
    report.pop('observed_at', None)
    for section in report.get('sections', {}).values():
        for item in section:
            item.pop('waiting_seconds', None)
    for item in report.get('candidates', []):
        item.pop('waiting_seconds', None)
    if report.get('selected'):
        report['selected'].pop('waiting_seconds', None)
    return report


class FastQueueTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-fast-queue-')
        self.addCleanup(temp.cleanup)
        self.prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=temp.name)
        from sphereceti import config
        original = config.resource_text
        patcher = patch('sphereceti.config.resource_text',
                        side_effect=lambda name: CHECKS if name == 'merge-checks.toml' else original(name))
        patcher.start()
        self.addCleanup(patcher.stop)

    def listing(self, hub, *, bulk, concurrent, cache, page=20, limit=100, kind='queue'):
        reader = SurveyReader(hub, bulk=bulk, concurrent=concurrent, page=page, limit=limit)
        client = RestClient(hub, concurrent=concurrent)
        hub.calls.clear()
        if kind == 'queue':
            report = queue(PROJECT, POLICY, self.prefs, api=reader, client=client, use_cache=cache)
            text = render(report)
            return stable(report), text, list(hub.calls)
        report = select(PROJECT, POLICY, self.prefs, api=reader, client=client, use_cache=cache)
        return stable(report), None, list(hub.calls)

    def test_bulk_parallel_and_cached_listings_equal_the_rest_listing(self):
        baseline, text, rest_calls = self.listing(world(), bulk=False, concurrent=False, cache=False)
        self.assertIn(9, [e['pr'] for e in baseline['sections']['new']])  # the scope exception held
        self.assertEqual(sum(c.startswith('comments') for c in rest_calls), 9)  # every open non-draft PR
        for bulk, concurrent, cache in ((True, False, False), (False, True, False), (True, True, False),
                                        (True, True, True), (True, True, True)):  # the last run is warm
            with self.subTest(bulk=bulk, concurrent=concurrent, cache=cache):
                report, rendered, calls = self.listing(world(), bulk=bulk, concurrent=concurrent, cache=cache)
                self.assertEqual(report, baseline)
                self.assertEqual(rendered.split('\n', 1)[1], text.split('\n', 1)[1])
                if bulk:
                    self.assertFalse([c for c in calls if c.startswith('comments')])
                    self.assertEqual(calls.count('graphql'), 1)
        _, _, warm = self.listing(world(), bulk=True, concurrent=True, cache=True)
        self.assertEqual([c for c in warm if c.startswith('scope')], ['scope commits/main'])  # main: fresh;
        self.assertNotIn('compare', warm)  # the scope verdict and the exact-commit compare: cached

    def test_bare_selection_is_identical_too(self):
        baseline, _, _ = self.listing(world(), bulk=False, concurrent=False, cache=False, kind='select')
        for cache in (True, True):
            report, _, _ = self.listing(world(), bulk=True, concurrent=True, cache=cache, kind='select')
            self.assertEqual(report, baseline)

    def test_prs_changing_between_runs_match_a_fresh_listing(self):
        hub = world()
        self.listing(hub, bulk=True, concurrent=True, cache=True)  # warm the cache
        prefix = f'repos/{PROJECT.repository}'

        def rerun(h):  # a new trusted run attempt: new statuses point at run 101, which failed
            url = h.prs[-1]['statusCheckRollup'][1]['targetUrl'].replace('/100/', '/101/')
            h.prs[-1]['statusCheckRollup'][1]['targetUrl'] = url
            statuses = deepcopy(h.scope[f'{prefix}/commits/{SCOPE_HEAD}/statuses?per_page=100'])
            for status in statuses:
                status['target_url'] = url
            h.scope[f'{prefix}/commits/{SCOPE_HEAD}/statuses?per_page=100'] = statuses
            h.scope[f'{prefix}/actions/runs/101'] = {**h.scope[f'{prefix}/actions/runs/100'], 'id': 101,
                                                    'conclusion': 'failure'}
            h.scope[f'{prefix}/actions/runs/101/attempts/1/jobs?per_page=100'] = deepcopy(
                h.scope[f'{prefix}/actions/runs/100/attempts/1/jobs?per_page=100'])

        def push(h):  # the scope PR is pushed; the old trusted run no longer matches its head
            h.scope[f'{prefix}/commits/{"e" * 40}/statuses?per_page=100'] = h.scope[
                f'{prefix}/commits/{SCOPE_HEAD}/statuses?per_page=100']
            h.prs[-1]['headRefOid'] = 'e' * 40

        def main_moves(h):
            h.scope[f'{prefix}/commits/main'] = {'sha': 'd' * 40}

        changes = [rerun, push, main_moves,
                   lambda h: h.comments.setdefault(2, []).append(record(40, 2)),  # a new review record
                   lambda h: h.prs[2].update(headRefOid='f' * 40)]             # a revision of a reviewed PR
        for change in changes:
            change(hub)
            fresh, _, _ = self.listing(hub, bulk=False, concurrent=False, cache=False)
            cached, _, _ = self.listing(hub, bulk=True, concurrent=True, cache=True)
            self.assertEqual(cached, fresh)
            if change is rerun:  # the cached verdict for run 100 would have said ready: it was not reused
                self.assertNotIn(9, [e['pr'] for e in cached['sections']['new']])

    def test_truncated_comments_are_read_through_rest_for_that_pr_only(self):
        hub = world()
        hub.comments[3] += [comment(100 + i, 3, f'note {i}', 'bob') for i in range(3)]
        baseline, _, _ = self.listing(hub, bulk=False, concurrent=False, cache=False)
        report, _, calls = self.listing(hub, bulk=True, concurrent=True, cache=False, limit=4, page=3)
        self.assertEqual(report, baseline)
        self.assertEqual([c for c in calls if c.startswith('comments')], ['comments 3'])
        self.assertEqual(calls.count('graphql'), 4)  # ten PRs, three per page

    def test_failed_reads_fail_closed_in_parallel(self):
        hub = world()
        hub.scope[f'repos/{PROJECT.repository}/actions/runs/100'] = WorkerError('GitHub survey failed; '
                                                                               'queue is unknown (no fallback)')
        with self.assertRaises(WorkerError):
            self.listing(hub, bulk=True, concurrent=True, cache=True)
        hub = world()
        hub.compare = {}
        hub.comments[3][0] = record(10, 3, head=OLD)

        class Broken(RestClient):
            def comments(self, repository, number):
                return None
        reader = SurveyReader(hub, bulk=False, concurrent=True)
        with self.assertRaises(RecordError):
            queue(PROJECT, POLICY, self.prefs, api=reader, client=Broken(hub, concurrent=True), use_cache=True)

    def test_a_changed_queue_between_pages_or_a_graphql_error_raises(self):
        hub = world()
        reader = SurveyReader(hub, bulk=True, page=4)
        original = reader.read
        state = {'n': 0}

        def shifting(args, limit=None):
            value = original(args, limit)
            state['n'] += 1
            if state['n'] == 2:  # a new PR appears while paging: the count no longer matches
                value['data']['repository']['pullRequests']['totalCount'] += 1
            return value
        reader.read = shifting
        with self.assertRaises(WorkerError):
            survey(PROJECT, None, api=reader)
        reader = SurveyReader(world(), bulk=True)
        reader.read = lambda args, limit=None: {'errors': [{'message': 'something broke'}]}
        with self.assertRaises(WorkerError):
            survey(PROJECT, None, api=reader)

    def test_no_cache_neither_reads_nor_writes_the_store(self):
        self.listing(world(), bulk=True, concurrent=True, cache=False)
        self.assertFalse(list(Path(self.prefs.storage).rglob('queue-cache.json')))
        self.listing(world(), bulk=True, concurrent=True, cache=True)
        [path] = list(Path(self.prefs.storage).rglob('queue-cache.json'))
        data = json.loads(path.read_text())
        self.assertEqual(len(data['scope']), 1)
        self.assertEqual(len(data['compare']), 1)
        self.assertEqual(len(data['merged']), 1)  # gone-branch: a merged PR headed it

    def test_merge_decisions_never_reach_the_queue_cache_or_bulk_reads(self):
        root = Path(__file__).resolve().parents[1] / 'tools/project/sphereceti'
        for name in ('merge_controller.py', 'auto_approval.py', 'merge_observation.py', 'merge_checks.py',
                     'carry_over.py', 'review_approval.py', 'local_review.py', 'review_post.py'):
            text = (root / name).read_text()
            with self.subTest(name):
                self.assertNotIn('queue_cache', text)
                self.assertNotIn('from .bulk', text)
                self.assertNotIn('ready_to_merge import Cached', text)


class CarryHistoryTest(unittest.TestCase):
    """Carry-over walks main's first-parent history; the queue reads it 100 commits per listing."""

    def test_history_listings_decide_as_commit_by_commit_reads_with_far_fewer_calls(self):
        from test_carry_over import REVIEWER, Repo, RepoAPI, git, record_comment
        from test_review_queue import SurveyAPI, stamp
        from test_worker import gh_pr
        from sphereceti.config import parse_policy
        from review_fixture import automation_policy
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-carry-history-')
        self.addCleanup(temp.cleanup)
        repo = Repo(Path(temp.name))
        for i in range(30):  # a longer main history, as on SphereCeti
            repo.main_commit({f'docs/infrastructure/n{i}.md': f'{i}\n'})
        head = repo.update(repo.h1, repo.main())

        class Listing(RepoAPI):
            def call(self, endpoint, **kwargs):
                path = endpoint.removeprefix(f'repos/{REPO}/')
                if path.startswith('commits?sha='):
                    self.calls.append(endpoint)
                    sha = path.split('=')[1].split('&')[0]
                    out = []
                    for line in git(self.repo.path, 'rev-list', '--parents', '-n', '100', sha).splitlines():
                        commit, *parents = line.split()
                        out.append({'sha': commit, 'parents': [{'sha': p} for p in parents],
                                    'commit': {'tree': {'sha': git(self.repo.path, 'rev-parse', f'{commit}^{{tree}}')}}})
                    return out
                return super().call(endpoint, **kwargs)

        policy = parse_policy(automation_policy(authorized_reviewers=[f'user:{REVIEWER}']))
        comments = {3: [record_comment(3, repo.h1, repo.m0, repo.m0, login='yvonne')]}
        prs = [gh_pr(3, author={'login': 'bob'}, headRefOid=head, baseRefOid=repo.main(),
                     updatedAt=stamp(timedelta(hours=1)))]
        outputs = []
        for client, cache in ((RepoAPI(repo, comments), False), (Listing(repo, comments), True),
                              (Listing(repo, comments), True)):
            prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=temp.name + '/store')
            report = queue(PROJECT, policy, prefs, api=SurveyAPI(prs, actor='yvonne'), client=client, use_cache=cache)
            outputs.append((stable(report), [c for c in client.calls if '/git/commits/' in c or 'commits?sha=' in c]))
        (plain, one_by_one), (cold, listed), (warm, none) = outputs
        self.assertEqual(plain['done'][0]['code'], 'reviewed_by_you')  # carried over through update-branch
        self.assertEqual(cold, plain)
        self.assertEqual(warm, plain)
        self.assertGreater(len(one_by_one), 30)
        self.assertLessEqual(len(listed), 3)
        self.assertEqual(none, [])  # warm: every commit fact comes from the queue cache


class RateLimitTest(unittest.TestCase):
    def run_with(self, outcomes):
        results = iter(outcomes)

        def fake(command, **kwargs):
            code, err = next(results)
            return subprocess.CompletedProcess(command, code, '{"ok": 1}' if code == 0 else '', err)
        return fake

    def test_secondary_limits_back_off_and_retry_reads_only(self):
        self.assertEqual(rate_limit_reason('gh: You have exceeded a secondary rate limit (HTTP 403)'), 'secondary')
        self.assertEqual(rate_limit_reason('gh: API rate limit exceeded for user ID 1 (HTTP 403)'), 'primary')
        self.assertIsNone(rate_limit_reason('gh: Not Found (HTTP 404)'))
        api = GitHub()
        with patch('subprocess.run', self.run_with([(1, 'secondary rate limit (HTTP 403)'), (0, '')])), \
                patch('time.sleep') as sleep:
            self.assertEqual(api.read(['api', 'user']), {'ok': 1})
        sleep.assert_called_once_with(5)
        with patch('subprocess.run', self.run_with([(1, 'API rate limit exceeded for user ID 1 (HTTP 403)')])), \
                patch('sphereceti.worker_cli.primary_reset', return_value='23:28Z'), patch('time.sleep') as sleep:
            with self.assertRaisesRegex(WorkerError, r'rate limit exhausted \(resets 23:28Z\)'):
                api.read(['api', 'user'])
        sleep.assert_not_called()
        from sphereceti.review_post import GitHub as Client
        with patch('subprocess.run', self.run_with([(1, 'secondary rate limit (HTTP 403)'), (0, '')])) as run, \
                patch('time.sleep'):
            self.assertEqual(Client().call('repos/x/y/pulls/1'), {'ok': 1})
        with patch('subprocess.run', self.run_with([(1, 'secondary rate limit (HTTP 403)')])), patch('time.sleep'):
            with self.assertRaises(RecordError):  # a write is never retried
                Client().call('repos/x/y/issues/1/comments', payload={'body': 'x'})


if __name__ == '__main__':
    unittest.main()
