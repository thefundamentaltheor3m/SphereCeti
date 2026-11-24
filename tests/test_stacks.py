# SPDX-License-Identifier: Apache-2.0
"""Stack-aware review: roots first, children wait for review-satisfied parents."""
from datetime import timedelta
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences
from sphereceti.local_review import RUBRICS
from sphereceti.review_queue import queue, render
from sphereceti.review_records import RecordError
from sphereceti.review_select import rationale, select
from sphereceti.stacks import stacks
from sphereceti.worker_cli import survey
from test_review_queue import BASE, HEAD, POLICY, PROJECT, REPO, SurveyAPI, pr
import test_review_queue

FORK = 'CBirkbeck/SphereCeti'
AUTHORIZED = 2009342  # the shipped policy's authorized reviewer


def stacked(number, base_ref, head_ref, *, repo=REPO, ago=timedelta(hours=1), **updates):
    return pr(number, 'bob', ago=ago, baseRefName=base_ref, headRefName=head_ref,
              headRepository={'nameWithOwner': repo}, **updates)


def accepted(cid, number, approvals=10):
    """An authorized, complete, non-advisory record on HEAD approving `approvals` of the ten rubrics."""
    from sphereceti.review_records import make_record
    verdicts = {r: ('approve' if i < approvals else 'request_changes') for i, r in enumerate(RUBRICS)}
    result = {'repository': REPO, 'pr': number, 'head': HEAD, 'base': BASE, 'diff_base': BASE, 'tooling': 'd' * 40,
              'completion': 'complete', 'execution_mode': 'commit', 'tooling_approved': True,
              'installed_tooling_matches_T': True, 'missing_context': [], 'config_differences': [],
              'verdicts': verdicts, 'reviews': {},
              **{k: 'e' * 64 for k in ('dependency_digest', 'engine_digest', 'effective_rubrics_digest',
                                       'installed_tooling_digest', 'policy_digest', 'review_context_digest',
                                       'description_digest')}}
    _, rendered = make_record(result)
    return {'id': cid, 'body': rendered, 'user': {'id': AUTHORIZED, 'type': 'User', 'login': 'maintainer'},
            'issue_url': f'https://api.github.com/repos/{REPO}/issues/{number}',
            'created_at': '2026-11-20T10:00:00Z', 'updated_at': '2026-11-20T10:00:00Z'}


def queue_prs():
    """The live shape: #64, #116 and #71 on #63; #115 on #75 (a fork head); #86 on #85."""
    return [stacked(63, 'main', 'presented-lattice', ago=timedelta(hours=2)),
            stacked(64, 'presented-lattice', 'even-lattice', ago=timedelta(hours=9)),
            stacked(116, 'presented-lattice', 'count-roots', ago=timedelta(hours=8)),
            stacked(71, 'even-lattice', 'integral-inner', ago=timedelta(hours=7)),
            stacked(75, 'main', 'min-norm', repo=FORK, ago=timedelta(hours=3)),
            stacked(115, 'min-norm', 'even-min-norm', ago=timedelta(hours=6)),
            stacked(85, 'main', 'structure-factor', ago=timedelta(hours=4)),
            stacked(86, 'structure-factor', 'defects', ago=timedelta(hours=5)),
            stacked(90, 'main', 'covolume', ago=timedelta(hours=10))]  # oldest, unstacked


class Client(test_review_queue.Client):
    def __init__(self, comments=None, closed=None, pulls=None):
        super().__init__(comments)
        self.closed, self.pulls = closed or {}, pulls or {}

    def call(self, endpoint, **kwargs):
        if '/pulls?state=closed&head=' in endpoint:
            branch = endpoint.split('head=')[1].split('&')[0].split(':', 1)[1]
            return [self.closed.get(branch, [])]
        if endpoint in self.pulls:
            return self.pulls[endpoint]
        return super().call(endpoint, **kwargs)


class StackDetectionTest(unittest.TestCase):
    def test_parents_chains_roots_and_descendants_including_a_fork_head(self):
        snapshot = survey(PROJECT, None, api=SurveyAPI(queue_prs() + [stacked(140, 'gone', 'x'),
                                                                     stacked(141, 'old-parent', 'y')]))
        self.assertEqual(snapshot['schema'], 'sphereceti.worker-survey/v4')
        client = Client(closed={'old-parent': [{'number': 30, 'merged_at': '2026-11-01T00:00:00Z'}]})
        info = stacks(snapshot, PROJECT, client=client)
        self.assertEqual({n: info[n]['parent'] for n in (63, 64, 116, 71, 75, 115, 86, 90)},
                         {63: None, 64: 63, 116: 63, 71: 64, 75: None, 115: 75, 86: 85, 90: None})
        self.assertEqual((info[71]['chain'], info[71]['root']), ([64, 63], 63))
        self.assertEqual(info[115]['parent_state'], 'open')  # the fork PR #75 heads `min-norm`
        self.assertEqual({n: info[n]['descendants'] for n in (63, 64, 75, 85, 90)},
                         {63: 3, 64: 1, 75: 1, 85: 1, 90: 0})
        self.assertEqual((info[140]['parent_state'], info[141]['parent_state']), ('missing', 'merged'))

    def test_a_same_repository_head_wins_over_a_fork_with_the_same_branch_name(self):
        prs = [stacked(10, 'main', 'feature'), stacked(11, 'main', 'feature', repo=FORK), stacked(12, 'feature', 'z')]
        info = stacks(survey(PROJECT, None, api=SurveyAPI(prs)), PROJECT)
        self.assertEqual(info[12]['parent'], 10)


    def test_the_survey_budget_grows_with_the_open_queue(self):
        import time
        from sphereceti.worker_cli import GitHub
        api = GitHub()
        before = api.deadline
        api.allow_for(49)  # 49 open PRs, each possibly needing its scope provenance read
        self.assertGreaterEqual(api.deadline - time.monotonic(), 60 + 3 * 49 - 1)
        self.assertGreater(api.deadline, before)


class StackSelectionTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-stacks-')
        self.addCleanup(temp.cleanup)
        self.prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=temp.name)

    def choose(self, prs, comments=None):
        return select(PROJECT, POLICY, self.prefs, api=SurveyAPI(prs), client=Client(comments))

    def test_roots_blocking_the_most_children_rank_first(self):
        result = self.choose(queue_prs())
        # #63 unblocks three; #85 and #75 one each (#85 waited longer); #90, the oldest, unblocks none.
        self.assertEqual([c['pr'] for c in result['candidates']], [63, 85, 75, 90])
        self.assertEqual([c['unblocks'] for c in result['candidates']], [3, 1, 1, 0])
        self.assertIn('no current review; unblocks 3 stacked PRs;', rationale(result))

    def test_children_wait_with_each_reason(self):
        failed = [{'__typename': 'CheckRun', 'status': 'COMPLETED', 'conclusion': 'FAILURE'}]
        prs = [p for p in queue_prs() if p['number'] != 85] + [
            stacked(85, 'main', 'structure-factor', statusCheckRollup=failed)]
        # #64 itself is 10/10, so #71 waits on its grandparent #63.
        result = self.choose(prs, {63: [accepted(10, 63, approvals=9)], 64: [accepted(11, 64)], 75: []})
        reasons = {s['pr']: s['reason'] for s in result['skipped'] if s['code'] == 'waiting_on_parent'}
        self.assertEqual(reasons, {64: 'waiting on parent #63 (9/10 on its head)',
                                   116: 'waiting on parent #63 (9/10 on its head)',
                                   71: 'waiting on ancestor #63 (9/10 on its head)',
                                   115: 'waiting on parent #75 (no review on its head)',
                                   86: 'waiting on parent #85 (not ready)'})

    def test_a_child_of_a_review_satisfied_parent_is_eligible(self):
        prs = [stacked(63, 'main', 'presented-lattice'), stacked(64, 'presented-lattice', 'even-lattice')]
        result = self.choose(prs, {63: [accepted(10, 63)]})
        self.assertEqual([c['pr'] for c in result['candidates']], [64])  # #63 itself is already reviewed
        self.assertEqual(result['skipped'][0]['code'], 'reviewed')


class BlockedSectionTest(unittest.TestCase):
    def test_reviews_lists_blocked_children_grouped_by_root_with_counts(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-stacks-')
        self.addCleanup(temp.cleanup)
        prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=temp.name)
        report = queue(PROJECT, POLICY, prefs, api=SurveyAPI(queue_prs() + [stacked(123, 'periodic-base', 'p')]),
                       client=Client({63: [accepted(10, 63, approvals=9)], 64: [accepted(11, 64)]}))
        groups = report['blocked_by_parent']
        self.assertEqual([(g['root'], g['unblocks'], [i['pr'] for i in g['items']]) for g in groups],
                         [(63, 3, [64, 71, 116]), (75, 1, [115]), (85, 1, [86]), (None, 1, [123])])
        self.assertEqual(groups[-1]['branch'], 'periodic-base')
        self.assertEqual([e['pr'] for e in report['sections']['new']], [85, 75, 90])  # #63 has an accepted review
        self.assertNotIn(64, [e['pr'] for e in report['sections']['new']])
        text = render(report)
        self.assertIn('Blocked by a parent (6):', text)
        self.assertIn('  base branch periodic-base: #123 waiting on base branch periodic-base '
                      '(no open or merged PR heads it)', text)
        self.assertIn('  stack #63 (unblocks 3): #64 waiting on parent #63 (9/10 on its head); '
                      '#71 waiting on ancestor #63 (9/10 on its head); #116 waiting on parent #63 (9/10 on its head)',
                      text)
        self.assertIn('  stack #75 (unblocks 1): #115 waiting on parent #75 (no review on its head)', text)


class IntendParentTest(unittest.TestCase):
    def test_an_unmerged_parent_is_warned_and_kept_in_the_registration(self):
        from sphereceti.intentions import lookup, register, render_lookup
        world = {'issues': [], 'prs': [], 'comments': {}}
        from test_intentions_cli import FakeClient

        class Pulls(FakeClient):
            def call(inner, endpoint, **kwargs):
                if endpoint == f'repos/{REPO}/pulls/63':
                    return {'number': 63, 'merged': False, 'state': 'open'}
                if endpoint == f'repos/{REPO}/pulls/55':
                    return {'number': 55, 'merged': True, 'state': 'closed'}
                if endpoint == f'repos/{REPO}/pulls/99':
                    return {'message': 'Not Found'}
                return FakeClient.call(inner, endpoint, **kwargs)
        client = Pulls(world)
        result = lookup(PROJECT, 'SphereCeti.EuclideanLattice.foo', client=client, item='C3',
                        module='SphereCeti/Lattice/Foo.lean', parent=63)
        self.assertEqual(result['warnings'], ['parent #63 is not merged: stacked proofs wait for their parents; '
                                              'start from main when you can'])
        self.assertTrue(render_lookup(result).startswith('Warning: parent #63 is not merged'))
        self.assertIn('parent_pr=%2363', result['register_url'])
        outcome = register(PROJECT, result, client=client, parent=63, delay=0)
        self.assertEqual(outcome['state'], 'registered')
        self.assertIn('### Parent PR\n\n#63', world['issues'][-1]['body'])
        merged = lookup(PROJECT, 'SphereCeti.EuclideanLattice.bar', client=client, parent=55)
        self.assertEqual(merged['warnings'], [])
        with self.assertRaises(RecordError):  # an unreadable parent is an error, not a silent pass
            lookup(PROJECT, 'X.y', client=client, parent=99)


if __name__ == '__main__':
    unittest.main()
