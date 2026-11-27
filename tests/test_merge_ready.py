# SPDX-License-Identifier: Apache-2.0
"""`sphereceti merge-ready`: the maintainer's sweep, against scripted GitHub state (no network)."""
from copy import deepcopy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences, parse_policy
from sphereceti.merge_ready import Sweep, render
from sphereceti.review_post import HTTPError
from sphereceti.review_records import RecordError
from bulk_fixture import graphql_page
from review_fixture import automation_policy
from test_ready_to_merge import CAROL, accepted
from test_review_claims import claim_comment
from test_review_queue import PROJECT, REPO
from test_worker import gh_pr

ME, BOB, DAVE = 7, 11, 21
LOGINS = {ME: 'yvonne', BOB: 'bob', DAVE: 'dave'}
POLICY = parse_policy(automation_policy(authorized_reviewers=[f'user:{CAROL}', f'user:{ME}', f'user:{DAVE}']))
RULES = [{'type': 'required_status_checks', 'parameters': {'required_status_checks': [
    {'context': 'build', 'integration_id': 15368}]}}]
CHECK = {'success': ('COMPLETED', 'SUCCESS'), 'pending': ('IN_PROGRESS', None), 'failure': ('COMPLETED', 'FAILURE'),
         'cancelled': ('COMPLETED', 'CANCELLED')}


def sha(tag):
    import hashlib
    return hashlib.sha1(tag.encode()).hexdigest()


class Hub:
    """Scripted GitHub: open PRs, comments, reviews, CI per head, and the writes the sweep makes."""

    def __init__(self):
        self.main = sha('0')
        self.prs, self.writes, self.reads, self.comment_store = {}, [], [], {}
        self.carry_ok, self.fail_on, self.on_write = {}, None, {}
        self.tick = 0

    def add(self, number, *, author=BOB, head=None, base_ref='main', head_ref=None, behind=0, ci='success',
            draft=False, record=True, reviews=(), merge_status=None, update=None, mergeable_state=None):
        head = head or sha('abcdef'[number % 6] + str(number))
        self.prs[number] = {'number': number, 'title': f'Prove lemma {number}', 'author': author, 'head': head,
                            'base_ref': base_ref, 'head_ref': head_ref or f'branch-{number}', 'behind': behind,
                            'ci': {head: [ci] if isinstance(ci, str) else list(ci)}, 'draft': draft, 'state': 'open',
                            'merged': False, 'reviews': list(reviews), 'merge_status': merge_status,
                            'update': update, 'mergeable_state': mergeable_state, 'merge_commit': None}
        self.comment_store[number] = [accepted(30 + number, number, head=head)] if record else []
        return self.prs[number]

    def open(self):
        return [p for p in sorted(self.prs.values(), key=lambda p: -p['number']) if p['state'] == 'open']

    def ci_state(self, pr, head, advance=False):
        states = pr['ci'].setdefault(head, ['success'])
        if advance and len(states) > 1:
            return states.pop(0)
        return states[0]

    @staticmethod
    def rollup(state):
        """A scripted state: 'success'/'pending'/... for `build` alone, or a full rollup with the
        build check's state."""
        if isinstance(state, dict):
            return state['rollup'], state['build']
        status, conclusion = CHECK[state]
        return [{'__typename': 'CheckRun', 'status': status, 'conclusion': conclusion, 'name': 'build',
                 'workflowName': 'CI'}], state

    def gh_shape(self, pr, advance=False):
        rollup, _ = self.rollup(self.ci_state(pr, pr['head'], advance))
        return gh_pr(pr['number'], title=pr['title'], author={'login': LOGINS[pr['author']]}, headRefOid=pr['head'],
                     baseRefOid=self.main, baseRefName=pr['base_ref'], headRefName=pr['head_ref'],
                     isDraft=pr['draft'], updatedAt=f'2026-11-2{pr["number"] % 5}T00:00:00Z',
                     statusCheckRollup=rollup)

    # The survey reader (worker_cli.GitHub's shape).
    def reader(self):
        hub = self

        class Reader:
            bulk, concurrent = True, False

            def __init__(self):
                self.queue_comments, self.scope_cache = {}, None

            def read(self, args, limit=None):
                hub.reads.append(' '.join(args[:3]))
                if args[:2] == ['api', 'graphql']:
                    fields = dict(a.split('=', 1) for a in args if '=' in a and not a.startswith('query='))
                    return graphql_page([hub.gh_shape(p) for p in hub.open()], hub.comment_store, LOGINS[ME],
                                        fields.get('cursor'))
                if args[:2] == ['pr', 'view']:
                    return hub.gh_shape(hub.prs[int(args[2])], advance=True)
                if args[-1] == 'user':
                    return {'login': LOGINS[ME]}
                raise AssertionError(args)
        return Reader()

    # The REST client (review_post.GitHub's shape).
    def comments(self, repository, number):
        return deepcopy(self.comment_store.get(number, []))

    def call(self, endpoint, *, payload=None, paginate=False, method=None):
        path = endpoint.removeprefix(f'repos/{REPO}/')
        if self.fail_on and self.fail_on in path:
            raise RecordError('GitHub operation failed; publication is unconfirmed')
        if payload is not None:
            return self.write(path, payload, method)
        self.reads.append(path)
        if path == 'user':
            return {'id': ME, 'login': LOGINS[ME]}
        if path == 'commits/main':
            return {'sha': self.main}
        if path == 'rules/branches/main':
            return RULES
        if path.startswith('compare/'):
            head = path.split('...')[1]
            pr = next(p for p in self.prs.values() if p['head'] == head)
            return {'behind_by': pr['behind'], 'ahead_by': 1, 'status': 'diverged' if pr['behind'] else 'ahead'}
        if path.startswith('commits/') and '/check-runs' in path:
            head = path.split('/')[1]
            pr = next(p for p in self.prs.values() if p['head'] == head)
            status, conclusion = CHECK[self.rollup(self.ci_state(pr, head))[1]]
            return [{'total_count': 1, 'check_runs': [{'id': 1, 'name': 'build', 'head_sha': head,
                                                       'status': status.lower(), 'app': {'id': 15368},
                                                       'conclusion': (conclusion or '').lower() or None}]}]
        if path.startswith('actions/runs?head_sha='):
            return [{'total_count': 0, 'workflow_runs': []}]
        if path.startswith('pulls?state=closed'):
            return [[]]
        if path.endswith('/reviews?per_page=100'):
            return [deepcopy(self.prs[int(path.split('/')[1])]['reviews'])]
        if path.startswith('pulls/') and path.count('/') == 1:
            pr = self.prs[int(path.split('/')[1])]
            return {'number': pr['number'], 'state': pr['state'], 'merged': pr['merged'], 'draft': pr['draft'],
                    'user': {'id': pr['author'], 'login': LOGINS[pr['author']]},
                    'head': {'sha': pr['head'], 'ref': pr['head_ref']}, 'base': {'ref': pr['base_ref']},
                    'mergeable': pr['mergeable_state'] != 'dirty',
                    'mergeable_state': self.mergeable_state(pr),
                    'merge_commit_sha': pr['merge_commit']}
        raise RecordError('unexpected read ' + endpoint)

    @staticmethod
    def mergeable_state(pr):
        """As GitHub reports it here: conflicts first, then the ruleset's one required approval."""
        if pr['mergeable_state']:
            return pr['mergeable_state']
        if pr['behind']:
            return 'behind'
        approved = any(r['state'] == 'APPROVED' and r['user']['id'] != pr['author'] for r in pr['reviews'])
        return 'clean' if approved else 'blocked'

    def write(self, path, payload, method):
        number = int(path.split('/')[1])
        pr = self.prs[number]
        self.writes.append((method or 'POST', path, dict(payload)))
        hook = self.on_write.get(path)
        if hook:
            hook()
        if path.endswith('/update-branch'):
            if payload['expected_head_sha'] != pr['head']:
                raise HTTPError('GitHub operation failed; publication is unconfirmed', 422)
            pr['head'] = pr['update']['head']
            pr['ci'].setdefault(pr['head'], list(pr['update'].get('ci', ['success'])))
            pr['behind'] = 0
            return {'message': 'Updating pull request branch.'}
        if path.endswith('/reviews'):
            review = {'id': 900 + len(self.writes), 'user': {'id': ME, 'login': LOGINS[ME]}, 'state': 'APPROVED',
                      'commit_id': payload['commit_id'], 'html_url': f'https://github.com/{REPO}/pull/{number}#r'}
            pr['reviews'].append(review)
            return review
        if path.endswith('/merge'):
            if pr['merge_status']:
                raise HTTPError('GitHub operation failed; publication is unconfirmed', pr['merge_status'])
            if payload['sha'] != pr['head']:
                raise HTTPError('GitHub operation failed; publication is unconfirmed', 409)
            self.tick += 1
            pr.update(state='closed', merged=True, merge_commit=sha(f'm{self.tick}'))
            self.main = sha(f'n{self.tick}')
            for other in self.open():
                if other['base_ref'] == 'main':
                    other['behind'] += 1
            return {'merged': True, 'sha': pr['merge_commit']}
        if method == 'PATCH':
            pr['base_ref'] = payload['base']
            return {'number': number, 'base': {'ref': payload['base']}}
        raise AssertionError(path)


class MergeReadyTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-merge-ready-')
        self.addCleanup(temp.cleanup)
        self.prefs = OperatorPreferences(storage=temp.name)
        self.hub = Hub()
        self.t = 0.0

    def sleep(self, seconds):
        self.t += seconds

    def sweep(self, **options):
        hub = self.hub
        carry = lambda source, h1, h2, main, tooling: {'carried': hub.carry_ok.get(h2, True), 'from': h1, 'to': h2,
                                                       'via': ['merge'], 'reason': 'the PR\'s own change differs'}
        sweep = Sweep(PROJECT, POLICY, self.prefs, client=hub, reader=hub.reader, carry=carry, sleep=self.sleep,
                      clock=lambda: self.t, **options)
        return sweep.run()

    def outcomes(self, report):
        return {i['pr']: (i['outcome'], i['reason']) for i in report['items']}

    def test_the_dry_run_plans_without_writing(self):
        self.hub.add(1)
        self.hub.add(2, behind=3, update={'head': sha('f2')})
        report = self.sweep()
        self.assertEqual(self.hub.writes, [])
        self.assertEqual({i['pr']: i['actions'] for i in report['items']},
                         {1: ['would approve', 'would merge'], 2: ['would update', 'would approve', 'would merge']})
        text = '\n'.join(render(report))
        self.assertIn('dry run: nothing was written', text)
        self.assertIn('Summary: 2 would merge, 0 skipped', text)

    def test_apply_merges_two_serially_updating_the_second_after_the_first_lands(self):
        self.hub.add(1)
        self.hub.add(2, update={'head': sha('f2'), 'ci': ['pending', 'pending', 'success']})
        report = self.sweep(apply=True)
        self.assertEqual(self.outcomes(report), {1: ('merged', None), 2: ('merged', None)})
        kinds = [(m, p.rsplit('/', 1)[-1], p.split('/')[1]) for m, p, _ in self.hub.writes]
        self.assertEqual(kinds, [('POST', 'reviews', '1'), ('PUT', 'merge', '1'), ('PUT', 'update-branch', '2'),
                                 ('POST', 'reviews', '2'), ('PUT', 'merge', '2')])
        update, approve, merge = self.hub.writes[2:]
        self.assertEqual(update[2], {'expected_head_sha': sha('c2')})
        self.assertEqual(approve[2]['commit_id'], sha('f2'))  # pinned to the updated head
        self.assertIn(f"carried over from {sha('c2')[:7]}", approve[2]['body'])
        self.assertEqual(merge[2], {'merge_method': 'squash', 'sha': sha('f2')})
        self.assertEqual(report['counts'], {'updated': 1, 'approved': 2, 'merged': 2, 'planned': 0, 'skipped': 0})
        self.assertGreaterEqual(self.t, 120)  # it waited politely for CI on the new head

    def test_the_expected_scope_failure_posted_early_waits_for_every_check_then_merges(self):
        # Live, #113/#75/#112/#111/#165/#171: trusted-scope (the expected human-review failure) was
        # posted before trusted-build and trusted-merge finished, so the head read as "CI failed"
        # about four minutes after the update, and every updated PR was skipped.
        def status(context, state):
            return {'__typename': 'StatusContext', 'context': context, 'state': state,
                    'targetUrl': 'https://github.com/x/actions/runs/7/attempts/1'}

        def run(name, status_, conclusion):
            return {'__typename': 'CheckRun', 'name': name, 'status': status_, 'conclusion': conclusion,
                    'workflowName': 'CI' if name == 'build' else 'Trusted candidate'}
        scope = status('trusted-scope', 'FAILURE')
        early = [{'rollup': [scope, run('build', 'IN_PROGRESS', None), run('candidate', 'IN_PROGRESS', None)],
                  'build': 'pending'},
                 {'rollup': [scope, run('build', 'COMPLETED', 'SUCCESS'), run('candidate', 'COMPLETED', 'SUCCESS'),
                             status('trusted-build', 'PENDING')], 'build': 'success'}]
        done = {'rollup': [scope, run('build', 'COMPLETED', 'SUCCESS'), run('candidate', 'COMPLETED', 'SUCCESS'),
                           status('trusted-build', 'SUCCESS'), status('trusted-merge', 'SUCCESS')], 'build': 'success'}
        from unittest.mock import patch
        verdicts = []

        def scope_check(api, project, pr, check, settings):
            verdicts.append(pr['headRefOid'])  # only ever asked once every other check has passed
            return {'accepted': True, 'note': None}
        self.hub.add(2, behind=1, update={'head': sha('f2'), 'ci': [*early, done]})
        with patch('sphereceti.worker_checks.human_review_scope', side_effect=scope_check):
            report = self.sweep(apply=True)
        self.assertEqual(self.outcomes(report)[2], ('merged', None))
        self.assertEqual(verdicts, [sha('f2')])
        # Once everything has finished, a real failure is named, and an unauthenticated scope
        # exception is said as such.
        for final, rejected, reason in (
                ({**done, 'rollup': [*done['rollup'][:2], run('candidate', 'COMPLETED', 'FAILURE'),
                                     *done['rollup'][3:]]}, False, 'candidate failed'),
                (done, True, 'trusted-scope failed and its human-review exception could not be authenticated')):
            with self.subTest(reason=reason):
                self.hub = Hub()
                self.hub.add(2, behind=1, update={'head': sha('f2'), 'ci': [*early, final]})
                with patch('sphereceti.worker_checks.human_review_scope',
                           return_value=False if rejected else {'accepted': True, 'note': None}):
                    report = self.sweep(apply=True)
                outcome, why = self.outcomes(report)[2]
                self.assertEqual(outcome, 'skipped')
                self.assertIn(reason, why)

    def test_an_update_whose_record_does_not_carry_over_is_skipped(self):
        self.hub.add(2, behind=1, update={'head': sha('f2')})
        self.hub.carry_ok[sha('f2')] = False
        report = self.sweep(apply=True)
        outcome, reason = self.outcomes(report)[2]
        self.assertEqual(outcome, 'skipped')
        self.assertIn('needs a fresh review after update', reason)
        self.assertEqual([p.rsplit('/', 1)[-1] for _, p, _ in self.hub.writes], ['update-branch'])

    def test_a_ci_wait_times_out(self):
        self.hub.add(2, behind=1, update={'head': sha('f2'), 'ci': ['pending']})
        report = self.sweep(apply=True, wait_ci=5)
        outcome, reason = self.outcomes(report)[2]
        self.assertEqual(outcome, 'skipped')
        self.assertIn(f"CI still running on {sha('f2')[:7]} after 5m00s", reason)
        self.assertEqual(self.t, 300)
        self.assertEqual([p.rsplit('/', 1)[-1] for _, p, _ in self.hub.writes], ['update-branch'])

    def test_approvals_are_pinned_and_never_on_your_own_pr_or_over_your_change_request(self):
        self.hub.add(1, author=ME)  # yours, no other approval
        self.hub.add(2, reviews=[{'id': 5, 'user': {'id': ME}, 'state': 'CHANGES_REQUESTED', 'commit_id': sha('c2')}])
        self.hub.add(3, author=ME, reviews=[{'id': 6, 'user': {'id': DAVE}, 'state': 'APPROVED',
                                             'commit_id': sha('d3')}])
        report = self.sweep(apply=True)
        outcomes = self.outcomes(report)
        self.assertEqual(outcomes[1][0], 'skipped')
        self.assertIn("your own PR: it needs another maintainer's approval", outcomes[1][1])
        # Your own change request keeps #2 out of the candidates (as Ready to merge reports it).
        self.assertNotIn(2, outcomes)
        self.assertIn({'pr': 2, 'reason': f'changes requested by user:{ME}'},
                      [{k: i[k] for k in ('pr', 'reason')} for i in report['not_ready']])
        self.assertEqual(outcomes[3], ('merged', None))
        self.assertFalse([w for w in self.hub.writes if w[1].endswith('/reviews')])  # nothing approved

    def test_a_405_on_merge_is_reported_and_not_retried(self):
        self.hub.add(1, merge_status=405)
        self.hub.add(4)
        report = self.sweep(apply=True)
        outcome, reason = self.outcomes(report)[1]
        self.assertEqual(outcome, 'skipped')
        self.assertIn('GitHub refused the merge (HTTP 405)', reason)
        self.assertEqual(sum(1 for _, p, _ in self.hub.writes if p == 'pulls/1/merge'), 1)
        self.assertEqual(self.outcomes(report)[4], ('merged', None))  # and the sweep went on

    def test_a_live_review_elsewhere_pauses_then_stops_when_it_outlasts_the_wait(self):
        self.hub.add(1)
        other = self.hub.add(9, record=False, ci='pending')
        self.hub.comment_store[9] = [claim_comment(77, pr=9, head=other['head'])]
        report = self.sweep(apply=True, wait_review=3)
        self.assertEqual(report['stopped'], 'a review is in progress on #9; rerun later')
        self.assertFalse([w for w in self.hub.writes if w[1].endswith('/merge')])
        self.assertEqual(self.t, 180)
        # A review that finishes during the pause: the merge goes ahead.
        self.hub = Hub()
        self.hub.add(1)
        other = self.hub.add(9, record=False, ci='pending')
        self.hub.comment_store[9] = [claim_comment(77, pr=9, head=other['head'])]
        real_sleep = self.sleep

        def finish(seconds):
            real_sleep(seconds)
            self.hub.comment_store[9] = []
        self.sleep = finish
        report = self.sweep(apply=True, wait_review=30)
        self.assertEqual(self.outcomes(report)[1], ('merged', None))

    def test_a_head_that_moves_between_read_and_write_is_skipped(self):
        self.hub.add(1)
        self.hub.add(4)
        moved = lambda: self.hub.prs[1].update(head=sha('e9'))
        self.hub.on_write['pulls/1/reviews'] = moved
        report = self.sweep(apply=True)
        outcome, reason = self.outcomes(report)[1]
        self.assertEqual(outcome, 'skipped')
        self.assertIn('the head moved before the merge', reason)
        self.assertFalse([w for w in self.hub.writes if w[1] == 'pulls/1/merge'])
        self.assertEqual(self.outcomes(report)[4], ('merged', None))

    def test_stacked_children_are_reported_and_retargeted_only_with_the_flag(self):
        self.hub.add(1, head_ref='lattice')
        self.hub.add(5, base_ref='lattice', record=False)
        report = self.sweep(apply=True)
        self.assertEqual(report['children'], [{'pr': 5, 'parent': 1, 'branch': 'lattice', 'retargeted': False,
                                               'note': 'retarget to main (or rerun with --retarget-children)'}])
        self.assertFalse([w for w in self.hub.writes if w[0] == 'PATCH'])
        self.hub = Hub()
        self.hub.add(1, head_ref='lattice')
        self.hub.add(5, base_ref='lattice', record=False)
        report = self.sweep(apply=True, retarget=True)
        self.assertEqual([w for w in self.hub.writes if w[0] == 'PATCH'], [('PATCH', 'pulls/5', {'base': 'main'})])
        self.assertTrue(report['children'][0]['retargeted'])

    def test_stacked_draft_and_conflicting_prs_are_never_touched(self):
        self.hub.add(5, base_ref='lattice')
        self.hub.add(6, draft=True)
        self.hub.add(7, mergeable_state='dirty')
        report = self.sweep(apply=True)
        self.assertEqual(self.hub.writes, [])
        self.assertEqual(report['items'], [])  # none is a candidate at all

    def test_an_unexpected_error_stops_the_sweep(self):
        self.hub.add(1)
        self.hub.add(4)
        self.hub.fail_on = 'compare/'
        report = self.sweep(apply=True)
        self.assertTrue(report['stopped'].startswith('unexpected error on #1'))
        self.assertEqual(self.hub.writes, [])
        self.assertEqual([i['pr'] for i in report['items']], [1])  # nothing after it


if __name__ == '__main__':
    unittest.main()
