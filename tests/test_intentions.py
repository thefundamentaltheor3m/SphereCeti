"""Intention claims: parsing, live-state decisions, write-then-replay races, expiry, and the form contract."""
from copy import deepcopy
from datetime import datetime, timedelta, timezone
from itertools import combinations
import json
from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import intentions as i

NOW = datetime(2026, 11, 24, 12, 0, tzinfo=timezone.utc)
BOT = {'login': 'github-actions[bot]', 'type': 'Bot', 'id': 41898282}
URL = 'https://github.com/thefundamentaltheor3m/SphereCeti/issues/7#issuecomment-'

# The body GitHub renders from .github/ISSUE_TEMPLATE/intention.yml.
ISSUE_BODY = """### Target declaration

```lean
theorem PeriodicSpherePacking.density_eq_card_div_covolume (P : PeriodicSpherePacking d) :
    P.density = P.numReps / covolume P.lattice
```

### Roadmap item or layer

D5, layer 4

### Parent PR

_No response_

### Intended module

SphereCeti/Packing/PeriodicDensity.lean

### Expected duration

3 weeks
"""


class FakeGitHub:
    """One live issue: comments get increasing IDs and timestamps; assignees are shared state."""
    def __init__(self, *, assignees=(), labels=('intention',), state='open', accept=True):
        self.data = {'number': 7, 'state': state, 'labels': [{'name': n} for n in labels]}
        self.assigned, self.items, self.next_id, self.clock = set(assignees), [], 1000, NOW
        self.accept, self.hooks = accept, {}

    def issue(self, number):
        return {**deepcopy(self.data), 'assignees': [{'login': a} for a in sorted(self.assigned)]}

    def issue_assignees(self, number):
        return sorted(self.assigned)

    def comments(self, number):
        return deepcopy(self.items)

    def post(self, body, user):
        self.next_id += 1
        self.clock += timedelta(seconds=1)
        self.items.append({'id': self.next_id, 'body': body, 'user': user, 'created_at': i.stamp(self.clock),
                           'html_url': URL + str(self.next_id)})
        return {'id': self.next_id}

    def comment(self, number, body):
        if 'before_write' in self.hooks and body.startswith(i.MARKER):
            self.hooks.pop('before_write')()
        posted = self.post(body, BOT)
        if 'after_write' in self.hooks and body.startswith(i.MARKER):
            self.hooks.pop('after_write')()
        return posted

    def add_assignee(self, number, login):
        if self.accept:
            self.assigned.add(login)
        return sorted(self.assigned)

    def remove_assignee(self, number, login):
        self.assigned.discard(login)

    def open_intentions(self):
        return [self.issue(7)]

    # Test helpers
    def say(self, login, body, *, association='NONE', user_type='User', stale_assignees=()):
        """A person's comment, and the event GitHub delivers for it (with possibly stale assignees)."""
        comment_id = self.post(body, {'login': login, 'id': 10 + len(login), 'type': user_type})['id']
        issue = {**deepcopy(self.data), 'assignees': [{'login': a} for a in stale_assignees]}
        return {'action': 'created', 'issue': issue,
                'comment': {'id': comment_id, 'body': body, 'author_association': association,
                            'user': {'login': login, 'id': 10 + len(login), 'type': user_type}}}

    def bot_texts(self):
        return [c['body'].split('-->\n', 1)[-1] for c in self.items if c['user'] == BOT]

    def holder(self):
        return i.fold(self.items)[0]['holder']


def seed(api, holder, expires):
    """An existing accepted claim marker written by the workflow."""
    api.comment(7, i.MARKER + json.dumps({'action': 'claim', 'holder': holder, 'expires': expires}) + '-->\nclaimed')
    api.assigned.add(holder)


class CommandParsingTests(unittest.TestCase):
    def test_commands_on_the_first_line(self):
        cases = {'claim': ('claim', 30), 'Claim': ('claim', 30), 'claim 3 weeks': ('claim', 21),
                 'claim 10d': ('claim', 10), 'claim 2 months': ('claim', 60), 'claim 1 week.': ('claim', 7),
                 'claim 90 days\nSplitting this into two PRs.': ('claim', 90),
                 'unclaim': ('unclaim', None), 'disclaim': ('unclaim', None)}
        for body, expected in cases.items():
            with self.subTest(body=body):
                self.assertEqual(i.parse_command(body), expected)

    def test_ordinary_comments_are_not_commands(self):
        for body in ('I will claim this tomorrow', 'claims are advisory', '> claim', 'Thanks!\nclaim', '', None):
            with self.subTest(body=body):
                self.assertIsNone(i.parse_command(body))

    def test_bad_durations_are_reported(self):
        for body, fragment in (('claim 4 months', 'between 1 and 90 days'), ('claim forever', 'cannot read'),
                               ('claim 0 days', 'between 1 and 90'), ('unclaim now', 'takes no argument'),
                               ('claim 5 minutes', 'cannot read')):
            with self.subTest(body=body):
                kind, reason = i.parse_command(body)
                self.assertEqual(kind, 'invalid')
                self.assertIn(fragment, reason)


class ClaimTests(unittest.TestCase):
    def test_claim_assigns_and_records_the_expiry(self):
        api = FakeGitHub()
        self.assertEqual(i.handle_comment(api, api.say('alice', 'claim 3 weeks'), NOW), 'claimed')
        self.assertEqual(api.assigned, {'alice'})
        state = i.fold(api.items)[0]
        self.assertEqual((state['holder'], state['expires']), ('alice', '2026-12-15T12:00:00Z'))
        self.assertIn('alice claimed this intention until **2026-12-15** (UTC).', api.bot_texts()[0])

    def test_holder_renews(self):
        api = FakeGitHub()
        seed(api, 'alice', '2026-12-01T00:00:00Z')
        self.assertEqual(i.handle_comment(api, api.say('alice', 'claim 60 days'), NOW), 'renewed')
        self.assertEqual(i.fold(api.items)[0]['expires'], '2027-01-23T12:00:00Z')

    def test_someone_elses_active_claim_is_refused_with_expiry_and_link(self):
        api = FakeGitHub()
        seed(api, 'bob', '2026-12-01T00:00:00Z')
        self.assertEqual(i.handle_comment(api, api.say('alice', 'claim'), NOW), 'refused')
        self.assertEqual(api.assigned, {'bob'})
        self.assertIn(f'Not changed: bob holds it until 2026-12-01 ({URL}1001).', api.bot_texts()[-1])

    def test_expired_claim_can_be_taken_before_the_sweep(self):
        api = FakeGitHub()
        seed(api, 'bob', '2026-11-01T00:00:00Z')
        self.assertEqual(i.handle_comment(api, api.say('alice', 'claim'), NOW), 'claimed')
        self.assertEqual((api.holder(), api.assigned), ('alice', {'alice'}))

    def test_unclaim_by_holder_or_maintainer_only(self):
        api = FakeGitHub()
        seed(api, 'alice', '2026-12-01T00:00:00Z')
        self.assertEqual(i.handle_comment(api, api.say('bob', 'unclaim'), NOW), 'refused')
        self.assertEqual(i.handle_comment(api, api.say('alice', 'unclaim'), NOW), 'released')
        self.assertEqual((api.holder(), api.assigned), (None, set()))
        self.assertEqual(i.handle_comment(api, api.say('alice', 'disclaim'), NOW), 'refused')
        seed(api, 'carol', '2026-12-01T00:00:00Z')
        self.assertEqual(i.handle_comment(api, api.say('dan', 'unclaim', association='COLLABORATOR'), NOW), 'released')
        self.assertEqual(api.assigned, set())

    def test_rejected_assignment_is_still_recorded(self):
        api = FakeGitHub(accept=False)
        self.assertEqual(i.handle_comment(api, api.say('alice', 'claim'), NOW), 'claimed')
        self.assertEqual(api.holder(), 'alice')
        self.assertIn('GitHub did not accept the assignment', api.bot_texts()[-1])

    def test_invalid_command_explains_usage(self):
        api = FakeGitHub()
        self.assertEqual(i.handle_comment(api, api.say('alice', 'claim 6 months'), NOW), 'invalid')
        self.assertIn('Not changed: a claim lasts between 1 and 90 days.', api.bot_texts()[0])
        self.assertEqual(api.assigned, set())

    def test_ignored_events_and_live_issue_state(self):
        for make, why in ((lambda a: a.say('renovate[bot]', 'claim', user_type='Bot'), 'person'),
                          (lambda a: a.say('alice', 'Looks good'), 'no command')):
            api = FakeGitHub()
            self.assertIn(why, i.handle_comment(api, make(api), NOW))
            self.assertEqual(api.bot_texts(), [])
        for api in (FakeGitHub(labels=('enhancement',)), FakeGitHub(state='closed')):
            event = api.say('alice', 'claim')
            event['issue'].update(state='open', labels=[{'name': 'intention'}])  # stale payload
            self.assertIn('not an open intention issue', i.handle_comment(api, event, NOW))
            self.assertEqual((api.bot_texts(), api.assigned), ([], set()))
        api = FakeGitHub()
        event = api.say('alice', 'claim')
        event['issue']['pull_request'] = {'url': 'x'}
        self.assertIn('person', i.handle_comment(api, event, NOW))

    def test_only_this_workflows_markers_count(self):
        api = FakeGitHub()
        seed(api, 'bob', '2026-11-01T00:00:00Z')
        api.post(i.MARKER + json.dumps({'action': 'claim', 'holder': 'mallory', 'expires': '2027-01-01T00:00:00Z'})
                 + '-->', {'login': 'mallory', 'type': 'User'})
        self.assertEqual(api.holder(), 'bob')
        self.assertEqual(i.handle_comment(api, api.say('alice', 'claim'), NOW), 'claimed')


class RaceTests(unittest.TestCase):
    """Concurrent jobs: each decides from live state, writes, re-reads; the marker order decides."""
    def run_interleaved(self, logins, order):
        api = FakeGitHub()
        events = {login: api.say(login, 'claim') for login in logins}  # every payload: zero assignees
        plans, marks, outcomes = {}, {}, {}
        for login, step in order:
            if step == 'decide':
                plans[login] = i.decide(api, events[login], NOW)
            elif step == 'write':
                if plans[login][0] == 'write':
                    marks[login] = i.write(api, 7, plans[login][1], plans[login][2])
            elif plans[login][0] == 'write':
                outcomes[login] = i.resolve(api, 7, plans[login], marks[login])
            else:
                api.comment(7, plans[login][2])
                outcomes[login] = plans[login][1]
        return api, outcomes

    def interleavings(self, logins):
        steps = ('decide', 'write', 'resolve')
        if len(logins) == 2:
            for slots in combinations(range(6), 3):
                order, a, b = [], iter(steps), iter(steps)
                for n in range(6):
                    order.append((logins[0], next(a)) if n in slots else (logins[1], next(b)))
                yield order
        else:  # all decide, all write, then resolve in every order of interest
            for resolve in (logins, logins[::-1], logins[1:] + logins[:1]):
                yield ([(l, 'decide') for l in logins] + [(l, 'write') for l in logins[::-1]]
                       + [(l, 'resolve') for l in resolve])

    def check_one_holder(self, api, outcomes, logins):
        holder = api.holder()
        self.assertIn(holder, logins)
        self.assertEqual(api.assigned, {holder})
        self.assertEqual(outcomes[holder], 'claimed')
        expires = i.fold(api.items)[0]['expires'][:10]
        for login in set(logins) - {holder}:
            self.assertIn(outcomes[login], ('lost', 'refused'))
            told = [t for t in api.bot_texts() if f'{holder} holds it until {expires} ({URL}' in t
                    and (login in t or t.startswith('Not changed'))]
            self.assertTrue(told, api.bot_texts())

    def test_two_claims_from_stale_empty_payloads_in_every_interleaving(self):
        for order in self.interleavings(['alice', 'bob']):
            with self.subTest(order=[f'{l[0]}:{s}' for l, s in order]):
                api, outcomes = self.run_interleaved(['alice', 'bob'], order)
                self.check_one_holder(api, outcomes, ['alice', 'bob'])

    def test_three_rapid_claims_lose_nothing_and_grant_once(self):
        logins = ['alice', 'bob', 'carol']
        for order in self.interleavings(logins):
            with self.subTest(order=order[-3:]):
                api, outcomes = self.run_interleaved(logins, order)
                self.assertEqual(set(outcomes), set(logins))  # every command answered
                self.check_one_holder(api, outcomes, logins)
                self.assertEqual(sum(t.startswith('Correction:') for t in api.bot_texts()), 2)

    def test_sweep_racing_a_renewal(self):
        late = NOW + timedelta(days=40)  # alice's claim has expired; she claims it again
        # The renewal lands between the sweep's read and its expire marker: the expiry is void.
        api = FakeGitHub()
        seed(api, 'alice', '2026-12-01T00:00:00Z')
        renew = api.say('alice', 'claim 30 days')
        api.hooks['before_write'] = lambda: self.assertEqual(i.handle_comment(api, renew, late), 'claimed')
        self.assertEqual(i.sweep(api, late), [])
        self.assertEqual((api.holder(), api.assigned), ('alice', {'alice'}))
        self.assertIn('Correction: the claim was renewed before it could expire', api.bot_texts()[-1])
        # The renewal decided on stale state and lands after the expire marker: it is a fresh claim.
        api = FakeGitHub()
        seed(api, 'alice', '2026-12-01T00:00:00Z')
        renew = api.say('alice', 'claim 30 days')
        plan = i.decide(api, renew, late)
        api.hooks['after_write'] = lambda: self.assertEqual(
            i.resolve(api, 7, plan, i.write(api, 7, plan[1], plan[2])), 'claimed')
        i.sweep(api, late)
        self.assertEqual((api.holder(), api.assigned), ('alice', {'alice'}))
        self.assertEqual(i.fold(api.items)[0]['expires'], i.stamp(late + timedelta(days=30)))


class SweepTests(unittest.TestCase):
    def test_sweep_releases_an_expired_claim(self):
        api = FakeGitHub()
        seed(api, 'alice', '2026-11-20T00:00:00Z')
        self.assertEqual(i.sweep(api, NOW), [7])
        self.assertEqual((api.holder(), api.assigned), (None, set()))
        self.assertIn('The claim by alice expired on 2026-11-20 and has been released.', api.bot_texts()[-1])
        self.assertEqual(i.sweep(api, NOW), [])

    def test_sweep_keeps_active_claims_and_heals_the_mirror(self):
        api = FakeGitHub()
        seed(api, 'bob', '2026-12-20T00:00:00Z')
        api.assigned.clear()
        self.assertEqual(i.sweep(api, NOW), [])
        self.assertEqual(api.assigned, {'bob'})

    def test_expiry_is_exact(self):
        api = FakeGitHub()
        seed(api, 'alice', i.stamp(NOW))
        self.assertEqual(i.sweep(api, NOW - timedelta(seconds=1)), [])
        self.assertEqual(i.sweep(api, NOW), [7])


class IssueFormContractTests(unittest.TestCase):
    def test_rendered_body_parses_by_form_id(self):
        self.assertEqual(i.parse_intention(ISSUE_BODY), {
            'target': 'theorem PeriodicSpherePacking.density_eq_card_div_covolume (P : PeriodicSpherePacking d) :\n'
                      '    P.density = P.numReps / covolume P.lattice',
            'roadmap_item': 'D5, layer 4', 'parent_pr': None,
            'module': 'SphereCeti/Packing/PeriodicDensity.lean', 'duration': '3 weeks'})
        self.assertEqual(i.parse_intention('free text'), dict.fromkeys(i.FIELDS.values()))

    def test_form_fields_match_the_parser(self):
        # Plain-text checks: the suite runs without PyYAML.
        form = (ROOT / '.github/ISSUE_TEMPLATE/intention.yml').read_text()
        self.assertIn(f'labels: ["{i.LABEL}"]', form)
        fields = dict((label, key) for key, label in
                      re.findall(r'^    id: (\w+)\n    attributes:\n      label: (.+)$', form, re.M))
        self.assertEqual(fields, i.FIELDS)
        self.assertIn('render: lean', form)

    def test_workflow_is_token_only_and_never_interpolates_comment_text(self):
        text = (ROOT / '.github/workflows/intentions.yml').read_text()
        self.assertIn('\npermissions: {}\n', text)
        self.assertIn('    permissions:\n      contents: read\n      issues: write\n', text)
        self.assertEqual(text.count('permissions:'), 2)
        for forbidden in ('comment.body', 'secrets.', 'pull_request_target', 'issue.title', 'issue.body'):
            with self.subTest(forbidden=forbidden):
                self.assertNotIn(forbidden, text)
        # A concurrency group would let GitHub cancel a pending job, dropping a command.
        self.assertNotIn('concurrency:', text)
        for required in ("contains(github.event.issue.labels.*.name, 'intention')",
                         "github.event.comment.user.type == 'User'", '!github.event.issue.pull_request',
                         'persist-credentials: false', 'sparse-checkout: scripts/intentions.py',
                         'run: python3 -I scripts/intentions.py "$MODE"'):
            with self.subTest(required=required):
                self.assertIn(required, text)

if __name__ == '__main__':
    unittest.main()
