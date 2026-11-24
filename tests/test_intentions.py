"""Intention claims: comment parsing, assignment, expiry, and the issue-form contract. No network."""
from datetime import datetime, timedelta, timezone
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

# A trimmed issue_comment event, shaped as GitHub delivers it.
def event(body, *, login='alice', user_type='User', labels=('intention',), state='open',
          assignees=(), pull_request=None, comment_id=500):
    issue = {'number': 7, 'state': state, 'labels': [{'name': n} for n in labels],
             'assignees': [{'login': a} for a in assignees]}
    if pull_request:
        issue['pull_request'] = {'url': 'https://api.github.com/repos/o/r/pulls/7'}
    return {'action': 'created', 'issue': issue,
            'comment': {'id': comment_id, 'body': body, 'user': {'login': login, 'id': 11, 'type': user_type}}}


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


class FakeAPI:
    def __init__(self, comments=(), accept=True):
        self.existing = list(comments)
        self.posted, self.added, self.removed = [], [], []
        self.accept = accept
        self.issues = []

    def comments(self, number):
        return self.existing + [{'id': 1000 + n, 'user': BOT, 'body': b} for n, b in enumerate(self.posted)]

    def comment(self, number, body):
        self.posted.append(body)

    def add_assignee(self, number, login):
        self.added.append(login)
        return [login] if self.accept else []

    def remove_assignee(self, number, login):
        self.removed.append(login)

    def open_intentions(self):
        return self.issues


def marker(holder, expires, *, user=BOT, number=900):
    data = {'action': 'claim', 'holder': holder, 'expires': expires}
    return {'id': number, 'user': user, 'body': i.MARKER + json.dumps(data) + '-->\nclaimed'}


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
        api = FakeAPI()
        self.assertEqual(i.handle_comment(api, event('claim 3 weeks'), NOW), 'claimed')
        self.assertEqual(api.added, ['alice'])
        state = i.marker_state(api.comments(7))
        self.assertEqual(state, {'action': 'claim', 'holder': 'alice', 'holder_id': 11,
                                 'expires': '2026-12-15T12:00:00Z', 'comment': 500})
        self.assertIn('alice claimed this intention until **2026-12-15** (UTC).', api.posted[0])

    def test_holder_renews(self):
        api = FakeAPI([marker('alice', '2026-12-01T00:00:00Z')])
        self.assertEqual(i.handle_comment(api, event('claim 60 days', assignees=['alice']), NOW), 'renewed')
        self.assertEqual(i.marker_state(api.comments(7))['expires'], '2027-01-23T12:00:00Z')

    def test_someone_elses_active_claim_is_not_taken(self):
        api = FakeAPI([marker('bob', '2026-12-01T00:00:00Z')])
        self.assertEqual(i.handle_comment(api, event('claim', assignees=['bob']), NOW), 'refused')
        self.assertEqual((api.added, api.removed), ([], []))
        self.assertIn('bob holds this intention until 2026-12-01', api.posted[0])

    def test_expired_claim_can_be_taken_before_the_sweep(self):
        api = FakeAPI([marker('bob', '2026-11-01T00:00:00Z')])
        self.assertEqual(i.handle_comment(api, event('claim', assignees=['bob']), NOW), 'claimed')
        self.assertEqual((api.removed, api.added), (['bob'], ['alice']))

    def test_manually_unassigned_holder_no_longer_holds(self):
        api = FakeAPI([marker('bob', '2026-12-01T00:00:00Z')])
        self.assertEqual(i.handle_comment(api, event('claim'), NOW), 'claimed')

    def test_unclaim_only_by_the_holder(self):
        api = FakeAPI([marker('alice', '2026-12-01T00:00:00Z')])
        self.assertEqual(i.handle_comment(api, event('unclaim', login='bob', assignees=['alice']), NOW), 'refused')
        self.assertEqual(i.handle_comment(api, event('unclaim', assignees=['alice']), NOW), 'released')
        self.assertEqual(api.removed, ['alice'])
        self.assertIsNone(i.marker_state(api.comments(7))['holder'])
        self.assertEqual(i.handle_comment(FakeAPI(), event('disclaim'), NOW), 'refused')

    def test_rejected_assignment_is_still_recorded(self):
        api = FakeAPI(accept=False)
        self.assertEqual(i.handle_comment(api, event('claim'), NOW), 'claimed')
        self.assertIn('GitHub did not accept the assignment', api.posted[0])

    def test_invalid_command_explains_usage(self):
        api = FakeAPI()
        self.assertEqual(i.handle_comment(api, event('claim 6 months'), NOW), 'invalid')
        self.assertIn('Not changed: a claim lasts between 1 and 90 days.', api.posted[0])
        self.assertEqual(api.added, [])

    def test_ignored_events(self):
        cases = (event('claim', login='renovate[bot]', user_type='Bot'), event('claim', user_type='Bot'),
                 event('claim', labels=('enhancement',)), event('claim', state='closed'),
                 event('claim', pull_request=True), event('Looks good to me'))
        for item in cases:
            api = FakeAPI()
            with self.subTest(item=item['comment']['user'], issue=item['issue']):
                self.assertTrue(i.handle_comment(api, item, NOW).startswith('ignored'))
                self.assertEqual((api.posted, api.added, api.removed), ([], [], []))

    def test_only_this_workflows_markers_count(self):
        forged = marker('mallory', '2027-01-01T00:00:00Z', user={'login': 'mallory', 'type': 'User'}, number=950)
        api = FakeAPI([marker('bob', '2026-11-01T00:00:00Z'), forged])
        self.assertEqual(i.marker_state(api.comments(7))['holder'], 'bob')
        self.assertEqual(i.handle_comment(api, event('claim', assignees=['bob', 'mallory']), NOW), 'claimed')


class SweepTests(unittest.TestCase):
    def test_sweep_releases_only_expired_claims(self):
        api = FakeAPI()
        stores = {1: [marker('alice', '2026-11-20T00:00:00Z')], 2: [marker('bob', '2026-12-20T00:00:00Z')],
                  3: [], 4: [marker('carol', '2026-11-01T00:00:00Z')]}
        api.issues = [{'number': 1, 'assignees': [{'login': 'alice'}]}, {'number': 2, 'assignees': [{'login': 'bob'}]},
                      {'number': 3, 'assignees': []}, {'number': 4, 'assignees': []}]
        api.comments = lambda number: stores[number]
        self.assertEqual(i.sweep(api, NOW), [1])
        self.assertEqual(api.removed, ['alice'])
        self.assertIn('The claim by alice expired on 2026-11-20 and has been released.', api.posted[0])
        self.assertTrue(api.posted[0].startswith(i.MARKER + '{"action":"expire","expires":null,"holder":null'))

    def test_expiry_is_exact(self):
        just = marker('alice', i.stamp(NOW))
        self.assertTrue(i.holder([just], ['alice'], NOW)['expired'])
        self.assertFalse(i.holder([just], ['alice'], NOW - timedelta(seconds=1))['expired'])


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
        for required in ("contains(github.event.issue.labels.*.name, 'intention')",
                         "github.event.comment.user.type == 'User'", '!github.event.issue.pull_request',
                         'persist-credentials: false', 'sparse-checkout: scripts/intentions.py',
                         'run: python3 -I scripts/intentions.py "$MODE"'):
            with self.subTest(required=required):
                self.assertIn(required, text)

if __name__ == '__main__':
    unittest.main()
