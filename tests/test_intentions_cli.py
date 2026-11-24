# SPDX-License-Identifier: Apache-2.0
"""`sphereceti intentions` / `intend`: claims beside open proof PRs, exact matching, registration."""
import base64
import copy
from datetime import datetime, timedelta, timezone
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import parse_project, resource_text
import threading

from sphereceti.intentions import (LOOKUP_SCHEMA, MARKER, SCHEMA, RegistrationRefused, added_lines,
                                   declarations, issue_body, lookup, observe, parse_fields, render,
                                   render_lookup, render_registration)
from sphereceti.intentions import register as _register


def register(*args, **kwargs):
    """No real waiting between confirm reads in tests."""
    return _register(*args, **{'delay': 0, **kwargs})
from sphereceti.review_records import RecordError

ROOT = Path(__file__).resolve().parents[1]
PROJECT = parse_project(resource_text('sphereceti.toml'))
REPO = PROJECT.repository
NOW = datetime.now(timezone.utc)
FUTURE = (NOW + timedelta(days=7)).strftime('%Y-%m-%dT%H:%M:%SZ')
PAST = (NOW - timedelta(days=2)).strftime('%Y-%m-%dT%H:%M:%SZ')

# #134's rendered-form fixture (tests/test_intentions.py ISSUE_BODY at 89aefc1), copied verbatim.
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
ISSUE_FIELDS = {'target': 'theorem PeriodicSpherePacking.density_eq_card_div_covolume (P : PeriodicSpherePacking d) :\n'
                          '    P.density = P.numReps / covolume P.lattice',
                'roadmap_item': 'D5, layer 4', 'parent_pr': None,
                'module': 'SphereCeti/Packing/PeriodicDensity.lean', 'duration': '3 weeks'}


def marker(cid, holder, expires, *, by='github-actions[bot]', kind='Bot', action='claim', at=None, **extra):
    """A marker comment in #134's shape (written by its workflow at `at`)."""
    data = {'action': action, 'comment': cid - 1, 'expires': expires, 'holder': holder, 'holder_id': 9, **extra}
    return {'id': cid, 'user': {'login': by, 'type': kind}, 'created_at': at or '2026-11-20T10:00:00Z',
            'body': MARKER + json.dumps(data, sort_keys=True, separators=(',', ':')) + f'-->\n{action}'}

LINTEGRAL = '''module

public import Mathlib.MeasureTheory.Group.LIntegral

/-! # Counting points of a set in translates

`theorem not_a_declaration` in a docstring.
-/

namespace MeasureTheory

variable {G : Type*}

theorem lintegral_encard_inter_vadd (x : G) : True := trivial

-- lemma commented_out : True := trivial

theorem exists_encard_mul_le_encard_inter_vadd_mul : True := trivial

end MeasureTheory
'''
BOX_OLD = '''namespace EuclideanSpace

theorem norm_le_of_mem_centeredBox : True := trivial

end EuclideanSpace
'''
BOX_NEW = '''namespace EuclideanSpace

theorem norm_le_of_mem_centeredBox : True := trivial

section Averaging

theorem exists_encard_mul_volume_centeredBox_le : True := trivial

instance : Inhabited Unit := ⟨()⟩

protected noncomputable def averaged : Nat := 0

theorem _root_.volume_closedBall_ratio : True := trivial

end Averaging

end EuclideanSpace
'''


def patch_for(old, new):
    """A one-hunk unified diff adding every line of `new` not in `old` (enough for the fixtures)."""
    lines = new.splitlines()
    body = [('+' if line not in old.splitlines() else ' ') + line for line in lines]
    return f"@@ -1,{len(old.splitlines())} +1,{len(lines)} @@\n" + "\n".join(body)


def pr(number, title, path, source, *, status='added', old='', body='', author='CBirkbeck', head=None):
    head = head or f'{number:040x}'
    patch = patch_for(old, source) if status != 'added' else '@@ -0,0 +1 @@\n' + '\n'.join('+' + l for l in source.splitlines())
    return {'pr': {'number': number, 'title': title, 'body': body, 'user': {'login': author}, 'draft': False,
                   'html_url': f'https://github.com/{REPO}/pull/{number}', 'head': {'sha': head}},
            'files': [{'filename': path, 'status': status, 'patch': patch},
                      {'filename': 'SphereCeti.lean', 'status': 'modified', 'patch': '@@ -1 +1,2 @@\n+public import X'}],
            'contents': {f'{path}?ref={head}': source}}


def form_issue(number, *, target=None, item='D5', module='SphereCeti/Packing/X.lean', holders=('alice',),
               labels=('intention',), body=None):
    return {'number': number, 'title': f'[Intention]: {number}', 'html_url': f'https://github.com/{REPO}/issues/{number}',
            'body': body or issue_body(target, item, module, None, None),
            'assignees': [{'login': h} for h in holders], 'labels': [{'name': l} for l in labels]}


def d5_world():
    return {
        'issues': [form_issue(200, target='theorem EuclideanSpace.periodicRepetition_card (n : ℕ) :\n    True'),
                   form_issue(201, target='Foo.bar', item='A1', holders=('bob',)),
                   form_issue(203, body=ISSUE_BODY, holders=(), labels=()),  # form body, label not applied
                   {'number': 202, 'title': 'An ordinary bug', 'body': 'Nothing to see', 'assignees': [], 'labels': [],
                    'html_url': f'https://github.com/{REPO}/issues/202'}],
        'prs': [pr(105, 'Count the points of a finite set in the translates of a set (Layer 3, D5 averaging step)',
                   'SphereCeti/MeasureTheory/Group/LIntegral.lean', LINTEGRAL),
                pr(112, 'Average a finite point set over translates of a coordinate box (Layer 3, D5 averaging)',
                   'SphereCeti/MeasureTheory/Measure/Haar/BoxAveraging.lean', BOX_NEW, status='modified',
                   old=BOX_OLD),
                {'pr': {'number': 98, 'title': 'Docs only', 'body': '', 'user': {'login': 'x'}, 'draft': False,
                        'html_url': '', 'head': {'sha': 'f' * 40}},
                 'files': [{'filename': 'CONTRIBUTING.md', 'status': 'modified', 'patch': '@@ -1 +1 @@\n+x'}],
                 'contents': {}}],
        'comments': {'200': [marker(5, 'alice', FUTURE)],
                     '201': [marker(6, 'bob', PAST)],
                     '203': [marker(7, 'mallory', FUTURE, by='mallory', kind='User')]},  # forged: ignored
    }


class FakeClient:
    """GitHub's REST shapes, in memory. `on_create` runs just before a new issue is stored."""

    LOCK = threading.RLock()  # two callers in two threads share one world

    def __init__(self, world, fail=None):
        self.world, self.fail, self.calls, self.on_create = world, fail, [], None
        self.hidden = {}        # issue number -> listings that still miss it (eventual consistency)
        self.after_create = None

    def call(self, endpoint, *, payload=None, paginate=False, method=None):
        creating = bool(payload) and endpoint == f'repos/{REPO}/issues'
        if creating and self.on_create:  # outside the lock, so the other caller can proceed
            hook, self.on_create = self.on_create, None
            hook()
        with self.LOCK:
            value = self._call(endpoint, payload=payload, paginate=paginate, method=method)
        if creating and self.after_create:
            self.after_create()
        return value

    def _call(self, endpoint, *, payload=None, paginate=False, method=None):
        self.calls.append((method or ('POST' if payload else 'GET'), endpoint, payload))
        if self.fail and self.fail in endpoint:
            raise RecordError('GitHub operation failed; publication is unconfirmed')
        prefix = f'repos/{REPO}/'
        path = endpoint[len(prefix):]
        prs = {p['pr']['number']: p for p in self.world['prs']}
        if path == 'issues?state=open&per_page=100':
            listed = []
            for issue in self.world['issues']:
                if issue.get('state', 'open') != 'open':
                    continue
                if self.hidden.get(issue['number'], 0) > 0:
                    self.hidden[issue['number']] -= 1
                    continue
                listed.append(copy.deepcopy(issue))
            return [listed]
        if path == 'pulls?state=open&per_page=100':
            return [[p['pr'] for p in self.world['prs']]]
        if path.startswith('pulls/') and path.endswith('/files?per_page=100'):
            return [prs[int(path.split('/')[1])]['files']]
        if path.startswith('contents/'):
            key = path[len('contents/'):]
            source = next(p['contents'][key] for p in self.world['prs'] if key in p['contents'])
            return {'encoding': 'base64', 'content': base64.b64encode(source.encode()).decode()}
        if path.startswith('issues/') and path.endswith('/comments?per_page=100'):
            return [list(self.world['comments'].get(path.split('/')[1], []))]
        if path == 'issues' and payload:
            number = max([i['number'] for i in self.world['issues']] + [300]) + 1
            for other, misses in self.world.get('hide_new', {}).items():  # the other caller's view
                if other is not self:
                    other.hidden[number] = misses
            issue = {'number': number, 'title': payload['title'], 'body': payload['body'], 'assignees': [],
                     'labels': [], 'html_url': f'https://github.com/{REPO}/issues/{number}'}
            self.world['issues'].append(issue)  # labels dropped, as for contributors without triage rights
            return dict(issue)
        if path.startswith('issues/') and path.endswith('/comments') and payload:
            comment = {'id': 900 + len(self.calls), 'body': payload['body'], 'user': {'login': 'me', 'type': 'User'}}
            self.world['comments'].setdefault(path.split('/')[1], []).append(comment)
            return comment
        if path.startswith('issues/') and method == 'PATCH':
            issue = next(i for i in self.world['issues'] if i['number'] == int(path.split('/')[1]))
            issue.update(payload)
            return dict(issue)
        raise AssertionError(endpoint)

    def writes(self):
        return [c for c in self.calls if c[0] != 'GET']


class DeclarationTest(unittest.TestCase):
    def test_added_declarations_resolve_namespaces_sections_and_root(self):
        self.assertEqual(declarations(LINTEGRAL), ['MeasureTheory.lintegral_encard_inter_vadd',
                                                   'MeasureTheory.exists_encard_mul_le_encard_inter_vadd_mul'])
        lines = added_lines(patch_for(BOX_OLD, BOX_NEW))
        self.assertEqual(declarations(BOX_NEW, lines), ['EuclideanSpace.exists_encard_mul_volume_centeredBox_le',
                                                        'EuclideanSpace.averaged', 'volume_closedBall_ratio'])


class FormatContractTest(unittest.TestCase):
    def test_parser_mirrors_134_on_its_rendered_form_fixture(self):
        self.assertEqual(parse_fields(ISSUE_BODY), ISSUE_FIELDS)
        self.assertEqual(parse_fields('free text'), dict.fromkeys(ISSUE_FIELDS))
        # The CLI writes #134's layout: the target in a ```lean block, `_No response_` when empty.
        written = issue_body(ISSUE_FIELDS['target'], 'D5, layer 4', ISSUE_FIELDS['module'], None, '3 weeks')
        self.assertEqual(written, ISSUE_BODY)
        script = ROOT / 'scripts' / 'intentions.py'
        if script.is_file():  # once #134 has landed, both parsers must agree on its fixture
            import importlib.util
            spec = importlib.util.spec_from_file_location('workflow_intentions', script)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            self.assertEqual(module.parse_intention(ISSUE_BODY), parse_fields(ISSUE_BODY))
            self.assertEqual(module.MARKER, MARKER)


T0, T1, T2, T3 = '2026-11-01T00:00:00Z', '2026-11-02T00:00:00Z', '2026-11-20T00:00:00Z', '2026-12-05T00:00:00Z'
E1, E2 = '2026-12-01T00:00:00Z', '2026-12-31T00:00:00Z'
SEQUENCES = {
    # Bob's claim lands while Alice's is live: its marker exists but does not take effect.
    'lost claim': ([marker(10, 'alice', E1, at=T0), marker(11, 'bob', E2, at=T1)],
                   ('alice', E1), {10: True, 11: False}),
    'renewal': ([marker(10, 'alice', E1, at=T0), marker(11, 'alice', E2, at=T2, action='renew')],
                ('alice', E2), {10: True, 11: True}),
    # A sweep that observed the old expiry loses to a renewal written before it.
    'expire vs renew': ([marker(10, 'alice', E1, at=T0), marker(11, 'alice', E2, at=T2, action='renew'),
                         marker(12, None, None, at=T3, action='expire', released='alice', observed=E1)],
                        ('alice', E2), {10: True, 11: True, 12: False}),
    'expire applies': ([marker(10, 'alice', E1, at=T0),
                        marker(12, None, None, at=T3, action='expire', released='alice', observed=E1)],
                       (None, None), {10: True, 12: True}),
    'release by holder': ([marker(10, 'alice', E1, at=T0), marker(11, None, None, at=T1, action='release',
                                                                    released='bob'),
                           marker(12, None, None, at=T2, action='release', released='alice')],
                          (None, None), {10: True, 11: False, 12: True}),
    'claim after expiry': ([marker(10, 'alice', E1, at=T0), marker(11, 'bob', E2, at=T3)],
                           ('bob', E2), {10: True, 11: True}),
}


class FoldTest(unittest.TestCase):
    """The CLI replays #134's markers exactly as #134's `fold` does; a latest-marker reader would not."""

    def test_replay_matches_134_on_scripted_marker_sequences(self):
        from sphereceti.intentions import fold
        theirs = None
        script = ROOT / 'scripts' / 'intentions.py'
        if script.is_file():  # once #134 has landed
            import importlib.util
            spec = importlib.util.spec_from_file_location('workflow_intentions', script)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            theirs = getattr(module, 'fold', None)
        for name, (comments, (holder, expires), accepted) in SEQUENCES.items():
            with self.subTest(name):
                forged = dict(marker(99, 'mallory', E2, at=T1), user={'login': 'mallory', 'type': 'User'})
                state, ok = fold(comments + [forged])
                self.assertEqual((state['holder'], state['expires']), (holder, expires))
                self.assertEqual(ok, accepted)
                if theirs:
                    their_state, their_ok = theirs(comments + [forged])
                    self.assertEqual((their_state['holder'], their_state['expires'], their_ok),
                                     (state['holder'], state['expires'], ok))

    def test_the_lost_claimant_is_not_reported_as_holder_even_if_assigned(self):
        comments, _, _ = SEQUENCES['lost claim']
        issue = form_issue(260, target='X.y', holders=('bob',))  # a stale mirror
        world = {'issues': [issue], 'prs': [], 'comments': {'260': comments}}
        [found] = observe(PROJECT, client=FakeClient(world), now=datetime(2026, 11, 3, tzinfo=timezone.utc))['intentions']
        self.assertEqual((found['holders'], found['state']), (['alice'], 'claimed'))


class LookupTest(unittest.TestCase):
    def setUp(self):
        self.world = d5_world()
        self.client = FakeClient(self.world)
        self.observed = observe(PROJECT, client=self.client, now=NOW)

    def look(self, target, **kwargs):
        return lookup(PROJECT, target, observed=self.observed, **kwargs)

    def test_observation_lists_intentions_beside_proof_prs_grouped_by_item(self):
        self.assertEqual(self.observed['schema'], SCHEMA)
        self.assertEqual([i['number'] for i in self.observed['intentions']], [200, 201, 203])  # not the bug #202
        self.assertEqual([p['number'] for p in self.observed['pull_requests']], [105, 112])  # #98 has no module
        d5 = next(g for g in self.observed['groups'] if g['key'] == 'D5')
        self.assertEqual((d5['intentions'], d5['pull_requests']), ([200, 203], [105, 112]))
        form = next(i for i in self.observed['intentions'] if i['number'] == 203)
        self.assertEqual((form['declarations'], form['items'], form['layers'], form['state']),
                         (['PeriodicSpherePacking.density_eq_card_div_covolume'], ['D5'], ['4'], 'unclaimed'))
        text = render(self.observed)
        self.assertIn('Roadmap item D5:', text)
        self.assertIn(f'intention #200 claimed by alice until {FUTURE[:10]}: EuclideanSpace.periodicRepetition_card', text)
        self.assertIn(f'intention #201 EXPIRED claim by bob (expired {PAST[:10]}): Foo.bar', text)
        self.assertIn('intention #203 registered, unclaimed', text)  # mallory's forged marker is ignored

    def test_exact_match_on_an_intention(self):
        result = self.look('EuclideanSpace.periodicRepetition_card')
        self.assertEqual((result['verdict'], [w['number'] for w in result['claimed']]), ('claimed', [200]))
        self.assertTrue(render_lookup(result).startswith('Already claimed: declaration '))
        self.assertIn(f'https://github.com/{REPO}/issues/200', render_lookup(result))
        # Registered but unclaimed still blocks its exact target.
        self.assertEqual(self.look('PeriodicSpherePacking.density_eq_card_div_covolume')['verdict'], 'claimed')

    def test_exact_match_on_an_open_prs_added_declaration_even_unqualified(self):
        for target in ('lintegral_encard_inter_vadd', 'MeasureTheory.lintegral_encard_inter_vadd'):
            result = self.look(target)
            self.assertEqual((result['verdict'], [w['number'] for w in result['claimed']]), ('claimed', [105]))
        self.assertEqual(self.look('encard_inter_vadd')['verdict'], 'no_exact_claim')  # a suffix is not a name

    def test_same_item_different_lemma_is_related_not_claimed(self):
        result = self.look('EuclideanSpace.box_average_tendsto', item='D5')
        self.assertEqual(result['verdict'], 'no_exact_claim')
        self.assertEqual(sorted(w['number'] for w in result['related']), [105, 112, 200, 203])
        text = render_lookup(result)
        self.assertTrue(text.startswith('No exact claim found for declaration EuclideanSpace.box_average_tendsto.'))
        self.assertIn('Related open PRs and intentions', text)
        item = self.look('D5')
        self.assertEqual((item['kind'], item['verdict'], len(item['related'])), ('item', 'no_exact_claim', 4))
        self.assertIn('target=EuclideanSpace.box_average_tendsto', result['register_url'])
        self.assertIn('template=intention.yml', result['register_url'])

    def test_nothing_related_never_says_free(self):
        result = self.look('Totally.unrelated_lemma')
        text = render_lookup(result)
        self.assertEqual(result['verdict'], 'no_exact_claim')
        self.assertNotIn('free', text.lower())
        self.assertIn('No exact claim found for declaration Totally.unrelated_lemma.', text)
        self.assertIn('issues/new?template=intention.yml', text)
        self.assertEqual(set(result), {'schema', 'repository', 'target', 'kind', 'item', 'module', 'verdict',
                                       'claimed', 'related', 'register_url', 'observed_at', 'registration'})
        self.assertEqual(result['schema'], LOOKUP_SCHEMA)

    def test_expired_claims_are_shown_expired_and_do_not_block(self):
        result = self.look('Foo.bar')
        self.assertEqual(result['verdict'], 'no_exact_claim')
        self.assertEqual([(w['number'], w['state']) for w in result['related']], [(201, 'expired')])

    def test_a_failed_lookup_raises_and_never_reports_no_claim(self):
        for endpoint in ('issues?state=open', '/comments?per_page', 'pulls?state=open', '/files', 'contents/'):
            with self.subTest(endpoint=endpoint), self.assertRaises(RecordError):
                lookup(PROJECT, 'X.y', client=FakeClient(d5_world(), fail=endpoint))


class RegisterTest(unittest.TestCase):
    MODULE = 'SphereCeti/MeasureTheory/Measure/Haar/BoxAveraging.lean'

    def setUp(self):
        self.world = d5_world()

    def client(self):
        return FakeClient(self.world)

    def start(self, client, target, **kwargs):
        return lookup(PROJECT, target, client=client, **{'item': 'D5', 'module': self.MODULE, **kwargs})

    def test_register_creates_134s_issue_comments_claim_and_lists_like_a_form_issue(self):
        client = self.client()
        result = self.start(client, 'EuclideanSpace.box_average_tendsto')
        outcome = register(PROJECT, result, client=client, parent=112, duration='3 weeks', now=NOW)
        self.assertEqual(outcome['state'], 'registered')
        number = outcome['issue']['number']
        [(_, create, payload), (_, comment, claim)] = client.writes()
        self.assertEqual((create, payload['title'], payload['labels']),
                         (f'repos/{REPO}/issues', '[Intention]: EuclideanSpace.box_average_tendsto', ['intention']))
        self.assertEqual(payload['body'], issue_body('EuclideanSpace.box_average_tendsto', 'D5', self.MODULE, 112,
                                                     '3 weeks'))
        self.assertIn('### Target declaration\n\n```lean\nEuclideanSpace.box_average_tendsto\n```', payload['body'])
        self.assertEqual((comment, claim), (f'repos/{REPO}/issues/{number}/comments', {'body': 'claim 3 weeks'}))
        # The created issue (unlabelled, as for a contributor without triage rights) parses like the
        # form-filed #203, and its exact target is now claimed for everyone else.
        again = self.start(self.client(), 'EuclideanSpace.box_average_tendsto')
        self.assertEqual([w['number'] for w in again['claimed']], [number])
        listed = {i['number']: i for i in observe(PROJECT, client=self.client(), now=NOW)['intentions']}
        self.assertEqual(set(listed[203]), set(listed[number]))
        self.assertEqual(listed[number]['parent_pr'], 112)

    def test_near_simultaneous_same_declaration_race_the_second_sees_the_first(self):
        # Both looked and saw no exact claim. A registers first; B's pre-check sees A's issue, even
        # before #134's workflow has assigned A, and writes nothing.
        a_client, b_client = self.client(), self.client()
        a = self.start(a_client, 'EuclideanSpace.box_average_tendsto')
        b = self.start(b_client, 'EuclideanSpace.box_average_tendsto')
        first = register(PROJECT, a, client=a_client, now=NOW)
        self.assertEqual(first['state'], 'registered')
        lost = register(PROJECT, b, client=b_client, now=NOW)
        self.assertEqual(lost['state'], 'claimed')
        self.assertEqual(lost['winner']['url'], first['issue']['url'])
        self.assertEqual(b_client.writes(), [])
        # Truly simultaneous: A's issue lands between B's pre-check and B's creation.
        world = d5_world()
        b_client = FakeClient(world)
        b = lookup(PROJECT, 'EuclideanSpace.other_lemma', client=b_client, item='D5', module=self.MODULE)
        rival = form_issue(250, target='EuclideanSpace.other_lemma', holders=())
        b_client.on_create = lambda: world['issues'].append(rival)
        lost = register(PROJECT, b, client=b_client, now=NOW)
        self.assertEqual(lost['state'], 'lost_race')
        self.assertEqual((lost['winner']['number'], lost['winner']['url']), (250, f'https://github.com/{REPO}/issues/250'))
        mine = lost['issue']['number']
        self.assertEqual([(m, e) for m, e, _ in b_client.writes()],
                         [('POST', f'repos/{REPO}/issues'), ('POST', f'repos/{REPO}/issues/{mine}/comments'),
                          ('PATCH', f'repos/{REPO}/issues/{mine}')])  # only our own duplicate, and no `claim`
        self.assertIn('Duplicate of #250', b_client.writes()[1][2]['body'])
        self.assertIn('Lost the race: intention #250', render_lookup({**b, 'registration': lost}))

    def test_an_expired_intention_is_claimed_in_place_not_duplicated(self):
        client = self.client()
        result = lookup(PROJECT, 'Foo.bar', client=client, item='A1', module='SphereCeti/Packing/X.lean')
        outcome = register(PROJECT, result, client=client, now=NOW)
        self.assertEqual((outcome['state'], outcome['issue']['number']), ('claim_requested', 201))
        self.assertEqual([(e, p) for _, e, p in client.writes()], [(f'repos/{REPO}/issues/201/comments', {'body': 'claim'})])

    def test_distinct_d5_lemmas_both_go_through(self):
        first, second = self.client(), self.client()
        a = self.start(first, 'EuclideanSpace.box_average_tendsto')
        b = self.start(second, 'EuclideanSpace.periodic_density_limit')
        self.assertEqual(register(PROJECT, a, client=first, now=NOW)['state'], 'registered')
        self.assertEqual(register(PROJECT, b, client=second, now=NOW)['state'], 'registered')
        listed = observe(PROJECT, client=self.client(), now=NOW)['intentions']
        self.assertEqual(len([i for i in listed if 'D5' in i['items']]), 4)

    def test_no_write_on_dry_run_claim_refusal_or_lookup_failure(self):
        client = self.client()
        result = self.start(client, 'EuclideanSpace.box_average_tendsto')
        dry = register(PROJECT, result, client=client, dry_run=True, now=NOW)
        self.assertEqual((dry['state'], dry['claim']), ('dry_run', 'claim'))
        claimed = self.start(client, 'lintegral_encard_inter_vadd')
        self.assertEqual(register(PROJECT, claimed, client=client, now=NOW)['state'], 'claimed')
        with self.assertRaises(RegistrationRefused):  # the form requires an item and a module
            register(PROJECT, lookup(PROJECT, 'X.y', client=client), client=client, now=NOW)
        self.assertEqual(client.writes(), [])
        failing = FakeClient(self.world, fail='issues?state=open')
        with self.assertRaises(RecordError):
            register(PROJECT, result, client=failing, now=NOW)  # the pre-check read fails
        self.assertEqual(failing.writes(), [])


class ConcurrentRegistrationTest(unittest.TestCase):
    """Both initial lookups are empty; scripted interleavings must end on ONE open intention."""
    TARGET = 'EuclideanSpace.box_average_tendsto'
    MODULE = 'SphereCeti/MeasureTheory/Measure/Haar/BoxAveraging.lean'

    def setUp(self):
        self.world = d5_world()
        self.a, self.b = FakeClient(self.world), FakeClient(self.world)
        self.a_start = lookup(PROJECT, self.TARGET, client=self.a, item='D5', module=self.MODULE)
        self.b_start = lookup(PROJECT, self.TARGET, client=self.b, item='D5', module=self.MODULE)
        self.assertEqual((self.a_start['verdict'], self.b_start['verdict']), ('no_exact_claim', 'no_exact_claim'))

    def open_intentions_for_target(self):
        return [i['number'] for i in self.world['issues'] if i.get('state', 'open') == 'open'
                and self.TARGET in (i.get('body') or '')]

    def claims(self, number):
        return [c['body'] for c in self.world['comments'].get(str(number), []) if c['body'] in ('claim', 'unclaim')]

    def assert_converged(self, outcomes):
        [winner] = self.open_intentions_for_target()
        links = set()
        for outcome in outcomes:
            if outcome['state'] == 'registered':
                links.add(outcome['issue']['number'])
            elif outcome['state'] in ('lost_race', 'claimed'):
                links.add(outcome['winner']['number'])
            else:
                self.fail(outcome)
        self.assertEqual(links, {winner})            # both callers point to the same intention
        self.assertEqual(self.claims(winner), ['claim'])
        return winner

    def run_both(self, a, b):
        results = {}
        threads = [threading.Thread(target=lambda key, f: results.__setitem__(key, f()), args=(k, f))
                   for k, f in (('a', a), ('b', b))]
        for t in threads:
            t.start()
        for t in threads:
            t.join(30)
        return results['a'], results['b']

    def test_both_create_then_both_confirm_converge_on_the_lower_number(self):
        before, after = threading.Barrier(2, timeout=10), threading.Barrier(2, timeout=10)
        self.a.on_create = self.b.on_create = before.wait     # both pre-checks saw nothing
        self.a.after_create = self.b.after_create = after.wait  # nobody confirms before both created
        a, b = self.run_both(lambda: register(PROJECT, self.a_start, client=self.a, now=NOW),
                             lambda: register(PROJECT, self.b_start, client=self.b, now=NOW))
        winner = self.assert_converged([a, b])
        self.assertEqual(winner, 301)  # the lower number wins, whoever posted first
        loser = next(o for o in (a, b) if o['state'] == 'lost_race')
        self.assertEqual(loser['issue']['number'], 302)
        self.assertEqual(self.claims(302), [])  # the duplicate never claimed

    def test_one_confirms_before_the_other_creates(self):
        a = register(PROJECT, self.a_start, client=self.a, now=NOW)
        b = register(PROJECT, self.b_start, client=self.b, now=NOW)  # B's pre-check sees A's issue
        self.assert_converged([a, b])
        self.assertEqual(b['state'], 'claimed')
        # And when B's pre-check read also missed A's issue, B creates and then withdraws.
        self.setUp()
        self.world['hide_new'] = {self.b: 1}
        a = register(PROJECT, self.a_start, client=self.a, now=NOW)
        b = register(PROJECT, self.b_start, client=self.b, now=NOW)
        self.assertEqual(b['state'], 'lost_race')
        self.assert_converged([a, b])

    def test_a_confirm_read_that_misses_the_other_issue_still_converges(self):
        # A creates #301 first, but B's next reads miss it: B creates #302 and its FIRST confirm
        # sees only #302. The second confirm pass sees #301, so B withdraws before claiming.
        before, after = threading.Barrier(2, timeout=10), threading.Barrier(2, timeout=10)
        self.a.on_create = self.b.on_create = before.wait
        self.a.after_create = self.b.after_create = after.wait
        self.world['hide_new'] = {self.b: 1, self.a: 1}  # each caller's first confirm misses the other
        a, b = self.run_both(lambda: register(PROJECT, self.a_start, client=self.a, now=NOW),
                             lambda: register(PROJECT, self.b_start, client=self.b, now=NOW))
        self.assert_converged([a, b])
        # Missed for longer, until after B claimed: B's post-claim check releases with `unclaim`.
        self.setUp()
        self.a.after_create = self.b.after_create = None
        a = register(PROJECT, self.a_start, client=self.a, now=NOW)
        self.world['hide_new'] = {}
        self.b.hidden[a['issue']['number']] = 3  # pre-check and both confirm passes miss #301
        b = register(PROJECT, self.b_start, client=self.b, now=NOW)
        self.assertEqual((b['state'], b['unclaimed']), ('lost_race', True))
        self.assertEqual(self.claims(b['issue']['number']), ['claim', 'unclaim'])
        self.assert_converged([a, b])

    def test_when_convergence_cannot_be_shown_both_links_are_surfaced(self):
        # Both pre-checks see nothing; A creates #301, then B creates #302. B's reads never show
        # #301 in time, so B keeps #302. A, the earliest, still holds and surfaces #302.
        b_ready, a_created, b_created = threading.Event(), threading.Event(), threading.Event()
        self.a.on_create = lambda: b_ready.wait(10)
        self.b.on_create = lambda: (b_ready.set(), a_created.wait(10))
        self.a.after_create = lambda: (a_created.set(), b_created.wait(10))  # A confirms after B created
        self.b.after_create = b_created.set
        self.world['hide_new'] = {self.b: 99}
        a, b = self.run_both(lambda: register(PROJECT, self.a_start, client=self.a, now=NOW),
                             lambda: register(PROJECT, self.b_start, client=self.b, now=NOW))
        self.assertEqual((a['issue']['number'], b['issue']['number']), (301, 302))
        self.assertEqual((a['state'], [w['number'] for w in a['concurrent']]), ('registered', [302]))
        text = render_registration(a)
        self.assertIn('another intention for this target was created at the same time: #302', text)
        self.assertIn('coordinate there', text)
        self.assertNotIn('commented `claim`', text)  # not reported as a clean success


FAKE_GH = r'''
import base64, json, pathlib, sys
root = pathlib.Path(__file__).parent
args = sys.argv[1:]
state_path = root / "world.json"
world = json.loads(state_path.read_text())
with (root / "calls.jsonl").open("a") as f:
    f.write(json.dumps(args) + "\n")
assert args[:3] == ["api", "--hostname", "github.com"]
endpoint = args[3]
if world.get("fail") and world["fail"] in endpoint:
    sys.exit(1)
repo = "thefundamentaltheor3m/SphereCeti"
path = endpoint[len(f"repos/{repo}/"):]
prs = {str(p["pr"]["number"]): p for p in world["prs"]}
if "--input" in args and path.endswith("/comments"):
    payload = json.load(sys.stdin)
    out = {"id": 900, "body": payload["body"], "user": {"login": "me", "type": "User"}}
    world["comments"].setdefault(path.split("/")[1], []).append(out)
    state_path.write_text(json.dumps(world))
elif "--input" in args:
    payload = json.load(sys.stdin)
    number = max([i["number"] for i in world["issues"]] + [300]) + 1
    out = {"number": number, "title": payload["title"], "body": payload["body"], "assignees": [], "labels": [],
           "html_url": f"https://github.com/{repo}/issues/{number}"}
    world["issues"].append(out)
    state_path.write_text(json.dumps(world))
elif path.endswith("/comments?per_page=100"):
    out = [world["comments"].get(path.split("/")[1], [])]
elif path == "issues?state=open&per_page=100":
    out = [world["issues"]]
elif path == "pulls?state=open&per_page=100":
    out = [[p["pr"] for p in world["prs"]]]
elif path.endswith("/files?per_page=100"):
    out = [prs[path.split("/")[1]]["files"]]
elif path.startswith("contents/"):
    key = path[len("contents/"):]
    source = next(p["contents"][key] for p in world["prs"] if key in p["contents"])
    out = {"encoding": "base64", "content": base64.b64encode(source.encode()).decode()}
else:
    sys.exit(4)
print(json.dumps(out))
'''


class IntentionsCliTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-intentions-')
        self.addCleanup(temp.cleanup)
        self.bin = Path(temp.name)
        (self.bin / 'gh').write_text(f'#!{sys.executable}\n' + FAKE_GH)
        (self.bin / 'gh').chmod(0o755)
        self.world(d5_world())

    def world(self, value):
        (self.bin / 'world.json').write_text(json.dumps(value))

    def run_cli(self, *args):
        env = {**os.environ, 'PATH': str(self.bin) + os.pathsep + os.environ['PATH']}
        launcher = [sys.executable, '-c', f'import sys; sys.path.insert(0, {str(ROOT / "tools/project")!r}); '
                    'from sphereceti.cli import main; sys.exit(main())']
        return subprocess.run([*launcher, *args], env=env, capture_output=True, text=True, timeout=120,
                              stdin=subprocess.DEVNULL)

    def writes(self):
        path = self.bin / 'calls.jsonl'
        calls = [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []
        return [c for c in calls if '--input' in c]

    def test_json_shapes_and_register_from_intend(self):
        listed = json.loads(self.run_cli('intentions', '--json').stdout)
        self.assertEqual(set(listed), {'schema', 'repository', 'observed_at', 'intentions', 'pull_requests',
                                       'groups', 'register_url'})
        looked = self.run_cli('intend', 'lintegral_encard_inter_vadd', '--json')
        self.assertEqual(looked.returncode, 0, looked.stderr)
        self.assertEqual(json.loads(looked.stdout)['verdict'], 'claimed')
        flags = ('--item', 'D5', '--module', 'SphereCeti/MeasureTheory/Measure/Haar/BoxAveraging.lean')
        dry = self.run_cli('intend', 'EuclideanSpace.box_average_tendsto', *flags, '--register', '--dry-run')
        self.assertIn('Dry run: would create an intention issue', dry.stdout)
        self.assertEqual(self.writes(), [])
        missing = self.run_cli('intend', 'EuclideanSpace.box_average_tendsto', '--register')
        self.assertEqual(missing.returncode, 2)
        self.assertIn('not registered: an intention claims one declaration', missing.stderr)
        made = self.run_cli('intend', 'EuclideanSpace.box_average_tendsto', *flags, '--register')
        self.assertEqual(made.returncode, 0, made.stderr)
        self.assertIn('No exact claim found for declaration EuclideanSpace.box_average_tendsto.', made.stdout)
        self.assertIn(f'Registered intention #301: https://github.com/{REPO}/issues/301 and commented `claim`',
                      made.stdout)
        self.assertEqual(len(self.writes()), 2)  # the issue, then `claim` as the contributor
        again = self.run_cli('intend', 'EuclideanSpace.box_average_tendsto', '--register')
        self.assertEqual(again.returncode, 0)
        self.assertTrue(again.stdout.startswith('Already claimed: declaration EuclideanSpace.box_average_tendsto'))
        self.assertEqual(len(self.writes()), 2)

    def test_a_failed_lookup_exits_two_and_writes_nothing(self):
        world = d5_world()
        world['fail'] = '/files'
        self.world(world)
        for args in (('intentions',), ('intend', 'X.y', '--register')):
            with self.subTest(args=args):
                result = self.run_cli(*args)
                self.assertEqual(result.returncode, 2)
                self.assertIn('GitHub lookup failed', result.stderr)
                self.assertEqual(result.stdout, '')
        self.assertEqual(self.writes(), [])


if __name__ == '__main__':
    unittest.main()
