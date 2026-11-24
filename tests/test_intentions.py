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
from sphereceti.intentions import (LOOKUP_SCHEMA, SCHEMA, added_lines, declarations, issue_body, lookup,
                                   observe, register, render, render_lookup)
from sphereceti.review_records import RecordError

ROOT = Path(__file__).resolve().parents[1]
PROJECT = parse_project(resource_text('sphereceti.toml'))
REPO = PROJECT.repository
NOW = datetime.now(timezone.utc)
FUTURE = (NOW + timedelta(days=7)).strftime('%Y-%m-%d')
PAST = (NOW - timedelta(days=2)).strftime('%Y-%m-%d')

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


def form_issue(number, *, declarations_text=None, item=None, module=None, expires=FUTURE, holders=('alice',),
               labels=('intention',)):
    return {'number': number, 'title': f'Intention {number}', 'html_url': f'https://github.com/{REPO}/issues/{number}',
            'body': issue_body(declarations_text, item, module, None, expires),
            'assignees': [{'login': h} for h in holders], 'labels': [{'name': l} for l in labels]}


def d5_world():
    return {
        'issues': [form_issue(200, declarations_text='EuclideanSpace.periodicRepetition_card', item='D5'),
                   form_issue(201, declarations_text='Foo.bar', expires=PAST, holders=('bob',)),
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
    }


class FakeClient:
    """GitHub's REST shapes, in memory. `on_create` runs just before a new issue is stored."""

    def __init__(self, world, fail=None):
        self.world, self.fail, self.calls, self.on_create = world, fail, [], None

    def call(self, endpoint, *, payload=None, paginate=False, method=None):
        self.calls.append((method or ('POST' if payload else 'GET'), endpoint, payload))
        if self.fail and self.fail in endpoint:
            raise RecordError('GitHub operation failed; publication is unconfirmed')
        prefix = f'repos/{REPO}/'
        path = endpoint[len(prefix):]
        prs = {p['pr']['number']: p for p in self.world['prs']}
        if path == 'issues?state=open&per_page=100':
            return [[copy.deepcopy(i) for i in self.world['issues'] if i.get('state', 'open') == 'open']]
        if path == 'pulls?state=open&per_page=100':
            return [[p['pr'] for p in self.world['prs']]]
        if path.startswith('pulls/') and path.endswith('/files?per_page=100'):
            return [prs[int(path.split('/')[1])]['files']]
        if path.startswith('contents/'):
            key = path[len('contents/'):]
            source = next(p['contents'][key] for p in self.world['prs'] if key in p['contents'])
            return {'encoding': 'base64', 'content': base64.b64encode(source.encode()).decode()}
        if path == 'issues' and payload:
            if self.on_create:
                hook, self.on_create = self.on_create, None
                hook()
            number = max([i['number'] for i in self.world['issues']] + [300]) + 1
            issue = {'number': number, 'title': payload['title'], 'body': payload['body'], 'assignees': [],
                     'labels': [], 'html_url': f'https://github.com/{REPO}/issues/{number}'}
            self.world['issues'].append(issue)  # labels dropped, as for contributors without triage rights
            return dict(issue)
        if path.startswith('issues/') and path.endswith('/comments') and payload:
            return {'id': 1, 'body': payload['body']}
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


class LookupTest(unittest.TestCase):
    def setUp(self):
        self.world = d5_world()
        self.client = FakeClient(self.world)
        self.observed = observe(PROJECT, client=self.client, now=NOW)

    def look(self, target, **kwargs):
        return lookup(PROJECT, target, observed=self.observed, **kwargs)

    def test_observation_lists_intentions_beside_proof_prs_grouped_by_item(self):
        self.assertEqual(self.observed['schema'], SCHEMA)
        self.assertEqual([i['number'] for i in self.observed['intentions']], [200, 201])
        self.assertEqual([p['number'] for p in self.observed['pull_requests']], [105, 112])  # #98 has no module
        d5 = next(g for g in self.observed['groups'] if g['key'] == 'D5')
        self.assertEqual((d5['intentions'], d5['pull_requests']), ([200], [105, 112]))
        self.assertEqual(set(self.observed['pull_requests'][0]), {
            'kind', 'number', 'url', 'title', 'author', 'draft', 'head', 'modules', 'declarations', 'declared',
            'items', 'layers', 'incomplete'})
        text = render(self.observed)
        self.assertIn('Roadmap item D5:', text)
        self.assertIn(f'intention #200 claimed by alice until {FUTURE}: EuclideanSpace.periodicRepetition_card', text)
        self.assertIn(f'intention #201 EXPIRED claim by bob (expired {PAST}): Foo.bar', text)

    def test_exact_match_on_an_intention(self):
        result = self.look('EuclideanSpace.periodicRepetition_card')
        self.assertEqual((result['verdict'], [w['number'] for w in result['claimed']]), ('claimed', [200]))
        self.assertTrue(render_lookup(result).startswith('Already claimed: declaration '))
        self.assertIn('https://github.com/thefundamentaltheor3m/SphereCeti/issues/200', render_lookup(result))

    def test_exact_match_on_an_open_prs_added_declaration_even_unqualified(self):
        for target in ('lintegral_encard_inter_vadd', 'MeasureTheory.lintegral_encard_inter_vadd'):
            result = self.look(target)
            self.assertEqual((result['verdict'], [w['number'] for w in result['claimed']]), ('claimed', [105]))
        self.assertEqual(self.look('encard_inter_vadd')['verdict'], 'no_exact_claim')  # a suffix is not a name

    def test_same_item_different_lemma_is_related_not_claimed(self):
        result = self.look('EuclideanSpace.box_average_tendsto', item='D5')
        self.assertEqual(result['verdict'], 'no_exact_claim')
        self.assertEqual(sorted(w['number'] for w in result['related']), [105, 112, 200])
        text = render_lookup(result)
        self.assertTrue(text.startswith('No exact claim found for declaration EuclideanSpace.box_average_tendsto.'))
        self.assertIn('Related open PRs and intentions', text)
        item = self.look('D5')
        self.assertEqual((item['kind'], item['verdict'], len(item['related'])), ('item', 'no_exact_claim', 3))

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
        for endpoint in ('issues?state=open', 'pulls?state=open', '/files', 'contents/'):
            with self.subTest(endpoint=endpoint), self.assertRaises(RecordError):
                lookup(PROJECT, 'X.y', client=FakeClient(d5_world(), fail=endpoint))


class RegisterTest(unittest.TestCase):
    def setUp(self):
        self.world = d5_world()

    def client(self):
        return FakeClient(self.world)

    def start(self, client, target, **kwargs):
        return lookup(PROJECT, target, client=client, **kwargs)

    def test_register_creates_a_form_format_issue_that_lists_like_a_form_issue(self):
        client = self.client()
        result = self.start(client, 'EuclideanSpace.box_average_tendsto', item='D5')
        outcome = register(PROJECT, result, client=client, parent=112, now=NOW)
        self.assertEqual(outcome['state'], 'registered')
        [(_, endpoint, payload)] = [w for w in client.writes()]
        self.assertEqual(endpoint, f'repos/{REPO}/issues')
        self.assertEqual(payload['labels'], ['intention'])
        self.assertIn('### Declarations\n\nEuclideanSpace.box_average_tendsto', payload['body'])
        self.assertIn('### Roadmap item\n\nD5', payload['body'])
        self.assertIn('### Parent PR\n\n#112', payload['body'])
        # The created issue (unlabelled, as for a contributor without triage rights) parses exactly
        # like the form-filed #200, and now claims the declaration for everyone else.
        again = self.start(self.client(), 'EuclideanSpace.box_average_tendsto')
        self.assertEqual([w['number'] for w in again['claimed']], [outcome['issue']['number']])
        form = next(i for i in observe(PROJECT, client=self.client(), now=NOW)['intentions'] if i['number'] == 200)
        mine = next(i for i in observe(PROJECT, client=self.client(), now=NOW)['intentions']
                    if i['number'] == outcome['issue']['number'])
        self.assertEqual(set(form), set(mine))

    def test_near_simultaneous_same_declaration_race_the_second_sees_the_first(self):
        # Both contributors looked and saw no exact claim. A registers first; B's pre-check sees it.
        a_client, b_client = self.client(), self.client()
        a = self.start(a_client, 'EuclideanSpace.box_average_tendsto', item='D5')
        b = self.start(b_client, 'EuclideanSpace.box_average_tendsto', item='D5')
        self.assertEqual(register(PROJECT, a, client=a_client, now=NOW)['state'], 'registered')
        lost = register(PROJECT, b, client=b_client, now=NOW)
        self.assertEqual(lost['state'], 'claimed')
        self.assertIn('/issues/', lost['winner']['url'])
        self.assertEqual(b_client.writes(), [])
        # Truly simultaneous: A's issue lands between B's pre-check and B's creation.
        world = d5_world()
        b_client = FakeClient(world)
        b = self.start(b_client, 'EuclideanSpace.other_lemma', item='D5')
        rival = form_issue(250, declarations_text='EuclideanSpace.other_lemma', item='D5', holders=())
        b_client.on_create = lambda: world['issues'].append(rival)
        lost = register(PROJECT, b, client=b_client, now=NOW)
        self.assertEqual(lost['state'], 'lost_race')
        self.assertEqual(lost['winner']['number'], 250)
        self.assertEqual(lost['winner']['url'], f'https://github.com/{REPO}/issues/250')
        mine = lost['issue']['number']
        self.assertEqual([(m, e) for m, e, _ in b_client.writes()],
                         [('POST', f'repos/{REPO}/issues'), ('POST', f'repos/{REPO}/issues/{mine}/comments'),
                          ('PATCH', f'repos/{REPO}/issues/{mine}')])  # only our own duplicate is touched
        self.assertIn('Duplicate of #250', b_client.writes()[1][2]['body'])
        text = render_lookup({**b, 'registration': lost})
        self.assertIn('Lost the race: intention #250', text)

    def test_distinct_d5_lemmas_both_go_through(self):
        first, second = self.client(), self.client()
        a = self.start(first, 'EuclideanSpace.box_average_tendsto', item='D5')
        b = self.start(second, 'EuclideanSpace.periodic_density_limit', item='D5')
        self.assertEqual(register(PROJECT, a, client=first, now=NOW)['state'], 'registered')
        self.assertEqual(register(PROJECT, b, client=second, now=NOW)['state'], 'registered')
        claimed = observe(PROJECT, client=self.client(), now=NOW)['intentions']
        self.assertEqual(len([i for i in claimed if 'D5' in i['items']]), 3)

    def test_no_write_on_dry_run_claim_or_lookup_failure(self):
        client = self.client()
        result = self.start(client, 'EuclideanSpace.box_average_tendsto', item='D5')
        dry = register(PROJECT, result, client=client, dry_run=True, now=NOW)
        self.assertEqual(dry['state'], 'dry_run')
        claimed = self.start(client, 'lintegral_encard_inter_vadd')
        self.assertEqual(register(PROJECT, claimed, client=client, now=NOW)['state'], 'claimed')
        self.assertEqual(client.writes(), [])
        failing = FakeClient(self.world, fail='issues?state=open')
        with self.assertRaises(RecordError):
            register(PROJECT, result, client=failing, now=NOW)  # the pre-check read fails
        self.assertEqual(failing.writes(), [])


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
if "--input" in args:
    payload = json.load(sys.stdin)
    number = max([i["number"] for i in world["issues"]] + [300]) + 1
    out = {"number": number, "title": payload["title"], "body": payload["body"], "assignees": [], "labels": [],
           "html_url": f"https://github.com/{repo}/issues/{number}"}
    world["issues"].append(out)
    state_path.write_text(json.dumps(world))
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
        dry = self.run_cli('intend', 'EuclideanSpace.box_average_tendsto', '--item', 'D5', '--register', '--dry-run')
        self.assertIn('Dry run: would create an intention issue', dry.stdout)
        self.assertEqual(self.writes(), [])
        made = self.run_cli('intend', 'EuclideanSpace.box_average_tendsto', '--item', 'D5', '--register')
        self.assertEqual(made.returncode, 0, made.stderr)
        self.assertIn('No exact claim found for declaration EuclideanSpace.box_average_tendsto.', made.stdout)
        self.assertIn(f'Registered intention #301: https://github.com/{REPO}/issues/301', made.stdout)
        self.assertEqual(len(self.writes()), 1)
        again = self.run_cli('intend', 'EuclideanSpace.box_average_tendsto', '--register')
        self.assertEqual(again.returncode, 0)
        self.assertTrue(again.stdout.startswith('Already claimed: declaration EuclideanSpace.box_average_tendsto'))
        self.assertEqual(len(self.writes()), 1)

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
