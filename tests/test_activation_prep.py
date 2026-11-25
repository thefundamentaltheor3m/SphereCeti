# SPDX-License-Identifier: Apache-2.0
"""Activation, prepared inert: the live race probe, the halt after an unexpected refusal, and the flips.

Decisions 3 and 4 on #100. Nothing here can merge: the workflow is installed with every switch off,
and these tests use fake GitHub only.
"""
from copy import deepcopy
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import textwrap
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools/project'))
from sphereceti import controller_halt as halt
from sphereceti.merge_controller import Backend, Rejected, Writer, reconcile, run
from sphereceti.review_records import RecordError
from test_merge_controller import FakeBackend, H, M, T

REPO = 'thefundamentaltheor3m/SphereCeti'
MOVED = '4' * 40
WORKFLOW = ROOT / '.github/workflows/merge-controller.yml'
STALE = 'Head branch is not up to date with the base branch'


class ProbeBackend(FakeBackend):
    """FakeBackend plus GitHub's main, its strict merge rule, the real bounded hold, and halt records."""
    hold = Backend.hold
    PROBE_WAIT, PROBE_POLL = 20 * 60, 15

    def __init__(self, *, event='workflow_dispatch', moves_after=2, refusal=None):
        super().__init__()
        self.activation['executor'] = {'run': {'event': event}}
        self.github_main, self.moves_after, self.refusal = T, moves_after, refusal
        self.events, self.now, self.polls, self.halts = [], 0.0, 0, []

    def clock(self):
        return self.now

    def sleep(self, seconds):
        self.now += seconds

    def refresh(self):
        super().refresh()
        self.events.append(('final check', self.github_main))

    def main(self):
        self.polls += 1
        if self.moves_after is not None and self.polls > self.moves_after:
            self.github_main = MOVED  # Another PR lands while the probe holds.
        return self.github_main

    def merge(self, number, head):
        self.events.append(('put', self.github_main))
        self.puts.append((number, head))
        if self.refusal:
            raise Rejected(*self.refusal)
        if self.github_main != T:  # The strict ruleset: the pinned head no longer contains main.
            raise Rejected('405', STALE)
        self.pr.update(merged=True, state='closed', merge_commit_sha=M)
        return {'merged': True, 'sha': M}

    def record_halt(self, number, head, refusal):
        self.halts.append((number, head, refusal))
        return 7


class RaceProbeTests(unittest.TestCase):
    def test_the_probe_holds_after_the_final_check_and_github_refuses_the_stale_combination(self):
        b = ProbeBackend()
        result = reconcile(b, lambda: [1], applying=True, probe='race')
        # Final check at T, then main moves (third poll), then exactly one head-pinned PUT, refused.
        self.assertEqual(b.events, [('final check', T), ('put', MOVED)])
        self.assertEqual(b.puts, [(1, H)])
        self.assertEqual(result['probe'], {
            'mode': 'race', 'proof': True, 'outcome': 'rejected_stale',
            'final_check': {'action': 'merge', 'main': T, 'tested_tree': '5' * 40, 'head': H},
            'main_moved_to': MOVED, 'refusal': {'status': '405', 'message': STALE}})
        self.assertEqual((result['state'], result['results'][0]['state']), ('rejected', 'rejected_stale'))
        self.assertEqual(b.halts, [])  # The expected refusal never halts.

    def test_main_not_moving_within_the_bound_sends_nothing(self):
        b = ProbeBackend(moves_after=None)
        result = reconcile(b, lambda: [1], applying=True, probe='race')
        self.assertEqual((result['state'], b.puts, result['probe']['proof']), ('probe_timeout', [], False))
        self.assertEqual(b.now, 20 * 60)  # Bounded: twenty minutes of polls, then stop.

    def test_a_merge_or_any_other_refusal_is_not_a_proof(self):
        b = ProbeBackend(refusal=('403', 'Resource not accessible by integration'))
        result = reconcile(b, lambda: [1], applying=True, probe='race')
        self.assertEqual((result['probe']['proof'], result['probe']['outcome']), (False, 'rejected_unexpected'))
        self.assertEqual(result['state'], 'stopped');self.assertEqual(len(b.halts), 1)

    def test_the_probe_is_impossible_in_scheduled_runs_and_without_merging(self):
        b = ProbeBackend(event='schedule')
        result = reconcile(b, lambda: [1], applying=True, probe='race')
        self.assertEqual(result['state'], 'refused')
        self.assertIn("runs only in a workflow_dispatch run (this run is 'schedule')", result['probe']['refused'])
        self.assertEqual((b.puts, b.observations), ([], 0))
        b = ProbeBackend();b.activation.update(merging_requested=False, ready=False)
        self.assertEqual(reconcile(b, lambda: [1], applying=True, probe='race')['state'], 'disabled')
        self.assertEqual(b.puts, [])
        for kwargs in ({'pr': None, 'apply': True}, {'pr': 1, 'apply': False}):
            args = SimpleNamespace(command='merge-control', probe='race', cache_dir=Path(tempfile.mkdtemp()), **kwargs)
            with patch('sphereceti.merge_controller.Backend'), self.assertRaises(RecordError):
                run(args, SimpleNamespace(repository=REPO))

    def test_without_a_probe_nothing_holds(self):
        b = ProbeBackend()
        result = reconcile(b, lambda: [1], applying=True)
        self.assertEqual((result['state'], b.polls), ('completed', 0))
        self.assertNotIn('probe', result)


def bot_issue(number=5, body=None, **change):
    found = {'number': number, 'user': {'id': halt.BOT_ID, 'login': halt.BOT_LOGIN, 'type': 'Bot'},
             'body': body or halt.issue(99, 3, 'b' * 40, {'status': '403', 'message': 'nope'})['body'],
             'created_at': '2026-11-24T10:00:00Z'}
    found.update(change)
    return found


def ack(cid=1, uid=2009342, **change):
    found = {'id': cid, 'body': halt.ACKNOWLEDGE + '\nchecked the refusal', 'user': {'id': uid, 'type': 'User'},
             'author_association': 'COLLABORATOR', 'created_at': '2026-11-24T11:00:00Z',
             'updated_at': '2026-11-24T11:00:00Z'}
    found.update(change)
    return found


class HaltTests(unittest.TestCase):
    MAINTAINERS = ('user:2009342', 'user:56166236')

    def assess(self, issues, comments):
        return halt.assess(issues, lambda n: comments.get(n, []), self.MAINTAINERS)

    def test_an_unacknowledged_halt_stops_and_a_maintainer_acknowledges_it(self):
        found = self.assess([bot_issue()], {})
        self.assertEqual([h['issue'] for h in found['halted']], [5])
        self.assertIn('acknowledges with `/sphereceti acknowledge-halt` on issue #5', halt.reason(found['halted']))
        found = self.assess([bot_issue()], {5: [ack()]})
        self.assertEqual(found['halted'], [])
        self.assertEqual(found['halts'][0]['acknowledged'], {'comment': 1, 'by': 'user:2009342', 'at': '2026-11-24T11:00:00Z'})

    def test_only_a_maintainer_action_acknowledges(self):
        for name, comment in (('not authorized', ack(uid=8)), ('edited', ack(updated_at='2026-11-24T12:00:00Z')),
                              ('a bot', ack(user={'id': 2009342, 'type': 'Bot'})),
                              ('contributor association', ack(author_association='CONTRIBUTOR')),
                              ('before the halt', ack(created_at='2026-11-24T09:00:00Z',
                                                       updated_at='2026-11-24T09:00:00Z')),
                              ('other words', ack(body='looks fine, carry on'))):
            with self.subTest(name):
                self.assertEqual(len(self.assess([bot_issue()], {5: [comment]})['halted']), 1)

    def test_only_the_bots_marked_issues_are_halts(self):
        human = bot_issue(user={'id': 2009342, 'login': 'cameronfreer', 'type': 'User'})
        unmarked = bot_issue(body='an ordinary bot issue')
        pull = bot_issue(pull_request={'url': 'x'})
        self.assertEqual(self.assess([human, unmarked, pull], {})['halts'], [])

    def test_the_inventory_is_read_get_only_and_must_be_complete(self):
        class Client:
            def __init__(self, issues):
                self.issues, self.calls = issues, []

            def call(self, endpoint, *, paginate=False, payload=None):
                assert payload is None and paginate
                self.calls.append(endpoint)
                if '/comments' in endpoint:
                    return [[ack()]]
                return self.issues
        client = Client([[bot_issue()]])
        found = halt.read(client, REPO, self.MAINTAINERS)
        self.assertEqual(found['halted'], [])
        self.assertEqual(client.calls, [f'repos/{REPO}/issues?creator=github-actions%5Bbot%5D&state=all&per_page=100',
                                        f'repos/{REPO}/issues/5/comments?per_page=100'])
        for broken in ([], None, [{}]):
            with self.subTest(broken=broken), self.assertRaises(RecordError):
                halt.read(Client(broken), REPO, self.MAINTAINERS)

    def test_the_job_token_may_create_only_the_halt_issue(self):
        writer = Writer(REPO, 'ghs_fixture')
        sent = []
        writer.run = lambda command, payload, env: (sent.append((command, payload)) or
                                                    subprocess.CompletedProcess(command, 0, '{"number": 12}', ''))
        self.assertEqual(writer.halt(99, 3, 'b' * 40, {'status': '403', 'message': 'nope'}), {'number': 12})
        command, payload = sent[0]
        self.assertEqual(command[4:7], [f'repos/{REPO}/issues', '--method', 'POST'])
        self.assertEqual(payload['title'], halt.TITLE)
        self.assertTrue(payload['body'].startswith(halt.MARKER))
        for bad in ({'title': 'Anything', 'body': halt.MARKER}, {'title': halt.TITLE, 'body': 'no marker'},
                    {'title': halt.TITLE, 'body': halt.MARKER, 'labels': ['x']}):
            with self.subTest(bad=bad), self.assertRaises(RecordError):
                writer.call(f'repos/{REPO}/issues', bad)
        with self.assertRaises(RecordError):
            halt.issue(99, 3, 'b' * 40, {'status': '500', 'message': 'server'})
        self.assertEqual(len(sent), 1)

    def test_an_unexpected_refusal_records_a_halt(self):
        b = ProbeBackend(refusal=('405', 'At least 1 approving review is required by reviewers with write access.'))
        result = reconcile(b, lambda: [1], applying=True)
        entry = result['results'][0]
        self.assertEqual((result['state'], entry['state'], entry['halt_issue']), ('stopped', 'rejected_unexpected', 7))
        self.assertEqual(b.halts, [(1, H, {'status': '405', 'message':
                                           'At least 1 approving review is required by reviewers with write access.'})])


def step_script():
    lines = WORKFLOW.read_text().splitlines()
    start = next(i for i, line in enumerate(lines) if line.strip().startswith('- name: Run the controller'))
    at = next(i for i in range(start, len(lines)) if lines[i].strip() == 'run: |')
    indent = len(lines[at]) - len(lines[at].lstrip())
    body = []
    for line in lines[at + 1:]:
        if line.strip() and len(line) - len(line.lstrip()) <= indent:
            break
        body.append(line)
    return textwrap.dedent('\n'.join(body)) + '\n'


class WorkflowTests(unittest.TestCase):
    def run_step(self, **env):
        with tempfile.TemporaryDirectory() as t:
            fake = Path(t) / 'python3'
            fake.write_text('#!/bin/sh\necho "$*" >> "$LOG"\n')
            fake.chmod(0o755)
            log = Path(t) / 'log'
            log.write_text('')
            base = {'PATH': f'{t}:/usr/bin:/bin', 'LOG': str(log), 'RUNNER_TEMP': t, 'CONTROLLER': 'doctor',
                    'PR_NUMBER': '', 'PROBE': '', 'GITHUB_EVENT_NAME': 'workflow_dispatch'}
            done = subprocess.run(['/bin/bash', '-c', step_script()], env={**base, **env}, capture_output=True,
                                  text=True, timeout=30)
            return done, log.read_text().replace(t, '$TMP').splitlines()

    def test_installed_inert_the_doctor_runs(self):
        done, calls = self.run_step()
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(calls, ['-m sphereceti.cli merge-doctor --executor --json --source-repo . '
                                 '--cache-dir $TMP/merge-controller'])

    def test_after_activation_sweeps_single_prs_and_the_probe(self):
        tail = '--json --source-repo . --cache-dir $TMP/merge-controller'
        for env, expected in (({}, f'-m sphereceti.cli merge-control --apply --sweep {tail}'),
                              ({'PR_NUMBER': '12'}, f'-m sphereceti.cli merge-control --apply --pr 12 {tail}'),
                              ({'PR_NUMBER': '12', 'PROBE': 'race'},
                               f'-m sphereceti.cli merge-control --apply --pr 12 --probe race {tail}')):
            with self.subTest(env=env):
                done, calls = self.run_step(CONTROLLER='apply', **env)
                self.assertEqual((done.returncode, calls), (0, [expected]), done.stderr)
        for env in ({'PROBE': 'race'}, {'PR_NUMBER': '12', 'PROBE': 'race', 'GITHUB_EVENT_NAME': 'schedule'},
                    {'PR_NUMBER': '12; rm -rf /'}, {'CONTROLLER': 'merge-everything'}):
            with self.subTest(env=env):
                done, calls = self.run_step(**{'CONTROLLER': 'apply', **env})
                self.assertNotEqual(done.returncode, 0);self.assertEqual(calls, [])

    def test_the_activation_flips_are_exactly_the_marked_lines(self):
        text = WORKFLOW.read_text()
        self.assertEqual(text, (ROOT / 'tools/ci/merge-controller.yml').read_text())
        flipped = flip(text)
        changed = [(a, b) for a, b in zip(text.splitlines(), flipped.splitlines()) if a != b]
        self.assertEqual(len(changed), 7)  # 1 mode line, 4 permissions, 2 schedule lines
        self.assertIn('          CONTROLLER: apply', flipped)
        self.assertNotIn(': read', flipped.split('concurrency:')[0].split('permissions:')[1])
        self.assertIn("  schedule:\n    - cron: '17 * * * *'\n", flipped)


def flip(text):
    """The later activation PR, mechanically: the lines marked ACTIVATION, nothing else."""
    text = text.replace('          CONTROLLER: doctor', '          CONTROLLER: apply')
    head, rest = text.split('permissions:\n', 1)
    block, tail = rest.split('concurrency:', 1)
    text = head + 'permissions:\n' + block.replace(': read', ': write') + 'concurrency:' + tail
    return text.replace("  # schedule:\n  #   - cron: '17 * * * *'", "  schedule:\n    - cron: '17 * * * *'")


if __name__ == '__main__':
    unittest.main()
