# SPDX-License-Identifier: Apache-2.0
"""`sphereceti reviews` fits on one screen by default; --all keeps the full listing; JSON is unchanged."""
from copy import deepcopy
from datetime import timedelta
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences
from sphereceti.feedback import Progress
from sphereceti.review_queue import next_command, queue, render, render_concise
from test_review_queue import HEAD, OLD, POLICY, PROJECT, Client, SurveyAPI, comment, pr, record

PENDING = [{'__typename': 'CheckRun', 'status': 'IN_PROGRESS', 'conclusion': None}]
FAILED = [{'__typename': 'CheckRun', 'status': 'COMPLETED', 'conclusion': 'FAILURE'}]


def eighty():
    """20 revised, 25 new, 20 stacked on three roots, 10 awaiting CI, 5 failing: 80 open PRs."""
    prs, comments, compare = [], {}, {f'{OLD}...{HEAD}': {'status': 'ahead', 'ahead_by': 2}}
    long = 'Prove the Cohn–Elkies linear programming bound for the periodic packings of a lattice'
    for n in range(1, 21):
        prs.append(pr(n, 'carol', title=f'{long} {n}', ago=timedelta(hours=n)))
        comments[n] = [record(100 + n, n, head=OLD)] + ([comment(200 + n, n, 'Fixed.', 'carol')] if n % 4 == 0 else [])
    for n in range(21, 46):
        prs.append(pr(n, 'bob', title=f'Short {n}', ago=timedelta(hours=n)))
    roots = {21: 'root-a', 22: 'root-b', 23: 'root-c'}
    for p in prs:
        if p['number'] in roots:
            p['headRefName'] = roots[p['number']]
    for i, n in enumerate(range(46, 66)):
        prs.append(pr(n, 'dave', title=f'Child {n}', baseRefName=list(roots.values())[i % 3] if i < 18 else 'gone'))
    for n in range(66, 76):
        prs.append(pr(n, 'erin', statusCheckRollup=PENDING))
    for n in range(76, 81):
        prs.append(pr(n, 'erin', statusCheckRollup=FAILED))
    return prs, comments, compare


class StackClient(Client):
    def call(self, endpoint, **kwargs):
        if '/pulls?state=closed&head=' in endpoint:
            return [[]]
        return super().call(endpoint, **kwargs)


class ConciseQueueTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-concise-')
        self.addCleanup(temp.cleanup)
        prefs = OperatorPreferences(provider='claude', budget_usd=5, storage=temp.name)
        prs, comments, compare = eighty()
        self.report = queue(PROJECT, POLICY, prefs, api=SurveyAPI(prs), client=StackClient(comments, compare))

    def test_the_default_fits_on_one_screen(self):
        snapshot = json.dumps(self.report)
        text = render_concise(self.report)
        lines = text.split('\n')
        self.assertLessEqual(len(lines), 25, text)
        self.assertEqual(json.dumps(self.report), snapshot)  # rendering never changes the JSON
        self.assertEqual(lines[0], 'Queue: 0 ready to merge · 20 revised · 25 new · 20 waiting on parents · '
                                   '10 awaiting CI')
        self.assertIn('Revised since your review:', lines)
        self.assertIn('  … and 12 more (sphereceti reviews --all)', lines)
        revised = lines[lines.index('Revised since your review:') + 1]
        self.assertRegex(revised, r'^  #\d+ carol  Prove the Cohn–Elkies linear programming bound fo…( |$)')
        self.assertTrue(all(len(line) <= 100 for line in lines), text)
        self.assertIn('(unblocks 6)', text)
        self.assertIn('(author replied)', text)
        self.assertIn('20 PRs wait on a parent (biggest stacks: #21 ×6, #22 ×6, #23 ×6)', lines)
        self.assertIn('10 PRs await CI', lines)
        self.assertIn('Not ready: 5 failing CI', lines)
        self.assertEqual(lines[-1], 'Next: sphereceti review --revised --limit 10')
        for noise in ('waiting 1h', 'human-review scope', 'no review by you', HEAD[:7]):
            self.assertNotIn(noise, text)

    def test_all_keeps_the_full_listing(self):
        full = render(self.report)
        self.assertGreater(len(full.split('\n')), 50)  # today's listing: every PR on its own line
        for n in range(1, 21):
            self.assertIn(f'  #{n} carol ', full)
        self.assertIn('Blocked by a parent (20):', full)

    def test_the_next_command(self):
        report = deepcopy(self.report)
        self.assertEqual(next_command(report), 'sphereceti review --revised --limit 10')
        report['ready_to_merge']['items'] = [{'pr': 9, 'next_step': 'approve + merge'}]
        self.assertEqual(next_command(report), 'sphereceti merge-ready --apply')
        report['ready_to_merge']['items'] = [{'pr': 9, 'next_step': 'waiting on CI (held: needs maintainer approval)'}]
        self.assertEqual(next_command(report), 'sphereceti review --revised --limit 10')
        report['sections']['revised'], report['sections']['author_replied'] = [], []
        self.assertEqual(next_command(report), 'sphereceti review --new --limit 10')
        report['sections']['new'] = report['sections']['new'][:3]
        self.assertEqual(next_command(report), 'sphereceti review --new --limit 3')
        report['sections']['new'] = []
        self.assertEqual(next_command(report), 'nothing needs your review now')


class SummaryLineTest(unittest.TestCase):
    def test_one_updating_line_on_a_terminal_and_one_final_line_elsewhere(self):
        for tty, expected in ((True, '\r\x1b[KReading open PRs…\r\x1b[KReading 84 open PRs… done in 26s\n'),
                              (False, 'Reading 84 open PRs… done in 26s\n')):
            stream = io.StringIO()
            p = Progress(stream, tty=tty, verbose=False)
            p.summary('Reading open PRs…')
            p.line('Surveying open PRs… (84 open)')  # per-phase lines only with --verbose
            p.counter('scope', 10, 84)
            p.summary('Reading 84 open PRs… done in 26s', final=True)
            self.assertEqual(stream.getvalue(), expected)


if __name__ == '__main__':
    unittest.main()
