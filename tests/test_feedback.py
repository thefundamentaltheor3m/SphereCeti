# SPDX-License-Identifier: Apache-2.0
"""Progress lines: stderr only, suppressed by --quiet, no carriage returns off a terminal."""
import io
import json
from pathlib import Path
import re
import sys
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences
from sphereceti.feedback import Progress, RubricWatch, current, duration, install
from sphereceti.local_review import RUBRICS
from review_post_fixture import PostingFixture

STAMP = re.compile(r'^\[\d\d:\d\d:\d\d\] ')


class Clock:
    def __init__(self):
        self.t = 0.0

    def __call__(self):
        return self.t


class ProgressTest(unittest.TestCase):
    def make(self, tty=False):
        self.stream, self.clock = io.StringIO(), Clock()
        return Progress(self.stream, tty=tty, clock=self.clock)

    def test_lines_are_stamped_and_phases_say_how_long(self):
        p = self.make()
        with p.phase('Preparing evidence for #63 at 9c587b5 (fetching pinned sources…)', 'Evidence for #63 ready'):
            self.clock.t = 92
        lines = self.stream.getvalue().splitlines()
        self.assertTrue(all(STAMP.match(line) for line in lines))
        self.assertEqual([STAMP.sub('', line) for line in lines],
                         ['Preparing evidence for #63 at 9c587b5 (fetching pinned sources…)',
                          'Evidence for #63 ready in 1m32s'])
        with self.assertRaises(ValueError):
            with p.phase('Surveying open PRs… (49 open)', 'Surveying open PRs… done', 'Surveying open PRs… failed'):
                self.clock.t = 95
                raise ValueError
        self.assertTrue(self.stream.getvalue().endswith('Surveying open PRs… failed after 3s\n'))
        self.assertEqual((duration(4), duration(130), duration(3725)), ('4s', '2m10s', '1h02m'))

    def test_counters_off_a_terminal_print_every_tenth_and_the_last_without_carriage_returns(self):
        p = self.make(tty=False)
        for i in range(1, 50):
            p.counter('scope', i, 49)
        text = self.stream.getvalue()
        self.assertNotIn('\r', text)
        self.assertEqual([STAMP.sub('', line) for line in text.splitlines()],
                         ['  scope 10/49', '  scope 20/49', '  scope 30/49', '  scope 40/49', '  scope 49/49'])

    def test_counters_on_a_terminal_overwrite_one_line_at_most_every_two_seconds(self):
        p = self.make(tty=True)
        for i in range(1, 50):
            self.clock.t = i * 0.5
            p.counter('scope', i, 49)
        text = self.stream.getvalue()
        updates = text.split('\r\033[K')[1:]
        self.assertEqual(len(updates), 13)  # items 1, 5, 9, ..., 45 (one per 2s), then the final 49
        self.assertTrue(updates[-1].endswith('scope 49/49\n'))
        self.assertEqual(text.count('\n'), 1)
        p.counter('reading comments', 1, 3)
        p.line('Selected #63')  # a normal line clears an open counter first
        self.assertTrue(self.stream.getvalue().endswith('reading comments 1/3\r\033[K' +
                                                        self.stream.getvalue().rsplit('\r\033[K', 1)[1]))

    def test_disabled_progress_writes_nothing(self):
        stream = io.StringIO()
        p = Progress(stream, enabled=False)
        p.line('x')
        p.counter('scope', 10, 10)
        with p.phase('a', 'b'):
            pass
        self.assertEqual(stream.getvalue(), '')
        self.assertFalse(current().enabled)  # library callers get a silent reporter by default


class RubricWatchTest(unittest.TestCase):
    def test_start_and_done_lines_follow_the_engine_ledger(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-feedback-')
        self.addCleanup(temp.cleanup)
        ledger = Path(temp.name) / 'ledger.json'
        head = 'a' * 40
        prior = {'verdict': 'approve', 'reviewed_sha': head, 'run_id': 'old'}
        ledger.write_text(json.dumps({'days': {}, 'prs': {'63': {'state': {'naming': prior}}}}))
        stream = io.StringIO()
        watch = RubricWatch(Progress(stream, tty=False), ledger, '63', head, RUBRICS, ['codex'])
        watch.poll()
        ledger.write_text('{"days": {}, "prs": ')  # mid-write: ignored until the next poll
        watch.poll()
        ledger.write_text(json.dumps({'in_flight': {'rubric': 'generality', 'model': 'gpt-6.1-sol'},
                                      'prs': {'63': {'state': {'naming': prior}}}}))
        watch.poll()
        watch.poll()  # one start line per rubric
        done = {'verdict': 'approve', 'reviewed_sha': head, 'run_id': 'new', 'duration_s': 130,
                'cost_usd': 0.0712, 'cost_estimated': True}
        stop = {'verdict': 'request_changes', 'reviewed_sha': head, 'run_id': 'n2', 'duration_s': 4,
                'cost_usd': 0.02}
        ledger.write_text(json.dumps({'prs': {'63': {'state': {'naming': prior, 'generality': done,
                                                               'scope': stop}}}}))
        watch.finish()  # as when the engine exits: the final poll, then cases reused unchanged
        self.assertEqual([STAMP.sub('', line) for line in stream.getvalue().splitlines()], [
            'Rubric 6/10 generality: running (codex gpt-6.1-sol)…',
            'Rubric 3/10 scope: request_changes (4s, $0.02)',
            'Rubric 6/10 generality: approve (2m10s, est. $0.07)',
            'Rubric 8/10 naming: approve (reused: already current at this head)'])


class CliProgressTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-feedback-cli-')
        self.addCleanup(temp.cleanup)
        self.fixture = PostingFixture(Path(temp.name))

    def test_a_posted_review_reports_each_phase_in_order_on_stderr_only(self):
        (self.fixture.bin / 'claude-sleep').write_text('0.8')  # slow enough for the ledger poll
        run = self.fixture.run(extra=('--post',))
        self.assertEqual(run.returncode, 0, run.stderr)
        json.loads(run.stdout)  # stdout is exactly the --json document
        self.assertNotIn('\r', run.stderr)
        lines = run.stderr.splitlines()
        self.assertTrue(lines and all(STAMP.match(line) for line in lines), run.stderr)
        text = [STAMP.sub('', line) for line in lines]
        repo = 'https://github.com/thefundamentaltheor3m/SphereCeti/pull/1#issuecomment-'
        expected = [f'Preparing evidence for #1 at {self.fixture.head[:7]} (fetching pinned sources…)',
                    'Evidence for #1 ready in ', 'Posting "reviewing now" claim on #1…', 'claim posted: ' + repo]
        for i, rubric in enumerate(RUBRICS, 1):
            expected += [f'Rubric {i}/10 {rubric}: running (claude ', f'Rubric {i}/10 {rubric}: approve (']
        expected += ['Posting record…', 'posted ' + repo]
        position = 0
        for prefix in expected:
            found = next((k for k in range(position, len(text)) if text[k].startswith(prefix)), None)
            self.assertIsNotNone(found, f'{prefix!r} missing or out of order in:\n' + '\n'.join(text))
            position = found + 1
        self.assertIn('Rubric 1/10 correctness: approve (', '\n'.join(text))
        self.assertRegex('\n'.join(text), r'Rubric 1/10 correctness: approve \(\d+s, \$0\.01\)')

    def test_quiet_suppresses_progress_and_dry_runs_still_show_evidence(self):
        quiet = self.fixture.run(output='quiet', extra=('--dry-run', '--quiet'))
        self.assertEqual(quiet.returncode, 0, quiet.stderr)
        self.assertEqual(quiet.stderr, '')
        json.loads(quiet.stdout)
        loud = self.fixture.run(output='loud', extra=('--dry-run',))
        self.assertEqual(loud.returncode, 0, loud.stderr)
        json.loads(loud.stdout)
        self.assertEqual([STAMP.sub('', line).split(' ready in ')[0] for line in loud.stderr.splitlines()],
                         [f'Preparing evidence for #1 at {self.fixture.head[:7]} (fetching pinned sources…)',
                          'Evidence for #1'])


class QueueProgressTest(unittest.TestCase):
    def test_reviews_reports_the_survey_and_comment_reads(self):
        from sphereceti.review_queue import queue
        from test_review_queue import POLICY, PROJECT, Client, SurveyAPI, pr
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-feedback-queue-')
        self.addCleanup(temp.cleanup)
        stream = io.StringIO()
        previous = current()
        install(Progress(stream, tty=False))
        self.addCleanup(install, previous)
        queue(PROJECT, POLICY, OperatorPreferences(storage=temp.name), api=SurveyAPI([pr(n) for n in range(1, 13)]),
              client=Client())
        text = [STAMP.sub('', line) for line in stream.getvalue().splitlines()]
        self.assertEqual(text[0], 'Surveying open PRs… (12 open)')
        self.assertEqual(text[1:3], ['  scope 10/12', '  scope 12/12'])
        self.assertRegex(text[3], r'^Surveying open PRs… done in \d+s$')
        self.assertEqual(text[4:], ['  reading comments 10/12', '  reading comments 12/12'])


class ApprovalProgressTest(unittest.TestCase):
    def test_the_approval_outcome_gets_a_line(self):
        import test_review_approval as approval
        stream = io.StringIO()
        previous = current()
        install(Progress(stream, tty=False))
        self.addCleanup(install, previous)
        case = approval.ApprovalTest('test_opted_in_maintainer_submits_exactly_one_approve_after_readback')
        case.setUp()
        self.addCleanup(case.doCleanups)
        case.review()
        case.review(no_approve=True)
        text = [STAMP.sub('', line) for line in stream.getvalue().splitlines()]
        self.assertIn('approval: submitted', text)
        self.assertIn('approval: not submitted (--no-approve)', text)


if __name__ == '__main__':
    unittest.main()
