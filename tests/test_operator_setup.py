# SPDX-License-Identifier: Apache-2.0
"""First-run review preferences and `sphereceti setup`, with fake terminals and a fake Codex."""
from argparse import Namespace
import io
import os
from pathlib import Path
import pty
import select
import subprocess
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.config import OperatorPreferences, parse_operator
from sphereceti.operator_setup import (BUDGET_NOTE, SetupError, first_run, render, run_setup,
                                       write_new)
from review_fixture import ROOT, ReviewFixture
from test_review_select import BareReviewHarness


class Terminal(io.StringIO):
    def __init__(self, text='', tty=True):
        super().__init__(text)
        self.tty = tty

    def isatty(self):
        return self.tty


class FirstRunTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-setup-')
        self.addCleanup(temp.cleanup)
        self.path = Path(temp.name) / 'config/sphereceti/operator.toml'

    def ask(self, answers, tty=True, **kwargs):
        self.stderr = io.StringIO()
        return first_run(path=self.path, stdin=Terminal(answers, tty), stdout=Terminal(tty=tty),
                         stderr=self.stderr, **kwargs)

    def test_defaults_are_saved_with_private_mode(self):
        prefs = self.ask('\n\n')
        self.assertEqual(prefs, OperatorPreferences(provider='codex', budget_usd=5.0))
        self.assertEqual(self.path.read_text(), 'provider = "codex"\nbudget_usd = 5\n')
        self.assertEqual(self.path.stat().st_mode & 0o777, 0o600)
        self.assertEqual(parse_operator(self.path.read_text()), prefs)
        text = self.stderr.getvalue()
        self.assertIn('Review provider (claude, sonnet, codex, kiro, deepseek, minimax, grok) [codex]: ', text)
        self.assertIn(BUDGET_NOTE, text)
        self.assertIn('not a cap on subscription usage', text)
        self.assertIn(f'Saved review preferences to {self.path}. Change them with `sphereceti setup`.', text)

    def test_entered_values_and_invalid_answers_are_asked_again(self):
        prefs = self.ask('gpt\nclaude\nfree\nnan\n2.5\n')
        self.assertEqual((prefs.provider, prefs.budget_usd), ('claude', 2.5))
        self.assertEqual(self.path.read_text(), 'provider = "claude"\nbudget_usd = 2.5\n')
        self.assertEqual(self.stderr.getvalue().count('provider must be one of'), 1)
        self.assertEqual(self.stderr.getvalue().count('budget must be'), 2)

    def test_repeated_invalid_input_or_end_of_input_errors_without_a_file(self):
        for answers in ('x\ny\nz\n', 'codex\n', ''):
            with self.subTest(answers=answers), self.assertRaises(SetupError):
                self.ask(answers)
        self.assertFalse(self.path.exists())

    def test_command_line_provider_is_the_offered_default(self):
        self.assertEqual(self.ask('\n\n', provider='claude').provider, 'claude')

    def test_without_a_terminal_there_is_no_prompt(self):
        with self.assertRaises(SetupError) as error:
            self.ask('codex\n5\n', tty=False)
        self.assertEqual(str(error.exception), 'no review preferences yet; create them with '
                         '`sphereceti setup --provider codex --budget-usd 5` (or pass --provider and --budget-usd)')
        self.assertEqual(self.stderr.getvalue(), '')
        self.assertFalse(self.path.exists())

    def test_an_existing_file_is_never_overwritten(self):
        self.path.parent.mkdir(parents=True)
        self.path.write_text('provider = "claude"\nbudget_usd = 1\n')
        with self.assertRaises(SetupError):
            write_new(self.path, render(OperatorPreferences(provider='codex', budget_usd=5)))
        with self.assertRaises(SetupError):
            self.ask('\n\n')
        self.assertEqual(self.path.read_text(), 'provider = "claude"\nbudget_usd = 1\n')


class SetupCommandTest(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-setup-')
        self.addCleanup(temp.cleanup)
        self.path = Path(temp.name) / 'operator.toml'

    def setup(self, answers='', tty=True, **flags):
        self.stderr = io.StringIO()
        args = Namespace(provider=None, budget_usd=None, operator_config=self.path, **flags)
        return run_setup(args, stdin=Terminal(answers, tty), stdout=Terminal(tty=tty), stderr=self.stderr)

    def test_rerun_shows_current_values_offers_them_and_keeps_storage(self):
        self.path.write_text('provider = "claude"\nbudget_usd = 2\nstorage = "/srv/reviews"\n')
        message = self.setup('\n7\n')
        self.assertIn('Current preferences', self.stderr.getvalue())
        self.assertIn('provider = claude, budget_usd = 2', self.stderr.getvalue())
        self.assertIn('[claude]: ', self.stderr.getvalue())
        self.assertIn('[2]: ', self.stderr.getvalue())
        self.assertEqual(self.path.read_text(),
                         'provider = "claude"\nbudget_usd = 7\nstorage = "/srv/reviews"\n')
        self.assertEqual(self.path.stat().st_mode & 0o777, 0o600)
        self.assertEqual(message, f'Saved review preferences to {self.path}: provider = claude, budget_usd = 7.')

    def test_flags_need_no_terminal_and_bad_values_change_nothing(self):
        args = Namespace(provider='codex', budget_usd='5', operator_config=self.path)
        run_setup(args, stdin=Terminal(tty=False), stdout=Terminal(tty=False), stderr=io.StringIO())
        self.assertEqual(self.path.read_text(), 'provider = "codex"\nbudget_usd = 5\n')
        for provider, budget in (('nobody', '5'), ('codex', '0'), (None, '5')):
            args = Namespace(provider=provider, budget_usd=budget, operator_config=self.path)
            with self.subTest(provider=provider, budget=budget), self.assertRaises(SetupError):
                run_setup(args, stdin=Terminal(tty=False), stdout=Terminal(tty=False), stderr=io.StringIO())
        self.assertEqual(self.path.read_text(), 'provider = "codex"\nbudget_usd = 5\n')


class FirstRunCliTest(unittest.TestCase):
    """The real CLI in a pseudo-terminal: no preferences, then the same review continues."""

    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-first-run-')
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.fixture = ReviewFixture(self.root)
        self.fixture.codex_subscription()  # a ChatGPT-login Codex in HOME; no operator file is used
        self.saved = self.fixture.home / '.config/sphereceti/operator.toml'

    def command(self, *extra, output='result'):
        command = self.fixture.command(output=output, extra=('--rubrics', 'correctness', *extra))
        for flag in ('--operator-config', '--auth', '--json'):
            i = command.index(flag)
            del command[i:i + (1 if flag == '--json' else 2)]
        return command

    def in_terminal(self, command, answers):
        master, slave = pty.openpty()
        process = subprocess.Popen(command, stdin=slave, stdout=slave, stderr=slave, cwd=self.fixture.foreign,
                                   env=self.fixture.env, close_fds=True)
        os.close(slave)
        os.write(master, answers.encode())
        output, deadline = b'', time.monotonic() + 120
        while time.monotonic() < deadline:
            ready, _, _ = select.select([master], [], [], 1)
            if ready:
                try:
                    chunk = os.read(master, 4096)
                except OSError:
                    break
                if not chunk:
                    break
                output += chunk
            elif process.poll() is not None:
                break
        os.close(master)
        return process.wait(timeout=30), output.decode().replace('\r\n', '\n')

    def test_terminal_prompt_saves_defaults_and_the_review_continues(self):
        code, output = self.in_terminal(self.command(), '\n\n')
        self.assertEqual(code, 0, output)
        self.assertIn('Review provider', output)
        self.assertIn('not a cap on subscription usage', output)
        self.assertIn(f'Saved review preferences to {self.saved}', output)
        self.assertEqual(self.saved.read_text(), 'provider = "codex"\nbudget_usd = 5\n')
        self.assertEqual(self.saved.stat().st_mode & 0o777, 0o600)
        self.assertIn('Review #1: partial', output)
        self.assertEqual(len([c for c in self.fixture.codex_calls() if c['argv'][:1] == ['exec']]), 1)
        # The next review reads the saved file and asks nothing.
        code, output = self.in_terminal(self.command(output='second'), '')
        self.assertEqual(code, 0, output)
        self.assertNotIn('Review provider', output)

    def test_no_terminal_prints_the_command_and_never_prompts(self):
        process = subprocess.run(self.command(), cwd=self.fixture.foreign, env=self.fixture.env,
                                 capture_output=True, text=True, timeout=120, stdin=subprocess.DEVNULL)
        self.assertEqual(process.returncode, 2)
        self.assertEqual(process.stderr, 'sphereceti: no review preferences yet; create them with '
                         '`sphereceti setup --provider codex --budget-usd 5` (or pass --provider and --budget-usd)\n')
        self.assertNotIn('Review provider', process.stdout + process.stderr)
        self.assertFalse(self.saved.exists())
        self.assertFalse(self.fixture.codex_calls())

    def test_dry_run_and_explicit_budget_never_prompt(self):
        for extra in (('--dry-run',), ('--provider', 'codex', '--budget-usd', '3')):
            with self.subTest(extra=extra):
                code, output = self.in_terminal(self.command(*extra, output='out' + str(len(extra))), '')
                self.assertEqual(code, 0, output)
                self.assertNotIn('Review provider', output)
        self.assertFalse(self.saved.exists())


class BareFirstRunTest(BareReviewHarness):
    def bare(self, *extra):
        launcher = [sys.executable, '-c', f'import sys; sys.path.insert(0, {str(ROOT / "tools/project")!r}); '
                    'from sphereceti.cli import main; sys.exit(main())']
        command = [*launcher, 'review', '--source-repo', str(self.fixture.repo), '--dependencies-dir',
                   str(self.fixture.deps), '--output', str(self.root / 'result'), *extra]
        return subprocess.run(command, cwd=self.fixture.foreign, env=self.fixture.env, capture_output=True,
                              text=True, timeout=120, stdin=subprocess.DEVNULL)

    def test_bare_review_asks_only_once_a_review_will_start(self):
        process = self.bare()
        self.assertEqual(process.returncode, 2)
        self.assertTrue(process.stdout.startswith('Reviewing #47 '))
        self.assertIn('sphereceti setup --provider codex --budget-usd 5', process.stderr)
        self.assertFalse(self.fixture.calls())
        self.assertEqual(self.bare('--dry-run').returncode, 0)
        self.table['user']['login'] = 'bob'  # nothing qualifies: no preferences are needed
        self.queue[0]['author'] = {'login': 'bob'}
        self.write_table()
        nothing = self.bare()
        self.assertEqual(nothing.returncode, 0, nothing.stderr)
        self.assertTrue(nothing.stdout.startswith('No PRs need your review'))


if __name__ == '__main__':
    unittest.main()



class BatchFirstRunTest(unittest.TestCase):
    def test_a_batch_asks_once_before_its_first_review_and_uses_the_answer(self):
        from argparse import Namespace
        from datetime import timedelta
        from sphereceti.review_queue import run_batch
        from test_review_queue import POLICY as QUEUE_POLICY, PROJECT as QUEUE_PROJECT, Client, FakeRun, SurveyAPI, pr
        temp = tempfile.TemporaryDirectory(prefix='sphereceti-batch-setup-')
        self.addCleanup(temp.cleanup)
        api = SurveyAPI([pr(2, ago=timedelta(hours=3)), pr(3)])
        seen, asked = [], []

        class Run(FakeRun):
            def __call__(inner, args, project, prefs, guard):
                seen.append(prefs.provider)
                return FakeRun.__call__(inner, args, project, prefs, guard)

        def prepare():
            asked.append(True)
            return OperatorPreferences(provider='codex', budget_usd=5, storage=temp.name)
        args = Namespace(new=True, revised=False, all=False, limit=2, dry_run=False, post=False, no_post=True,
                         post_default=True, output=None, budget_usd=None, max_call_cost=1.0, provider=None,
                         codex_model=None, claude_model=None, kiro_model=None, local_sources=False,
                         read_records=False, shadow=None, replies_json=None, head=None, base=None,
                         description_file=None, reply_file=None, reply_rubric=None, mode='commit', pr=None)
        result = run_batch(args, QUEUE_PROJECT, QUEUE_POLICY, OperatorPreferences(storage=temp.name), api=api,
                           client=Client(), run=Run(api), prepare=prepare)
        self.assertEqual(asked, [True])
        self.assertEqual(seen, ['codex', 'codex'])
        self.assertEqual(result['reviewed'], 2)
