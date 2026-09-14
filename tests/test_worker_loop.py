# SPDX-License-Identifier: Apache-2.0
"""Bounded-loop stop conditions and real shared-engine reuse without live providers."""
from copy import deepcopy
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from types import SimpleNamespace
import signal
import sys
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools/project'))
from sphereceti import cli
from sphereceti.worker import WorkerError
from sphereceti.worker_loop import run_loop
from sphereceti.worker_execution import run_round
from sphereceti.worker_cli import run_worker


class WorkerLoopTests(unittest.TestCase):
    def setUp(self):
        self.args=SimpleNamespace(max_rounds=3,interval_seconds=10,execute=True)
        self.project=SimpleNamespace(repository='thefundamentaltheor3m/SphereCeti')
        self.sleep=Mock()

    def outcome(self,n=1,state='complete'):
        return {'state':state,'pr':n,'head':'a'*40,'base':'b'*40}

    def loop(self,runner):
        return run_loop(self.args,self.project,None,None,round_runner=runner,sleep=self.sleep)

    def test_round_limit_and_fresh_assessed_set(self):
        runner=Mock(side_effect=[self.outcome(n) for n in (1,2,3)])
        result=self.loop(runner)
        self.assertEqual(result['state'],'round_limit')
        self.assertEqual([len(c.kwargs['assessed']) for c in runner.call_args_list],[0,1,2])
        self.assertEqual(self.sleep.call_count,2)

    def test_incomplete_or_disabled_outcomes_stop_without_retry(self):
        for state in ('error','partial','disabled','unavailable','planned'):
            with self.subTest(state=state):
                runner=Mock(return_value=self.outcome(state=state))
                self.assertEqual(self.loop(runner)['state'],state)
                runner.assert_called_once();self.sleep.assert_not_called()

    def test_unconfirmed_state_publication_stops(self):
        runner=Mock(return_value={**self.outcome(),'state_publication':{'state':'unconfirmed'}})
        self.assertEqual(self.loop(runner)['state'],'unconfirmed_publication')
        runner.assert_called_once();self.sleep.assert_not_called()

    def test_preview_is_one_round_without_sleep(self):
        self.args.execute=False
        runner=Mock(return_value=self.outcome(state='planned'))
        self.loop(runner);runner.assert_called_once();self.sleep.assert_not_called()

    def test_duplicate_outcome_and_missing_evidence_fail(self):
        for outcomes in ([self.outcome(),self.outcome()],[{'state':'complete'}]):
            with self.assertRaises(WorkerError):self.loop(Mock(side_effect=outcomes))

    def test_bounds_reject_before_survey(self):
        for field,value in [('max_rounds',None),('max_rounds',0),('max_rounds',21),
                            ('max_rounds',True),('interval_seconds',0),('interval_seconds',3601)]:
            with self.subTest(field=field,value=value):
                args=deepcopy(self.args);setattr(args,field,value)
                runner=Mock()
                with self.assertRaises(WorkerError):
                    run_loop(args,self.project,None,None,round_runner=runner,sleep=self.sleep)
                runner.assert_not_called()

    def test_error_propagates_without_retry_and_restores_signal_handler(self):
        prior=signal.getsignal(signal.SIGTERM)
        runner=Mock(side_effect=WorkerError('queue unknown'))
        with self.assertRaises(WorkerError):self.loop(runner)
        runner.assert_called_once();self.sleep.assert_not_called()
        self.assertIs(signal.getsignal(signal.SIGTERM),prior)

    def test_sigterm_during_pause_stops_before_next_round(self):
        prior=signal.getsignal(signal.SIGTERM)
        def stop(_):signal.getsignal(signal.SIGTERM)(signal.SIGTERM,None)
        runner=Mock(return_value=self.outcome())
        with self.assertRaises(KeyboardInterrupt):
            run_loop(self.args,self.project,None,None,round_runner=runner,sleep=stop)
        runner.assert_called_once()
        self.assertIs(signal.getsignal(signal.SIGTERM),prior)

    def test_bare_command_only_selects_read_only_plan(self):
        report={'schema':'sphereceti.worker-plan/v1','repository':self.project.repository,
                'selected':None,'pull_requests':[],'roadmap':{'reason':'not approved'},
                'execution_reason':'preview only'}
        with patch('sphereceti.worker_cli.run_worker',return_value=report) as run, redirect_stdout(StringIO()):
            self.assertEqual(cli.main([]),0)
        self.assertEqual(run.call_args.args[0].worker_command,'plan')

    def fixture(self):
        from test_worker_round import WorkerRoundTest
        case=WorkerRoundTest();case.setUp();self.addCleanup(case.doCleanups)
        case.args.loop=True;case.args.max_rounds=3;case.args.interval_seconds=10
        return case

    def test_real_loop_assesses_same_head_once_and_keeps_shared_accounting(self):
        case=self.fixture()
        sleep=Mock()
        result=run_loop(case.args,case.profile,case.policy,case.prefs,sleep=sleep)
        self.assertEqual([r['state'] for r in result['rounds']],['complete','unavailable'])
        self.assertEqual(len(case.fixture.calls()),10)
        self.assertEqual(len(case.archive_records()),1)
        sleep.assert_called_once_with(10)

    def test_assessed_review_never_hides_maintenance(self):
        case=self.fixture()
        case.snapshot['pull_requests'][0].update(author='operator',ci='failed')
        result=run_round(case.args,case.profile,case.policy,case.prefs,
                         assessed=frozenset({(1,case.fixture.head,case.fixture.tooling)}))
        self.assertEqual(result['plan']['selected']['stage'],'ci-repair')
        self.assertFalse(case.fixture.calls())

    def test_loop_disabled_policy_never_surveys(self):
        case=self.fixture()
        from dataclasses import replace
        with patch('sphereceti.worker_execution.survey') as survey:
            result=run_worker(case.args,case.profile,replace(case.policy,posting=False),case.prefs)
        self.assertEqual(result['state'],'disabled');survey.assert_not_called()


if __name__=='__main__':unittest.main()
