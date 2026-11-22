# SPDX-License-Identifier: Apache-2.0
"""Real shared-engine dispatch under fake GitHub and a fake provider; no external calls."""
from dataclasses import replace
from pathlib import Path
import json
import os
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools/project'))
from sphereceti import cli, local_review, review_resources
from sphereceti.config import parse_operator, parse_policy, parse_project
from sphereceti.worker import WorkerError
from sphereceti.worker_cli import add_parser
from sphereceti.worker_execution import run_round
from sphereceti.worker_leases import utcnow, stamp
from review_post_fixture import PostingFixture
from review_fixture import automation_policy, git, commit
from test_worker_execution import API


class WorkerRoundTest(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.fixture=PostingFixture(self.root)
        f=self.fixture
        git(f.repo,'checkout','-q',f.tooling)
        profile=(f.repo/'sphereceti.toml').read_bytes()
        policy=automation_policy(review_generation=True, posting=True,
                                 authorized_reviewers=('user:7',)).encode()
        self.files=review_resources.tooling_files()
        self.files.update({'sphereceti.toml':profile,'policy/automation.toml':policy})
        for name,body in self.files.items():
            path=f.repo/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(body)
        f.tooling=commit(f.repo)
        (f.repo/'README.md').write_text('PROPOSED SENTINEL: proposed roadmap')
        f.head=commit(f.repo)
        self.api=API();self.api.head=f.head;self.api.base=self.api.tooling=f.tooling
        self.profile=parse_project(profile.decode());self.policy=parse_policy(policy.decode())
        self.prefs=parse_operator(f.operator.read_text())
        self.snapshot={'schema':'sphereceti.worker-survey/v1','repository':self.profile.repository,
                       'actor':'operator','observed_at':stamp(utcnow()),'scope':[1],
                       'pull_requests':[{'number':1,'title':'title','author':'other','head':f.head,'base':f.tooling,
                         'updated_at':stamp(utcnow()),'state':'OPEN','draft':False,'mergeable':'MERGEABLE','ci':'passed'}]}
        import argparse
        parser=argparse.ArgumentParser();add_parser(parser.add_subparsers(dest='command'))
        self.args=parser.parse_args(['worker','run','--execute','--pr','1','--auth','api',
                                   '--source-repo',str(f.repo),'--dependencies-dir',str(f.deps)])
        for mock in (patch('sphereceti.local_review.tooling_files',return_value=self.files),
                     patch('sphereceti.review_resources.tooling_files',return_value=self.files),
                     patch('sphereceti.review_post.GitHub',return_value=self.api),
                     patch('sphereceti.worker_execution.survey',return_value=self.snapshot),
                     patch.dict(os.environ,f.env,clear=True)):
            mock.start();self.addCleanup(mock.stop)

    def run_round(self):return run_round(self.args,self.profile,self.policy,self.prefs)

    def test_real_engine_round_dispatches_once_and_preserves_shared_budget(self):
        receipt=self.run_round()
        self.assertEqual(receipt['state'],'complete')
        self.assertEqual(len(self.fixture.calls()),10)
        self.assertEqual(receipt['coordination']['release'],'confirmed')
        self.assertEqual(len(self.api.all),2)  # acquisition/release, no posted review by default
        self.assertTrue((Path(receipt['output'])/'worker-result.json').is_file())
        self.assertFalse(json.loads((Path(receipt['output'])/'result.json').read_text())['merge_eligible'])
        second=self.run_round()
        self.assertEqual(second['state'],'complete')
        self.assertEqual(len(self.fixture.calls()),10)  # same engine store/context, no second spend
        self.assertAlmostEqual(self.fixture.ledger()['days'][str(__import__('datetime').date.today())],0.1)

    def archive_records(self):
        from sphereceti.archive_store import snapshot, validate
        journal=self.root/'state/thefundamentaltheor3m__SphereCeti/archive/journal'
        return validate(snapshot(journal),self.profile.repository)

    def test_worker_execution_captures_all_completed_attempts(self):
        self.run_round()
        records=self.archive_records()
        self.assertEqual(len(records),1)
        self.assertEqual(len(records[0]['runs']),10)
        self.assertAlmostEqual(sum(r['cost_usd'] for r in records[0]['runs']),.1)

    def test_cancelled_bridge_retains_accounting_without_postable_approval(self):
        self.args.post_review=True
        invoke=local_review.invoke_bridge
        def cancelled(*args,**kwargs):
            invoke(*args,**kwargs)
            raise KeyboardInterrupt('cancel after completed attempts')
        with patch.object(local_review,'invoke_bridge',side_effect=cancelled):
            with self.assertRaises(KeyboardInterrupt):self.run_round()
        records=self.archive_records()
        self.assertEqual(records[0]['review']['completion'],'error')
        self.assertEqual(len(records[0]['runs']),10)
        self.assertAlmostEqual(sum(r['cost_usd'] for r in records[0]['runs']),.1)
        self.assertEqual(len(self.api.all),2)  # lease acquisition/release only
        self.assertEqual(len(self.fixture.calls()),10)

    def test_lease_loss_after_inference_captures_error_and_blocks_post(self):
        self.args.post_review=True
        invoke=local_review.invoke_bridge
        def drift(*args,**kwargs):
            code=invoke(*args,**kwargs)
            self.api.head='f'*40
            return code
        with patch.object(local_review,'invoke_bridge',side_effect=drift):
            with self.assertRaises(WorkerError):self.run_round()
        records=self.archive_records()
        self.assertEqual(records[0]['review']['completion'],'error')
        self.assertEqual(len(records[0]['runs']),10)
        self.assertEqual(len(self.api.all),2)

    def test_renewal_keeps_one_inference_dispatch_and_archive(self):
        from datetime import timedelta
        from sphereceti.worker_leases import Lease
        invoke=local_review.invoke_bridge
        def renew(*args,**kwargs):
            self.api.now+=timedelta(seconds=190)
            kwargs['heartbeat']()
            return invoke(*args,**kwargs)
        def lease(*args,**kwargs):return Lease(*args,**kwargs,now=lambda:self.api.now)
        with patch('sphereceti.worker_execution.Lease',side_effect=lease), \
                patch.object(local_review,'invoke_bridge',side_effect=renew) as dispatch:
            self.run_round()
        self.assertEqual(dispatch.call_count,1)
        self.assertEqual(len(self.fixture.calls()),10)
        self.assertEqual(len(self.api.all),3)  # acquire, renew, release
        self.assertEqual(len(self.archive_records()),1)

    def test_explicit_review_publication_uses_existing_authenticated_record(self):
        self.args.post_review=True
        receipt=self.run_round()
        self.assertEqual(receipt['publication']['state'],'confirmed')
        self.assertTrue(receipt['publication']['authorized'])
        self.assertEqual(len(self.api.all),3)
        second=self.run_round()
        self.assertEqual(second['state'],'idle')
        self.assertEqual(len(self.fixture.calls()),10)

    def test_provider_failure_does_not_fall_through_and_releases(self):
        (self.fixture.bin/'mode').write_text('error')
        receipt=self.run_round()
        self.assertNotEqual(receipt['state'],'complete')
        self.assertEqual(receipt['coordination']['release'],'confirmed')
        self.assertEqual({c[0] for c in self.api.calls if '/pulls/' in c[0]},
                         {f'repos/{self.profile.repository}/pulls/1'})

    def test_changed_head_between_survey_and_dispatch_prevents_spend(self):
        self.api.head=self.fixture.tooling
        with self.assertRaises(WorkerError):self.run_round()
        self.assertFalse(self.fixture.calls())
        self.assertFalse(self.api.all)

    def test_low_budget_leaves_no_provider_calls(self):
        self.args.budget_usd=1
        store=self.root/'state/thefundamentaltheor3m__SphereCeti/engine'
        store.mkdir(parents=True)
        day=str(__import__('datetime').date.today())
        (store/'ledger.json').write_text(json.dumps({'days':{day:1.0},'prs':{}}))
        receipt=self.run_round()
        self.assertNotEqual(receipt['state'],'complete')
        self.assertFalse(self.fixture.calls())
        self.assertEqual(receipt['coordination']['release'],'confirmed')

    def codex_round(self,*extra):
        import argparse
        self.fixture.codex_subscription()
        parser=argparse.ArgumentParser();add_parser(parser.add_subparsers(dest='command'))
        self.args=parser.parse_args(['worker','run','--execute','--pr','1','--provider','codex',
                                     '--auth','subscription','--source-repo',str(self.fixture.repo),
                                     '--dependencies-dir',str(self.fixture.deps),*extra])
        return self.run_round()

    def test_explicit_codex_model_reaches_the_subscription_provider(self):
        receipt=self.codex_round('--codex-model','gpt-6.1-sol')
        self.assertEqual(receipt['state'],'complete')
        self.assertEqual(receipt['codex_model'],'gpt-6.1-sol')
        self.assertEqual(json.loads((Path(receipt['output'])/'worker-result.json').read_text())['codex_model'],
                         'gpt-6.1-sol')
        calls=self.fixture.codex_calls()
        self.assertEqual(len(calls),10)
        self.assertFalse(self.fixture.calls())
        for call in calls:
            self.assertEqual(call['argv'][call['argv'].index('-m')+1],'gpt-6.1-sol')
            self.assertIsNone(call['openai_key'])
            self.assertIn('FAKE-CHATGPT-LOGIN',call['auth'])
            self.assertEqual(call['leaked'],[])
        [record]=self.archive_records()
        self.assertEqual(record['request']['auth'],'subscription')
        self.assertEqual({(r['provider'],r['model']) for r in record['runs']},{('codex','gpt-6.1-sol')})
        self.assertTrue(all(r['cost_estimated'] for r in record['runs']))
        # Same estimate and shared ledger as the direct command: ten rubrics at $0.058 each.
        self.assertAlmostEqual(sum(r['cost_usd'] for r in record['runs']),.58)
        self.assertAlmostEqual(self.fixture.ledger()['days'][str(__import__('datetime').date.today())],.58)
        self.assertEqual(len(self.api.all),2)  # lease acquisition/release only

    def test_unspecified_codex_model_keeps_the_engine_default(self):
        receipt=self.codex_round()
        self.assertEqual(receipt['state'],'complete')
        self.assertNotIn('codex_model',receipt)
        models={c['argv'][c['argv'].index('-m')+1] for c in self.fixture.codex_calls()}
        self.assertEqual(models,{'gpt-5.6-sol'})
        self.assertEqual({r['model'] for r in self.archive_records()[0]['runs']},{'gpt-5.6-sol'})

    def test_unpriced_codex_model_is_rejected_before_inference(self):
        receipt=self.codex_round('--codex-model','gpt-99-sol')
        self.assertEqual(receipt['state'],'error')
        self.assertEqual(receipt['codex_model'],'gpt-99-sol')
        self.assertFalse(self.fixture.codex_calls())
        self.assertEqual(receipt['coordination']['release'],'confirmed')

    def live_survey(self, after=None):
        """Real survey/normalization over a fake read-only gh that reports the fake PR's head."""
        from sphereceti.worker_cli import survey
        from test_worker import gh_pr
        api, reads = self.api, []
        class GH:
            def read(self, args):
                reads.append(args)
                assert args[0] == 'api' and 'GET' in args or args[:2] == ['pr', 'view'], args
                return ({'login': 'operator'} if args[0] == 'api' else
                        gh_pr(1, headRefOid=api.head, baseRefOid=api.base))
        def observe(project, requested):
            result = survey(project, requested, api=GH())
            if after:
                after()
            return result
        self.reads = reads
        return patch('sphereceti.worker_execution.survey', side_effect=observe)

    def cli(self, *extra):
        """`sphereceti worker run` with the explicit enabled fixture policy and profile."""
        import io
        out = io.StringIO()
        with patch('sys.stdout', out), patch('sphereceti.cli.parse_project', return_value=self.profile), \
                patch('sphereceti.cli.parse_policy', return_value=self.policy):
            code = cli.main(['worker', 'run', '--pr', '1', '--operator-config', str(self.fixture.operator),
                             '--json', *extra])
        return code, json.loads(out.getvalue())

    def execute(self, *extra):
        self.fixture.codex_subscription()
        return self.cli('--execute', '--provider', 'codex', '--auth', 'subscription',
                        '--source-repo', str(self.fixture.repo), '--dependencies-dir', str(self.fixture.deps),
                        *extra)

    def test_expected_head_changed_after_preview_makes_no_model_call_or_write(self):
        authorized = self.fixture.head
        with self.live_survey():
            code, preview = self.cli('--expect-head', authorized)
            self.assertEqual((code, preview['state']), (0, 'planned'))
            self.assertEqual(preview['plan']['selected']['head'], authorized)
            # The PR advances after the operator's authorization to a real, reviewable head B.
            (self.fixture.repo / 'README.md').write_text('PROPOSED SENTINEL: a newer head')
            advanced = self.api.head = commit(self.fixture.repo)
            code, receipt = self.execute('--expect-head', authorized, '--post-review', '--publish-state')
        self.assertEqual(code, 1)
        self.assertEqual(receipt['state'], 'stale_authorization')
        self.assertFalse(receipt['executed'])
        self.assertIn('head changed since authorization', receipt['reason'])
        self.assertEqual((receipt['pr'], receipt['expected_head'], receipt['observed_head']),
                         (1, authorized, advanced))
        self.assertFalse(self.fixture.codex_calls())  # the fake Codex never ran
        self.assertFalse(self.fixture.calls())
        self.assertEqual(self.api.calls, [])  # no REST call at all, hence no POST/PATCH/PUT/DELETE
        self.assertFalse(self.api.all)
        self.assertTrue(all(r[0] == 'pr' or r[:5] == ['api', '--hostname', 'github.com', '--method', 'GET']
                            for r in self.reads))
        self.assertFalse((self.root / 'state/thefundamentaltheor3m__SphereCeti/runs').exists())
        with self.live_survey():  # the read-only preview reports the same refusal
            self.assertEqual(self.cli('--expect-head', authorized)[0], 1)
            self.assertEqual(self.cli('--expect-head', authorized, '--expect-base', 'c' * 40)[1]['state'],
                             'stale_authorization')
        self.assertEqual(self.api.calls, [])

    def test_changed_expected_base_alone_stops_before_any_write(self):
        with self.live_survey():
            code, receipt = self.execute('--expect-head', self.fixture.head, '--expect-base', 'c' * 40)
        self.assertEqual((code, receipt['state']), (1, 'stale_authorization'))
        self.assertIn('base changed since authorization', receipt['reason'])
        self.assertEqual(receipt['observed_base'], self.fixture.tooling)
        self.assertFalse(self.fixture.codex_calls())
        self.assertEqual(self.api.calls, [])

    def test_matching_expected_head_proceeds_as_without_it(self):
        with self.live_survey():
            code, receipt = self.execute('--expect-head', self.fixture.head, '--expect-base', self.fixture.tooling)
        self.assertEqual((code, receipt['state']), (0, 'complete'))
        self.assertEqual((receipt['head'], receipt['base']), (self.fixture.head, self.fixture.tooling))
        self.assertEqual(len(self.fixture.codex_calls()), 10)
        self.assertEqual(receipt['coordination']['release'], 'confirmed')
        self.assertEqual(len(self.api.all), 2)  # lease acquisition/release, as without the option
        self.assertNotIn('expected_head', receipt)
        stored = json.loads((Path(receipt['output']) / 'worker-result.json').read_text())
        self.assertEqual(stored['state'], 'complete')

    def test_head_change_after_matching_survey_still_stops_the_round(self):
        def advance():
            self.api.head = self.fixture.tooling
        with self.live_survey(after=advance), patch('sys.stderr') as err, self.assertRaises(SystemExit) as exit:
            self.execute('--expect-head', self.fixture.head, '--post-review')
        self.assertEqual(exit.exception.code, 2)
        self.assertFalse(self.fixture.codex_calls())
        self.assertFalse(self.api.all)
        self.assertTrue(all(payload is None for _, payload in self.api.calls))

    def budget_round(self,budget,reservation,*,alternate=False,spent=None):
        """A pinned Sol61 round; each fake Codex attempt reports 300k fresh input and 1k output."""
        from datetime import datetime,timezone
        from sphereceti.review_cost_bound import RequestLimits,installed_price_windows,round_cost_bound
        (self.fixture.bin/'codex-usage.json').write_text(json.dumps(
            {'input_tokens':300000,'cached_input_tokens':0,'output_tokens':1000}))
        if alternate:(self.fixture.bin/'codex-alternate').write_text('')
        day=datetime.now(timezone.utc).strftime('%Y-%m-%d')  # the engine's UTC ledger day
        if spent is not None:
            store=self.root/'state/thefundamentaltheor3m__SphereCeti/engine';store.mkdir(parents=True)
            (store/'ledger.json').write_text(json.dumps({'days':{day:spent},'prs':{}}))
        receipt=self.codex_round('--codex-model','gpt-6.1-sol','--budget-usd',str(budget),
                                 '--max-call-cost',str(reservation))
        attempts=len(self.fixture.codex_calls())
        bound=round_cost_bound(installed_price_windows(),('gpt-6.1-sol',),RequestLimits(300000,1000,1))
        ledger=self.fixture.ledger()['days'].get(day,0)
        # Analytics price of what the provider would bill: the whole request at the long-context tier.
        return receipt,attempts,ledger,attempts*1.215,bound

    def test_budget_is_a_stop_threshold_checked_only_before_each_rubric(self):
        # $0.61 is charged per rubric after it finishes, against a $0.10 reservation: the second
        # rubric starts at $0.61 + $0.10 <= $1 and lands the ledger $0.22 above the threshold.
        receipt,attempts,ledger,true,bound=self.budget_round(1,0.1)
        self.assertEqual(receipt['state'],'partial')
        self.assertEqual(attempts,2)
        self.assertAlmostEqual(ledger,1.22)
        self.assertLessEqual(ledger-1,bound.ledger_overshoot(0.1))
        self.assertLessEqual(true,bound.spend_ceiling(1,0.1))
        self.assertLessEqual(true-1,bound.overshoot(1,0.1))
        self.assertEqual(receipt['coordination']['release'],'confirmed')

    def test_retried_rubric_is_charged_after_both_attempts(self):
        # Every odd attempt yields no verdict, so each rubric uses its one retry before the next check.
        receipt,attempts,ledger,true,bound=self.budget_round(2,0.1,alternate=True)
        self.assertEqual(receipt['state'],'partial')
        self.assertEqual(attempts,4)
        self.assertAlmostEqual(ledger,2.44)
        self.assertAlmostEqual(bound.ledger_per_rubric,1.22)
        self.assertLessEqual(ledger-2,bound.ledger_overshoot(0.1))
        self.assertLessEqual(true,bound.spend_ceiling(2,0.1))

    def test_covering_reservation_keeps_the_ledger_within_the_budget(self):
        receipt,attempts,ledger,true,bound=self.budget_round(4,3.03)
        self.assertAlmostEqual(bound.reservation,3.03)
        self.assertEqual(attempts,2)
        self.assertAlmostEqual(ledger,1.22)
        self.assertLessEqual(ledger,4)
        self.assertEqual(bound.ledger_overshoot(3.03),0)
        self.assertLessEqual(true,bound.spend_ceiling(4,3.03))

    def test_reached_threshold_starts_no_new_work(self):
        receipt,attempts,ledger,true,bound=self.budget_round(1,0.5,spent=0.51)
        self.assertNotEqual(receipt['state'],'complete')
        self.assertEqual(attempts,0)
        self.assertAlmostEqual(ledger,0.51)
        self.assertEqual(bound.spend_ceiling(1,0.5,spent_today=0.51),0)
        self.assertEqual(receipt['coordination']['release'],'confirmed')

    # Enforced canary limits: no sub-agents, a per-attempt deadline, and a stop on unknown usage.

    def canary_round(self,*extra,hang=None,no_usage=False,alternate=False):
        for name,on,body in (('codex-hang',hang,hang),('codex-no-usage',no_usage,''),
                             ('codex-alternate',alternate,'')):
            if on:(self.fixture.bin/name).write_text(body)
        return self.codex_round('--codex-model','gpt-6.1-sol',*extra)

    def exec_calls(self):
        return [c for c in self.fixture.codex_calls() if c['argv'][:1]==['exec']]

    def assert_gone(self,*pids):
        """Every pid has exited (a zombie awaiting its reaper counts as exited)."""
        import time
        deadline=time.monotonic()+10
        for pid in pids:
            while True:
                try:
                    state=Path(f'/proc/{pid}/stat').read_text().rsplit(')',1)[1].split()[0]
                except (FileNotFoundError,ProcessLookupError):
                    break
                if state=='Z':break
                self.assertLess(time.monotonic(),deadline,f'process {pid} still running')
                time.sleep(0.1)

    def unknown_facts(self,receipt):
        """The attempt facts as archived, and the ledger's unknown-usage marker for today."""
        from datetime import datetime,timezone
        day=datetime.now(timezone.utc).strftime('%Y-%m-%d')
        [record]=self.archive_records()
        return record['runs'],self.fixture.ledger(),day

    def test_codex_attempts_run_without_sub_agents_in_their_own_process_group(self):
        receipt=self.canary_round()
        self.assertEqual(receipt['state'],'complete')
        calls,debug=self.exec_calls(),self.fixture.codex_debug_calls()
        self.assertEqual(len(calls),10)
        self.assertEqual([d['argv'] for d in debug],[['debug','models','--bundled']]*10)
        for call,probe in zip(calls,debug):
            self.assertEqual(probe['codex_home'],call['codex_home'])  # the attempt's own Codex binary/home
            self.assertIn('features.multi_agent_v2=false',call['settings'])
            self.assertIn('features.multi_agent=false',call['settings'])
            [catalog]=[v for v in call['settings'] if v.startswith('model_catalog_json=')]
            self.assertTrue(Path(json.loads(catalog.split('=',1)[1])).is_relative_to(call['tmpdir']))
            # The bundled catalog, unchanged except that no model is marked for sub-agents.
            self.assertEqual(call['catalog'],{'models':[{'slug':'gpt-6.1-sol','context_window':500000},
                                                        {'slug':'gpt-5.6-sol'}]})
            self.assertTrue(call['pgid_is_own'])
            self.assertEqual(call['argv'][call['argv'].index('-m')+1],'gpt-6.1-sol')

    def test_timed_out_attempt_stops_its_children(self):
        receipt=self.canary_round('--attempt-timeout','2',hang='all')
        [pids]=self.fixture.codex_pids()
        self.assert_gone(pids['leader'],pids['child'])
        self.assertEqual(len(self.exec_calls()),1)
        self.assertEqual(receipt['stop_reason'],'usage_unknown')
        runs,ledger,day=self.unknown_facts(receipt)
        [attempt]=runs[0]['attempts']
        self.assertEqual(attempt['returncode'],124)
        self.assertEqual(ledger['unknown_usage'][day][0]['reasons'],['timeout'])

    def test_missing_usage_is_recorded_as_unknown_not_zero(self):
        receipt=self.canary_round(no_usage=True)
        self.assertEqual(len(self.exec_calls()),1)  # it approved, but its price is unknown
        runs,ledger,day=self.unknown_facts(receipt)
        [run]=runs
        self.assertEqual(run['usage_status'],'unknown')
        self.assertNotIn('cost_usd',run)
        [attempt]=run['attempts']
        self.assertEqual(attempt['usage_status'],'unknown')
        self.assertNotIn('cost_usd',attempt)
        self.assertNotIn('usage',attempt)
        [entry]=ledger['unknown_usage'][day]
        self.assertEqual((entry['rubric'],entry['model'],entry['attempts'],entry['reasons']),
                         ('correctness','gpt-6.1-sol',1,['not_reported']))
        self.assertNotIn('in_flight',ledger)
        self.assertEqual(receipt['usage_unknown_rubrics'],['correctness'])
        stored=json.loads((Path(receipt['output'])/'worker-result.json').read_text())
        self.assertEqual(stored['stop_reason'],'usage_unknown')

    def test_unknown_usage_stops_before_a_retry_or_another_rubric(self):
        # The first attempt has neither a verdict nor usage; ordinarily the engine would retry it.
        receipt=self.canary_round(no_usage=True,alternate=True)
        self.assertEqual(len(self.exec_calls()),1)
        self.assertEqual(receipt['state'],'partial')
        self.assertEqual(receipt['stop_reason'],'usage_unknown')
        result=json.loads((Path(receipt['output'])/'result.json').read_text())
        self.assertEqual(result['finished_rubrics'],[])
        self.assertEqual([r for r,v in result['verdicts'].items() if v!='absent'],['correctness'])
        stop=json.loads((Path(receipt['output'])/'usage-stop.json').read_text())
        self.assertEqual((stop['after_rubric'],stop['unknown_rubrics']),('correctness',['correctness']))
        rounds=self.fixture.ledger()['prs']['1']['rounds']
        self.assertEqual(rounds[-1]['stop_reason'],'usage_unknown')

    def test_first_attempt_timeout_loses_no_process_records_unknown_and_starts_nothing_more(self):
        # The fake answers every attempt after the first, so any retry or later rubric would show.
        receipt=self.canary_round('--attempt-timeout','2',hang='first')
        [pids]=self.fixture.codex_pids()
        self.assert_gone(pids['child'],pids['leader'])               # (1) the child too
        runs,ledger,day=self.unknown_facts(receipt)
        [run]=runs
        [attempt]=run['attempts']                                     # (2) unknown, not zero
        self.assertEqual((attempt['usage_status'],run['usage_status']),('unknown','unknown'))
        self.assertNotIn('cost_usd',attempt);self.assertNotIn('cost_usd',run)
        self.assertEqual(ledger['unknown_usage'][day][0]['reasons'],['timeout'])
        self.assertEqual(ledger['days'].get(day,0),0)                 # only known spend is summed
        self.assertEqual(receipt['stop_reason'],'usage_unknown')
        self.assertEqual(len(self.exec_calls()),1)                    # (3) no retry, no next rubric
        self.assertEqual(len(self.fixture.codex_debug_calls()),1)
        self.assertEqual(receipt['coordination']['release'],'confirmed')

    def test_whole_run_deadline_stops_the_attempt_group_and_marks_usage_unknown(self):
        with patch.object(local_review,'RUN_TIMEOUT',4):
            receipt=self.canary_round(hang='all')
        [pids]=self.fixture.codex_pids()
        self.assert_gone(pids['child'],pids['leader'])
        self.assertEqual(receipt['state'],'error')
        self.assertEqual(receipt['stop_reason'],'usage_unknown')
        from datetime import datetime,timezone
        day=datetime.now(timezone.utc).strftime('%Y-%m-%d')
        ledger=self.fixture.ledger()
        self.assertNotIn('in_flight',ledger)
        [entry]=ledger['unknown_usage'][day]
        self.assertEqual((entry['rubric'],entry['reasons']),('correctness',['run_stopped']))

    def only_attempt(self):
        runs,ledger,day=self.unknown_facts(None)
        [run]=runs
        [attempt]=run['attempts']
        return run,attempt,ledger,day

    def test_partial_usage_is_unknown_and_starts_no_later_rubric(self):
        # (e) A usage event without cached_input_tokens or output_tokens, then a normal verdict.
        (self.fixture.bin/'codex-usage.json').write_text(json.dumps({'input_tokens':1000}))
        receipt=self.canary_round()
        self.assertEqual(len(self.exec_calls()),1)
        run,attempt,ledger,day=self.only_attempt()
        self.assertEqual((attempt['usage_status'],run['usage_status']),('unknown','unknown'))
        self.assertEqual(attempt['usage'],{'input_tokens':1000})  # retained as provenance only
        self.assertNotIn('cost_usd',attempt);self.assertNotIn('cost_usd',run)
        self.assertEqual(ledger['unknown_usage'][day][0]['reasons'],['incomplete'])
        self.assertEqual(ledger['days'].get(day,0),0)
        self.assertEqual(receipt['stop_reason'],'usage_unknown')

    def test_partial_usage_without_a_verdict_is_not_retried(self):
        (self.fixture.bin/'codex-usage.json').write_text(json.dumps({'input_tokens':1000,'output_tokens':5}))
        receipt=self.canary_round(alternate=True)  # a retry would answer
        self.assertEqual(len(self.exec_calls()),1)
        run,attempt,ledger,day=self.only_attempt()
        self.assertEqual(attempt['usage_status'],'unknown')
        self.assertNotIn('cost_usd',attempt)
        self.assertEqual(ledger['unknown_usage'][day][0]['reasons'],['incomplete'])
        self.assertEqual(receipt['stop_reason'],'usage_unknown')

    def test_usage_printed_before_a_timeout_is_still_unknown(self):
        # (f) A complete-looking usage event, then a hang past the deadline; a retry would answer.
        (self.fixture.bin/'codex-usage-before-hang').write_text('')
        receipt=self.canary_round('--attempt-timeout','2',hang='first')
        [pids]=self.fixture.codex_pids()
        self.assert_gone(pids['leader'],pids['child'])
        self.assertEqual(len(self.exec_calls()),1)
        run,attempt,ledger,day=self.only_attempt()
        self.assertEqual(attempt['usage_status'],'unknown')
        self.assertEqual(attempt['usage'],{'input_tokens':1000,'cached_input_tokens':0,'output_tokens':10})
        self.assertNotIn('cost_usd',attempt);self.assertNotIn('cost_usd',run)
        self.assertEqual(ledger['unknown_usage'][day][0]['reasons'],['timeout_after_usage'])
        self.assertEqual(ledger['days'].get(day,0),0)
        self.assertEqual(receipt['stop_reason'],'usage_unknown')

    def test_catalog_probe_and_exec_share_one_attempt_deadline(self):
        # (g) The probe takes 2.5 of the 3 seconds; exec gets the remainder, not a fresh 3 seconds.
        (self.fixture.bin/'codex-probe-sleep').write_text('2.5')
        receipt=self.canary_round('--attempt-timeout','3',hang='all')
        self.assertEqual(len(self.exec_calls()),1)  # exec started inside the shared deadline
        [pids]=self.fixture.codex_pids()
        self.assert_gone(pids['leader'],pids['child'])
        run,attempt,ledger,day=self.only_attempt()
        self.assertGreaterEqual(attempt['secs'],2.9)
        self.assertLess(attempt['secs'],4.5)  # separate deadlines would take at least 5.5 seconds
        self.assertEqual(attempt['usage_status'],'unknown')
        self.assertEqual(ledger['unknown_usage'][day][0]['reasons'],['timeout'])
        self.assertEqual(receipt['stop_reason'],'usage_unknown')
        self.assertEqual(len(self.fixture.codex_debug_calls()),1)

    def test_nonzero_exit_after_complete_usage_and_verdict_is_unknown_and_rejected(self):
        # Complete counters and a valid approve verdict, then exit 1; a retry would answer.
        (self.fixture.bin/'codex-exit').write_text('1')
        receipt=self.canary_round()
        self.assertEqual(len(self.exec_calls()),1)                    # no retry, no next rubric
        result=json.loads((Path(receipt['output'])/'result.json').read_text())
        self.assertEqual(result['verdicts']['correctness'],'error')  # the approve is rejected
        self.assertEqual(result['finished_rubrics'],[])
        run,attempt,ledger,day=self.only_attempt()
        self.assertEqual(attempt['returncode'],1)
        self.assertEqual(attempt['usage'],{'input_tokens':100000,'cached_input_tokens':80000,
                                           'output_tokens':1000,'reasoning_output_tokens':400})
        self.assertEqual((attempt['usage_status'],run['usage_status']),('unknown','unknown'))
        self.assertNotIn('cost_usd',attempt);self.assertNotIn('cost_usd',run)
        self.assertEqual(ledger['unknown_usage'][day][0]['reasons'],['exit_nonzero_after_usage'])
        self.assertEqual(ledger['days'].get(day,0),0)
        self.assertEqual(ledger['prs']['1']['state']['correctness']['verdict'],'error')
        self.assertEqual(receipt['stop_reason'],'usage_unknown')
        self.assertEqual(json.loads((Path(receipt['output'])/'usage-stop.json').read_text())['after_rubric'],
                         'correctness')

    def test_unsupported_maintenance_never_falls_through_to_review(self):
        self.snapshot['pull_requests'][0].update(author='operator',ci='failed')
        self.assertEqual(self.run_round()['state'],'unavailable')
        self.assertFalse(self.api.calls)
        self.assertFalse(self.fixture.calls())


if __name__=='__main__':unittest.main()
