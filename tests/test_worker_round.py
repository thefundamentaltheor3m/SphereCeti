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
from review_fixture import git, commit
from test_worker_execution import API


class WorkerRoundTest(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.fixture=PostingFixture(self.root)
        f=self.fixture
        git(f.repo,'checkout','-q',f.tooling)
        profile=(f.repo/'sphereceti.toml').read_bytes()
        policy=(f.repo/'policy/automation.toml').read_bytes().replace(b'review_generation = false',b'review_generation = true')
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

    def test_unsupported_maintenance_never_falls_through_to_review(self):
        self.snapshot['pull_requests'][0].update(author='operator',ci='failed')
        self.assertEqual(self.run_round()['state'],'unavailable')
        self.assertFalse(self.api.calls)
        self.assertFalse(self.fixture.calls())


if __name__=='__main__':unittest.main()
