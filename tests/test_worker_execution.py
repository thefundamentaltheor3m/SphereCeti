# SPDX-License-Identifier: Apache-2.0
"""Adversarial worker coordination/dispatch tests with no network or paid provider."""
from copy import deepcopy
from dataclasses import replace
from datetime import timedelta
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools/project'))
from sphereceti import cli, local_review
from sphereceti.config import parse_policy, parse_project, parse_operator, resource_text
from sphereceti.worker import WorkerError
from sphereceti.worker_execution import ReviewGuard, NothingToDo
from sphereceti.worker_leases import Lease, active_claims, encode, utcnow, stamp, MARKER
from sphereceti.review_records import RecordError, sha
from test_review_records import result as review_result, comment as review_comment

PROJECT = parse_project(resource_text('sphereceti.toml'))
POLICY = replace(parse_policy(resource_text('automation.toml')), review_generation=True,
                 posting=True, authorized_reviewers=('user:7', 'user:8'))
PREFS = parse_operator('provider="claude"\nbudget_usd=5')


class API:
    def __init__(self):
        self.now = utcnow()
        self.all = []
        self.owner = 7
        self.calls = []
        self.fail_read = False
        self.fail_write = False
        self.after_write = None
        self.head, self.base, self.tooling = '2'*40, '3'*40, '1'*40
        self.closed = False
        self.description = 'body'

    def comments(self, repo, number):
        if self.fail_read:
            raise RecordError('API unavailable')
        return deepcopy(self.all)

    def approved_revision(self, repository, revision, current):
        return revision == current

    def call(self, endpoint, *, payload=None, **kwargs):
        self.calls.append((endpoint, payload))
        if self.fail_read and payload is None:
            raise RecordError('API unavailable')
        if endpoint == 'user':
            return {'type':'User', 'id':self.owner, 'login':'operator'}
        if '/pulls/' in endpoint:
            return {'number':1, 'state':'closed' if self.closed else 'open', 'draft':False,
                    'head':{'sha':self.head}, 'base':{'sha':self.base, 'repo':{'full_name':PROJECT.repository}},
                    'user':{'id':99}, 'title':'title', 'body':self.description}
        if endpoint.endswith('/commits/main'):
            return {'sha': self.tooling}
        if payload is not None:
            if self.fail_write:
                raise RecordError('POST unconfirmed')
            c = {'id':max([0]+[c['id'] for c in self.all])+1, 'body':payload['body'],
                 'user':{'id':self.owner,'type':'User'},
                 'issue_url':f'https://api.github.com/repos/{PROJECT.repository}/issues/1',
                 'created_at':stamp(self.now), 'updated_at':stamp(self.now)}
            self.all.append(c)
            if self.after_write:
                hook,self.after_write=self.after_write,None
                hook(c)
            return deepcopy(c)
        if '/issues/comments/' in endpoint:
            return deepcopy(next(c for c in self.all if c['id']==int(endpoint.split('/')[-1])))
        raise AssertionError(endpoint)


def context():
    r=review_result()
    r.update(source_mode='github', description_digest=sha('title\n\nbody'))
    return r


class LeaseTests(unittest.TestCase):
    def setUp(self):
        self.api=API()
        self.context=context()
        self.lease=Lease(self.api,self.context,POLICY.authorized_reviewers,'user:7','one',now=lambda:self.api.now)

    def active(self):
        return active_claims(self.api.all,self.context,POLICY.authorized_reviewers,self.api.now)

    def test_acquire_confirm_renew_release(self):
        self.assertTrue(self.lease.acquire())
        self.api.now+=timedelta(seconds=190)
        self.lease.check()
        self.assertEqual(self.lease.last['kind'],'renew')
        self.assertEqual(self.lease.last['sequence'],1)
        self.lease.release()
        self.assertEqual(self.active(),[])

    def test_duplicate_worker_does_not_post_or_dispatch(self):
        self.assertTrue(self.lease.acquire())
        second=Lease(self.api,self.context,POLICY.authorized_reviewers,'user:8','two',now=lambda:self.api.now)
        writes=len(self.api.all)
        self.assertFalse(second.acquire())
        self.assertEqual(len(self.api.all),writes)

    def test_expired_lease_cannot_renew_and_can_be_replaced(self):
        self.lease.acquire()
        self.api.now+=timedelta(seconds=301)
        with self.assertRaises(WorkerError): self.lease.check()
        replacement=Lease(self.api,self.context,POLICY.authorized_reviewers,'user:7','two',now=lambda:self.api.now)
        self.assertTrue(replacement.acquire())

    def test_new_head_has_separate_revision_bound_claim(self):
        self.lease.acquire()
        new=Lease(self.api,{**self.context,'head':'f'*40},POLICY.authorized_reviewers,'user:7','two',now=lambda:self.api.now)
        self.assertTrue(new.acquire())

    def test_identity_spoof_and_edited_lease_fail(self):
        self.lease.acquire()
        original=deepcopy(self.api.all)
        self.api.all[0]['user']['id']=8
        with self.assertRaises(WorkerError): self.active()
        self.api.all=deepcopy(original)
        self.api.all[0]['updated_at']=stamp(self.api.now+timedelta(seconds=1))
        with self.assertRaises(WorkerError): self.active()
        self.api.all=deepcopy(original)
        self.api.all[0]['user']['id']=900
        self.assertEqual(self.active(),[])

    def test_lost_race_releases_own_claim(self):
        # Simulate an earlier server comment becoming visible after our POST.
        earlier=Lease(self.api,self.context,POLICY.authorized_reviewers,'user:7','peer',now=lambda:self.api.now)
        earlier.acquire()
        hidden=self.api.all.pop()
        self.api.after_write=lambda c:(c.update(id=2),self.api.all.insert(0,hidden))
        self.assertFalse(self.lease.acquire())
        self.assertEqual(self.lease.last['kind'],'release')
        self.assertEqual(self.active()[0]['claim'],earlier.claim)

    def test_unconfirmed_write_or_readback_never_acquires(self):
        self.api.fail_write=True
        with self.assertRaises(RecordError): self.lease.acquire()
        self.assertIsNone(self.lease.last)
        self.api.fail_write=False
        self.api.after_write=lambda c:c.update(body='changed')
        with self.assertRaises(WorkerError): self.lease.acquire()
        self.assertIsNone(self.lease.last)

    def test_api_failure_never_becomes_empty(self):
        self.api.fail_read=True
        with self.assertRaises(RecordError): self.lease.acquire()
        self.assertFalse(self.api.all)

    def test_missing_or_forked_history_fails(self):
        self.lease.acquire()
        self.api.now+=timedelta(seconds=190)
        self.lease.check()
        self.api.all.pop(0)
        with self.assertRaises(WorkerError): self.active()

    def test_excessive_lifetime_wrong_issue_and_duplicate_pages_fail(self):
        self.lease.acquire()
        original=deepcopy(self.api.all)
        self.api.all.append(deepcopy(self.api.all[0]))
        with self.assertRaises(WorkerError): self.active()
        self.api.all=deepcopy(original)
        self.api.all[0]['issue_url']+='0'
        with self.assertRaises(WorkerError): self.active()
        self.api.all=deepcopy(original)
        data=json.loads(self.api.all[0]['body'][len(MARKER):-3])
        data['expires']=stamp(self.api.now+timedelta(hours=1))
        self.api.all[0]['body']=encode(data)
        with self.assertRaises(WorkerError): self.active()


class GuardTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.api=API(); self.report={**context(),'output':self.temp.name}
        self.args=local_review.add_parser(__import__('argparse').ArgumentParser().add_subparsers()).parse_args(['1'])
        self.guard=ReviewGuard(PROJECT,PREFS,{'pr':1,'head':'2'*40,'base':'3'*40},'test-worker')
        self.provider=patch('sphereceti.local_review.shutil.which',return_value='/fake/claude')
        self.provider.start(); self.addCleanup(self.provider.stop)

    def test_guard_yields_check_and_releases(self):
        with self.guard(self.args,self.report,POLICY,self.api) as check:
            check()
            self.assertEqual(self.guard.lease.last['kind'],'acquire')
        self.assertEqual(self.guard.lease.last['kind'],'release')
        self.assertEqual(self.guard.receipt['release'],'confirmed')

    def test_defaults_or_unapproved_tooling_prevent_all_writes(self):
        cases=[(self.report,replace(POLICY,review_generation=False)),
               (self.report,replace(POLICY,posting=False)),
               ({**self.report,'installed_tooling_matches_T':False},POLICY),
               ({**self.report,'tooling_approved':False},POLICY),
               ({**self.report,'config_differences':['lean-toolchain']},POLICY)]
        for report,policy in cases:
            with self.subTest(report=report),self.assertRaises(WorkerError):
                with self.guard(self.args,report,policy,self.api): pass
        self.assertFalse(self.api.all)

    def test_unavailable_provider_and_invalid_budget_precede_lease(self):
        with patch('sphereceti.local_review.shutil.which',return_value=None),self.assertRaises(local_review.ReviewError):
            with self.guard(self.args,self.report,POLICY,self.api): pass
        self.args.budget_usd=float('nan')
        with self.assertRaises(local_review.ReviewError):
            with self.guard(self.args,self.report,POLICY,self.api): pass
        self.assertFalse(self.api.all)

    def test_unauthorized_identity_cannot_claim(self):
        self.api.owner=900
        with self.assertRaises(WorkerError):
            with self.guard(self.args,self.report,POLICY,self.api): pass
        self.assertFalse(self.api.all)

    def test_changed_head_base_policy_description_or_closure_stops_work(self):
        for key,value in [('head','f'*40),('base','f'*40),('tooling','f'*40),('description','changed'),('closed',True)]:
            with self.subTest(key=key):
                api=API(); guard=ReviewGuard(PROJECT,PREFS,{'pr':1,'head':'2'*40,'base':'3'*40},'test')
                with self.assertRaises(WorkerError):
                    with guard(self.args,self.report,POLICY,api) as check:
                        setattr(api,key,value); check()
                self.assertEqual(guard.receipt['release'],'confirmed')

    def test_current_approval_or_negative_decision_does_not_spend_again(self):
        for verdict in ('approve','block'):
            r={**self.report,'verdicts':{k:verdict for k in local_review.RUBRICS}}
            self.api.all=[review_comment(r)[0]]
            with self.assertRaises(NothingToDo):
                with self.guard(self.args,self.report,POLICY,self.api): pass
            self.assertEqual(len(self.api.all),1)

    def test_engine_error_releases_and_release_outage_is_explicit(self):
        with self.assertRaises(RuntimeError):
            with self.guard(self.args,self.report,POLICY,self.api):
                raise RuntimeError('provider failed')
        self.assertEqual(self.guard.receipt['release'],'confirmed')
        with self.guard(self.args,self.report,POLICY,self.api):
            self.api.fail_write=True
        self.assertIn('unconfirmed',self.guard.receipt['release'])

    def test_default_cli_execute_is_disabled_without_network(self):
        out=io.StringIO()
        with patch('sys.stdout',out),patch('subprocess.run') as run:
            code=cli.main(['worker','run','--execute','--pr','1','--json'])
        self.assertEqual(code,0)
        self.assertEqual(json.loads(out.getvalue())['state'],'disabled')
        run.assert_not_called()

    def test_invalid_target_and_execution_flags_fail_before_network(self):
        for argv in (['--pr',''],['--post-review'],['--publish-state']):
            with patch('sys.stderr',io.StringIO()),patch('subprocess.run') as run,self.assertRaises(SystemExit) as exc:
                cli.main(['worker','run',*argv])
            self.assertEqual(exc.exception.code,2); run.assert_not_called()

    def test_empty_comment_page_envelope_is_not_a_confirmed_empty_queue(self):
        from sphereceti.review_post import GitHub
        with patch.object(GitHub,'call',return_value=[]),self.assertRaises(RecordError):
            GitHub().comments(PROJECT.repository,1)

    def test_sigterm_handler_restored_after_interruption(self):
        import signal
        from argparse import Namespace
        from sphereceti.worker_execution import run_round
        original=signal.getsignal(signal.SIGTERM)
        def stop(*args, **kwargs):
            signal.getsignal(signal.SIGTERM)(signal.SIGTERM,None)
        with patch('sphereceti.worker_execution._run_round',side_effect=stop),self.assertRaises(KeyboardInterrupt):
            run_round(Namespace(),PROJECT,POLICY,PREFS)
        self.assertIs(signal.getsignal(signal.SIGTERM),original)

    def test_heartbeat_failure_terminates_owned_process_group(self):
        from unittest.mock import Mock
        process=Mock(pid=123,args=['fake-provider'])
        process.wait.side_effect=[subprocess.TimeoutExpired('fake-provider',30),0]
        process.poll.return_value=None
        tick=Mock(side_effect=[None,WorkerError('lease lost')])
        with patch('sphereceti.local_review.subprocess.Popen',return_value=process),patch('os.killpg') as kill:
            with self.assertRaises(WorkerError):
                local_review.invoke_bridge(Path('/fake/request'),{},3,heartbeat=tick)
        kill.assert_called_once_with(123,__import__('signal').SIGTERM)
        self.assertEqual(tick.call_count,2)


if __name__=='__main__': unittest.main()
