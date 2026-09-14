"""Controller, activation, credential boundary and restart tests; no external writes."""
from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest.mock import patch
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools/project'))
from sphereceti.merge_activation import WORKFLOW, executor, parse_controller, protections
from sphereceti.merge_controller import Writer, local_lock, reconcile
from sphereceti.review_records import RecordError
from sphereceti.config import resource_text

REPO='thefundamentaltheor3m/SphereCeti'
T='1'*40;H='2'*40;M='3'*40


def setup_data():
    settings={'schema_version':1,'workflow_id':10,'bot_user_id':7,'checks_app_id':9,'merge_method':'squash'}
    account={'id':7,'type':'User','login':'dedicated-machine','site_admin':False}
    permission={'permission':'write','role_name':'write','user':{'id':7}}
    protection={'url':f'https://api.github.com/repos/{REPO}/branches/main/protection',
                'required_status_checks':{'strict':True,'checks':[{'context':c,'app_id':9} for c in ('trusted-build','trusted-scope')]},
                'enforce_admins':{'enabled':True},'allow_force_pushes':{'enabled':False},'allow_deletions':{'enabled':False},
                'required_pull_request_reviews':{'required_approving_review_count':1,'dismiss_stale_reviews':True,
                                                 'bypass_pull_request_allowances':{'users':[],'teams':[],'apps':[]}}}
    env={'GITHUB_ACTIONS':'true','GITHUB_REPOSITORY':REPO,'GITHUB_REF':'refs/heads/main','GITHUB_SHA':T,
         'GITHUB_WORKFLOW_REF':f'{REPO}/{WORKFLOW}@refs/heads/main','GITHUB_RUN_ID':'100','GITHUB_RUN_ATTEMPT':'1'}
    run={'id':100,'run_attempt':1,'workflow_id':10,'head_sha':T,'head_branch':'main','path':WORKFLOW,
         'status':'in_progress','event':'workflow_dispatch','repository':{'full_name':REPO}}
    return settings,account,permission,protection,env,run


class FakeBackend:
    def __init__(self):
        self.activation={'ready':True,'executor_verified':True,'tooling':T,'policy_digest':'a','merging_requested':True}
        self.pr={'number':1,'state':'open','merged':False,'draft':False,'head':{'sha':H},'merge_commit_sha':None}
        self.decision={'eligibility':'eligible','head':H,'base':T,'tooling':T,'reasons':[]}
        self.setups=0;self.observations=0;self.puts=[];self.refreshed=0
        self.change_setup=None;self.change_observation=None;self.on_refresh=None;self.ambiguous=False;self.reject=False
    def setup(self,applying):
        self.setups+=1
        return deepcopy(self.change_setup if self.setups==2 and self.change_setup is not None else self.activation)
    def state(self,number):return deepcopy(self.pr)
    def observation(self,number):
        self.observations+=1
        return deepcopy(self.change_observation if self.observations==2 and self.change_observation is not None else self.decision)
    def refresh(self):
        self.refreshed+=1
        if self.on_refresh:self.on_refresh()
    def merge(self,number,head):
        self.puts.append((number,head))
        if self.reject:raise RecordError('server refused the changed base/head or required checks')
        self.pr.update(merged=True,state='closed',merge_commit_sha=M)
        if self.ambiguous:raise RecordError('network timeout after PUT')
        return {'merged':True,'sha':M}


class ControllerTests(unittest.TestCase):
    def test_preview_never_merges_and_apply_attempts_at_most_one(self):
        b=FakeBackend();r=reconcile(b,lambda:[1,2]);self.assertFalse(b.puts)
        self.assertEqual([x['state'] for x in r['results']],['would_merge','would_merge'])
        b=FakeBackend();r=reconcile(b,lambda:[1,2],applying=True)
        self.assertEqual(b.puts,[(1,H)]);self.assertEqual(r['results'][0]['state'],'merged');self.assertEqual(b.refreshed,1)

    def test_switch_and_executor_gate_single_and_sweep_before_queue_reads(self):
        for denied in ({'ready':False},{'executor_verified':False},{'merging_requested':False}):
            b=FakeBackend();b.activation.update(denied)
            def forbidden():raise AssertionError('disabled controller enumerated work')
            r=reconcile(b,forbidden,applying=True)
            self.assertEqual(r['state'],'disabled');self.assertFalse(b.puts)

    def test_revoked_review_and_changed_head_base_or_policy_require_new_run(self):
        for change in ({'eligibility':'blocked','reasons':['revoked review']},{'head':'4'*40},
                       {'base':'4'*40},{'tooling':'4'*40}):
            with self.subTest(change=change):
                b=FakeBackend();b.change_observation={**b.decision,**change}
                self.assertEqual(reconcile(b,lambda:[1],applying=True)['state'],'revalidation_required');self.assertFalse(b.puts)
        for change in ({'ready':False,'merging_requested':False},{'executor_verified':False},
                       {'policy_digest':'b'},{'evidence_digest':'new protection'}):
            b=FakeBackend();b.change_setup={**b.activation,**change}
            self.assertEqual(reconcile(b,lambda:[1],applying=True)['state'],'revalidation_required');self.assertFalse(b.puts)

    def test_final_live_refresh_failure_prevents_put(self):
        b=FakeBackend()
        def changed():raise RecordError('stop switch changed on final refresh')
        b.on_refresh=changed
        with self.assertRaises(RecordError):reconcile(b,lambda:[1],applying=True)
        self.assertFalse(b.puts)

    def test_restart_and_duplicate_events_reconcile_actual_merged_state(self):
        b=FakeBackend();reconcile(b,lambda:[1],applying=True)
        r=reconcile(b,lambda:[1],applying=True)
        self.assertEqual(len(b.puts),1);self.assertEqual(r['results'][0]['state'],'already_merged')

    def test_closed_draft_and_human_auto_merge_are_left_alone(self):
        for change,state in (({'state':'closed'},'closed'),({'draft':True},'human_managed'),
                             ({'auto_merge':{'enabled_by':7}},'human_managed')):
            b=FakeBackend();b.pr.update(change)
            self.assertEqual(reconcile(b,lambda:[1],applying=True)['results'][0]['state'],state)
            self.assertFalse(b.puts);self.assertEqual(b.observations,0)

    def test_ambiguous_put_is_read_back_without_repeating_or_advancing_sweep(self):
        b=FakeBackend();b.ambiguous=True
        r=reconcile(b,lambda:[1,2],applying=True)
        self.assertEqual(r['results'][0]['state'],'merged_observed');self.assertEqual(len(b.puts),1)
        self.assertEqual(reconcile(b,lambda:[1],applying=True)['results'][0]['state'],'already_merged')
        self.assertEqual(len(b.puts),1)

    def test_server_rejection_is_unconfirmed_and_never_retried_in_run(self):
        b=FakeBackend();b.reject=True
        r=reconcile(b,lambda:[1,2],applying=True)
        self.assertEqual(r['state'],'unconfirmed');self.assertEqual(len(b.puts),1)

    def test_base_advances_after_final_read_and_server_strict_checks_reject(self):
        b=FakeBackend()
        def advance():
            b.decision['base']='4'*40
            b.reject=True
        b.on_refresh=advance
        r=reconcile(b,lambda:[1,2],applying=True)
        self.assertEqual(r['state'],'unconfirmed');self.assertEqual(b.puts,[(1,H)])

    def test_ineligible_observation_does_not_gain_authority_from_activation(self):
        for state in ('human_review','blocked'):
            b=FakeBackend();b.decision['eligibility']=state
            r=reconcile(b,lambda:[1],applying=True)
            self.assertFalse(b.puts);self.assertEqual(r['results'][0]['state'],state)

    def test_nested_controller_lock_is_rejected_and_release_allows_restart(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t)
            with local_lock(root):
                with self.assertRaises(RecordError):
                    with local_lock(root):pass
            with local_lock(root):pass
            (root/'controller.lock').unlink();(root/'controller.lock').symlink_to(root/'elsewhere')
            with self.assertRaises(OSError):
                with local_lock(root):pass


class ActivationTests(unittest.TestCase):
    def test_conservative_classic_protection_and_dedicated_write_identity(self):
        s,a,p,b,env,run=setup_data()
        self.assertEqual(protections(b,REPO,s,a,p),[])
        for role in ('admin','maintain','custom'):
            self.assertTrue(protections(b,REPO,s,a,{**p,'role_name':role}))
        self.assertTrue(protections(b,REPO,s,{**a,'id':8},p))
        self.assertTrue(protections(b,REPO,s,{**a,'type':'Bot'},p))
        self.assertTrue(protections(b,REPO,s,{**a,'site_admin':True},p))

    def test_protection_and_producer_weakening_never_pass(self):
        s,a,p,b,env,run=setup_data()
        changes=[('url','wrong'),('enforce_admins',{'enabled':False}),('allow_force_pushes',{'enabled':True}),
                 ('allow_deletions',{}),('required_pull_request_reviews',None),
                 ('required_status_checks',{'strict':False,'checks':b['required_status_checks']['checks']}),
                 ('required_status_checks',{'strict':True,'checks':[{'context':c,'app_id':-1} for c in ('trusted-build','trusted-scope')]}),
                 ('required_status_checks',{'strict':True,'contexts':['trusted-build','trusted-scope']})]
        for key,value in changes:
            with self.subTest(key=key,value=value):self.assertTrue(protections({**b,key:value},REPO,s,a,p))
        for change in ({'dismiss_stale_reviews':False},{'required_approving_review_count':0},
                       {'required_approving_review_count':True},{'bypass_pull_request_allowances':{'users':[7]}},
                       {'bypass_pull_request_allowances':{'teams':[1]}},{'bypass_pull_request_allowances':{'apps':[9]}}):
            changed=deepcopy(b);changed['required_pull_request_reviews'].update(change)
            self.assertTrue(protections(changed,REPO,s,a,p))

    def test_run_environment_is_consistent_with_exact_live_workflow(self):
        s,a,p,b,env,run=setup_data()
        self.assertEqual(executor(run,s,T,REPO,env),[])
        for key in env:
            self.assertTrue(executor(run,s,T,REPO,{**env,key:'wrong'}))
        for key,value in [('event','pull_request'),('head_sha','4'*40),('workflow_id',11),('status','completed'),
                          ('path','.github/workflows/other.yml'),('run_attempt',2),('repository',{'full_name':'other/repo'})]:
            self.assertTrue(executor({**run,key:value},s,T,REPO,env))

    def test_policy_remains_unconfigured_and_rejects_unknown_escape_hatches(self):
        data=parse_controller(resource_text('merge-controller.toml'))
        self.assertEqual(data['workflow_id'],0);self.assertEqual(data['bot_user_id'],0)
        for extra in ('\nbypass = true','\nprovider = "codex"'):
            with self.assertRaises(ValueError):parse_controller(resource_text('merge-controller.toml')+extra)
        with self.assertRaises(ValueError):parse_controller(resource_text('merge-controller.toml').replace('workflow_id = 0','workflow_id = true'))
        with self.assertRaises(ValueError):parse_controller(resource_text('merge-controller.toml').replace('"squash"','"merge"'))


class TransportTests(unittest.TestCase):
    def test_merge_uses_put_expected_head_and_only_the_dedicated_credential(self):
        w=Writer(REPO,'writer-fixture-secret')
        response=subprocess.CompletedProcess([],0,json.dumps({'merged':True,'sha':M}),'')
        with patch.dict(os.environ,{'GH_TOKEN':'read-secret','PERSONAL_SECRET':'private','SPHERECETI_MERGE_TOKEN':'different'}),patch('sphereceti.merge_controller.subprocess.run',return_value=response) as call:
            w.merge(1,H)
            args=call.call_args
            self.assertIn('--method',args.args[0]);self.assertIn('PUT',args.args[0])
            self.assertEqual(json.loads(args.kwargs['input']),{'sha':H,'merge_method':'squash'})
            self.assertEqual(args.kwargs['env']['GH_TOKEN'],'writer-fixture-secret')
            self.assertNotIn('PERSONAL_SECRET',args.kwargs['env']);self.assertNotIn('SPHERECETI_MERGE_TOKEN',args.kwargs['env'])
            with self.assertRaises(RecordError):w.call(f'repos/{REPO}/issues/1/comments',{})
            self.assertEqual(call.call_count,1)

    def test_timeout_does_not_leak_tokens_or_retry(self):
        w=Writer(REPO,'secret-never-in-error')
        with patch('sphereceti.merge_controller.subprocess.run',side_effect=subprocess.TimeoutExpired('gh',45)) as call:
            with self.assertRaises(RecordError) as error:w.merge(1,H)
            self.assertNotIn('secret-never',str(error.exception));self.assertEqual(call.call_count,1)



class InstalledFlowTests(unittest.TestCase):
    def test_real_cli_uses_main_policy_and_removes_writer_token_before_reads(self):
        from controller_fixture import installed_controller_smoke
        with tempfile.TemporaryDirectory() as t:installed_controller_smoke(None,Path(t))

    def test_new_auto_merge_request_blocks_shared_observation(self):
        from test_merge_observation import DecisionTests
        case=DecisionTests();case.setUp();case.pr['auto_merge']={'enabled_by':7}
        self.assertEqual(case.decision()['eligibility'],'blocked')

if __name__=='__main__':unittest.main()
