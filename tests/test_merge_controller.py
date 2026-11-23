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
from types import SimpleNamespace
from sphereceti.merge_activation import (HUMAN_ROUTE, WORKFLOW, admits, automatic, executor, executor_bypass,
                                         pages, parse_controller, protections, server)
from sphereceti.merge_controller import Writer, local_lock, reconcile
from sphereceti.review_records import RecordError
from review_fixture import DISABLED_CONTROLLER
from ruleset_fixture import GITHUB_ACTIONS_APP, LIVE_EFFECTIVE, live

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

    def test_unconfigured_policy_fixture_and_unknown_escape_hatches(self):
        data=parse_controller(DISABLED_CONTROLLER)
        self.assertEqual(data['workflow_id'],0);self.assertEqual(data['bot_user_id'],0)
        for extra in ('\nbypass = true','\nprovider = "codex"'):
            with self.assertRaises(ValueError):parse_controller(DISABLED_CONTROLLER+extra)
        with self.assertRaises(ValueError):parse_controller(DISABLED_CONTROLLER.replace('workflow_id = 0','workflow_id = true'))
        with self.assertRaises(ValueError):parse_controller(DISABLED_CONTROLLER.replace('"squash"','"merge"'))


UNCONFIGURED={'schema_version':1,'workflow_id':0,'bot_user_id':0,'checks_app_id':0,'merge_method':'squash'}
CONFIGURED={**UNCONFIGURED,'workflow_id':10,'bot_user_id':7,'checks_app_id':GITHUB_ACTIONS_APP}
ADMIN_BYPASS=[{'actor_id':5,'actor_type':'RepositoryRole','bypass_mode':'always'}]


class FakeClient:
    """Dictionary-backed GETs; an unexpected endpoint is a test failure, not an empty answer."""
    def __init__(self,responses):self.responses,self.calls=responses,[]
    def call(self,endpoint,*,paginate=False):
        self.calls.append(endpoint)
        if endpoint not in self.responses:raise AssertionError(f'unexpected read {endpoint}')
        return deepcopy(self.responses[endpoint])


def client(branch,effective,listing,detail,classic=None):
    p=f'repos/{REPO}/'
    responses={p+'branches/main':branch,p+'rules/branches/main?per_page=100':effective,
               p+'rulesets?includes_parents=true&per_page=100':listing}
    if detail is not None:responses[p+f'rulesets/{detail["id"]}']=detail
    if classic is not None:responses[p+'branches/main/protection']=classic
    return FakeClient(responses)


def ruleset(mutate=None,bypass=None):
    """Live shapes with one consistent edit to the ruleset detail and the effective rules."""
    branch,_,listing,detail=live()
    if mutate:mutate(detail['rules'])
    effective=[[{**r,'ruleset_source_type':'Repository','ruleset_source':REPO,'ruleset_id':detail['id']}
                for r in detail['rules']]]
    if bypass is not None:detail['bypass_actors']=bypass
    return branch,effective,listing,detail


def rule(rules,kind):return next(r for r in rules if r['type']==kind)
def strict(rules):rule(rules,'required_status_checks')['parameters']['strict_required_status_checks_policy']=True
def drop(kind):return lambda rules:rules.remove(rule(rules,kind))
def review(**change):return lambda rules:rule(rules,'pull_request')['parameters'].update(change)
def require(*contexts):
    return lambda rules:rule(rules,'required_status_checks')['parameters']['required_status_checks'].extend(
        {'context':c,'integration_id':GITHUB_ACTIONS_APP} for c in contexts)


class RulesetTests(unittest.TestCase):
    def test_live_ruleset_reports_verified_protections_and_exact_gaps(self):
        self.assertEqual(ruleset()[1],[LIVE_EFFECTIVE])  # The two live reads describe the same rules.
        found=server(client(*live()),REPO,UNCONFIGURED)
        self.assertEqual((found['source'],found['ruleset_id']),('ruleset',21449770))
        self.assertEqual(found['verified'],[
            'deletion of main is blocked','force pushes to main are blocked',
            'pull_request requires 1 approving review(s)','allowed merge methods ["squash"] include squash',
            'review threads must be resolved',
            'human-reviewed policy and dependency PRs can land with an approval and a passing build'])
        self.assertEqual(found['findings'],[
            'dismiss_stale_reviews_on_push is false: approvals survive later pushes (recommended, not yet required)',
            'require_last_push_approval is false: the last pusher may supply the approval (recommended, not yet required)'])
        self.assertEqual(found['missing'],[
            'ruleset 21449770 bypass actors are not visible to this reader; an administration-read token must confirm them',
            'build is required from integration 15368, but checks_app_id is unconfigured',
            'strict_required_status_checks_policy is false: GitHub would accept a merge after main advances '
            'past the base the executor verified (humans can still update a branch and merge)'])
        # Nothing recommends requiring the trusted contexts for every PR.
        self.assertFalse([x for x in found['missing']+found['findings'] if 'trusted-' in x])

    def test_automatic_path_lists_executor_evidence_and_unconfigured_items(self):
        policy=SimpleNamespace(merging=False,mathematical_paths=(),authorized_reviewers=('user:2009342',))
        path=automatic(policy,{'workflow_id':358051984,'status_creator_ids':[41898282]},UNCONFIGURED,True)
        self.assertEqual(path['missing'],[
            'global merging switch is off','no approved mathematical change class',
            'serialized controller workflow is not configured (policy/merge-controller.toml workflow_id = 0)',
            'dedicated merge identity is not configured (policy/merge-controller.toml bot_user_id = 0)',
            'required-check integration is not configured (policy/merge-controller.toml checks_app_id = 0)'])
        self.assertIn('358051984',path['executor_verifies'][0]);self.assertIn('41898282',path['executor_verifies'][0])
        self.assertTrue(any('"mathematical"' in x for x in path['executor_verifies']))
        self.assertIn('first merge canary',path['end_state'][0])

    def test_proposed_ruleset_admits_human_policy_and_dependency_prs(self):
        data=ruleset(strict,ADMIN_BYPASS)
        found=server(client(*data),REPO,CONFIGURED)
        self.assertEqual(found['missing'],[])
        self.assertIn('admin role may bypass (always); the write-role merge identity does not hold it',found['verified'])
        rules=data[1][0]
        for route,pr in HUMAN_ROUTE.items():
            with self.subTest(route=route):
                self.assertEqual(pr['checks']['trusted-scope'],'failure')  # human_review, not mathematical
                self.assertEqual(admits(rules,pr),[])
        policy_pr=HUMAN_ROUTE['policy']
        self.assertEqual(admits(rules,{**policy_pr,'approvals':0}),['approvals'])
        self.assertEqual(admits(rules,{**policy_pr,'checks':{**policy_pr['checks'],'build':'failure'}}),['build'])
        recommended=ruleset(lambda r:(strict(r),review(dismiss_stale_reviews_on_push=True,require_last_push_approval=True)(r)),[])
        found=server(client(*recommended),REPO,CONFIGURED)
        self.assertEqual((found['missing'],found['findings']),([],[]))

    def test_universally_required_trusted_contexts_are_reported_as_blocking_the_human_route(self):
        policy,dependency='ruleset would block human-reviewed policy PRs: ','ruleset would block human-reviewed dependency PRs: '
        for contexts,blocked in ((('trusted-scope',),[policy+'trusted-scope',dependency+'trusted-scope']),
                                 (('trusted-build',),[dependency+'trusted-build']),
                                 (('trusted-build','trusted-scope'),[policy+'trusted-scope',dependency+'trusted-build, trusted-scope'])):
            with self.subTest(contexts=contexts):
                found=server(client(*ruleset(lambda r:(strict(r),require(*contexts)(r)),ADMIN_BYPASS)),REPO,CONFIGURED)
                self.assertEqual([x for x in found['missing'] if 'would block' in x],blocked)
                self.assertNotIn('human-reviewed policy and dependency PRs can land with an approval and a passing build',
                                 found['verified'])

    def test_bypass_actors_that_could_cover_the_merge_identity_are_rejected(self):
        for actor in ({'actor_id':5,'actor_type':'RepositoryRole'},{'actor_id':2,'actor_type':'RepositoryRole'},
                      {'actor_id':1,'actor_type':'OrganizationAdmin'}):
            found=server(client(*ruleset(strict,[{**actor,'bypass_mode':'pull_request'}])),REPO,CONFIGURED)
            self.assertEqual(found['missing'],[])
        for actor in ({'actor_id':4,'actor_type':'RepositoryRole'},{'actor_id':1,'actor_type':'RepositoryRole'},
                      {'actor_id':12345,'actor_type':'RepositoryRole'},{'actor_id':77,'actor_type':'Team'},
                      {'actor_id':GITHUB_ACTIONS_APP,'actor_type':'Integration'},{'actor_id':None,'actor_type':'DeployKey'}):
            with self.subTest(actor=actor):
                found=server(client(*ruleset(strict,ADMIN_BYPASS+[{**actor,'bypass_mode':'always'}])),REPO,CONFIGURED)
                self.assertEqual(found['missing'],[f"bypass actor {actor['actor_type']} {actor['actor_id']} (always) could cover the merge identity"])
        with self.assertRaises(RecordError):server(client(*ruleset(strict,{'users':[]})),REPO,CONFIGURED)
        self.assertEqual(executor_bypass({'id':21449770,'current_user_can_bypass':'never'},21449770),[])
        for view in ({'id':21449770,'current_user_can_bypass':'always'},{'id':21449770,'current_user_can_bypass':'pull_requests_only'},
                     {'id':21449770,'current_user_can_bypass':'exempt'},{'id':21449770},{'id':1,'current_user_can_bypass':'never'},None):
            with self.subTest(view=view):self.assertTrue(executor_bypass(view,21449770))

    def test_multiple_inactive_or_foreign_rulesets_fail_closed(self):
        branch,effective,listing,detail=ruleset(strict,ADMIN_BYPASS)
        extra={**listing[0][0],'id':2,'name':'other','enforcement':'evaluate'}
        found=server(client(branch,effective,[listing[0]+[extra]],detail),REPO,CONFIGURED)
        self.assertIn("exactly one ruleset must exist and govern main; effective rules come from [21449770] "
                      "and the repository lists [2, 21449770]",found['missing'])
        self.assertIn("ruleset 2 enforcement is 'evaluate', not active",found['missing'])
        for enforcement in ('evaluate','disabled'):
            changed=deepcopy(listing);changed[0][0]['enforcement']=enforcement
            found=server(client(branch,effective,changed,detail),REPO,CONFIGURED)
            self.assertIn(f"ruleset 21449770 enforcement is '{enforcement}', not active",found['missing'])
            found=server(client(branch,effective,listing,{**detail,'enforcement':enforcement}),REPO,CONFIGURED)
            self.assertIn('ruleset 21449770 is not an active branch ruleset',found['missing'])
        split=deepcopy(effective);split[0][0]['ruleset_id']=2
        c=client(branch,split,listing,None)
        found=server(c,REPO,CONFIGURED)
        self.assertTrue(any(x.startswith('exactly one ruleset') for x in found['missing']))
        self.assertFalse([e for e in c.calls if '/rulesets/' in e])  # No detail is chosen for an ambiguous source.
        foreign=deepcopy(listing);foreign[0][0]['source_type']='Organization'
        found=server(client(branch,effective,foreign,detail),REPO,CONFIGURED)
        self.assertIn('ruleset 21449770 is not a branch ruleset owned by this repository',found['missing'])
        with self.assertRaises(RecordError):
            server(client(branch,effective,listing,{**detail,'rules':detail['rules'][:-1]}),REPO,CONFIGURED)
        with self.assertRaises(RecordError):
            server(client(branch,effective,[listing[0]*2],detail),REPO,CONFIGURED)

    def test_missing_or_weakened_approval_rule_is_reported(self):
        for mutate,reason in ((drop('pull_request'),'exactly one pull_request rule with parameters is required'),
                              (review(required_approving_review_count=0),'pull_request rule must require at least one approving review'),
                              (review(required_approving_review_count=True),'pull_request rule must require at least one approving review'),
                              (review(allowed_merge_methods=['merge']),'pull_request rule must allow squash merges'),
                              (review(bypass=True),"unknown pull_request parameters ['bypass']")):
            with self.subTest(reason=reason):
                found=server(client(*ruleset(lambda r:(strict(r),mutate(r)),ADMIN_BYPASS)),REPO,CONFIGURED)
                self.assertIn(reason,found['missing'])

    def test_missing_non_fast_forward_or_deletion_is_reported(self):
        for kind in ('non_fast_forward','deletion'):
            found=server(client(*ruleset(lambda r:(strict(r),drop(kind)(r)),ADMIN_BYPASS)),REPO,CONFIGURED)
            self.assertEqual(found['missing'],[f'{kind} rule is missing'])

    def test_unknown_rule_types_parameters_and_unbound_checks_fail_closed(self):
        for extra in ({'type':'update'},{'type':'merge_queue','parameters':{}},{'type':'required_linear_history'}):
            found=server(client(*ruleset(lambda r:(strict(r),r.append(extra)),ADMIN_BYPASS)),REPO,CONFIGURED)
            self.assertEqual(found['missing'],[f"unsupported rule type '{extra['type']}' needs a separately reviewed profile"])
        def unknown(rules):rule(rules,'required_status_checks')['parameters']['new_option']=True
        found=server(client(*ruleset(unknown,ADMIN_BYPASS)),REPO,CONFIGURED)
        self.assertIn('required_status_checks rule has missing or unknown parameters',found['missing'])
        def unbound(rules):rule(rules,'required_status_checks')['parameters']['required_status_checks']=[{'context':'build'}]
        found=server(client(*ruleset(lambda r:(strict(r),unbound(r)),ADMIN_BYPASS)),REPO,CONFIGURED)
        self.assertEqual(found['missing'],['build is required from any producer; bind it to an integration'])
        found=server(client(*ruleset(strict,ADMIN_BYPASS)),REPO,{**CONFIGURED,'checks_app_id':9})
        self.assertEqual(found['missing'],['build is required from integration 15368, not checks_app_id 9'])
        def none(rules):rule(rules,'required_status_checks')['parameters']['required_status_checks']=[]
        found=server(client(*ruleset(lambda r:(strict(r),none(r)),ADMIN_BYPASS)),REPO,CONFIGURED)
        self.assertEqual(found['missing'],['no status check is required for every PR'])

    def test_truncated_or_malformed_inventories_fail_closed(self):
        for value in ([],[{}],[[1]],[[{}]*99,[{}]],[[{}]*101],None):
            with self.subTest(value=value),self.assertRaises(RecordError):pages(value,'test')
        self.assertEqual(len(pages([[{}]*100,[{}]],'test')),101)
        branch,effective,listing,detail=live()
        for summary in ({},{'name':'main','protected':True},{'name':'main','protected':'yes','protection':{'enabled':False}}):
            with self.assertRaises(RecordError):server(client(summary,effective,listing,detail),REPO,CONFIGURED)

    def test_classic_protection_path_still_works(self):
        s,a,p,b,env,run=setup_data()
        enabled={'name':'main','protected':True,'protection':{'enabled':True}}
        found=server(client(enabled,[[]],[[]],None,b),REPO,s)
        self.assertEqual((found['source'],found['missing']),('classic',[]))
        weakened=server(client(enabled,[[]],[[]],None,{**b,'allow_force_pushes':{'enabled':True}}),REPO,s)
        self.assertEqual(weakened['missing'],['allow_force_pushes is not explicitly disabled'])
        c=client(enabled,[[]],[[]],None)
        self.assertEqual(server(c,REPO,UNCONFIGURED)['missing'],['classic protection is read only after controller IDs are configured'])
        self.assertNotIn(f'repos/{REPO}/branches/main/protection',c.calls)
        branch,effective,listing,detail=live()
        found=server(client(enabled,effective,listing,detail,b),REPO,s)
        self.assertEqual(found['missing'],['classic protection and rulesets both apply; a combined profile is unsupported'])
        bare={'name':'main','protected':False,'protection':{'enabled':False}}
        self.assertEqual(server(client(bare,[[]],[[]],None),REPO,s)['missing'],['main has neither classic protection nor a ruleset'])


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

    def test_merge_token_reads_only_identity_and_its_own_ruleset_view(self):
        w=Writer(REPO,'writer-fixture-secret')
        view={'id':21449770,'current_user_can_bypass':'never'}
        response=subprocess.CompletedProcess([],0,json.dumps(view),'')
        with patch('sphereceti.merge_controller.subprocess.run',return_value=response) as call:
            self.assertEqual(w.ruleset(21449770),view)
            self.assertEqual(call.call_args.args[0][-1],f'repos/{REPO}/rulesets/21449770')
            self.assertNotIn('--method',call.call_args.args[0])
            for endpoint,payload in ((f'repos/{REPO}/rulesets/21449770',{'sha':H,'merge_method':'squash'}),
                                     (f'repos/{REPO}/rulesets',None),(f'repos/{REPO}/rulesets/0',None),
                                     (f'repos/{REPO}/branches/main/protection',None)):
                with self.assertRaises(RecordError):w.call(endpoint,payload)
            with self.assertRaises(RecordError):w.ruleset('21449770')
            self.assertEqual(call.call_count,1)
            w.refresh_identity()
        changed=subprocess.CompletedProcess([],0,json.dumps({**view,'current_user_can_bypass':'always'}),'')
        with patch('sphereceti.merge_controller.subprocess.run',return_value=changed):
            with self.assertRaises(RecordError):w.refresh_identity()

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
