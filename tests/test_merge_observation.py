"""Observation eligibility and API provenance regressions; no provider or write calls."""
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools/project'))
from sphereceti.config import parse_policy, parse_project, resource_text
from sphereceti.merge_checks import assess_checks, parse_checks, WORKFLOW
from sphereceti.merge_observation import Reader, decide, observe
from sphereceti.review_post import GitHub
from sphereceti.review_records import RecordError, assess_records
from test_review_records import result, comment, REPO


def evidence():
    context = result(); context['base'] = context['diff_base'] = context['tooling']
    policy = replace(parse_policy(resource_text('automation.toml')), mathematical_paths=('SphereCeti/Math',),
                     authorized_reviewers=('user:7',))
    scope = {k:context[k] for k in ('repository','head','base','diff_base','dependency_digest','tooling')}
    scope.update(scope='mathematical', config_attested=True)
    pr = {'number':1, 'state':'open', 'draft':False, 'merged':False, 'mergeable':True, 'mergeable_state':'clean',
          'head':{'sha':context['head']}, 'base':{'sha':context['base'],'ref':'main','repo':{'full_name':REPO}},
          'user':{'id':99},'title':'Math', 'body':''}
    settings = {'schema_version':1,'workflow_id':71,'status_creator_ids':[42]}
    statuses = [{'id':i,'context':name,'state':'success','creator':{'id':42,'type':'Bot'},
                 'url':f'https://api.github.com/repos/{REPO}/statuses/{context["head"]}',
                 'target_url':f'https://github.com/{REPO}/actions/runs/100/attempts/1',
                 'created_at':'2026-09-12T10:01:00Z'} for i,name in enumerate(('trusted-build','trusted-scope'),1)]
    run = {'id':100,'run_attempt':1,'workflow_id':71,'path':WORKFLOW,'event':'pull_request_target',
           'status':'completed','conclusion':'success','head_sha':context['tooling'],
           'repository':{'full_name':REPO},'pull_requests':[{'number':1,'head':pr['head'],'base':pr['base']}]}
    jobs = [{'id':i,'name':name,'run_id':100,'run_attempt':1,'status':'completed','conclusion':'success',
             'started_at':'2026-09-12T10:00:00Z','completed_at':'2026-09-12T10:02:00Z'}
            for i,name in enumerate(('candidate','status'),1)]
    return context,policy,scope,pr,settings,statuses,run,jobs


class DecisionTests(unittest.TestCase):
    def setUp(self):
        self.context,self.policy,self.scope,self.pr,self.settings,self.statuses,self.run,self.jobs=evidence()

    def decision(self, comments=None):
        if comments is None: comments=[comment(self.context)[0]]
        review=assess_records(comments,self.context,self.policy,lambda rev:rev==self.context['tooling'],99)
        checks=assess_checks(self.statuses,self.run,self.jobs,self.context,self.settings)
        return decide(self.context,self.scope,review,checks,self.pr,self.policy,current_main=self.context['tooling'])

    def test_future_mathematical_fixture_is_eligible_but_never_action_authority(self):
        answer=self.decision()
        self.assertEqual(answer['eligibility'],'eligible',answer)
        self.assertFalse(answer['merge_eligible']);self.assertFalse(answer['merge_allowed'])
        self.policy=replace(self.policy,merging=True)
        self.assertFalse(self.decision()['merge_allowed'])

    def test_real_empty_allowlist_and_protected_scope_require_human(self):
        for field in ('empty','protected'):
            with self.subTest(field=field):
                if field=='empty':self.policy=replace(self.policy,mathematical_paths=())
                else:self.scope['scope']='human_review'
                self.assertEqual(self.decision()['eligibility'],'human_review')

    def test_record_authentication_and_contests_are_reused(self):
        self.assertEqual(self.decision([])['eligibility'],'blocked')
        self.assertEqual(self.decision([comment(self.context,actor=900)[0]])['eligibility'],'blocked')
        stale={**self.context,'base':'4'*40}
        self.assertEqual(self.decision([comment(stale)[0]])['eligibility'],'blocked')
        for change in ({'execution_mode':'shadow'},{'completion':'partial'},{'missing_context':['roadmap']}):
            with self.subTest(change=change):
                self.assertEqual(self.decision([comment({**self.context,**change})[0]])['eligibility'],'blocked')
        c,r=comment(self.context)
        contest={'id':11,'user':{'type':'User','id':99},'issue_url':c['issue_url'],
                 'created_at':c['created_at'],'updated_at':c['updated_at'],
                 'body':'<!--sphereceti-contest:v1 '+json.dumps({'comment':10,'record':r['record_id'],'rubric':'correctness'})+'-->\nChallenge'}
        self.assertEqual(self.decision([c,contest])['eligibility'],'blocked')

    def test_current_pr_state_and_integration_base_are_required(self):
        original=deepcopy(self.pr)
        for change in ({'state':'closed'},{'merged':True},{'draft':True},{'mergeable':None},
                       {'mergeable':False},{'mergeable_state':'unknown'},{'mergeable_state':'behind'}):
            with self.subTest(change=change):
                self.pr={**deepcopy(original),**change}
                self.assertEqual(self.decision()['eligibility'],'blocked')
        self.pr=original;self.pr['base']['ref']='stack-branch'
        self.assertEqual(self.decision()['eligibility'],'blocked')
        self.pr['base']['ref']='main';self.context['diff_base']='9'*40;self.scope['diff_base']='9'*40
        self.assertEqual(self.decision()['eligibility'],'blocked')

    def test_every_scope_binding_and_current_context_is_required(self):
        original=deepcopy(self.scope)
        for key in ('repository','head','base','diff_base','dependency_digest','tooling'):
            with self.subTest(key=key):
                self.scope={**original,key:'wrong'}
                self.assertEqual(self.decision()['eligibility'],'blocked')
        self.scope=original
        for key,value in [('tooling_approved',False),('installed_tooling_matches_T',False),
                          ('missing_context',['roadmap']),('config_differences',['lakefile.toml'])]:
            old=self.context[key];self.context[key]=value
            self.assertEqual(self.decision()['eligibility'],'blocked');self.context[key]=old

    def test_same_named_forged_or_stale_status_is_not_a_check(self):
        original=deepcopy(self.statuses)
        for change in ({'state':'pending'},{'state':'failure'},{'creator':{'id':8,'type':'Bot'}},
                       {'creator':{'id':42,'type':'User'}},{'url':'https://attacker.invalid'},
                       {'target_url':f'https://github.com/{REPO}/actions/runs/100'},
                       {'target_url':f'https://github.com/{REPO}/actions/runs/100/attempts/2'},
                       {'created_at':'2026-09-11T10:01:00Z'}):
            with self.subTest(change=change):
                self.statuses=[{**original[0],**change},original[1]]
                self.assertEqual(self.decision()['eligibility'],'blocked')
        self.statuses=original+[dict(original[0],id=3,state='failure')]
        self.assertEqual(self.decision()['eligibility'],'blocked')
        self.statuses=original+[dict(original[0],id=3,creator={'id':8,'type':'Bot'})]
        self.assertEqual(self.decision()['eligibility'],'blocked')

    def test_no_configuration_missing_status_or_duplicate_inventory_cannot_pass(self):
        self.settings=parse_checks(resource_text('merge-checks.toml'))
        self.assertEqual(self.decision()['eligibility'],'blocked')
        self.statuses=[];self.assertEqual(self.decision()['eligibility'],'blocked')
        self.statuses=[{'id':1,'context':'x'}]*2
        with self.assertRaises(RecordError):self.decision()

    def test_foreign_untrusted_workflow_rerun_or_failed_job_is_rejected(self):
        original=deepcopy(self.run)
        for change in ({'path':'.github/workflows/ci.yml'},{'event':'pull_request'},
                       {'head_sha':'9'*40},{'workflow_id':72},{'repository':{'full_name':'other/repo'}},
                       {'pull_requests':[]},{'run_attempt':2},{'conclusion':'failure'},{'status':'in_progress'}):
            with self.subTest(change=change):
                self.run={**original,**change};self.assertEqual(self.decision()['eligibility'],'blocked')
        self.run=original
        original_jobs=deepcopy(self.jobs)
        for jobs in ([],original_jobs[:1],original_jobs+original_jobs,
                     [dict(original_jobs[0],conclusion='failure'),original_jobs[1]],
                     [dict(original_jobs[0],run_attempt=2),original_jobs[1]]):
            self.jobs=jobs;self.assertEqual(self.decision()['eligibility'],'blocked')


class ReaderTests(unittest.TestCase):
    def test_only_fixed_repository_gets_and_no_payloads(self):
        client=Reader(REPO)
        with patch.object(GitHub,'call',return_value={'sha':'1'*40}) as api:
            client.call(f'repos/{REPO}/commits/main')
            with self.assertRaises(RecordError):client.call(f'repos/{REPO}/pulls/1/merge',payload={})
            with self.assertRaises(RecordError):client.call('repos/other/repo/pulls/1')
            self.assertEqual(api.call_count,1)

    def test_all_observed_api_data_is_refreshed(self):
        for old,new in [({'head':'a'},{'head':'b'}),([{'body':'approved'}],[]),
                        ({'run_attempt':1},{'run_attempt':2})]:
            client=Reader(REPO)
            with patch.object(GitHub,'call',side_effect=[old,new]):
                client.call(f'repos/{REPO}/anything')
                with self.assertRaisesRegex(RecordError,'changed'):client.revalidate()

    def test_paginated_status_and_job_inventories_must_be_complete(self):
        client=Reader(REPO)
        for data in ([],{},[None],[[{'id':1,'context':'x'}],[{'id':1,'context':'x'}]]):
            with patch.object(GitHub,'call',return_value=data),self.assertRaises(RecordError):client.statuses('2'*40)
        for data in ([],[{'total_count':2,'jobs':[{'id':1}]}],
                     [{'total_count':2,'jobs':[{'id':1}]},{'total_count':2,'jobs':[{'id':1}]}]):
            with patch.object(GitHub,'call',return_value=data),self.assertRaises(RecordError):client.jobs(1,1)
        with patch.object(GitHub,'call',return_value=[{'total_count':2,'jobs':[{'id':1}]},{'total_count':2,'jobs':[{'id':2}]}]):
            self.assertEqual(len(client.jobs(1,1)),2)

    def test_api_failure_never_becomes_empty_success(self):
        with patch('sphereceti.review_post.subprocess.run',side_effect=OSError('offline')):
            with self.assertRaises(RecordError):Reader(REPO).statuses('2'*40)

    def test_policy_rejects_floating_or_ambiguous_producers(self):
        for suffix in ('workflow_id = true\nstatus_creator_ids=[]','workflow_id = -1\nstatus_creator_ids=[]',
                       'workflow_id = 7\nstatus_creator_ids=[1,1]','workflow_id = 7\nstatus_creator_ids=[true]'):
            with self.assertRaises(ValueError):parse_checks('schema_version=1\n'+suffix)


class CliIntegrationTests(unittest.TestCase):
    def test_installed_shape_mathematical_path_without_any_provider_or_write(self):
        from merge_fixture import installed_merge_smoke
        with tempfile.TemporaryDirectory() as tmp:installed_merge_smoke(None,Path(tmp))

    def test_protected_roadmap_requires_human_without_dependency_materialization(self):
        from merge_fixture import MergeFixture
        with tempfile.TemporaryDirectory() as tmp:
            f=MergeFixture(Path(tmp))
            before=subprocess.check_output(['git','-C',str(f.repo),'status','--porcelain'])
            run=f.run();self.assertEqual(run.returncode,0,run.stderr)
            report=json.loads(run.stdout)
            self.assertEqual(report['eligibility'],'human_review')
            self.assertEqual(report['scope']['changes'],[{'path':'README.md','class':'protected'}])
            self.assertFalse((f.root/'cache/dependencies').exists())
            self.assertEqual(before,subprocess.check_output(['git','-C',str(f.repo),'status','--porcelain']))
            self.assertFalse(f.calls())

    def test_candidate_or_cwd_cannot_supply_unlanded_policy(self):
        from merge_fixture import MergeFixture
        with tempfile.TemporaryDirectory() as tmp:
            f=MergeFixture(Path(tmp),approved_policy=False)
            run=f.run();self.assertEqual(run.returncode,0,run.stderr)
            report=json.loads(run.stdout)
            self.assertEqual(report['eligibility'],'human_review')
            self.assertIn('approved main lacks policy/merge-checks.toml',report['reasons'])
            self.assertEqual(len(f.api()['calls']),4)

    def test_real_cli_refuses_head_race_and_unknown_options(self):
        from merge_fixture import MergeFixture
        with tempfile.TemporaryDirectory() as tmp:
            f=MergeFixture(Path(tmp))
            state=f.api();state['advance_at']=2;f.api_state.write_text(json.dumps(state))
            run=f.run();self.assertEqual(run.returncode,2)
            self.assertIn('changed during observation',run.stderr)
            self.assertFalse(f.calls())
            run=f.run(extra=('--merge',));self.assertEqual(run.returncode,2)

if __name__=='__main__':unittest.main()
