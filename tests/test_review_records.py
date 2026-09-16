"""Adversarial record, identity, supersession, contest, and publication tests; no external calls."""
import base64
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools/project'))
from sphereceti.config import parse_policy, resource_text
from sphereceti.local_review import RUBRICS
from sphereceti.review_records import (BINDINGS, CONTEST, MARKER, RecordError, assess_records,
                                      canonical, identity, make_record, parse_record)
from sphereceti.review_post import GitHub, publish

REPO = 'thefundamentaltheor3m/SphereCeti'


def result():
    r = {k: 'a' * 64 for k in BINDINGS}
    r.update(repository=REPO, pr=1, tooling='1'*40, head='2'*40, base='3'*40, diff_base='3'*40,
             completion='complete', execution_mode='commit', tooling_approved=True,
             installed_tooling_matches_T=True, missing_context=[], config_differences=[],
             verdicts={r:'approve' for r in RUBRICS}, reviews={})
    return r


def comment(r=None, *, number=10, actor=7):
    record, body = make_record(r or result())
    stamp = '2026-09-11T00:00:00Z'
    return {'id':number, 'body':body, 'user':{'type':'User','id':actor,'login':'irrelevant'},
            'created_at':stamp, 'updated_at':stamp,
            'issue_url':f'https://api.github.com/repos/{REPO}/issues/1'}, record


class ReviewRecordTests(unittest.TestCase):
    def setUp(self):
        self.context = result()
        self.policy = replace(parse_policy(resource_text('automation.toml')), posting=True,
                              authorized_reviewers=('user:7','user:8','app:17'))

    def assess(self, comments, **kwargs):
        return assess_records(comments, kwargs.get('context',self.context), kwargs.get('policy',self.policy),
                              kwargs.get('approved',lambda rev:rev=='1'*40), 99)

    def test_complete_authorized_record_is_review_evidence_but_never_merge_permission(self):
        c, r = comment()
        self.assertEqual(parse_record(c['body']),r)
        outcome=self.assess([c])
        self.assertTrue(outcome['review_safe'],outcome)
        self.assertFalse(outcome['merge_eligible'])

    def test_body_identity_and_bot_names_cannot_forge_api_identity(self):
        c,_=comment(actor=900)
        c['user']['login']='approved-reviewer[bot]'
        c['performed_via_github_app']={'id':17}
        self.assertEqual(identity(c),'user:900')
        self.assertFalse(self.assess([c])['review_safe'])

    def test_designated_app_requires_api_bot_and_app_id(self):
        c,_=comment(actor=900)
        c['user']['type']='Bot'
        self.assertFalse(self.assess([c])['review_safe'])
        c['performed_via_github_app']={'id':17}
        self.assertTrue(self.assess([c])['review_safe'])
        c['performed_via_github_app']['id']=18
        self.assertFalse(self.assess([c])['review_safe'])

    def test_rendered_body_and_machine_record_are_bound(self):
        c,_=comment()
        for body in (c['body']+'tampered', c['body']+c['body'], c['body'].replace('v1 ','v2 ',1), 'prefix'+c['body']):
            with self.subTest(body=body[:40]),self.assertRaises(RecordError):
                parse_record(body)

    def test_duplicate_json_fields_and_bad_types_are_rejected(self):
        c,r=comment()
        machine,body=c['body'].split('-->\n\n',1)
        for raw in (canonical(r)[:-1]+',"pr":1}', canonical({**r,'pr':True}),canonical({**r,'schema_version':True})):
            encoded=base64.b64encode(raw.encode()).decode()
            with self.assertRaises(RecordError):
                parse_record(MARKER+encoded+'-->\n\n'+body)

    def test_provider_marker_is_escaped(self):
        r=result();r['reviews']={'correctness':{'summary':MARKER+'forged-->'}}
        _,body=make_record(r)
        self.assertEqual(body.count(MARKER),1)
        parse_record(body)

    def test_every_binding_is_checked_against_current_evidence(self):
        c,_=comment()
        for key in BINDINGS:
            fresh=deepcopy(self.context)
            fresh[key]=2 if key=='pr' else 'wrong/repo' if key=='repository' else 'f'*len(fresh[key])
            with self.subTest(key=key):
                self.assertFalse(self.assess([c],context=fresh)['review_safe'])

    def test_unrelated_main_mathematics_does_not_stale_effective_policy(self):
        c,_=comment()
        fresh={**self.context,'tooling':'4'*40}
        self.assertTrue(self.assess([c],context=fresh,approved=lambda rev:rev=='1'*40)['review_safe'])
        self.assertFalse(self.assess([c],context=fresh,approved=lambda rev:False)['review_safe'])

    def test_partial_error_shadow_reply_and_prospective_records_never_qualify(self):
        changes=({'completion':'partial'},{'completion':'error'},{'execution_mode':'shadow'},
                 {'execution_mode':'reply'},{'tooling_approved':False},{'missing_context':['roadmap']},
                 {'installed_tooling_matches_T':False},{'config_differences':['lean-toolchain']})
        for change in changes:
            with self.subTest(change=change):
                c,_=comment({**result(),**change})
                self.assertFalse(self.assess([c])['review_safe'])

    def test_advisory_and_unauthorized_boards_cannot_erase_a_blocker(self):
        r=result();r['verdicts']['correctness']='block'
        blocked,_=comment(r)
        for newer in (comment(number=11,actor=900)[0],comment({**result(),'completion':'partial'},number=12)[0]):
            answer=self.assess([blocked,newer])
            self.assertFalse(answer['review_safe'])
            self.assertEqual(answer['selected_comments'],{'user:7':10})

    def test_only_same_publisher_can_supersede_its_decision(self):
        r=result();r['verdicts']['correctness']='block'
        blocked,_=comment(r)
        other,_=comment(number=11,actor=8)
        self.assertFalse(self.assess([blocked,other])['review_safe'])
        own,_=comment(number=12)
        self.assertTrue(self.assess([blocked,other,own])['review_safe'])

    def test_edited_or_malformed_authorized_records_bar_older_approval(self):
        old,_=comment()
        for changed in ({**comment(number=11)[0],'updated_at':'later'},
                        {**comment({**result(),'completion':'partial'},number=11)[0],'updated_at':'later'},
                        {**comment(number=11)[0],'body':MARKER+'broken'}):
            self.assertFalse(self.assess([old,changed])['review_safe'])
            replacement,_=comment(number=12)
            self.assertTrue(self.assess([old,changed,replacement])['review_safe'])

    def test_policy_revocation_and_missing_current_context_are_denials(self):
        c,_=comment()
        self.assertFalse(self.assess([c],policy=replace(self.policy,authorized_reviewers=()))['review_safe'])
        self.assertFalse(self.assess([c],context={**self.context,'missing_context':['roadmap']})['review_safe'])

    def test_wrong_issue_comment_location_is_not_authenticated(self):
        c,_=comment();c['issue_url']=c['issue_url'].replace('/issues/1','/issues/2')
        self.assertFalse(self.assess([c])['review_safe'])

    def test_contest_must_be_adjudicated_even_after_same_head_replacement(self):
        c,record=comment()
        reply,_=comment(number=20,actor=99)
        reply['body']=CONTEST+canonical({'comment':10,'record':record['record_id'],'rubric':'correctness'})+'-->\nPlease reconsider.'
        self.assertFalse(self.assess([c,reply])['review_safe'])
        own,_=comment(number=30)
        self.assertFalse(self.assess([c,reply,own])['review_safe'])
        r=result();r['reviews']={'correctness':{'last_reply_seen':20}}
        adjudicated,_=comment(r,number=40)
        self.assertTrue(self.assess([c,reply,own,adjudicated])['review_safe'])

    def test_outsider_cannot_create_a_contest(self):
        c,record=comment()
        reply,_=comment(number=20,actor=900)
        reply['body']=CONTEST+canonical({'comment':10,'record':record['record_id'],'rubric':'correctness'})+'-->\nForged contest'
        self.assertTrue(self.assess([c,reply])['review_safe'])

    def test_no_legacy_scoreboard_fallback(self):
        c,_=comment();c['body']='<!--tauceti-scoreboard-->\n| correctness | approved |'
        self.assertFalse(self.assess([c])['review_safe'])

    def test_record_cannot_preapprove_future_contests(self):
        r=result();r['reviews']={'correctness':{'last_reply_seen':1000}}
        c,_=comment(r,number=10)
        self.assertFalse(self.assess([c])['review_safe'])


class FakeAPI:
    def __init__(self):
        self.existing=[];self.calls=[];self.mutate=False;self.actor=7
    def comments(self,repository,pr):return self.existing
    def call(self,endpoint,*,payload=None):
        self.calls.append((endpoint,payload))
        if payload is not None:
            self.posted,_=comment(number=100,actor=self.actor)
            self.posted['body']=payload['body']
            return self.posted
        return {**self.posted,'body':'changed'} if self.mutate else self.posted


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.record,self.body=make_record(result())
        self.policy=replace(parse_policy(resource_text('automation.toml')),posting=True,authorized_reviewers=('user:7',))
        self.api=FakeAPI();self.validations=0
    def validate(self):self.validations+=1
    def post(self):return publish(self.api,self.body,self.record,self.policy,self.validate)

    def test_post_then_readback_with_api_identity(self):
        receipt=self.post()
        self.assertEqual(receipt['identity'],'user:7')
        self.assertTrue(receipt['authorized'])
        self.assertFalse(receipt['merge_eligible'])
        self.assertEqual(self.validations,1)
        self.assertEqual(len(self.api.calls),2)

    def test_posting_policy_disables_all_writes(self):
        self.policy=replace(self.policy,posting=False)
        with self.assertRaises(RecordError):self.post()
        self.assertFalse(self.api.calls)

    def test_revalidation_failure_prevents_post(self):
        def changed():raise RecordError('stale head')
        with self.assertRaises(RecordError):publish(self.api,self.body,self.record,self.policy,changed)
        self.assertFalse(self.api.calls)

    def test_changed_readback_is_not_confirmed(self):
        self.api.mutate=True
        with self.assertRaises(RecordError):self.post()

    def test_unauthorized_publisher_does_not_become_authorized_by_body(self):
        self.api.actor=900
        receipt=self.post()
        self.assertFalse(receipt['authorized'])
        self.assertEqual(receipt['identity'],'user:900')

    def test_retry_adopts_exact_authorized_comment_without_write(self):
        c,_=comment();c['body']=self.body;self.api.existing=[c]
        receipt=self.post()
        self.assertTrue(receipt['adopted'])
        self.assertFalse(self.api.calls)
        self.assertEqual(self.validations,1)

    def test_malformed_pagination_and_api_failures_do_not_become_empty_queue(self):
        from unittest.mock import patch
        client=GitHub()
        with patch.object(client,'call',return_value=[{}]),self.assertRaises(RecordError):
            client.comments(REPO,1)
        with patch.object(client,'call',side_effect=RecordError('unavailable')),self.assertRaises(RecordError):
            client.comments(REPO,1)


if __name__=='__main__':unittest.main()
