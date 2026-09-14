# SPDX-License-Identifier: Apache-2.0
"""Append-only operational state, isolation and publication-race regression contracts."""
import base64
from copy import deepcopy
from dataclasses import replace
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools/project'))
from sphereceti.worker import WorkerError
from sphereceti.worker_state import ANCHOR, canonical, expected_anchor, publish_state
from sphereceti.review_records import RecordError
from test_worker_execution import PROJECT, POLICY


def oid(raw):
    return hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()


class StateAPI:
    def __init__(self):
        raw=canonical(expected_anchor(PROJECT)).encode()
        self.blobs={oid(raw):raw}
        self.entries={ANCHOR:{'path':ANCHOR,'type':'blob','mode':'100644','sha':oid(raw)}}
        self.head='1'*40;self.tree='2'*40;self.calls=[];self.truncated=False
        self.missing=False;self.race=False;self.bad_readback=False
        self.new_entries=None

    def call(self,endpoint,*,payload=None,method=None):
        self.calls.append((endpoint,payload,method))
        if endpoint=='user':return {'type':'User','id':7}
        if endpoint.endswith('/git/ref/heads/reviews'):
            if self.missing:raise RecordError('branch missing')
            return {'ref':'refs/heads/reviews','object':{'type':'commit','sha':self.head}}
        if '/git/trees/' in endpoint:
            return {'sha':self.tree,'tree':list(self.entries.values()),'truncated':self.truncated}
        if '/git/blobs/' in endpoint:
            raw=self.blobs[endpoint.rsplit('/',1)[1]]
            return {'encoding':'base64','content':base64.b64encode(raw).decode(),'size':len(raw)}
        if endpoint.endswith('/git/blobs'):
            raw=payload['content'].encode(); self.blobs[oid(raw)]=raw
            return {'sha':oid(raw)}
        if endpoint.endswith('/git/trees'):
            self.new_entries={**self.entries,**{e['path']:e for e in payload['tree']}}
            self.new_entries['runs']={'path':'runs','type':'tree','mode':'040000','sha':'4'*40}
            return {'sha':'3'*40}
        if endpoint.endswith('/git/commits'):
            self.parent=payload['parents'][0]
            return {'sha':'5'*40}
        if endpoint.endswith('/git/refs/heads/reviews'):
            assert method=='PATCH' and payload['force'] is False
            if self.race:raise RecordError('non-fast-forward')
            self.head='6'*40 if self.bad_readback else payload['sha']
            self.tree='3'*40;self.entries=self.new_entries
            return {'object':{'sha':self.head}}
        raise AssertionError(endpoint)


def receipt():
    return {'schema':'sphereceti.worker-round/v1','repository':PROJECT.repository,'pr':1,
            'head':'2'*40,'base':'3'*40,'tooling':'1'*40,'state':'complete','executed':True,
            'output':'/private/location','prompt':'never publish',
            'coordination':{'owner':'user:7','claim':'f'*32,'worker':'local-private-name','lease_comment':9},
            'publication':{'state':'confirmed','private':'do not publish'}}


class StateTests(unittest.TestCase):
    def setUp(self):
        self.api=StateAPI();self.refreshes=0
    def refresh(self):self.refreshes+=1
    def publish(self,**kwargs):
        return publish_state(self.api,kwargs.get('project',PROJECT),kwargs.get('policy',POLICY),
                             kwargs.get('receipt',receipt()),kwargs.get('refresh',self.refresh))

    def test_confirmed_append_and_idempotent_explicit_retry(self):
        first=self.publish()
        self.assertEqual(first['state'],'confirmed');self.assertFalse(first['adopted'])
        writes=sum(p is not None for _,p,_ in self.api.calls)
        second=self.publish()
        self.assertTrue(second['adopted'])
        self.assertEqual(sum(p is not None for _,p,_ in self.api.calls),writes)
        self.assertEqual(self.api.parent,'1'*40)
        raw=self.api.blobs[self.api.entries[first['path']]['sha']].decode()
        for secret in ('/private','prompt','local-private-name','do not publish'):
            self.assertNotIn(secret,raw)
        self.assertEqual(json.loads(raw)['authority'],'operational-only')

    def test_disabled_or_wrong_state_branch_prevents_writes(self):
        for changes in ({'policy':replace(POLICY,posting=False)},
                        {'project':replace(PROJECT,reviews_branch='main')},
                        {'project':replace(PROJECT,archive_branch='reviews')}):
            with self.assertRaises(WorkerError):self.publish(**changes)
        self.assertFalse(self.api.calls)

    def test_missing_branch_never_creates_one(self):
        self.api.missing=True
        with self.assertRaises(RecordError):self.publish()
        self.assertFalse(any(p is not None for _,p,_ in self.api.calls))

    def test_anchor_mismatch_and_truncated_tree_reject_before_writes(self):
        self.api.truncated=True
        with self.assertRaises(WorkerError):self.publish()
        self.api.truncated=False
        self.api.entries={}
        with self.assertRaises(WorkerError):self.publish()
        self.assertFalse(any(p is not None for _,p,_ in self.api.calls))

    def test_foreign_path_and_symlinks_rejected(self):
        self.api.entries['README.md']={'path':'README.md','type':'blob','mode':'100644','sha':'f'*40}
        with self.assertRaises(WorkerError):self.publish()
        del self.api.entries['README.md']
        self.api.entries[ANCHOR]['mode']='120000'
        with self.assertRaises(WorkerError):self.publish()

    def test_revalidation_race_never_forces(self):
        def advance():
            self.refreshes+=1
            if self.refreshes==2:self.api.head='f'*40
        with self.assertRaises(WorkerError):self.publish(refresh=advance)
        self.assertFalse(any(method=='PATCH' for _,_,method in self.api.calls))
        self.api=StateAPI();self.api.race=True
        with self.assertRaises(RecordError):self.publish()
        patches=[p for _,p,m in self.api.calls if m=='PATCH']
        self.assertEqual(patches,[{'sha':'5'*40,'force':False}])

    def test_bad_readback_never_reports_success(self):
        self.api.bad_readback=True
        with self.assertRaises(WorkerError):self.publish()

    def test_source_destination_and_receipt_types_are_checked(self):
        for change in ({'repository':'other/repo'},{'pr':True},{'executed':False},
                       {'head':'main'},{'state':'planned'},{'coordination':{}}):
            with self.assertRaises(WorkerError):self.publish(receipt={**receipt(),**change})
        self.assertFalse(any(p is not None for _,p,_ in self.api.calls))



class SyncTests(unittest.TestCase):
    def test_disabled_sync_does_not_read_receipt_or_call_api(self):
        from argparse import Namespace
        from unittest.mock import patch
        from sphereceti.worker_state import sync_receipt
        with patch('sphereceti.review_post.GitHub') as api,self.assertRaises(WorkerError):
            sync_receipt(Namespace(receipt=Path('/missing')),PROJECT,replace(POLICY,posting=False))
        api.assert_not_called()

    def test_retry_checks_approved_policy_and_acquisition_without_dispatch(self):
        from argparse import Namespace
        from unittest.mock import patch
        import tempfile
        from sphereceti.config import resource_text
        from sphereceti.worker_leases import Lease
        from sphereceti.worker_state import sync_receipt
        from test_worker_execution import API, context
        lease_api=API()
        lease=Lease(lease_api,context(),POLICY.authorized_reviewers,'user:7','test',now=lambda:lease_api.now)
        lease.acquire()
        record=receipt();record['coordination'].update(claim=lease.claim,lease_comment=lease.last['comment_id'])
        api=StateAPI()
        effective = resource_text('automation.toml').replace('review_generation = false','review_generation = true').replace('posting = false','posting = true').replace('authorized_reviewers = []','authorized_reviewers = ["user:7", "user:8"]')
        resources = {'sphereceti.toml': resource_text('sphereceti.toml'), 'automation.toml': effective}
        original=api.call
        def read(endpoint,**kwargs):
            if endpoint.endswith('/commits/main'):return {'sha':'1'*40}
            if '/contents/' in endpoint:
                name=endpoint.split('/contents/')[1].split('?')[0]
                raw=resources['automation.toml' if name.startswith('policy/') else name].encode()
                api.blobs[oid(raw)]=raw
                return {'type':'file','sha':oid(raw)}
            if '/issues/comments/' in endpoint:return deepcopy(lease_api.all[0])
            return original(endpoint,**kwargs)
        api.call=read
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'receipt.json';path.write_text(json.dumps(record))
            with patch('sphereceti.config.resource_text',side_effect=resources.__getitem__), patch('sphereceti.review_post.GitHub',return_value=api),patch('subprocess.run') as process:
                answer=sync_receipt(Namespace(receipt=path),PROJECT,POLICY)
                self.assertEqual(answer['state'],'synced')
                process.assert_not_called()
            # Receipt identity cannot be redirected to another acquisition.
            record['coordination']['claim']='a'*32;path.write_text(json.dumps(record))
            with patch('sphereceti.config.resource_text',side_effect=resources.__getitem__), patch('sphereceti.review_post.GitHub',return_value=api),self.assertRaises(WorkerError):
                sync_receipt(Namespace(receipt=path),PROJECT,POLICY)

if __name__=='__main__':unittest.main()
