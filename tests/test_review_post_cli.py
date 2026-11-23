"""CLI publication/inspection integration, using fake providers and a fake GitHub executable."""
import json
import subprocess
from pathlib import Path
import tempfile
import unittest

from review_post_fixture import PostingFixture, installed_post_smoke


class PostingCLITests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory(prefix='sphereceti-post-test-')
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)

    def test_explicit_post_and_provider_free_record_inspection(self):
        installed_post_smoke(None,self.root)

    def test_default_review_posts_its_record(self):
        f=PostingFixture(self.root)
        r=f.run()
        self.assertEqual(r.returncode,0,r.stderr)
        report=json.loads(r.stdout)
        self.assertEqual(report['publication']['state'],'confirmed')
        self.assertTrue(report['publication']['authorized'])
        self.assertEqual(len(f.api()['comments']),1)
        self.assertEqual(sum(c[1:]==['--method','POST','--input','-'] for c in f.api()['calls']),1)
        text=f.run(output='text',extra=('--no-post',))
        self.assertEqual(text.returncode,0,text.stderr)

    def test_default_text_output_names_the_comment(self):
        f=PostingFixture(self.root)
        command=[a for a in f.command() if a!='--json']
        r=subprocess.run(command,cwd=f.foreign,env=f.env,capture_output=True,text=True,timeout=120)
        self.assertEqual(r.returncode,0,r.stderr)
        self.assertIn('Posted: https://github.com/thefundamentaltheor3m/SphereCeti/pull/1#issuecomment-100 '
                      '(authorized reviewer).',r.stdout.splitlines())

    def test_no_post_and_dry_run_never_write_to_github(self):
        f=PostingFixture(self.root)
        for output,extra in (('result',('--no-post',)),('dry',('--dry-run',))):
            r=f.run(output=output,extra=extra)
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertNotIn('publication',json.loads(r.stdout))
        self.assertEqual(f.api()['comments'],[])
        self.assertFalse(any('POST' in c for c in f.api()['calls']))
        self.assertTrue((self.root/'result/record.json').is_file())
        self.assertEqual(len(f.calls()),10)

    def test_post_and_no_post_together_is_a_usage_error(self):
        f=PostingFixture(self.root)
        r=f.run(extra=('--post','--no-post'))
        self.assertEqual(r.returncode,2)
        self.assertIn('not allowed with argument',r.stderr)
        self.assertEqual(f.api()['calls'],[])
        self.assertFalse(f.calls())

    def test_policy_disabled_default_keeps_the_record_local(self):
        f=PostingFixture(self.root,posting=False)
        r=f.run()
        self.assertEqual(r.returncode,0,r.stderr)
        report=json.loads(r.stdout)
        self.assertEqual(report['not_posted'],'posting is disabled by approved repository policy')
        self.assertNotIn('publication',report)
        self.assertEqual(len(f.calls()),10)
        self.assertEqual(f.api()['comments'],[])
        self.assertFalse(any('POST' in c for c in f.api()['calls']))

    def test_approved_policy_blocks_post_before_provider_spend(self):
        f=PostingFixture(self.root,posting=False)
        r=f.run(extra=('--post',))
        self.assertEqual(r.returncode,2)
        self.assertIn('posting is disabled',r.stderr)
        self.assertFalse(f.calls())
        self.assertFalse(f.api()['comments'])

    def test_head_advancing_during_review_prevents_publication(self):
        f=PostingFixture(self.root)
        state=f.api();state['advance_at']=3;f.api_state.write_text(json.dumps(state))
        r=f.run(extra=('--post',))
        self.assertEqual(r.returncode,2,r.stderr)
        self.assertFalse(f.api()['comments'])
        saved=json.loads((self.root/'result/result.json').read_text())
        self.assertEqual(saved['publication']['state'],'unconfirmed')
        self.assertTrue((self.root/'result/record.md').is_file())

    def test_local_reply_file_cannot_attest_to_a_github_contest(self):
        f=PostingFixture(self.root)
        reply=self.root/'replies.json';reply.write_text('{}')
        r=f.run(extra=('--post','--replies-json',str(reply)))
        self.assertEqual(r.returncode,2,r.stderr)
        self.assertFalse(f.calls())
        self.assertFalse(f.api()['comments'])

    def test_api_contest_enters_engine_and_records_adjudicated_comment_id(self):
        f=PostingFixture(self.root)
        first=f.run(extra=('--post',))
        self.assertEqual(first.returncode,0,first.stderr)
        record=json.loads((self.root/'result/record.json').read_text())
        state=f.api()
        reply={**state['comments'][0],'id':200,'user':{'id':99,'type':'User'}}
        reply['body']='<!--sphereceti-contest:v1 '+json.dumps({'comment':100,'record':record['record_id'],
                                                            'rubric':'correctness'})+'-->\nPlease reconsider this fixture.'
        state['comments'].append(reply);f.api_state.write_text(json.dumps(state))
        second=f.run(output='reply',extra=('--post',))
        self.assertEqual(second.returncode,0,second.stderr)
        answered=json.loads((self.root/'reply/record.json').read_text())
        self.assertEqual(answered['contests_through']['correctness'],200)
        self.assertTrue(any('Please reconsider this fixture' in c['prompt'] for c in f.calls()[10:]))
        self.assertEqual(len(f.api()['comments']),3)


if __name__=='__main__':unittest.main()
