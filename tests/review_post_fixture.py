"""Fake GitHub executable for installed/source record flows; never performs network I/O."""
import json
from pathlib import Path
import sys

from review_fixture import ReviewFixture, commit, git


class PostingFixture(ReviewFixture):
    def __init__(self, root, *, posting=True):
        super().__init__(root)
        git(self.repo,'checkout','-q',self.tooling)
        policy=self.repo/'policy/automation.toml'
        policy.write_text(policy.read_text().replace('posting = false',f'posting = {str(posting).lower()}').replace(
            'authorized_reviewers = []','authorized_reviewers = ["user:7"]'))
        self.tooling=commit(self.repo)
        (self.repo/'README.md').write_text('PROPOSED SENTINEL roadmap')
        self.head=commit(self.repo)
        self.api_state=self.bin/'github-state.json'
        self.api_state.write_text(json.dumps({'head':self.head,'tooling':self.tooling,'pull_reads':0,
                                              'comments':[],'calls':[],'advance_at':0}))
        fake=self.bin/'gh'
        fake.write_text(f'#!{sys.executable}\n'+r'''
import json,os,pathlib,sys
root=pathlib.Path(__file__).parent
path=root/'github-state.json'
s=json.loads(path.read_text())
a=sys.argv[1:]
assert a.pop(0)=='api'
if a[:2]==['--hostname','github.com']:a=a[2:]
endpoint=a[0]
s['calls'].append(a)
assert os.environ.get('GH_TOKEN')=='test-github-token-must-not-reach-provider'
repo='thefundamentaltheor3m/SphereCeti'
if endpoint==f'repos/{repo}/pulls/1':
 s['pull_reads']+=1
 head=s['tooling'] if s['advance_at'] and s['pull_reads']>=s['advance_at'] else s['head']
 out={'number':1,'title':'Proposed roadmap','body':'untrusted','user':{'id':99},
      'head':{'sha':head},'base':{'sha':s['tooling'],'repo':{'full_name':repo}}}
elif endpoint==f'repos/{repo}/commits/main':out={'sha':s['tooling']}
elif endpoint==f'repos/{repo}/issues/1/comments?per_page=100':
 assert a[1:]==['--paginate','--slurp'];out=[s['comments']]
elif endpoint==f'repos/{repo}/issues/1/comments':
 assert a[1:]==['--method','POST','--input','-']
 payload=json.load(sys.stdin)
 out={'id':max([99]+[c['id'] for c in s['comments']])+1,'body':payload['body'],'user':{'id':7,'type':'User'},
      'issue_url':f'https://api.github.com/repos/{repo}/issues/1',
      'created_at':'2026-09-11T00:00:00Z','updated_at':'2026-09-11T00:00:00Z'}
 s['comments'].append(out)
elif endpoint.startswith(f'repos/{repo}/issues/comments/'):
 out=next(c for c in s['comments'] if c['id']==int(endpoint.split('/')[-1]))
else:raise AssertionError(endpoint)
path.write_text(json.dumps(s))
print(json.dumps(out))
''')
        fake.chmod(0o755)

    def command(self, executable=None, *, output='result',extra=()):
        original=super().command(executable,output=output,extra=extra)
        command=[];i=0
        while i<len(original):
            arg=original[i]
            if arg in ('--tooling','--base','--head'):i+=2;continue
            if arg!='--local-sources':command.append(arg)
            i+=1
        return command

    def api(self):return json.loads(self.api_state.read_text())


def installed_post_smoke(executable,root):
    fixture=PostingFixture(root)
    run=fixture.run(executable,extra=('--post',))
    assert run.returncode==0,(run.stderr,run.stdout)
    report=json.loads(run.stdout)
    assert report['publication']['authorized'] is True
    assert report['publication']['identity']=='user:7'
    assert report['merge_eligible'] is False
    assert len(fixture.api()['comments'])==1
    assert len(fixture.calls())==10
    inspect=fixture.run(executable,output='inspect',extra=('--read-records',))
    assert inspect.returncode==0,inspect.stderr
    assert json.loads(inspect.stdout)['review_safe'] is False  # Fixture tooling is not the installed tree.
    assert len(fixture.calls())==10
    return fixture
