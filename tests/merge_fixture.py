"""Installed/source CLI observation with disposable Git and GET-only fake GitHub."""
import json
from pathlib import Path
import sys

from review_fixture import ReviewFixture, ROOT, commit, git


class MergeFixture(ReviewFixture):
    def __init__(self, root, *, mathematical=False, approved_policy=True):
        super().__init__(root)
        git(self.repo,'checkout','-q',self.tooling)
        if approved_policy:
            (self.repo/'policy/merge-checks.toml').write_text((ROOT/'policy/merge-checks.toml').read_text())
        if mathematical:
            policy=self.repo/'policy/automation.toml'
            policy.write_text(policy.read_text().replace('mathematical_paths = []','mathematical_paths = ["SphereCeti/Math"]'))
        self.tooling=commit(self.repo) if approved_policy or mathematical else self.tooling
        path=self.repo/('SphereCeti/Math/New.lean' if mathematical else 'README.md')
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text('proposed content\n')
        # Candidate configuration cannot supply missing approved-main policy.
        if not approved_policy:
            (self.repo/'policy/merge-checks.toml').write_text('schema_version=1\nworkflow_id=123\nstatus_creator_ids=[42]\n')
        self.head=commit(self.repo)
        self.api_state=self.bin/'github-state.json'
        self.api_state.write_text(json.dumps({'head':self.head,'tooling':self.tooling,'pull_reads':0,'calls':[],'advance_at':0}))
        fake=self.bin/'gh'
        fake.write_text(f'#!{sys.executable}\n'+r'''
import json,pathlib,sys
path=pathlib.Path(__file__).parent/'github-state.json'
s=json.loads(path.read_text());a=sys.argv[1:]
assert a[:3]==['api','--hostname','github.com'];a=a[3:]
assert '--method' not in a and '--input' not in a
endpoint=a[0];s['calls'].append(a)
repo='thefundamentaltheor3m/SphereCeti'
if endpoint==f'repos/{repo}/pulls/1':
 s['pull_reads']+=1
 head=s['tooling'] if s['advance_at'] and s['pull_reads']>=s['advance_at'] else s['head']
 out={'number':1,'title':'Proposed change','body':'untrusted','user':{'id':99},
      'head':{'sha':head},'base':{'sha':s['tooling'],'ref':'main','repo':{'full_name':repo}},
      'state':'open','draft':False,'merged':False,'mergeable':True,'mergeable_state':'clean'}
elif endpoint==f'repos/{repo}/commits/main':out={'sha':s['tooling']}
elif endpoint==f'repos/{repo}/commits/{s["head"]}/statuses?per_page=100':out=[[]]
elif endpoint==f'repos/{repo}/issues/1/comments?per_page=100':out=[[]]
else:raise AssertionError(endpoint)
path.write_text(json.dumps(s));print(json.dumps(out))
''')
        fake.chmod(0o755)
        (self.foreign/'policy').mkdir()
        (self.foreign/'policy/merge-checks.toml').write_text('workflow_id=999\nstatus_creator_ids=[42]\n')

    def command(self, executable=None, *, output='ignored', extra=()):
        launcher=[str(executable)] if executable else [sys.executable,'-c',
            f'import sys; sys.path.insert(0,{str(ROOT/"tools/project")!r}); from sphereceti.cli import main; sys.exit(main())']
        return [*launcher,'merge-observe','1','--source-repo',str(self.repo),'--dependencies-dir',str(self.deps),
                '--cache-dir',str(self.root/'cache'),'--json',*extra]

    def api(self):return json.loads(self.api_state.read_text())


def installed_merge_smoke(executable,root):
    fixture=MergeFixture(root,mathematical=True)
    run=fixture.run(executable)
    assert run.returncode==0,run.stderr
    result=json.loads(run.stdout)
    assert result['eligibility']=='blocked' and result['merge_allowed'] is False
    assert result['scope']['scope']=='mathematical'
    assert 'trusted check producers are not configured' in result['reasons']
    assert not fixture.calls()
    assert len(fixture.api()['calls'])==8  # PR, main, comments, statuses and their refreshes.
    assert not any('--method' in c for c in fixture.api()['calls'])
    return fixture
