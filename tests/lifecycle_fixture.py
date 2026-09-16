"""Fresh installed lifecycle CLI with exact Git policy and a GET-only GitHub fixture."""
import json
from pathlib import Path
import sys

from merge_fixture import MergeFixture
from review_fixture import ROOT, commit, git


class LifecycleFixture(MergeFixture):
    def __init__(self, root):
        super().__init__(root)
        sys.path.insert(0, str(ROOT / 'tools/project'))
        from sphereceti.review_resources import tooling_files
        git(self.repo, 'checkout', '-q', self.tooling)
        for name, data in tooling_files().items():
            target = self.repo / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        self.tooling = commit(self.repo)
        (self.repo / 'README.md').write_text('proposed change\n')
        self.head = commit(self.repo)
        self.api_state.write_text(json.dumps({'head': self.head, 'tooling': self.tooling, 'calls': [],
                                             'labels': [], 'fail_labels': False}))
        fake = self.bin / 'gh'
        fake.write_text(f'#!{sys.executable}\n' + r'''
import json,os,pathlib,sys
assert 'SPHERECETI_MAINTENANCE_TOKEN' not in os.environ
path=pathlib.Path(__file__).parent/'github-state.json'
s=json.loads(path.read_text());a=sys.argv[1:]
assert a[:3]==['api','--hostname','github.com'];a=a[3:]
assert '--method' not in a and '--input' not in a
endpoint=a[0];s['calls'].append(a)
repo='thefundamentaltheor3m/SphereCeti';prefix='repos/'+repo
if endpoint==prefix+'/commits/main':out={'sha':s['tooling']}
elif endpoint==prefix+'/pulls/1':
 out={'number':1,'title':'Proposed change','body':'untrusted','user':{'id':99},
      'head':{'sha':s['head']},'base':{'sha':s['tooling'],'ref':'main','repo':{'full_name':repo}},
      'state':'open','draft':False,'merged':False,'mergeable':True,'mergeable_state':'clean',
      'auto_merge':None,'updated_at':'2026-01-01T00:00:00Z'}
elif endpoint==prefix+'/pulls?state=open&per_page=100':out=[[{'number':1}]]
elif endpoint==prefix+'/issues/1/labels?per_page=100':
 assert not s['fail_labels']
 out=[[{'name':name} for name in s['labels']]]
elif endpoint==prefix+f'/commits/{s["head"]}/statuses?per_page=100':out=[[]]
elif endpoint==prefix+'/actions/workflows/ci.yml':out={'id':7,'path':'.github/workflows/ci.yml','state':'active'}
elif endpoint==prefix+'/actions/workflows/ci.yml/runs?branch=main&event=push&per_page=30':
 out={'total_count':1,'workflow_runs':[{'id':99,'workflow_id':7,'path':'.github/workflows/ci.yml',
      'head_branch':'main','head_sha':s['tooling'],'repository':{'full_name':repo},'event':'push',
      'created_at':'2026-01-01T00:00:00Z','status':'completed','conclusion':'success'}]}
else:raise AssertionError(endpoint)
path.write_text(json.dumps(s));print(json.dumps(out))
''')
        fake.chmod(0o755)
        (self.foreign / 'policy/lifecycle.toml').write_text('labels_enabled=true\nwriter_user_id=99\n')
        self.env['SPHERECETI_MAINTENANCE_TOKEN'] = 'private-writer-must-not-reach-reader'

    def command(self, executable=None, *, output='ignored', extra=()):
        launcher = [str(executable)] if executable else [sys.executable, '-c',
            f'import sys; sys.path.insert(0,{str(ROOT/"tools/project")!r}); from sphereceti.cli import main; sys.exit(main())']
        return [*launcher, 'maintenance', '--pr', '1', '--source-repo', str(self.repo),
                '--cache-dir', str(self.root / 'cache'), '--json', *extra]


def installed_lifecycle_smoke(executable, root):
    fixture = LifecycleFixture(root)
    result = fixture.run(executable)
    assert result.returncode == 0, result.stderr + result.stdout
    report = json.loads(result.stdout)
    assert report['results'][0]['add'] == ['sphereceti:human-review']
    assert report['main_health']['state'] == 'green'
    assert not report['setup']['ready'] and not report['merge_allowed']
    before = len(fixture.api()['calls'])
    result = fixture.run(executable, extra=('--apply-labels',))
    assert result.returncode == 1
    assert json.loads(result.stdout)['state'] == 'disabled'
    assert all('/pulls' not in call[0] for call in fixture.api()['calls'][before:])
    state = fixture.api(); state['fail_labels'] = True
    fixture.api_state.write_text(json.dumps(state))
    result = fixture.run(executable)
    assert result.returncode == 1
    assert json.loads(result.stdout)['results'][0]['state'] == 'error'
    assert not fixture.calls()
    return fixture
