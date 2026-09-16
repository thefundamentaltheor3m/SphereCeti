"""Installed controller diagnostics and disabled entry points with GET-only GitHub fixtures."""
import json
from pathlib import Path
import sys

from merge_fixture import MergeFixture
from review_fixture import ROOT, commit, git


class ControllerFixture(MergeFixture):
    def __init__(self,root):
        super().__init__(root)
        git(self.repo,'checkout','-q',self.tooling)
        (self.repo/'policy/merge-controller.toml').write_text((ROOT/'policy/merge-controller.toml').read_text())
        self.tooling=commit(self.repo)
        state=self.api();state['tooling']=self.tooling;self.api_state.write_text(json.dumps(state))
        fake=self.bin/'gh';source=fake.read_text().replace('import json,pathlib,sys','import json,pathlib,sys,os\nassert "SPHERECETI_MERGE_TOKEN" not in os.environ')
        fake.write_text(source)
        self.env['SPHERECETI_MERGE_TOKEN']='must-not-reach-reader-or-git'
        (self.foreign/'policy/merge-controller.toml').write_text('workflow_id=999\nbot_user_id=7\nchecks_app_id=9\n')

    def command(self,executable=None,*,output='ignored',extra=()):
        launcher=[str(executable)] if executable else [sys.executable,'-c',
            f'import sys; sys.path.insert(0,{str(ROOT/"tools/project")!r}); from sphereceti.cli import main; sys.exit(main())']
        return [*launcher,*extra,'--source-repo',str(self.repo),'--cache-dir',str(self.root/'cache'),'--json']


def installed_controller_smoke(executable,root):
    f=ControllerFixture(root)
    for command in (('merge-doctor',),('merge-control','--pr','1'),('merge-control','--sweep','--apply')):
        r=f.run(executable,extra=command)
        assert r.returncode==0,(r.stderr,r.stdout)
        value=json.loads(r.stdout)
        setup=value if command[0]=='merge-doctor' else value['setup']
        assert setup['ready'] is False and setup['merging_requested'] is False
        assert 'global merging switch is off' in setup['reasons']
        assert 'no approved mathematical change class' in setup['reasons']
        if command[0]=='merge-control':assert value['state']=='disabled' and value['merge_attempted'] is False
    assert not f.calls()
    assert len(f.api()['calls'])==6  # Main read and refresh only; disabled sweeps do not list work.
    return f
