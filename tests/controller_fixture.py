"""Installed controller diagnostics and disabled entry points with GET-only GitHub fixtures."""
import json
from pathlib import Path
import sys

from merge_fixture import MergeFixture
from review_fixture import ROOT, DISABLED_CONTROLLER, commit, git
from ruleset_fixture import REPO, live


class ControllerFixture(MergeFixture):
    def __init__(self,root):
        super().__init__(root)
        git(self.repo,'checkout','-q',self.tooling)
        (self.repo/'policy/merge-controller.toml').write_text(DISABLED_CONTROLLER)
        self.tooling=commit(self.repo)
        state=self.api();state['tooling']=self.tooling;self.api_state.write_text(json.dumps(state))
        # Live-shaped server rules, read even while the controller IDs are unconfigured.
        branch,effective,listing,detail=live();prefix=f'repos/{REPO}'
        (self.bin/'server-rules.json').write_text(json.dumps({
            prefix+'/branches/main':branch,prefix+'/rules/branches/main?per_page=100':effective,
            prefix+'/rulesets?includes_parents=true&per_page=100':listing,prefix+'/rulesets/21449770':detail,
            prefix:{'full_name':REPO,'allow_squash_merge':True,'allow_merge_commit':False,'allow_rebase_merge':False}}))
        fake=self.bin/'gh';source=fake.read_text().replace('import json,pathlib,sys','import json,pathlib,sys,os\nassert "SPHERECETI_MERGE_TOKEN" not in os.environ')
        source=source.replace('else:raise AssertionError(endpoint)',
            "elif endpoint in (rules:=json.loads((path.parent/'server-rules.json').read_text())):out=rules[endpoint]\n"
            'else:raise AssertionError(endpoint)')
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
        protection=setup['protection']
        assert (protection['source'],protection['ruleset_id'])==('ruleset',21449770)
        assert 'human-reviewed policy and dependency PRs can land with an approval and a passing build' in protection['verified']
        assert protection['missing']==[
            'ruleset 21449770 bypass actors are not visible to this reader; an administration-read token must confirm them',
            'build is required from integration 15368, but checks_app_id is unconfigured',
            'strict_required_status_checks_policy is false: GitHub would accept a merge after main advances '
            'past the base the executor verified (humans can still update a branch and merge)'],protection
        assert all(r in setup['reasons'] for r in protection['missing']+setup['automatic_path']['missing'])
        if command[0]=='merge-control':assert value['state']=='disabled' and value['merge_attempted'] is False
    assert not f.calls()
    # Main, branch summary, rules, ruleset list/detail and repository, each refreshed; no work listing.
    assert len(f.api()['calls'])==36
    assert not any('protection' in c[0] or 'collaborators' in c[0] for c in f.api()['calls'])
    return f
