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
            prefix:{'full_name':REPO,'allow_squash_merge':True,'allow_merge_commit':False,'allow_rebase_merge':False},
            # A preview classifies PR 1 read-only even while switches are off.
            prefix+'/pulls/1/files?per_page=100':[[{'filename':'README.md','status':'modified'}]],
            prefix+'/pulls/1/reviews?per_page=100':[[]],
            # Applying runs read the controller halt issues (decision 3); there are none.
            prefix+'/issues?creator=github-actions%5Bbot%5D&state=all&per_page=100':[[]]}))
        fake=self.bin/'gh';source=fake.read_text().replace('import json,pathlib,sys','import json,pathlib,sys,os\nassert "SPHERECETI_MERGE_TOKEN" not in os.environ')
        source=source.replace("'mergeable_state':'clean'}","'mergeable_state':'clean','changed_files':1,'auto_merge':None}")
        source=source.replace('else:raise AssertionError(endpoint)',
            "elif endpoint in (rules:=json.loads((path.parent/'server-rules.json').read_text())):out=rules[endpoint]\n"
            'else:raise AssertionError(endpoint)')
        fake.write_text(source)
        self.env['SPHERECETI_MERGE_TOKEN']='must-not-reach-reader-or-git'
        for key in [k for k in self.env if k.startswith('GITHUB_')]:del self.env[key]  # Hermetic even under CI.
        (self.foreign/'policy/merge-controller.toml').write_text('workflow_id=999\nchecks_app_id=9\n')

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
            'build is required from integration 15368, but checks_app_id is unconfigured',
            'strict_required_status_checks_policy is false: GitHub would accept a merge after main advances '
            'past the base the executor verified (humans can still update a branch and merge)'],protection
        assert all(r in setup['reasons'] for r in protection['missing']+setup['automatic_path']['missing'])
        executor=setup['executor']
        if command[-1]=='--apply':
            # Outside Actions the job token is absent: no run read, no view read, and every gap is reported.
            assert executor['context']=='github_actions' and executor['token_view']=='not read',executor
            assert 'missing exact workflow run/attempt' in executor['missing'] and setup['executor_verified'] is False
        else:
            assert executor['context']=='local' and executor['stand_in']['reader_current_user_can_bypass']=='never'
            assert ('executor not verified: run `merge-doctor --executor` in the approved workflow, '
                    'where the job token is available') in setup['reasons']
        if command[0]=='merge-control':
            assert value['state']=='disabled' and value['merge_attempted'] is False and value['refreshes_dispatched']==[]
        if command[1:]==('--pr','1'):
            # Switches off: the preview still classifies PR 1, read-only. A README change is human-route.
            [item]=value['results']
            assert item['state']=='blocked' and 'paths: README.md: roadmap specification requires human approval' in item['reasons']
        if command[-1]=='--apply':assert value['results']==[]
    assert not f.calls()
    # Main, branch summary, rules, ruleset list/detail and repository, each refreshed, per setup (3x12);
    # the preview's GET-only PR evidence (12); the disabled apply lists no work.
    calls=[c[0] for c in f.api()['calls']]
    # The disabled apply also reads (and refreshes) the halt inventory.
    assert len(calls)==50 and not any('pulls?state=open' in c for c in calls),calls
    assert not any('protection' in c[0] or 'collaborators' in c[0] for c in f.api()['calls'])
    return f
