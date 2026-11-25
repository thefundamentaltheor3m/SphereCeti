"""Read-only activation diagnostics for the disabled, serialized controller.

TauCetiReview@afb424eda89e8ac96d9eb69f6a88972055a4cd1b
.github/workflows/{merge-only,merge-sweep}.yml, Apache-2.0; TauCetiReview contributors.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import tomllib
from urllib.parse import quote

from . import controller_halt
from .config import fields, parse_policy, parse_project, resource_text, version
from .gate import blob, tree
from .local_review import object_source
from .merge_checks import CONTEXTS, WORKFLOW as TRUSTED_WORKFLOW, parse_checks
from .merge_observation import Reader
from .review_records import RecordError
from .review_resources import tooling_files

WORKFLOW = '.github/workflows/merge-controller.yml'


LEGACY_CONTROLLER = {'schema_version','workflow_id','bot_user_id','checks_app_id','merge_method'}


def parse_controller(text):
    value = tomllib.loads(text)
    if isinstance(value, dict) and set(value) == LEGACY_CONTROLLER:
        # An approved main from before option A stays diagnosable, but it can never be ready.
        version(value, 'merge controller')
        if any(type(value[k]) is not int or value[k] < 0 for k in ('workflow_id','bot_user_id','checks_app_id')):
            raise RecordError('controller IDs must be nonnegative integers')
        if value['merge_method'] != 'squash': raise RecordError('only the reviewed squash transport is supported')
        return {'schema_version': 1, 'workflow_id': value['workflow_id'], 'checks_app_id': value['checks_app_id'],
                'merge_method': 'squash', 'legacy': True}
    fields(value, {'schema_version','workflow_id','checks_app_id','merge_method'}, 'merge controller')
    version(value, 'merge controller')
    if any(type(value[k]) is not int or value[k] < 0 for k in ('workflow_id','checks_app_id')):
        raise RecordError('controller IDs must be nonnegative integers')
    if value['merge_method'] != 'squash': raise RecordError('only the reviewed squash transport is supported')
    return value


def classic(protection, repository, settings):
    """Conservative classic-protection profile, unchanged from the initial controller."""
    reasons = []
    if not isinstance(protection, dict): return ['branch protection is unavailable']
    if protection.get('url') != f'https://api.github.com/repos/{repository}/branches/main/protection':
        reasons.append('branch protection belongs to another branch/repository')
    checks = protection.get('required_status_checks') or {}
    if checks.get('strict') is not True: reasons.append('up-to-date branches are not required')
    entries = checks.get('checks')
    if not isinstance(entries, list): reasons.append('required status producers are not explicit')
    else:
        for name in CONTEXTS:
            matches = [c for c in entries if isinstance(c,dict) and c.get('context') == name]
            if (len(matches) != 1 or type(matches[0].get('app_id')) is not int or
                    matches[0]['app_id'] != settings['checks_app_id'] or settings['checks_app_id'] <= 0):
                reasons.append(f'{name} is not required from the approved App')
    if (protection.get('enforce_admins') or {}).get('enabled') is not True:
        reasons.append('branch rules do not apply to administrators')
    for name in ('allow_force_pushes','allow_deletions'):
        if (protection.get(name) or {}).get('enabled') is not False:
            reasons.append(f'{name} is not explicitly disabled')
    reviews = protection.get('required_pull_request_reviews')
    if not isinstance(reviews,dict): reasons.append('server-enforced PR reviews are missing')
    else:
        if type(reviews.get('required_approving_review_count')) is not int or reviews['required_approving_review_count'] < 1:
            reasons.append('at least one server-enforced approval is required')
        if reviews.get('dismiss_stale_reviews') is not True: reasons.append('stale server reviews are not dismissed')
        bypass = reviews.get('bypass_pull_request_allowances', {})
        if not isinstance(bypass,dict) or set(bypass)-{'users','teams','apps'} or any(bypass.values()):
            reasons.append('PR-review bypass allowances are present or unknown')
    return reasons


# Ruleset profile. Rule types, parameters and bypass actors outside these sets fail closed.
RULE_TYPES = ('deletion', 'non_fast_forward', 'pull_request', 'required_status_checks')
REVIEW_PARAMETERS = {'required_approving_review_count', 'dismiss_stale_reviews_on_push', 'required_reviewers',
                     'require_code_owner_review', 'require_last_push_approval', 'required_review_thread_resolution',
                     'require_extra_approval_for_unattributed_changes', 'allowed_merge_methods'}
CHECK_PARAMETERS = {'strict_required_status_checks_policy', 'do_not_enforce_on_create', 'required_status_checks'}
SOURCE_KEYS = {'ruleset_source_type', 'ruleset_source', 'ruleset_id'}
# GitHub's built-in repository-role IDs in bypass lists: 2 is maintain and 5 is admin. Organization
# owners hold admin. None of these is the standard write role required of the merge identity, so
# they can serve maintainers without letting the executor skip protection.
HUMAN_BYPASS = {('RepositoryRole', 2): 'maintain role', ('RepositoryRole', 5): 'admin role',
                ('OrganizationAdmin', None): 'organization admins', ('OrganizationAdmin', 1): 'organization admins'}
# Protected PRs (policy, dependencies, CI, review policy, merge machinery) take the human route.
# trusted-scope reports human_review as a non-success, and dependency changes also stop trusted-build.
# The ruleset must still admit them with a human approval and a passing ordinary `build`.
HUMAN_ROUTE = {
    'policy': {'approvals': 1, 'method': 'squash',
               'checks': {'build': 'success', 'trusted-build': 'success', 'trusted-scope': 'failure'}},
    'dependency': {'approvals': 1, 'method': 'squash',
                   'checks': {'build': 'success', 'trusted-build': 'failure', 'trusted-scope': 'failure'}},
}


def pages(value, name):
    """Rows from `gh api --paginate --slurp`; a short non-final page means a truncated inventory."""
    if (not isinstance(value, list) or not value or any(not isinstance(p, list) or len(p) > 100 for p in value) or
            any(len(p) != 100 for p in value[:-1])):
        raise RecordError(f'incomplete {name} inventory')
    rows = [r for p in value for r in p]
    if any(not isinstance(r, dict) for r in rows): raise RecordError(f'invalid {name} inventory')
    return rows


def admits(rules, pr):
    """Requirements of these supported rule types that a PR with the given evidence would fail."""
    blocked = []
    for rule in rules:
        parameters = rule.get('parameters') or {}
        if rule.get('type') == 'pull_request':
            if pr['approvals'] < parameters.get('required_approving_review_count', 0):
                blocked.append('approvals')
            if pr['method'] not in parameters.get('allowed_merge_methods', ()):
                blocked.append(f"{pr['method']} merges")
        elif rule.get('type') == 'required_status_checks':
            for check in parameters.get('required_status_checks', ()):
                if pr['checks'].get(check.get('context')) != 'success': blocked.append(check.get('context'))
    return blocked


def rulesets(effective, listing, detail, repository, settings):
    """Verify the single active repository ruleset that governs main; report every item."""
    verified, findings, missing = [], [], []
    ids = sorted({r.get('ruleset_id') for r in effective}, key=str)
    if any(type(i) is not int or i <= 0 for i in ids) or any(not isinstance(r.get('type'), str) for r in effective):
        raise RecordError('invalid branch-rules inventory')
    if any(type(r.get('id')) is not int for r in listing) or len({r['id'] for r in listing}) != len(listing):
        raise RecordError('invalid or duplicate ruleset inventory')
    rid = ids[0] if len(ids) == 1 else None
    if rid is None or [r['id'] for r in listing] != [rid]:
        missing.append(f'exactly one ruleset must exist and govern main; effective rules come from {ids or "none"} '
                       f'and the repository lists {sorted(r["id"] for r in listing)}')
    for ruleset in listing:
        if ruleset.get('enforcement') != 'active':
            missing.append(f'ruleset {ruleset["id"]} enforcement is {ruleset.get("enforcement")!r}, not active')
        if ruleset.get('source_type') != 'Repository' or ruleset.get('source') != repository or ruleset.get('target') != 'branch':
            missing.append(f'ruleset {ruleset["id"]} is not a branch ruleset owned by this repository')
    if any(r.get('ruleset_source_type') != 'Repository' or r.get('ruleset_source') != repository for r in effective):
        missing.append('an effective rule for main comes from outside this repository')
    bypass = None
    if rid is not None:
        rules = sorted(({k: v for k, v in r.items() if k not in SOURCE_KEYS} for r in effective), key=lambda r: json.dumps(r, sort_keys=True))
        if (not isinstance(detail, dict) or detail.get('id') != rid or not isinstance(detail.get('rules'), list) or
                sorted(detail['rules'], key=lambda r: json.dumps(r, sort_keys=True)) != rules):
            raise RecordError('ruleset detail disagrees with the effective rules for main')
        if detail.get('enforcement') != 'active' or detail.get('target') != 'branch':
            missing.append(f'ruleset {rid} is not an active branch ruleset')
        if 'bypass_actors' not in detail:
            # The workflow's job token never has administration access. The executor's own
            # current_user_can_bypass view, a blocker of the automatic path, decides for it.
            findings.append(f'ruleset {rid} bypass actors are not visible to this reader (administration access '
                            "is needed); the job token's own current_user_can_bypass view decides for the executor")
        else: bypass = detail['bypass_actors']
    types = [r['type'] for r in effective]
    for name in sorted(set(types) - set(RULE_TYPES)):
        missing.append(f'unsupported rule type {name!r} needs a separately reviewed profile')
    for name, label in (('deletion', 'deletion of main is blocked'), ('non_fast_forward', 'force pushes to main are blocked')):
        (verified if name in types else missing).append(label if name in types else f'{name} rule is missing')
    reviews = [r.get('parameters') for r in effective if r['type'] == 'pull_request']
    if len(reviews) != 1 or not isinstance(reviews[0], dict):
        missing.append('exactly one pull_request rule with parameters is required')
    else:
        p = reviews[0]
        if set(p) - REVIEW_PARAMETERS: missing.append(f'unknown pull_request parameters {sorted(set(p) - REVIEW_PARAMETERS)}')
        count = p.get('required_approving_review_count')
        if type(count) is int and count >= 1: verified.append(f'pull_request requires {count} approving review(s)')
        else: missing.append('pull_request rule must require at least one approving review')
        methods = p.get('allowed_merge_methods')
        if isinstance(methods, list) and 'squash' in methods: verified.append(f'allowed merge methods {json.dumps(methods)} include squash')
        else: missing.append('pull_request rule must allow squash merges')
        if p.get('required_review_thread_resolution') is True: verified.append('review threads must be resolved')
        for key, why in (('dismiss_stale_reviews_on_push', 'approvals survive later pushes'),
                         ('require_last_push_approval', 'the last pusher may supply the approval')):
            if p.get(key) is not True: findings.append(f'{key} is {json.dumps(p.get(key))}: {why} (recommended, not yet required)')
    checks = [r.get('parameters') for r in effective if r['type'] == 'required_status_checks']
    if any(not isinstance(c, dict) or set(c) - CHECK_PARAMETERS or not isinstance(c.get('required_status_checks'), list)
           for c in checks):
        missing.append('required_status_checks rule has missing or unknown parameters')
        checks = []
    entries = [e for c in checks for e in c['required_status_checks']]
    if any(not isinstance(e, dict) or not isinstance(e.get('context'), str) or set(e) - {'context', 'integration_id'}
           for e in entries):
        raise RecordError('invalid required status check entry')
    if not entries: missing.append('no status check is required for every PR')
    app = settings['checks_app_id']
    for entry in entries:
        name, producer = entry['context'], entry.get('integration_id')
        if type(producer) is not int: missing.append(f'{name} is required from any producer; bind it to an integration')
        elif app <= 0: missing.append(f'{name} is required from integration {producer}, but checks_app_id is unconfigured')
        elif producer != app: missing.append(f'{name} is required from integration {producer}, not checks_app_id {app}')
        else: verified.append(f'{name} is required from integration {producer}')
    strict = bool(entries) and any(c.get('strict_required_status_checks_policy') is True for c in checks)
    if strict:
        verified.append('PR branches must be up to date with main before merging')
    elif any(c.get('strict_required_status_checks_policy') is True for c in checks):
        missing.append('up-to-date branches are not enforced: GitHub ignores strict_required_status_checks_policy '
                       'without a required status check')
    else:
        missing.append('strict_required_status_checks_policy is false: GitHub would accept a merge after main advances '
                       'past the base the executor verified (humans can still update a branch and merge)')
    blocked = {route: admits(effective, pr) for route, pr in HUMAN_ROUTE.items()}
    for route, items in blocked.items():
        if items: missing.append(f'ruleset would block human-reviewed {route} PRs: {", ".join(items)}')
    if not any(blocked.values()):
        verified.append('human-reviewed policy and dependency PRs can land with an approval and a passing build')
    if bypass is not None:
        if not isinstance(bypass, list) or any(not isinstance(a, dict) for a in bypass): raise RecordError('invalid bypass actors')
        for actor in bypass:
            key, mode = (actor.get('actor_type'), actor.get('actor_id')), actor.get('bypass_mode')
            if key in HUMAN_BYPASS:
                verified.append(f'{HUMAN_BYPASS[key]} may bypass ({mode}); the write-role merge identity does not hold it')
            else: missing.append(f'bypass actor {key[0]} {key[1]} ({mode}) could cover the merge identity')
        if not bypass: verified.append('ruleset has no bypass actors')
    # Strict (with a required check, so it takes effect) is what makes GitHub refuse a head behind main:
    # the merge API pins only the head, so this is how the tested merge tree is the tree that lands.
    squash_only = len(reviews) == 1 and isinstance(reviews[0], dict) and reviews[0].get('allowed_merge_methods') == ['squash']
    return {'source': 'ruleset', 'ruleset_id': rid, 'verified': verified, 'findings': findings, 'missing': missing,
            'tested_tree_enforced': strict and not missing, 'squash_only': squash_only}


def merge_setting(repository, name, protection):
    """The squash-merge setting. The single ruleset's allowed_merge_methods is the authority when it is
    exactly ["squash"]: GitHub enforces it at merge time, and the job token can read it. The repository
    flag is omitted for a token without push access (the read-only job token, run 45274799597). When
    visible it must be true. When hidden it is advisory, but only under that ruleset. A disabled flag
    could only make GitHub refuse the executor's squash PUT, which is a stop, never another landing."""
    found = {'verified': [], 'findings': [], 'missing': []}
    if not isinstance(repository, dict) or repository.get('full_name') != name:
        found['missing'].append('repository identity is incompatible')
    elif 'allow_squash_merge' in repository:
        if repository['allow_squash_merge'] is True: found['verified'].append('repository allows squash merges')
        else: found['missing'].append('repository does not allow squash merges')
    elif protection.get('source') == 'ruleset' and protection.get('squash_only') is True:
        found['findings'].append('repository merge settings are not visible to this token; the ruleset\'s '
                                 'allowed_merge_methods ["squash"] is the authority')
    else:
        found['missing'].append('the squash-merge setting is not visible to this token, and no ruleset restricts '
                                'merges to squash')
    return found


def executor_bypass(view, rid):
    """The job token's own view of the ruleset; GitHub resolves its bypass status, so nothing is guessed."""
    if not isinstance(view, dict) or view.get('id') != rid: return [f'the job token cannot read ruleset {rid}']
    if 'current_user_can_bypass' not in view:
        return [f'GitHub omitted current_user_can_bypass for the job token on ruleset {rid}, '
                'so whether the executor can bypass it is unknown']
    if view['current_user_can_bypass'] != 'never':
        return [f"the job token may bypass ruleset {rid} (current_user_can_bypass: {view['current_user_can_bypass']!r})"]
    return []


def server(client, repository, settings):
    """Classic protection or the single repository ruleset; anything else fails closed."""
    branch = client.call(f'repos/{repository}/branches/main')
    summary = branch.get('protection') if isinstance(branch, dict) else None
    if (not isinstance(branch, dict) or branch.get('name') != 'main' or type(branch.get('protected')) is not bool or
            not isinstance(summary, dict) or type(summary.get('enabled')) is not bool):
        raise RecordError('incomplete branch protection summary')
    effective = pages(client.call(f'repos/{repository}/rules/branches/main?per_page=100', paginate=True), 'branch-rules')
    listing = pages(client.call(f'repos/{repository}/rulesets?includes_parents=true&per_page=100', paginate=True), 'ruleset')
    empty = {'verified': [], 'findings': []}
    if summary['enabled']:
        if effective or listing:
            return {'source': 'classic+ruleset', **empty,
                    'missing': ['classic protection and rulesets both apply; a combined profile is unsupported']}
        if any(not settings[k] for k in ('workflow_id', 'checks_app_id')):
            return {'source': 'classic', **empty,
                    'missing': ['classic protection is read only after controller IDs are configured']}
        found = classic(client.call(f'repos/{repository}/branches/main/protection'), repository, settings)
        return {'source': 'classic', 'verified': [] if found else ['classic profile'], 'findings': [], 'missing': found,
                'tested_tree_enforced': not found}  # The classic profile requires strict checks.
    if not effective and not listing:
        return {'source': None, **empty, 'missing': ['main has neither classic protection nor a ruleset']}
    ids = {r.get('ruleset_id') for r in effective}
    rid = next(iter(ids)) if len(ids) == 1 else None
    detail = client.call(f'repos/{repository}/rulesets/{rid}') if type(rid) is int and rid > 0 else None
    found = rulesets(effective, listing, detail, repository, settings)
    if branch['protected'] is not True: found['missing'].append('GitHub does not report main as protected')
    found['reader_view'] = detail.get('current_user_can_bypass', 'omitted') if isinstance(detail, dict) else None
    return found


def automatic(policy, checks, settings, roadmap):
    """What the no-click route needs beyond the ruleset; the executor verifies evidence per PR."""
    producers = (f"statuses from creator {checks['status_creator_ids']} in one attempt of workflow "
                 f"{checks['workflow_id']} ({TRUSTED_WORKFLOW})") if checks['workflow_id'] else 'configured producers'
    verifies = [f'trusted-build success: {producers}, bound to the exact PR head',
                "the trusted run built and audited the head merged into current approved main (trusted-merge "
                'attests that tree and main), so approved tooling tested what would land',
                'trusted-scope success, meaning scope "mathematical" within policy mathematical_paths',
                'an accepted official review record for the exact head from policy authorized_reviewers, '
                'published by someone other than the PR author',
                'the review is still valid: same change and no review input changed on main since it ran (option 2)',
                'the PR is open, targets main, has no conflicts and its head contains current main',
                "a qualifying formal approval: an opted-in maintainer's (approving_reviewers) latest review is APPROVE on the "
                'exact head, the maintainer is not the PR author, and no reviewer has outstanding changes requested',
                'one squash-merge PUT pinned to that head SHA']
    missing = []
    if not policy.merging: missing.append('global merging switch is off')
    if not policy.mathematical_paths: missing.append('no approved mathematical change class')
    if not policy.authorized_reviewers: missing.append('authorized reviewers are not configured')
    if not roadmap: missing.append('approved mathematical roadmap is missing')
    if not checks['workflow_id'] or not checks['status_creator_ids']: missing.append('trusted check producers are not configured')
    for key, label in (('workflow_id', 'serialized controller workflow'), ('checks_app_id', 'required-check integration')):
        if not settings[key]: missing.append(f'{label} is not configured (policy/merge-controller.toml {key} = 0)')
    if settings.get('legacy'):
        missing.append('approved policy/merge-controller.toml predates option A (it has bot_user_id)')
    if not policy.approving_reviewers:
        missing.append('no opted-in approving maintainer (policy/automation.toml approving_reviewers is empty)')
    end_state = ["the formal approval is an opted-in maintainer's own APPROVE, which their all-green `sphereceti review` "
                 'submits under their account (built separately); the controller merges only after it, using the '
                 "scheduled workflow's job token, never a bot or machine-user account"]
    return {'executor_verifies': verifies, 'missing': missing, 'end_state': end_state}


EXECUTOR_CHECKS = (
    'GITHUB_WORKFLOW_REF names .github/workflows/merge-controller.yml on refs/heads/main',
    'GITHUB_WORKFLOW_SHA and GITHUB_SHA equal approved main, and GITHUB_REF is refs/heads/main',
    'GITHUB_REPOSITORY is this repository and the event is workflow_dispatch or schedule',
    'the live run (GITHUB_RUN_ID/ATTEMPT) is in progress for that workflow path, head and repository',
    "the run's workflow_id equals policy/merge-controller.toml workflow_id",
    'the merge credential behaves as this repository\'s installation token: GET /installation/repositories '
    'with it lists exactly this repository (personal, OAuth and user-token prefixes are refused unsent)',
    "that token's own view of the ruleset reports current_user_can_bypass: \"never\"",
)


def executor(run, settings, revision, repository, environ):
    """Runtime checks of the approved run. The approved workflow's bytes bind the token it passes."""
    reasons = []
    expected = {'GITHUB_ACTIONS':'true','GITHUB_REPOSITORY':repository,'GITHUB_REF':'refs/heads/main',
                'GITHUB_SHA':revision,'GITHUB_WORKFLOW_SHA':revision,
                'GITHUB_WORKFLOW_REF':f'{repository}/{WORKFLOW}@refs/heads/main'}
    for key, value in expected.items():
        if environ.get(key) != value: reasons.append(f'{key} is {environ.get(key)!r}, expected {value!r}')
    if environ.get('GITHUB_EVENT_NAME') not in ('schedule','workflow_dispatch'):
        reasons.append(f"GITHUB_EVENT_NAME is {environ.get('GITHUB_EVENT_NAME')!r}, expected schedule or workflow_dispatch")
    rid, attempt = environ.get('GITHUB_RUN_ID',''), environ.get('GITHUB_RUN_ATTEMPT','')
    if not re.fullmatch(r'[1-9][0-9]*',rid) or not re.fullmatch(r'[1-9][0-9]*',attempt):
        return reasons + ['missing exact workflow run/attempt']
    if not isinstance(run,dict): return reasons + ['controller run is unavailable']
    expected_run = {'id':int(rid),'run_attempt':int(attempt),'head_sha':revision,'head_branch':'main',
                    'path':WORKFLOW,'status':'in_progress'}
    for key, value in expected_run.items():
        if run.get(key) != value or (type(value) is int and type(run.get(key)) is not int):
            reasons.append(f'controller run has {key} {run.get(key)!r}, expected {value!r}')
    if run.get('event') not in ('schedule','workflow_dispatch') or (run.get('repository') or {}).get('full_name') != repository:
        reasons.append('controller run event/repository is not approved')
    if not settings['workflow_id']:
        reasons.append(f"workflow_id is not configured; this run reports workflow_id {run.get('workflow_id')!r}")
    elif run.get('workflow_id') != settings['workflow_id'] or type(run.get('workflow_id')) is not int:
        reasons.append(f"controller run has workflow_id {run.get('workflow_id')!r}, expected {settings['workflow_id']}")
    return reasons


class Activation:
    def __init__(self, args, project, writer):
        self.args, self.project, self.writer = args, project, writer
        self.reader = self.settings = self.policy = self.checks = None

    def inspect(self, *, applying=False, verify_executor=False):
        """Setup diagnosis. The executor is verified with the job token for --apply or `merge-doctor --executor`."""
        project, args = self.project, self.args
        client = self.reader = Reader(project.repository)
        current = client.call(f'repos/{project.repository}/commits/{quote(project.default_branch,safe="")}')['sha']
        cache = args.cache_dir.expanduser().absolute(); cache.mkdir(parents=True,exist_ok=True)
        repo = object_source(args.source_repo, cache/'SphereCeti.git',f'https://github.com/{project.repository}',[current],False)
        approved = tree(repo,current)
        paths = ('sphereceti.toml','policy/automation.toml','policy/merge-checks.toml','policy/merge-controller.toml')
        missing = [p for p in paths if p not in approved]
        result = {'schema_version':1,'repository':project.repository,'tooling':current,'ready':False,
                  'merging_requested':False,'executor_verified':False,'reasons':[], 'merge_allowed':False}
        if missing:
            result['reasons']=['approved main lacks '+p for p in missing]; client.revalidate(); return result
        data = {p:blob(repo,approved[p]) for p in paths}
        selected = parse_project(data['sphereceti.toml'].decode())
        if selected.repository != project.repository or selected.implementation_repository != project.implementation_repository:
            raise RecordError('approved controller profile has another project identity')
        policy = self.policy = parse_policy(data['policy/automation.toml'].decode())
        checks = self.checks = parse_checks(data['policy/merge-checks.toml'].decode())
        settings = self.settings = parse_controller(data['policy/merge-controller.toml'].decode())
        result['merging_requested']=policy.merging
        path=automatic(policy,checks,settings,selected.roadmap_approved)
        template = resource_text('merge-controller.yml').encode()
        if WORKFLOW not in approved or blob(repo,approved[WORKFLOW]) != template:
            path['missing'].append('exact serialized controller workflow is not installed on approved main')
        matches = all(p in approved and approved[p].oid == hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
                      for p,b in tooling_files().items())
        if not matches: path['missing'].append('installed controller tooling differs from approved main')
        result['policy_digest']=hashlib.sha256(b'\0'.join(data[p] for p in paths)).hexdigest()
        # Server rules and repository settings need no administrative credential; bypass actors do.
        protection=server(client,project.repository,settings)
        found=merge_setting(client.call(f'repos/{project.repository}'),project.repository,protection)
        for key in ('verified','findings','missing'): protection[key]+=found[key]
        reader_view=protection.pop('reader_view',None)
        if applying or verify_executor:
            path['missing'] += self.executor(protection,settings,current,result)
        else:
            result['executor']={'context':'local','requires_job_token':list(EXECUTOR_CHECKS),
                                'stand_in':{'reader_current_user_can_bypass':reader_view,
                                            'note':'the token running this diagnostic is not the executor; '
                                                   'this view is informational and counts for nothing'}}
            path['missing'].append('executor not verified: run `merge-doctor --executor` in the approved '
                                   'workflow, where the job token is available')
        if applying:
            # Decision 3: an unacknowledged halt (controller_halt) stops every applying run.
            halt=result['halt']=controller_halt.read(client,project.repository,policy.authorized_reviewers)
            if halt['halted']: path['missing'].append(controller_halt.reason(halt['halted']))
        result['protection'],result['automatic_path']=protection,path
        result['reasons']=reasons=path['missing']+protection['missing']
        result['ready']=not reasons
        result['evidence_digest']=hashlib.sha256(json.dumps(client.reads,sort_keys=True).encode()).hexdigest()
        client.revalidate()
        return result

    def executor(self, protection, settings, current, result):
        """Verify this run and its job token; any gap is a blocker, and nothing is assumed."""
        repository, rid = self.project.repository, os.environ.get('GITHUB_RUN_ID','')
        run = self.reader.call(f'repos/{repository}/actions/runs/{rid}') if re.fullmatch(r'[1-9][0-9]*',rid) else None
        denied = executor(run,settings,current,repository,os.environ)
        view, token = None, self.writer.installation()
        if not token['installation']:
            # Its view would not describe the executor; a user-token prefix is never sent at all.
            shape = token['shape']
            denied.append(f"the merge credential is not this repository's installation token: {token['reason']} "
                          f"(non-secret shape: prefix {shape['prefix']!r}, length {shape['length']}, "
                          f"characters {', '.join(shape['classes']) or 'none'})")
        elif protection['source'] == 'ruleset' and protection['ruleset_id'] is not None:
            try: view = self.writer.ruleset(protection['ruleset_id'])
            except RecordError: view = None
            denied += executor_bypass(view,protection['ruleset_id'])
        else:
            denied.append('the job-token bypass check needs the single-ruleset profile')
        run = run if isinstance(run,dict) else {}
        result['executor'] = {'context':'github_actions','checks':list(EXECUTOR_CHECKS),'missing':denied,
                              'run':{k:run.get(k) for k in ('id','run_attempt','workflow_id','path','head_sha','event')},
                              'token':token,
                              'token_view':(view.get('current_user_can_bypass','omitted') if isinstance(view,dict)
                                            else 'unreadable' if token['installation'] else 'not read')}
        result['executor_verified'] = not denied
        return denied

    def refresh(self):
        if self.reader is None: raise RecordError('no activation snapshot')
        self.reader.revalidate()
        # The job token's ruleset view is read again; issue content or operator config never supplies it.
        self.writer.refresh()
