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

from .config import fields, parse_policy, parse_project, resource_text, version
from .gate import blob, tree
from .local_review import object_source
from .merge_checks import CONTEXTS, parse_checks
from .merge_observation import Reader
from .review_records import RecordError
from .review_resources import tooling_files

WORKFLOW = '.github/workflows/merge-controller.yml'


def parse_controller(text):
    value = tomllib.loads(text)
    fields(value, {'schema_version','workflow_id','bot_user_id','checks_app_id','merge_method'}, 'merge controller')
    version(value, 'merge controller')
    if any(type(value[k]) is not int or value[k] < 0 for k in ('workflow_id','bot_user_id','checks_app_id')):
        raise RecordError('controller IDs must be nonnegative integers')
    if value['merge_method'] != 'squash': raise RecordError('only the reviewed squash transport is supported')
    return value


def protections(protection, repository, settings, account, permission):
    """Conservative classic-protection profile; server rules must apply to the merge identity."""
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
    if (not isinstance(account,dict) or type(account.get('id')) is not int or
            account['id'] != settings['bot_user_id'] or settings['bot_user_id'] <= 0 or
            account.get('type') != 'User' or not isinstance(account.get('login'),str) or account.get('site_admin') is not False):
        reasons.append('merge token is not the configured dedicated machine-user identity')
    if (not isinstance(permission,dict) or permission.get('permission') != 'write' or permission.get('role_name') != 'write' or
            (permission.get('user') or {}).get('id') != settings['bot_user_id']):
        reasons.append('merge identity must have the standard write role, without admin/custom-role bypass')
    return reasons


def executor(run, settings, revision, repository, environ):
    """Runtime consistency checks, not an attestation for a caller already holding the merge token."""
    reasons = []
    expected = {'GITHUB_ACTIONS':'true','GITHUB_REPOSITORY':repository,'GITHUB_REF':'refs/heads/main',
                'GITHUB_SHA':revision,'GITHUB_WORKFLOW_REF':f'{repository}/{WORKFLOW}@refs/heads/main'}
    if any(environ.get(k) != v for k,v in expected.items()): reasons.append('not the approved serialized workflow environment')
    rid, attempt = environ.get('GITHUB_RUN_ID',''), environ.get('GITHUB_RUN_ATTEMPT','')
    if not re.fullmatch(r'[1-9][0-9]*',rid) or not re.fullmatch(r'[1-9][0-9]*',attempt):
        return reasons + ['missing exact workflow run/attempt']
    if not isinstance(run,dict): return reasons + ['controller run is unavailable']
    expected_run = {'id':int(rid),'run_attempt':int(attempt),'workflow_id':settings['workflow_id'],
                    'head_sha':revision,'head_branch':'main','path':WORKFLOW,'status':'in_progress'}
    if any(run.get(k) != v or (type(v) is int and type(run.get(k)) is not int) for k,v in expected_run.items()):
        reasons.append('controller run does not match the approved executor')
    if run.get('event') not in ('schedule','workflow_dispatch') or (run.get('repository') or {}).get('full_name') != repository:
        reasons.append('controller event/repository is not approved')
    return reasons


class Activation:
    def __init__(self, args, project, writer):
        self.args, self.project, self.writer = args, project, writer
        self.reader = None

    def inspect(self, *, applying=False):
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
        policy = parse_policy(data['policy/automation.toml'].decode())
        checks = parse_checks(data['policy/merge-checks.toml'].decode())
        settings = parse_controller(data['policy/merge-controller.toml'].decode())
        reasons = result['reasons']; result['merging_requested']=policy.merging
        if not policy.merging: reasons.append('global merging switch is off')
        if not policy.mathematical_paths: reasons.append('no approved mathematical change class')
        if not policy.authorized_reviewers: reasons.append('authorized reviewers are not configured')
        if not selected.roadmap_approved: reasons.append('approved mathematical roadmap is missing')
        if not checks['workflow_id'] or not checks['status_creator_ids']: reasons.append('trusted check producers are not configured')
        if any(not settings[k] for k in ('workflow_id','bot_user_id','checks_app_id')):
            reasons.append('controller workflow, merge identity, or required-check App is not configured')
        template = resource_text('merge-controller.yml').encode()
        if WORKFLOW not in approved or blob(repo,approved[WORKFLOW]) != template:
            reasons.append('exact serialized controller workflow is not installed on approved main')
        matches = all(p in approved and approved[p].oid == hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
                      for p,b in tooling_files().items())
        if not matches: reasons.append('installed controller tooling differs from approved main')
        result['policy_digest']=hashlib.sha256(b'\0'.join(data[p] for p in paths)).hexdigest()
        # Unconfigured setup can be diagnosed without requesting administrative metadata or credentials.
        if all(settings[k] for k in ('workflow_id','bot_user_id','checks_app_id')):
            protection=client.call(f'repos/{project.repository}/branches/main/protection')
            account=self.writer.identity()
            permission=client.call(f'repos/{project.repository}/collaborators/{quote(account["login"],safe="")}/permission')
            reasons += protections(protection,project.repository,settings,account,permission)
            repository=client.call(f'repos/{project.repository}')
            if repository.get('full_name') != project.repository or repository.get('allow_squash_merge') is not True:
                reasons.append('repository identity or squash-merge setting is incompatible')
            # Queue-specific rules need a separate adapter; never bypass or drain a human queue.
            pages=client.call(f'repos/{project.repository}/rules/branches/main?per_page=100',paginate=True)
            if not isinstance(pages,list) or not pages or any(not isinstance(p,list) for p in pages):
                raise RecordError('incomplete branch-rules inventory')
            if any(pages): reasons.append('active rulesets require a separately reviewed controller profile')
            result['bot_user_id']=account['id']
            if applying:
                rid=os.environ.get('GITHUB_RUN_ID','')
                run=client.call(f'repos/{project.repository}/actions/runs/{rid}') if re.fullmatch(r'[1-9][0-9]*',rid) else None
                denied=executor(run,settings,current,project.repository,os.environ)
                reasons += denied; result['executor_verified']=not denied
        elif applying:
            reasons.append('serialized executor cannot be verified without configured IDs')
        result['ready']=not reasons
        result['evidence_digest']=hashlib.sha256(json.dumps(client.reads,sort_keys=True).encode()).hexdigest()
        client.revalidate()
        return result

    def refresh(self):
        if self.reader is None: raise RecordError('no activation snapshot')
        self.reader.revalidate()
        # The writer identity is not supplied by issue content or operator configuration.
        self.writer.refresh_identity()
