"""Disabled-by-policy serialized controller: the auto-approval decision plus a formal approval.

The executor is the approved workflow's own job token (option A): no bot or machine-user account.

Adapted from TauCetiReview@afb424eda89e8ac96d9eb69f6a88972055a4cd1b
.github/workflows/{merge-only,merge-sweep}.yml; Apache-2.0, TauCetiReview contributors.
"""
from contextlib import contextmanager
from copy import copy
import fcntl
import json
import os
from pathlib import Path
import re
import stat
import subprocess

from .auto_approval import auto_approval
from .merge_activation import Activation, pages
from .merge_checks import TOOLING_ATTESTATION
from .merge_observation import Reader, pull
from .review_records import RecordError
from .worker_checks import SCOPE_FAILURE, STALE_TOOLING


# Personal (classic and fine-grained), OAuth, user-to-server and refresh tokens. They are never
# installation tokens, so they are refused before any request is made with them.
USER_TOKEN_PREFIXES = ('ghp_', 'github_pat_', 'gho_', 'ghu_', 'ghr_')
INSTALLATION_PROBE = 'installation/repositories?per_page=100'


def token_shape(token):
    """Non-secret diagnostics: the first 4 characters, the length and the character classes present."""
    if not isinstance(token, str): return {'prefix': None, 'length': 0, 'classes': []}
    classes = {'lowercase': str.islower, 'uppercase': str.isupper, 'digit': str.isdigit,
               'underscore': lambda c: c == '_', 'hyphen': lambda c: c == '-', 'period': lambda c: c == '.',
               'whitespace': str.isspace, 'non-ascii': lambda c: not c.isascii()}
    present = {name for c in token for name, test in classes.items() if test(c)}
    if any(c.isascii() and not (c.isalnum() or c.isspace() or c in '_-.') for c in token): present.add('other-ascii')
    return {'prefix': token[:4], 'length': len(token), 'classes': sorted(present)}


class Writer:
    """The job token, excluded from inherited reader/Git environments; one narrow PUT.

    It reads the installation probe and ruleset bypass status and may dispatch the approved
    trusted workflow on main for one PR and head. An installation token has no user.
    """
    def __init__(self, repository, token):
        self.repository, self._token, self.view, self.identity = repository, token, None, None

    def installation(self):
        """Identify the token by behaviour, never by format alone; cached for this run.

        GitHub does not document a stable character set or length for installation tokens, so the
        only static rule refuses known non-installation prefixes and malformed values, without any
        request. Any other token makes one GET to api.github.com: `installation/repositories`. Only an
        installation token can call it. It must list exactly this repository, as the job token does.
        """
        if self.identity is not None: return self.identity
        token, reason, listed = self._token, None, None
        if not isinstance(token, str) or not token:
            reason = 'no token reached the controller (SPHERECETI_MERGE_TOKEN is unset or empty)'
        elif token.startswith(USER_TOKEN_PREFIXES):
            reason = 'it has a personal, OAuth or user-token prefix; no request was made with it'
        elif len(token) > 4096 or not token.isascii() or any(c.isspace() or not c.isprintable() for c in token):
            reason = 'it is malformed (whitespace, control or non-ASCII characters, or over 4096 characters)'
        else:
            try: value = self.call(INSTALLATION_PROBE)
            except RecordError: value = None
            repos = value.get('repositories') if isinstance(value, dict) else None
            if not isinstance(repos, list):
                reason = 'GitHub refused GET /installation/repositories for it, so it is not an installation token'
            else:
                listed = [r.get('full_name') if isinstance(r, dict) else None for r in repos]
                if value.get('total_count') != 1 or listed != [self.repository]:
                    reason = (f"its installation lists {value.get('total_count')!r} repositories, "
                              f'not exactly {self.repository}')
        self.identity = {'installation': reason is None, 'reason': reason, 'shape': token_shape(token),
                         'repositories': len(listed) if listed is not None else None}
        return self.identity

    def run(self, command, payload, env):
        return subprocess.run(command,input=json.dumps(payload) if payload is not None else None,
                              text=True,capture_output=True,timeout=45,env=env)

    def call(self, endpoint, payload=None):
        if not self._token: raise RecordError('the job token is unavailable to the controller')
        merge=re.fullmatch(re.escape(f'repos/{self.repository}/pulls/')+r'[1-9][0-9]*/merge',endpoint)
        ruleset=re.fullmatch(re.escape(f'repos/{self.repository}/rulesets/')+r'[1-9][0-9]*',endpoint)
        dispatch=re.fullmatch(re.escape(f'repos/{self.repository}/actions/workflows/')+r'[1-9][0-9]*/dispatches',endpoint)
        read=ruleset or endpoint==INSTALLATION_PROBE
        if not ((merge or dispatch) and payload is not None) and not (read and payload is None):
            raise RecordError('unsupported merge-token operation')
        if merge and (set(payload)!={'sha','merge_method'} or not isinstance(payload['sha'],str) or
                not re.fullmatch(r'[0-9a-f]{40}',payload['sha']) or payload['merge_method']!='squash'):
            raise RecordError('invalid expected-head merge request')
        if dispatch and (set(payload)!={'ref','inputs'} or payload['ref']!='main' or not isinstance(payload['inputs'],dict) or
                set(payload['inputs'])!={'pr','head'} or not re.fullmatch(r'[1-9][0-9]{0,8}',str(payload['inputs']['pr'])) or
                not isinstance(payload['inputs']['head'],str) or not re.fullmatch(r'[0-9a-f]{40}',payload['inputs']['head'])):
            raise RecordError('invalid trusted-refresh dispatch')
        command=['gh','api','--hostname','github.com',endpoint]
        if payload is not None: command += ['--method','POST' if dispatch else 'PUT','--input','-']
        env={'PATH':os.environ.get('PATH',os.defpath),'GH_TOKEN':self._token,'GH_HOST':'github.com',
             'GH_PROMPT_DISABLED':'1'}
        try:
            response=self.run(command,payload,env)
            if response.returncode: raise RecordError('merge-token request failed; result is unconfirmed')
            if dispatch and not response.stdout.strip(): return {}  # GitHub answers a dispatch with 204.
            return json.loads(response.stdout)
        except (OSError,subprocess.SubprocessError,ValueError) as error:
            raise RecordError('merge-token request failed; result is unconfirmed') from error

    def ruleset(self, rid):
        if type(rid) is not int or rid<=0: raise RecordError('invalid ruleset ID')
        self.view=(rid,self.call(f'repos/{self.repository}/rulesets/{rid}'))
        return self.view[1]

    def refresh(self):
        if (self.identity or {}).get('installation'):
            repos = self.call(INSTALLATION_PROBE).get('repositories')
            if not isinstance(repos, list) or [r.get('full_name') for r in repos] != [self.repository]:
                raise RecordError('job-token installation changed')
        if self.view is not None and self.call(f'repos/{self.repository}/rulesets/{self.view[0]}') != self.view[1]:
            raise RecordError('job-token ruleset view changed')

    def merge(self, number, head):
        if type(number) is not int or number<=0: raise RecordError('invalid PR number')
        return self.call(f'repos/{self.repository}/pulls/{number}/merge',{'sha':head,'merge_method':'squash'})

    def dispatch_refresh(self, workflow_id, number, head):
        """One workflow_dispatch of the approved trusted workflow on main, for one PR and exact head."""
        if type(number) is not int or number<=0 or type(workflow_id) is not int or workflow_id<=0:
            raise RecordError('invalid trusted-refresh dispatch')
        return self.call(f'repos/{self.repository}/actions/workflows/{workflow_id}/dispatches',
                         {'ref':'main','inputs':{'pr':str(number),'head':head}})


@contextmanager
def local_lock(cache):
    """Avoid overlapping local preparations; cross-run serialization belongs to the exact workflow."""
    cache=cache.expanduser().absolute(); cache.mkdir(parents=True,exist_ok=True)
    if any(p.is_symlink() for p in (cache,*cache.parents)): raise RecordError('symlinked controller cache')
    fd=os.open(cache/'controller.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600)
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode): raise RecordError('controller lock must be a regular file')
        try: fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
        except BlockingIOError as error: raise RecordError('another local controller is already running') from error
        yield
    finally: os.close(fd)


MAINTAINERS = ('OWNER', 'MEMBER', 'COLLABORATOR')


def formal_approval(reviews, author, head, approvers):
    """A qualifying formal GitHub approval: an opted-in maintainer's current APPROVE on the exact head.

    `approvers` is the approved automation policy's approving_reviewers (a subset of authorized_reviewers).

    Each reviewer's latest APPROVED, CHANGES_REQUESTED or DISMISSED review is their current state, as
    on GitHub; comments do not change it. An all-green review record without this review does not
    qualify, and any outstanding change request blocks.
    """
    if not isinstance(reviews,list) or any(
            not isinstance(r,dict) or type(r.get('id')) is not int or not isinstance(r.get('user'),dict) or
            type(r['user'].get('id')) is not int or not isinstance(r.get('state'),str) for r in reviews):
        raise RecordError('invalid review inventory')
    if len({r['id'] for r in reviews}) != len(reviews): raise RecordError('duplicate review inventory')
    latest={}
    for review in sorted(reviews,key=lambda r:r['id']):
        if review['state'] in ('APPROVED','CHANGES_REQUESTED','DISMISSED'): latest[review['user']['id']]=review
    reasons,qualifying,rejected=[],[],[]
    changes=[f'user:{u}' for u,r in sorted(latest.items()) if r['state']=='CHANGES_REQUESTED']
    if changes: reasons.append('changes requested by '+', '.join(changes))
    for user,review in sorted(latest.items()):
        who=f'user:{user}'
        if review['state']!='APPROVED': continue
        if who not in approvers: rejected.append(f'{who} is not in approving_reviewers')
        elif who==author: rejected.append(f'{who} is the PR author')
        elif review.get('commit_id')!=head: rejected.append(f"{who} approved {str(review.get('commit_id'))[:12]}, not the head")
        elif review['user'].get('type')!='User' or review.get('author_association') not in MAINTAINERS:
            rejected.append(f'{who} is not a maintainer account')
        else: qualifying.append({'identity':who,'review_id':review['id'],'commit_id':head})
    if not qualifying:
        reasons.append('no qualifying approval: an opted-in maintainer (policy/automation.toml approving_reviewers) '
                       'other than the PR author must APPROVE the exact head'+(f" ({'; '.join(rejected)})" if rejected else ''))
    return {'qualifying':qualifying,'reasons':reasons}


# Failures that only a trusted run on current main resolves, when nothing else is wrong with the
# PR: older tooling, a missing or older attestation, or an older attested or associated base.
BUILD_STALE = {STALE_TOOLING, 'trusted-build does not attest its tooling commit; refresh the trusted run',
               'trusted-build attests another PR or base', 'trusted run lacks the exact PR head/base association',
               'trusted run PR association disagrees with the attested PR binding'}


def classify(decision, approval):
    """One action per candidate: merge, refresh_build, needs_review or blocked, with reasons.

    The review's base is the PR `base.sha` its record binds (GitHub's value when the review ran);
    the record also binds `diff_base`, the merge-base of that base and the head, which is the base
    of the reviewed diff. GitHub's `base.sha` is a snapshot, not live: it does not follow main
    (observed 2026-11-23, docs/infrastructure/merge-controller.md). So `commits/main` decides, and
    a review is current only when it is accepted for the current head and its base and diff base
    both equal current main.
    """
    req={r['id']:r for r in decision['requirements']}
    passed=lambda name:req[name]['status']=='pass'
    current,base,diff_base=decision['tooling'],decision['base'],decision.get('diff_base')
    # Not on the automatic route at all (paths, policy, a hypothesis): neither stale nor refreshable.
    if decision['hypothetical'] or not passed('paths') or not passed('policy'):
        return 'blocked',decision['reasons'] or ['not an automatic-merge candidate']
    review=[]
    if not passed('official_review') or not passed('independent_reviewer'):
        review.append('no accepted official review for the current head')
    # Conservative: a moved base means a stale review, even when the PR diff looks unchanged.
    # Accepting an older review because the diff is unchanged would be a separate, explicitly
    # approved policy decision; nothing here infers it.
    if base!=current:
        review.append(f'the PR base {base[:12]} that a review binds is not current main {current[:12]}')
    elif diff_base!=current:
        review.append(f'the reviewed diff base {str(diff_base)[:12]} is not current main {current[:12]}; '
                      'the PR must contain current main')
    if review:
        return 'needs_review',review
    pr_reasons=req['pull_request']['evidence'].get('reasons') or []
    checks=set(req['trusted_checks']['evidence'].get('reasons') or [])|set(req['compiled_audit']['evidence'].get('reasons') or [])
    if checks:
        stale=checks&BUILD_STALE
        if 'trusted-build attests another PR or base' in checks:
            build=(req['trusted_checks']['evidence'].get('statuses') or {}).get('trusted-build') or {}
            attested=TOOLING_ATTESTATION.fullmatch(build.get('description') or '')
            if not attested or not attested.group(2) or int(attested.group(2))!=decision['pr']:
                stale=set()  # Another PR's binding is a misbinding, never staleness.
        if not stale or not checks<=BUILD_STALE|{SCOPE_FAILURE}:
            return 'blocked',decision['reasons']
        if pr_reasons or approval['reasons']:
            return 'blocked',pr_reasons+approval['reasons']+['the trusted build is also stale']
        return 'refresh_build',sorted(checks)
    if pr_reasons or approval['reasons'] or decision['would_approve'] is not True:
        return 'blocked',decision['reasons']+approval['reasons']
    return 'merge',[]


class Backend:
    def __init__(self,args,project,writer):
        self.args,self.project,self.writer=args,project,writer
        self.activation=Activation(args,project,writer)
        self.observer=None

    def setup(self, applying, *, verify_executor=False):
        return self.activation.inspect(applying=applying,verify_executor=verify_executor)

    def state(self, number): return pull(Reader(self.project.repository),self.project,number)

    def observation(self, number):
        """The auto-approval decision under approved policy (never hypothetical) and a formal approval."""
        args=copy(self.args);args.pr=number;args.assume_proof_paths=None
        if self.activation.policy is None: raise RecordError('no activation snapshot')
        client=self.observer=Reader(self.project.repository)
        decision=auto_approval(args,self.project,client=client)
        reviews=pages(client.call(f'repos/{self.project.repository}/pulls/{number}/reviews?per_page=100',paginate=True),'review')
        approval=formal_approval(reviews,decision['author']['identity'],decision['head'],
                                 self.activation.policy.approving_reviewers)
        action,reasons=classify(decision,approval)
        return {'eligibility':'eligible' if action=='merge' else 'blocked','action':action,'head':decision['head'],
                'base':decision['base'],'diff_base':decision.get('diff_base'),'tooling':decision['tooling'],
                'reasons':reasons,'approval':approval['qualifying'],'decision_digest':decision['evidence_digest']}

    def refresh(self):
        self.observer.revalidate()
        self.activation.refresh()

    def merge(self, number, head): return self.writer.merge(number,head)

    def dispatch_refresh(self, number, head):
        return self.writer.dispatch_refresh(self.activation.checks['workflow_id'],number,head)

    def queue(self):
        client=Reader(self.project.repository)
        pages=client.call(f'repos/{self.project.repository}/pulls?state=open&base=main&per_page=100',paginate=True)
        if not isinstance(pages,list) or not pages or any(not isinstance(p,list) for p in pages):
            raise RecordError('incomplete sweep inventory')
        rows=[p for page in pages for p in page]
        if any(not isinstance(p,dict) or type(p.get('number')) is not int or p['number']<=0 for p in rows):
            raise RecordError('invalid sweep PR identity')
        numbers=[p['number'] for p in rows]
        if len(numbers)!=len(set(numbers)) or len(numbers)>1000: raise RecordError('duplicate or excessive sweep inventory')
        client.revalidate()
        return sorted(numbers)


def reconcile(backend, numbers, *, applying=False):
    """Per-PR actions; at most one merge and at most one trusted refresh per PR per run.

    Applying needs ready setup, the `merging` switch and the verified executor before any work is
    listed. A preview lists and classifies read-only even while switches are off, and only reports.
    """
    setup=backend.setup(applying)
    result={'schema_version':1,'mode':'apply' if applying else 'preview','setup':setup,'results':[],
            'merge_attempted':False,'refreshes_dispatched':[]}
    enabled=(setup.get('ready') is True and setup.get('merging_requested') is True and
             (not applying or setup.get('executor_verified') is True))
    if applying and not enabled:
        result['state']='disabled';return result
    dispatched=set()
    for number in numbers():
        pr=backend.state(number)
        if pr['merged'] is True or pr['state']=='closed':
            result['results'].append({'pr':number,'state':'already_merged' if pr['merged'] else 'closed'});continue
        if pr['draft'] is not False or pr.get('auto_merge') is not None:
            result['results'].append({'pr':number,'state':'human_managed'});continue
        first=backend.observation(number)
        action=first.get('action')
        if action=='refresh_build':
            entry={'pr':number,'action':action,'head':first['head'],'reasons':first['reasons']}
            if not applying or number in dispatched:
                entry.update(state='would_dispatch_refresh',note=f'would dispatch refresh for #{number}')
            else:
                # The refresh is a write; confirm the same evidence once more, then dispatch exactly once.
                second=backend.observation(number)
                if second!=first:
                    entry.update(state='changed',note='PR evidence changed before the refresh dispatch')
                else:
                    dispatched.add(number)
                    try:
                        backend.dispatch_refresh(number,first['head'])
                        entry.update(state='refresh_dispatched',note=f'dispatched refresh for #{number}; '
                                     'the next scheduled run re-evaluates')
                        result['refreshes_dispatched'].append(number)
                    except RecordError:
                        entry.update(state='refresh_unconfirmed',note='the dispatch was not confirmed; not retried in this run')
            result['results'].append(entry);continue
        if action!='merge':
            result['results'].append({'pr':number,'state':action,'action':action,'reasons':first['reasons']});continue
        if not applying:
            result['results'].append({'pr':number,'state':'would_merge','action':action,'head':first['head']});continue
        fresh_setup=backend.setup(True)
        second=backend.observation(number)
        if (fresh_setup != setup or fresh_setup.get('ready') is not True or
                fresh_setup.get('merging_requested') is not True or
                fresh_setup.get('executor_verified') is not True or second != first):
            result['results'].append({'pr':number,'state':'changed','reason':'policy, protection, identity or PR evidence changed'})
            result['state']='revalidation_required';return result
        backend.refresh()  # Last live read of head/base, review revocations, checks, stop switch and protections.
        result['merge_attempted']=True
        receipt=None
        try: receipt=backend.merge(number,first['head'])
        except RecordError: pass  # Never retry an ambiguous PUT; reconcile current GitHub state below.
        try: after=backend.state(number)
        except (RecordError,ValueError,KeyError,TypeError): after={}
        merged = (after.get('merged') is True and (after.get('head') or {}).get('sha')==first['head'] and
                  isinstance(after.get('merge_commit_sha'),str) and re.fullmatch(r'[0-9a-f]{40}',after['merge_commit_sha']))
        confirmed = merged and isinstance(receipt,dict) and receipt.get('merged') is True and receipt.get('sha')==after['merge_commit_sha']
        result['results'].append({'pr':number,'head':first['head'],
                                  'state':'merged' if confirmed else 'merged_observed' if merged else 'unconfirmed',
                                  'merge_commit':after.get('merge_commit_sha') if merged else None})
        result['state']='completed' if merged else 'unconfirmed'
        return result  # Base changed or outcome ambiguous: no next merge using the old snapshot.
    result['state']='completed' if enabled else 'disabled'
    if not enabled: result['note']='switches are off or setup is not ready: actions are reported only'
    return result


def render(report):
    """Text for merge-doctor / merge-control; the JSON carries the same facts."""
    setup=report.get('setup',report)
    lines=[f"setup: {'ready' if setup.get('ready') else 'not ready'}"]
    lines+=['  - '+r for r in setup.get('reasons') or []]
    if 'mode' in report:
        lines.insert(0,f"merge-control ({report['mode']}): {report.get('state')}")
        if report.get('note'): lines.append(report['note'])
    for item in report.get('results') or ([report['candidate']] if report.get('candidate') else []):
        text=f"#{item['pr']}: {item.get('state')}"
        if item.get('note'): text+=f" ({item['note']})"
        lines.append(text)
        lines+=['    - '+r for r in item.get('reasons') or []]
    return '\n'.join(lines)


def run(args,project):
    # Remove the writer credential before any reader/Git/observer subprocess is created.
    writer=Writer(project.repository,os.environ.pop('SPHERECETI_MERGE_TOKEN',None))
    backend=Backend(args,project,writer)
    with local_lock(args.cache_dir):
        if args.command=='merge-doctor':
            report=backend.setup(False,verify_executor=args.executor)
            if args.pr is not None:
                # Read-only per-PR action for diagnosis; nothing is dispatched or merged.
                if args.pr<=0: raise RecordError('PR number must be positive')
                found=backend.observation(args.pr)
                report['candidate']={'pr':args.pr,'state':found['action'],**{k:found[k] for k in ('action','head','base','reasons')}}
                if found['action']=='refresh_build': report['candidate']['note']=f'would dispatch refresh for #{args.pr}'
            return report
        if args.pr is not None and args.pr<=0: raise RecordError('PR number must be positive')
        return reconcile(backend,(lambda:[args.pr]) if args.pr is not None else backend.queue,applying=args.apply)


def add_parser(commands):
    for name in ('merge-doctor','merge-control'):
        p=commands.add_parser(name,help='diagnose activation' if name=='merge-doctor' else 'preview or run the disabled-by-policy controller')
        p.add_argument('--json',action='store_true')
        p.add_argument('--source-repo',type=Path)
        p.add_argument('--dependencies-dir',type=Path)
        p.add_argument('--cache-dir',type=Path,default=Path('~/.cache/sphereceti/merge-controller'))
        p.add_argument('--operator-config',type=Path,help='preferences only; cannot enable merging')
        if name=='merge-doctor':
            p.add_argument('--executor',action='store_true',
                           help='also verify this GitHub Actions run and its job token (the approved workflow passes it)')
            p.add_argument('--pr',type=int,help='also report the read-only action for one PR')
        if name=='merge-control':
            group=p.add_mutually_exclusive_group(required=True)
            group.add_argument('--pr',type=int)
            group.add_argument('--sweep',action='store_true')
            p.add_argument('--apply',action='store_true',help='requires approved policy, verified server setup and serialized executor')
