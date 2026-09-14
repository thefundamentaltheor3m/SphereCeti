"""Disabled-by-policy serialized controller, sharing #15's observer for all entry points.

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

from .merge_activation import Activation
from .merge_observation import Reader, observe, pull
from .review_records import RecordError


class Writer:
    """Dedicated credential, excluded from inherited reader/Git environments; one narrow PUT."""
    def __init__(self, repository, token):
        self.repository, self._token, self.account = repository, token, None

    def call(self, endpoint, payload=None):
        if not self._token: raise RecordError('dedicated merge token is unavailable')
        if endpoint != 'user' and not re.fullmatch(re.escape(f'repos/{self.repository}/pulls/')+r'[1-9][0-9]*/merge',endpoint):
            raise RecordError('unsupported merge-token operation')
        if payload is not None and (endpoint=='user' or set(payload)!={'sha','merge_method'} or
                not re.fullmatch(r'[0-9a-f]{40}',payload['sha']) or payload['merge_method']!='squash'):
            raise RecordError('invalid expected-head merge request')
        command=['gh','api','--hostname','github.com',endpoint]
        if payload is not None: command += ['--method','PUT','--input','-']
        env={'PATH':os.environ.get('PATH',os.defpath),'GH_TOKEN':self._token,'GH_HOST':'github.com',
             'GH_PROMPT_DISABLED':'1'}
        try:
            response=subprocess.run(command,input=json.dumps(payload) if payload is not None else None,
                                    text=True,capture_output=True,timeout=45,env=env)
            if response.returncode: raise RecordError('merge-token request failed; result is unconfirmed')
            return json.loads(response.stdout)
        except (OSError,subprocess.SubprocessError,ValueError) as error:
            raise RecordError('merge-token request failed; result is unconfirmed') from error

    def identity(self):
        self.account=self.call('user')
        return self.account

    def refresh_identity(self):
        if self.account is not None and self.call('user') != self.account:
            raise RecordError('merge-token identity changed')

    def merge(self, number, head):
        if type(number) is not int or number<=0: raise RecordError('invalid PR number')
        return self.call(f'repos/{self.repository}/pulls/{number}/merge',{'sha':head,'merge_method':'squash'})


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


class Backend:
    def __init__(self,args,project,writer):
        self.args,self.project,self.writer=args,project,writer
        self.activation=Activation(args,project,writer)
        self.observer=None

    def setup(self, applying): return self.activation.inspect(applying=applying)

    def state(self, number): return pull(Reader(self.project.repository),self.project,number)

    def observation(self, number):
        args=copy(self.args);args.pr=number
        self.observer=Reader(self.project.repository)
        return observe(args,self.project,client=self.observer)

    def refresh(self):
        self.observer.revalidate()
        self.activation.refresh()

    def merge(self, number, head): return self.writer.merge(number,head)

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
    """At most one merge attempt per run; restart reconciliation always comes from live GitHub."""
    setup=backend.setup(applying)
    result={'schema_version':1,'mode':'apply' if applying else 'preview','setup':setup,'results':[],
            'merge_attempted':False}
    if (setup.get('ready') is not True or setup.get('merging_requested') is not True or
            (applying and setup.get('executor_verified') is not True)):
        result['state']='disabled';return result
    for number in numbers():
        pr=backend.state(number)
        if pr['merged'] is True or pr['state']=='closed':
            result['results'].append({'pr':number,'state':'already_merged' if pr['merged'] else 'closed'});continue
        if pr['draft'] is not False or pr.get('auto_merge') is not None:
            result['results'].append({'pr':number,'state':'human_managed'});continue
        first=backend.observation(number)
        if first.get('eligibility')!='eligible':
            result['results'].append({'pr':number,'state':first['eligibility'],'reasons':first['reasons']});continue
        if not applying:
            result['results'].append({'pr':number,'state':'would_merge','head':first['head']});continue
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
    result['state']='completed';return result


def run(args,project):
    # Remove the writer credential before any reader/Git/observer subprocess is created.
    writer=Writer(project.repository,os.environ.pop('SPHERECETI_MERGE_TOKEN',None))
    backend=Backend(args,project,writer)
    with local_lock(args.cache_dir):
        if args.command=='merge-doctor': return backend.setup(False)
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
        if name=='merge-control':
            group=p.add_mutually_exclusive_group(required=True)
            group.add_argument('--pr',type=int)
            group.add_argument('--sweep',action='store_true')
            p.add_argument('--apply',action='store_true',help='requires approved policy, verified server setup and serialized executor')
