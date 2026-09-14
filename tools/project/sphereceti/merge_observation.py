"""Shared observation decision; no merge, enqueue, post, provider, or workflow dispatch.

Adapted from TauCetiReview@afb424eda89e8ac96d9eb69f6a88972055a4cd1b
runner/merge_from_scoreboard.py (Apache-2.0, TauCetiReview contributors).
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
from types import SimpleNamespace
from urllib.parse import quote

from .config import parse_policy, parse_project
from .gate import blob, evaluate, tree
from .local_review import object_source, prepare
from .merge_checks import assess_checks, latest_statuses, parse_checks, run_reference
from .review_post import GitHub
from .review_records import RecordError, assess_records


class Reader(GitHub):
    """Only fixed-repository GETs. Retain every response for an end-of-observation refresh."""
    def __init__(self, repository):
        self.repository = repository
        self.reads = []

    def call(self, endpoint, *, payload=None, paginate=False):
        if payload is not None or not endpoint.startswith(f'repos/{self.repository}/'):
            raise RecordError('merge observation permits only project API reads')
        try:
            value = super().call(endpoint, paginate=paginate)
        except RecordError as error:
            raise RecordError('GitHub read failed; observation is incomplete') from error
        self.reads.append((endpoint, paginate, deepcopy(value)))
        return value

    def revalidate(self):
        for endpoint, paginate, value in self.reads:
            try:
                fresh = super().call(endpoint, paginate=paginate)
            except RecordError as error:
                raise RecordError('GitHub refresh failed; observation is incomplete') from error
            if fresh != value:
                raise RecordError('GitHub evidence changed during observation; run it again')

    def statuses(self, head):
        pages = self.call(f'repos/{self.repository}/commits/{head}/statuses?per_page=100', paginate=True)
        if not isinstance(pages, list) or not pages or any(not isinstance(p, list) for p in pages):
            raise RecordError('incomplete status pages')
        result = [s for p in pages for s in p]
        latest_statuses(result)
        return result

    def jobs(self, rid, attempt):
        pages = self.call(f'repos/{self.repository}/actions/runs/{rid}/attempts/{attempt}/jobs?per_page=100', paginate=True)
        if not isinstance(pages, list) or not pages or any(not isinstance(p, dict) or
                not isinstance(p.get('jobs'), list) or type(p.get('total_count')) is not int for p in pages):
            raise RecordError('incomplete job pages')
        jobs = [j for p in pages for j in p['jobs']]
        if (any(p['total_count'] != len(jobs) for p in pages) or
                any(not isinstance(j, dict) or type(j.get('id')) is not int for j in jobs) or
                len({j['id'] for j in jobs}) != len(jobs)):
            raise RecordError('truncated or duplicate job inventory')
        return jobs


def decide(context, scope, review, checks, pr, policy, *, current_main):
    """One deterministic conjunction for trusted callers; inputs are not signed receipts.

    Eligibility describes this observation only. A future controller must collect fresh
    evidence and verify server protections; this function cannot authorize an action.
    """
    reasons = []
    human = scope.get('scope') != 'mathematical' or not policy.mathematical_paths
    if human: reasons.append('protected or unapproved paths require human review')
    if scope.get('config_attested') is not True: reasons.append('candidate configuration is not approved')
    for key in ('repository', 'head', 'base', 'diff_base', 'dependency_digest', 'tooling'):
        if scope.get(key) != context.get(key): reasons.append(f'scope has a mismatched {key}')
    if review.get('review_safe') is not True: reasons += review.get('reasons') or ['authorized review is not safe']
    for key in ('repository', 'pr', 'head'):
        if review.get(key) != context.get(key): reasons.append(f'review has a mismatched {key}')
    if checks.get('passed') is not True: reasons += checks.get('reasons') or ['trusted build/scope checks did not pass']
    for key in ('repository','head','base','tooling'):
        if checks.get(key) != context.get(key): reasons.append(f'checks have a mismatched {key}')
    if (context.get('tooling_approved') is not True or context.get('installed_tooling_matches_T') is not True or
            context.get('missing_context') or context.get('config_differences')):
        reasons.append('current approved review/tooling evidence is incomplete')
    if pr['state'] != 'open' or pr['merged'] is not False: reasons.append('PR is not open and unmerged')
    if pr['draft'] is not False: reasons.append('draft PR requires human action')
    if pr.get('auto_merge') is not None: reasons.append('existing auto-merge remains human-managed')
    if pr['base']['ref'] != 'main' or context['base'] != current_main:
        reasons.append('PR does not target the current approved main')
    if context['tooling'] != current_main: reasons.append('tooling is not current approved main')
    if context['diff_base'] != context['base']: reasons.append('candidate must be updated to the integration base')
    if pr['mergeable'] is not True or pr['mergeable_state'] != 'clean':
        reasons.append('GitHub mergeability is blocked or indeterminate')
    if (pr['number'] != context['pr'] or pr['head']['sha'] != context['head'] or
            pr['base']['sha'] != context['base'] or pr['base']['repo']['full_name'] != context['repository']):
        reasons.append('PR identity or revisions differ from the observed evidence')
    return {'schema_version':1, 'mode':'observation', 'repository':context['repository'], 'pr':context['pr'],
            'head':context['head'], 'base':context['base'], 'tooling':context['tooling'],
            'eligibility':'human_review' if human else 'blocked' if reasons else 'eligible',
            'reasons':list(dict.fromkeys(reasons)), 'review_safe':review.get('review_safe') is True,
            'checks_passed':checks.get('passed') is True, 'merge_eligible':False, 'merge_allowed':False,
            'automation_requested':policy.merging, 'activation_verified':False,
            'note':'Point-in-time observation, not merge authorization; controller and server protections are separate.'}


def pull(client, project, number):
    pr = client.call(f'repos/{project.repository}/pulls/{number}')
    # Missing/unknown fields fail, including GitHub's explicit null mergeability state.
    for key in ('number','state','merged','draft','mergeable','mergeable_state','head','base','user','title','body'):
        if key not in pr: raise RecordError('incomplete PR response')
    if (type(pr['number']) is not int or pr['number'] != number or
            pr['base']['repo']['full_name'] != project.repository or type(pr['user']['id']) is not int):
        raise RecordError('PR identity differs from the requested repository')
    return pr


def observe(args, project, *, client=None):
    if args.pr <= 0: raise RecordError('PR number must be positive')
    client = client or Reader(project.repository)
    pr = pull(client, project, args.pr)
    current = client.call(f'repos/{project.repository}/commits/{quote(project.default_branch, safe="")}')['sha']
    refs = {'tooling':current, 'head':pr['head']['sha'], 'base':pr['base']['sha'],
            'tooling_approved':True, 'source_mode':'github', 'description':pr['title']+'\n\n'+(pr['body'] or '')}
    cache = args.cache_dir.expanduser().absolute()
    cache.mkdir(parents=True, exist_ok=True)
    if shutil.disk_usage(cache).free < 2 * 1024**3: raise RecordError('observation needs 2 GiB free reserve')
    repo = object_source(args.source_repo, cache / 'SphereCeti.git', f'https://github.com/{project.repository}',
                         [refs[k] for k in ('tooling','head','base')], False)
    approved = tree(repo, current)
    required = ('sphereceti.toml','policy/automation.toml','policy/merge-checks.toml')
    missing = [p for p in required if p not in approved]
    if missing:
        client.revalidate()
        return {'schema_version':1, 'mode':'observation', 'repository':project.repository, 'pr':args.pr,
                'head':refs['head'], 'base':refs['base'], 'tooling':current,
                'eligibility':'human_review', 'reasons':['approved main lacks '+p for p in missing],
                'merge_eligible':False, 'merge_allowed':False, 'activation_verified':False}
    selected = parse_project(blob(repo, approved['sphereceti.toml']).decode())
    if selected.repository != project.repository or selected.implementation_repository != project.implementation_repository:
        raise RecordError('approved project identity differs from installed project')
    policy = parse_policy(blob(repo, approved['policy/automation.toml']).decode())
    settings = parse_checks(blob(repo, approved['policy/merge-checks.toml']).decode())
    scope = evaluate(repo, current, refs['base'], refs['head'])
    # Protected and scaffold PRs need no dependency download or review engine workspace.
    context = {**scope, 'pr':args.pr, 'tooling_approved':True, 'installed_tooling_matches_T':False,
               'missing_context':['review evidence not prepared for human-only scope']}
    review = {'review_safe':False, 'reasons':['review assessment not needed for human-only scope'],
              'repository':project.repository,'pr':args.pr,'head':refs['head']}
    if scope['scope'] == 'mathematical':
        with tempfile.TemporaryDirectory(prefix='merge-evidence-', dir=cache) as scratch:
            root = Path(scratch); (root / 'workspace').mkdir()
            prepared = SimpleNamespace(pr=args.pr, source_repo=repo, dependencies_dir=args.dependencies_dir,
                                       local_sources=False)
            context = prepare(prepared, selected, refs, cache, root / 'workspace', root / 'engine')
        comments = client.comments(project.repository, args.pr)
        review = assess_records(comments, context, policy,
                                lambda rev:client.approved_revision(project.repository, rev, current), pr['user']['id'])
    statuses = client.statuses(refs['head'])
    runs = {run_reference(s.get('target_url'), project.repository) for s in latest_statuses(statuses).values()}
    run, jobs = None, None
    if len(runs) == 1 and None not in runs:
        rid, attempt = next(iter(runs))
        run = client.call(f'repos/{project.repository}/actions/runs/{rid}')
        jobs = client.jobs(rid, attempt)
    checks = assess_checks(statuses, run, jobs, context, settings)
    result = decide(context, scope, review, checks, pr, policy, current_main=current)
    result.update(scope=scope, review=review, checks=checks,
                  check_policy_digest=hashlib.sha256(blob(repo, approved['policy/merge-checks.toml'])).hexdigest())
    client.revalidate()
    result['evidence_digest'] = hashlib.sha256(json.dumps(result,sort_keys=True).encode()).hexdigest()
    return result


def add_parser(commands):
    p = commands.add_parser('merge-observe', help='read-only shared merge eligibility observation')
    p.add_argument('pr', type=int)
    p.add_argument('--json', action='store_true')
    p.add_argument('--source-repo', type=Path, help='fully materialized local Git objects; authority still comes from remote main')
    p.add_argument('--dependencies-dir', type=Path, help='optional existing pinned dependency Git stores')
    p.add_argument('--cache-dir', type=Path, default=Path('~/.cache/sphereceti/merge-observation'), help='source-only evidence cache')
    p.add_argument('--operator-config', type=Path, help='preferences only; cannot change eligibility policy')
