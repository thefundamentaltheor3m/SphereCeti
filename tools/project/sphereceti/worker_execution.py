# SPDX-License-Identifier: Apache-2.0
"""One policy-gated review round through the existing SphereCeti review engine."""
from __future__ import annotations

import argparse
import signal
from contextlib import contextmanager
from pathlib import Path
from urllib.parse import quote

from . import local_review
from .review_records import (RecordError, assess_records, collect_records, contests, identity)
from .worker import WorkerError, require, targets
from .worker_cli import plan, survey
from .worker_leases import Lease


class NothingToDo(WorkerError):
    pass


class ReviewGuard:
    def __init__(self, project, prefs, candidate, worker):
        self.project, self.prefs, self.candidate, self.worker = project, prefs, candidate, worker
        self.lease = None
        self.report = None
        self.policy = None
        self.api = None
        self.pending = None
        self.receipt = {}

    def current(self):
        api, report, project = self.api, self.report, self.project
        pr = api.call(f'repos/{project.repository}/pulls/{report["pr"]}')
        require(isinstance(pr, dict) and all(isinstance(pr.get(k), dict) for k in ('head', 'base', 'user')) and
                isinstance(pr['base'].get('repo'), dict) and isinstance(pr.get('title'), str) and
                (pr.get('body') is None or isinstance(pr.get('body'), str)) and type(pr.get('number')) is int and pr['number'] == report['pr'] and
                pr.get('state') == 'open' and pr.get('draft') is False and
                pr.get('base', {}).get('repo', {}).get('full_name') == project.repository,
                'PR closed, draft or destination changed; stop work')
        require(pr['head']['sha'] == report['head'] and pr['base']['sha'] == report['base'],
                'PR head or base changed; stop work')
        main = api.call(f'repos/{project.repository}/commits/{quote(project.default_branch, safe="")}')
        require(isinstance(main, dict) and main.get('sha') == report['tooling'],
                'approved tooling/policy changed; stop work')
        require(type(pr.get('user', {}).get('id')) is int and pr['user']['id'] > 0,
                'PR author identity is unavailable')
        # Bind mutable title/body as well as commits: this is part of shared review context.
        from .review_records import sha
        require(sha(pr['title'] + '\n\n' + (pr['body'] or '')) == report['description_digest'],
                'PR description changed; stop work')
        return pr

    def assess(self, pr):
        comments = self.api.comments(self.project.repository, self.report['pr'])
        # comments() in the older adapter accepts zero pages. Worker coordination does not.
        require(isinstance(comments, list), 'unknown review records')
        outcome = assess_records(comments, self.report, self.policy,
            lambda rev: self.api.approved_revision(self.project.repository, rev, self.report['tooling']),
            pr['user']['id'])
        pending = contests(comments, collect_records(comments, self.report, self.policy),
                           self.report, self.policy, pr['user']['id'])
        return outcome, pending

    def check(self):
        self.current()
        self.lease.check()

    @contextmanager
    def __call__(self, args, report, policy, api):
        self.report, self.policy, self.api = report, policy, api
        require(policy is not None and policy.review_generation and policy.posting,
                'worker review generation and coordination posting are disabled by approved policy')
        require(report['tooling_approved'] and report['installed_tooling_matches_T'] and
                report['source_mode'] == 'github', 'worker execution requires installed tooling equal to approved main')
        require(report['repository'] == self.project.repository and report['pr'] == self.candidate['pr'] and
                all(report[k] == self.candidate[k] for k in ('head', 'base')), 'planned evidence changed; survey again')
        require(not report['config_differences'], 'configuration changes require the human review route')
        # A missing mathematical roadmap does not prevent infrastructure reviews; the shared
        # engine keeps those records advisory. It still cannot authorize mathematical work.
        local_review.execution_settings(args, self.prefs)  # Provider outage/invalid budget precedes every write.
        user = api.call('user')
        owner = identity({'user': user}) if isinstance(user, dict) else None
        require(owner is not None and owner.startswith('user:') and owner in policy.authorized_reviewers,
                'worker requires an approved GitHub user identity')
        pr = self.current()
        outcome, pending = self.assess(pr)
        if outcome['review_safe']:
            raise NothingToDo('current authorized reviews already approve this evidence')
        if outcome['selected_comments'] and not pending:
            # A completed negative decision needs author work; malformed/stale decisions need
            # explicit human inspection. The worker never loops over the same negative result.
            raise NothingToDo('existing review decision requires author/human attention')
        self.pending = pending
        selected_comments = outcome["selected_comments"]
        if pending:
            path = Path(report['output']) / 'worker-contests.json'
            local_review.write_json(path, {r: [c for c in pending if c['rubric'] == r] for r in local_review.RUBRICS})
            args.replies_json, args.mode = path, 'manual'
        self.lease = Lease(api, report, policy.authorized_reviewers, owner, self.worker)
        acquired = False
        try:
            acquired = self.lease.acquire()
            if not acquired:
                raise NothingToDo('another worker holds this review lease')
            self.receipt = {'owner': owner, 'worker': self.worker, 'claim': self.lease.claim,
                            'lease_comment': self.lease.last['comment_id']}
            self.check()
            outcome, current_pending = self.assess(self.current())
            if (outcome['review_safe'] or current_pending != pending or
                    outcome['selected_comments'] != selected_comments):
                raise NothingToDo('review/contest evidence changed while acquiring the lease')
            yield self.check
            self.check()
        finally:
            if self.lease.last is not None and self.lease.last['kind'] != 'release':
                try:
                    self.lease.release()
                    self.receipt['release'] = 'confirmed'
                except (WorkerError, RecordError):
                    self.receipt['release'] = 'unconfirmed; expires automatically'


def review_arguments(args, number):
    parser = argparse.ArgumentParser()
    local_review.add_parser(parser.add_subparsers(dest='command'))
    review = parser.parse_args(['review', str(number)])
    for key in ('source_repo', 'dependencies_dir', 'provider', 'auth', 'budget_usd', 'max_call_cost'):
        setattr(review, key, getattr(args, key))
    review.post = args.post_review
    return review


def run_round(args, project, policy, prefs, *, assessed=frozenset()):
    # SIGINT already raises KeyboardInterrupt. Give SIGTERM the same owned-process
    # cleanup path; restore the caller's handler when this single CLI round ends.
    def interrupted(signum, frame):
        raise KeyboardInterrupt("worker stopped")
    prior = signal.signal(signal.SIGTERM, interrupted)
    try:
        return _run_round(args, project, policy, prefs, assessed=assessed)
    finally:
        signal.signal(signal.SIGTERM, prior)


def _run_round(args, project, policy, prefs, *, assessed=frozenset()):
    require(not (args.post_review or args.publish_state) or args.execute,
            '--post-review and --publish-state require --execute')
    requested = targets(args.pr)
    if args.execute and not (policy.review_generation and policy.posting):
        return {'schema': 'sphereceti.worker-round/v1', 'state': 'disabled', 'executed': False,
                'reason': 'installed policy disables worker review generation or coordination posting'}
    observed = survey(project, requested)
    planned = plan(observed, project, requested=requested)
    if not args.execute:
        return {'schema': 'sphereceti.worker-round/v1', 'state': 'planned', 'executed': False, 'plan': planned}
    # Filtering follows complete survey validation. It only narrows review work and never
    # hides maintenance, incomplete observations or the caller's strict target constraints.
    candidates = [item for item in planned['candidates'] if not (
        item['stage'] == 'review-assessment' and (item['pr'], item['head'], item['base']) in assessed)]
    selected = candidates[0] if candidates else None
    planned = {**planned, 'selected': selected, 'candidates': candidates}
    if selected is None or selected['stage'] != 'review-assessment':
        return {'schema': 'sphereceti.worker-round/v1', 'state': 'unavailable', 'executed': False,
                'reason': 'only the shared-review execution adapter is implemented; no fallback', 'plan': planned}
    guard = ReviewGuard(project, prefs, selected, args.worker_id)
    review = review_arguments(args, selected['pr'])
    try:
        result = local_review.run_review(review, project, prefs, guard=guard)
    except NothingToDo as error:
        return {'schema': 'sphereceti.worker-round/v1', 'state': 'idle', 'executed': False,
                'reason': str(error), 'pr': selected['pr'], 'head': selected['head'],
                'base': selected['base'], 'coordination': guard.receipt}
    except (WorkerError, RecordError, local_review.ReviewError, KeyboardInterrupt) as error:
        if guard.report is not None:
            local_review.write_json(Path(guard.report['output']) / 'worker-result.json', {
                'schema': 'sphereceti.worker-round/v1', 'state': 'interrupted', 'executed': None,
                'repository': project.repository, 'pr': selected['pr'],
                'reason': str(error), 'coordination': guard.receipt})
        raise
    receipt = {'schema': 'sphereceti.worker-round/v1', 'state': result['completion'], 'executed': True,
               'repository': project.repository, 'pr': selected['pr'], 'head': result['head'],
               'base': result['base'], 'tooling': result['tooling'], 'output': result['output'],
               'coordination': guard.receipt, 'publication': result.get('publication')}
    local_review.write_json(Path(result['output']) / 'worker-result.json', receipt)
    if args.publish_state:
        from .worker_state import publish_state
        # State publication is a separate, explicit action; a failed sync cannot erase the
        # local run or turn an analytics receipt into an accepted review.
        try:
            receipt['state_publication'] = publish_state(guard.api, project, guard.policy, receipt, guard.current)
        except (WorkerError, RecordError) as error:
            receipt['state_publication'] = {'state': 'unconfirmed', 'reason': str(error)}
        local_review.write_json(Path(result['output']) / 'worker-result.json', receipt)
    return receipt
