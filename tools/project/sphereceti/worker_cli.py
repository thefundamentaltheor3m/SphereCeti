# SPDX-License-Identifier: Apache-2.0
"""Read-only GitHub observations and the single-roadmap worker planning front door."""
from __future__ import annotations

from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess
import time

from .local_review import ATTEMPT_TIMEOUT
from .worker import (MAX_PRS, WorkerError, plan, require, targets, text,
                     validate_snapshot)

PR_FIELDS = "number,title,author,headRefOid,baseRefOid,updatedAt,state,isDraft,mergeable,statusCheckRollup"


def load_json(raw: str):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "duplicate JSON field")
            result[key] = value
        return result
    try:
        return json.loads(raw, object_pairs_hook=unique,
                          parse_constant=lambda _: (_ for _ in ()).throw(WorkerError("nonfinite JSON number")))
    except (ValueError, RecursionError) as error:
        raise WorkerError("invalid worker JSON") from error


def read_json(path: Path):
    with path.open(encoding="utf-8") as stream:
        raw = stream.read(2_000_001)
    require(len(raw) <= 2_000_000, "worker input exceeds 2 MB")
    return load_json(raw)


class GitHub:
    """Only fixed-host read commands; one survey gets a 60-second total budget."""

    def __init__(self):
        self.deadline = time.monotonic() + 60

    def read(self, args: list[str]):
        remaining = self.deadline - time.monotonic()
        require(remaining > 0, "GitHub survey deadline exceeded; queue is unknown")
        env = os.environ.copy()
        env["GH_HOST"] = "github.com"
        env["GH_PROMPT_DISABLED"] = "1"
        try:
            result = subprocess.run(["gh", *args], text=True, capture_output=True,
                                    timeout=min(remaining, 45), env=env, check=False)
        except (OSError, subprocess.TimeoutExpired) as error:
            raise WorkerError("GitHub survey unavailable; queue is unknown") from error
        require(result.returncode == 0, "GitHub survey failed; queue is unknown (no fallback)")
        require(len(result.stdout) <= 2_000_000, "GitHub survey response exceeds 2 MB")
        return load_json(result.stdout)


def ci_summary(checks) -> str:
    require(checks is None or isinstance(checks, list), "invalid check summary")
    if not checks:
        return "unknown"
    observed = []
    for check in checks:
        require(isinstance(check, dict), "invalid check observation")
        kind = check.get("__typename")
        if kind == "CheckRun":
            status = check.get("status")
            require(status in ("QUEUED", "IN_PROGRESS", "COMPLETED", "WAITING", "PENDING", "REQUESTED"),
                    "unknown check status")
            conclusion = check.get("conclusion")
            if status != "COMPLETED":
                observed.append("pending")
            elif conclusion in ("FAILURE", "TIMED_OUT", "CANCELLED", "ACTION_REQUIRED", "STARTUP_FAILURE", "STALE"):
                observed.append("failed")
            elif conclusion == "SUCCESS":
                observed.append("passed")
            else:
                observed.append("unknown")
        elif kind == "StatusContext":
            state = check.get("state")
            require(state in ("ERROR", "FAILURE", "PENDING", "SUCCESS", "EXPECTED"), "unknown status context")
            observed.append({"ERROR": "failed", "FAILURE": "failed", "SUCCESS": "passed"}.get(state, "pending"))
        else:
            raise WorkerError("unsupported check observation")
    # gh's summary can be capped. Never infer all-green from a full page.
    if len(checks) >= 100:
        observed.append("unknown")
    return next(state for state in ("failed", "unknown", "pending", "passed") if state in observed)


# Jobs whose workflow runs them only for pushes to main (`docs-cache.yml`: `if: github.ref ==
# 'refs/heads/main' && github.event_name != 'pull_request' && ...`), so GitHub reports them SKIPPED
# on every pull request. Only these exact workflow/job pairs are ignored; any other SKIPPED or
# NEUTRAL check still blocks the exception.
MAIN_ONLY_JOBS = frozenset({('Documentation and cache', 'deploy-pages'),
                            ('Documentation and cache', 'publish-cache')})


def main_only_skip(check) -> bool:
    return (check.get('__typename') == 'CheckRun' and check.get('status') == 'COMPLETED' and
            check.get('conclusion') == 'SKIPPED' and
            (check.get('workflowName'), check.get('name')) in MAIN_ONLY_JOBS)


def review_ci_summary(pr, project, api, *, aggregate=None) -> str:
    """Preserve aggregate CI; only an authenticated scope failure is review-ready."""
    checks = pr['statusCheckRollup']
    if aggregate is None:
        aggregate = ci_summary(checks)
    if aggregate != 'failed' or len(checks) >= 100:
        return aggregate
    scope = [c for c in checks if c.get('__typename') == 'StatusContext' and
             c.get('context') == 'trusted-scope' and c.get('state') == 'FAILURE']
    others = [c for c in checks if not (scope and c is scope[0]) and not main_only_skip(c)]
    if len(scope) != 1 or ci_summary(others) != 'passed':
        return aggregate
    from .config import resource_text
    from .merge_checks import parse_checks
    from .worker_checks import human_review_scope
    settings = parse_checks(resource_text('merge-checks.toml'))
    return 'passed' if human_review_scope(api, project, pr, scope[0], settings) else aggregate


def normalize(pr, project, api) -> dict:
    require(isinstance(pr, dict) and set(pr) == set(PR_FIELDS.split(",")), "incomplete PR observation")
    require(isinstance(pr["author"], dict), "missing PR author")
    aggregate = ci_summary(pr["statusCheckRollup"])
    return {"number": pr["number"], "title": pr["title"], "author": pr["author"].get("login"),
            "head": pr["headRefOid"], "base": pr["baseRefOid"], "updated_at": pr["updatedAt"],
            "state": pr["state"], "draft": pr["isDraft"], "mergeable": pr["mergeable"],
            "ci": aggregate,
            "review_ci": review_ci_summary(pr, project, api, aggregate=aggregate)}


def survey(project, requested=None, *, api=None) -> dict:
    api = api or GitHub()
    user = api.read(["api", "--hostname", "github.com", "--method", "GET", "user"])
    require(isinstance(user, dict), "missing authenticated actor")
    actor = text(user.get("login"), "authenticated actor")
    repo_args = ["--repo", "github.com/" + project.repository, "--json", PR_FIELDS]
    if requested is None:
        raw = api.read(["pr", "list", *repo_args, "--state", "open", "--limit", str(MAX_PRS + 1)])
        require(isinstance(raw, list) and len(raw) <= MAX_PRS,
                "open queue exceeds 100 PRs or is incomplete; use explicit --pr targeting")
    else:
        raw = [api.read(["pr", "view", str(number), *repo_args]) for number in requested]
    result = {"schema": "sphereceti.worker-survey/v2", "repository": project.repository,
              "actor": actor, "observed_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
              "scope": list(requested) if requested is not None else None,
              "pull_requests": [normalize(pr, project, api) for pr in raw]}
    validate_snapshot(result, project, datetime.now(timezone.utc))
    return result


def add_parser(commands):
    worker = commands.add_parser("worker", help="read-only single-roadmap planning")
    sub = worker.add_subparsers(dest="worker_command", required=True)
    for command in ("survey", "plan"):
        parser = sub.add_parser(command)
        parser.add_argument("--pr", action="append", help="strict target set, e.g. --pr 9,11; never widens")
        parser.add_argument("--json", action="store_true")
        parser.add_argument("--operator-config", type=Path)
        if command == "plan":
            parser.add_argument("--snapshot", type=Path, help="offline survey; never calls GitHub")
            parser.add_argument("--frontier", type=Path, help="optional derived work estimates for the single roadmap")
    run = sub.add_parser("run", help="one shared-review round; execution requires approved policy")
    run.add_argument("--pr", action="append")
    run.add_argument("--json", action="store_true")
    run.add_argument("--execute", action="store_true")
    run.add_argument("--expect-head", metavar="SHA",
                     help="authorized full head commit; with exactly one --pr, stop unless the survey matches")
    run.add_argument("--expect-base", metavar="SHA", help="authorized full base commit; requires --expect-head")
    run.add_argument("--loop", action="store_true", help="bounded sequential rounds; requires --max-rounds")
    run.add_argument("--max-rounds", type=int, help="with --loop: number of sequential rounds, 1-20")
    run.add_argument("--interval-seconds", type=int, default=60)
    run.add_argument("--post-review", action="store_true")
    run.add_argument("--publish-state", action="store_true")
    run.add_argument("--worker-id", default="worker")
    run.add_argument("--operator-config", type=Path)
    run.add_argument("--source-repo", type=Path)
    run.add_argument("--dependencies-dir", type=Path)
    run.add_argument("--provider")
    run.add_argument("--auth", choices=("subscription", "api"), default="subscription")
    run.add_argument("--budget-usd", type=float)
    run.add_argument("--max-call-cost", type=float, default=1.0)
    run.add_argument("--codex-model", help="exact Codex model, as for `review`; default: the engine's")
    run.add_argument("--attempt-timeout", type=int, default=ATTEMPT_TIMEOUT,
                     help="seconds before one provider attempt is stopped, as for `review`")
    sync = sub.add_parser("sync", help="explicitly retry one operational run receipt; no provider")
    sync.add_argument("--receipt", type=Path, required=True)
    sync.add_argument("--json", action="store_true")
    sync.add_argument("--operator-config", type=Path)
    return worker


def run_worker(args, project, policy=None, prefs=None) -> dict:
    if args.worker_command == "sync":
        from .worker_state import sync_receipt
        return sync_receipt(args, project, policy)
    if args.worker_command == "run":
        if args.loop:
            from .worker_loop import run_loop
            return run_loop(args, project, policy, prefs)
        require(args.max_rounds is None and args.interval_seconds == 60,
                '--max-rounds and --interval-seconds require --loop')
        from .worker_execution import run_round
        return run_round(args, project, policy, prefs)
    requested = targets(args.pr)
    snapshot = (read_json(args.snapshot) if getattr(args, "snapshot", None) else survey(project, requested))
    if args.worker_command == "survey":
        return snapshot
    frontier = read_json(args.frontier) if args.frontier else None
    return plan(snapshot, project, requested=requested, frontier=frontier)


def render(report) -> str:
    if report["schema"] == "sphereceti.worker-loop/v1":
        return f"SphereCeti worker: {len(report['rounds'])} round(s), stopped: {report['state']}."
    if report["schema"] == "sphereceti.worker-round/v1":
        return f"SphereCeti worker: {report['state']}. " + report.get('reason', 'See --json for the round receipt.')
    if report["schema"] in ("sphereceti.worker-survey/v1", "sphereceti.worker-survey/v2"):
        return (f"Observed {len(report['pull_requests'])} PR(s) in {report['repository']} "
                f"as {report['actor']}. Use --json to save the survey.")
    lines = [f"SphereCeti worker: advisory plan for {report['repository']}"]
    selected = report["selected"]
    if selected:
        target = f"PR #{selected['pr']}" if "pr" in selected else selected["work_id"]
        lines.append(f"Suggested next: {selected['stage']} — {target} ({selected['destination']})")
    else:
        lines.append("No supported recommendation from this observation.")
    lines.extend(f"#{pr['pr']}: {pr['reason']}" for pr in report["pull_requests"])
    lines.extend([report["roadmap"]["reason"], report["execution_reason"]])
    return "\n".join(lines)
