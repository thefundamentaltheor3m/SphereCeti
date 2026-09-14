"""Project diagnostics, review, Worker operations and local reporting."""

from __future__ import annotations

import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tomllib

from . import __version__
from .config import (ConfigError, parse_operator, parse_policy, parse_project,
                     parse_source_lock, resource_text)


class QueueError(RuntimeError):
    """Unknown GitHub state must not be reported as no work."""


def pull_requests(repository: str) -> list[dict]:
    try:
        result = subprocess.run(
            ["gh", "api", "--paginate", "--slurp",
             f"repos/{repository}/pulls?state=open&per_page=100"],
            capture_output=True, text=True, timeout=45, check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise QueueError(f"GitHub query unavailable: {error}") from error
    if result.returncode:
        raise QueueError(f"GitHub query failed: {result.stderr.strip() or 'no diagnostic'}")
    try:
        pages = json.loads(result.stdout)
        if not isinstance(pages, list) or not pages:
            raise ValueError("expected at least one page")
        prs = []
        for page in pages:
            if not isinstance(page, list):
                raise ValueError("expected paginated arrays")
            for pr in page:
                if not isinstance(pr, dict) or type(pr.get("number")) is not int or not isinstance(pr.get("title"), str):
                    raise ValueError("incomplete pull request")
                prs.append({"number": pr["number"], "title": pr["title"]})
        return prs
    except (ValueError, TypeError) as error:
        raise QueueError(f"GitHub returned invalid queue data: {error}") from error


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if not argv:
        argv = ["worker", "plan"]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", action="version", version=__version__)
    commands = parser.add_subparsers(dest="command", required=True)
    from .local_review import add_parser, run_review, ReviewError
    from .gate import GateError
    from .review_records import RecordError
    add_parser(commands)
    from .archive_cli import add_parser as add_archive_parser, run_archive
    add_archive_parser(commands)
    from .worker_cli import add_parser as add_worker_parser, render, run_worker
    from .worker import WorkerError
    add_worker_parser(commands)
    from .evaluation_cli import add_parser as add_evaluation_parser, run_evaluation, render as render_evaluation
    add_evaluation_parser(commands)
    from .progress import add_parser as add_progress_parser, run as run_progress
    from .progress_evidence import ProgressError
    add_progress_parser(commands)
    from .merge_observation import add_parser as add_observer, observe
    add_observer(commands)
    from .merge_controller import add_parser as add_controller, run as run_controller
    add_controller(commands)
    from .lifecycle_api import add_parser as add_maintenance, run as run_maintenance
    add_maintenance(commands)
    for command in ('profile-plan', 'profile-run'):
        sub = commands.add_parser(command, help='local advisory exact-revision profiling')
        sub.add_argument('--repo', type=Path, required=True)
        for name in ('tooling', 'base', 'head'):
            sub.add_argument('--' + name, required=True)
        if command == 'profile-run':
            for name in ('workspace', 'toolchain', 'dependencies'):
                sub.add_argument('--' + name, type=Path, required=True)
    for command in ("doctor", "status"):
        sub = commands.add_parser(command)
        sub.add_argument("--json", action="store_true")
        sub.add_argument("--offline", action="store_true", help="do not query GitHub; queue remains unknown")
        sub.add_argument("--operator-config", type=Path, help="preferences only; cannot override repository policy")
    args = parser.parse_args(argv)
    if args.command in ('profile-plan', 'profile-run'):
        from .profiling import plan
        from .profile_runner import run
        from .sandbox import SandboxError
        try:
            if args.command == 'profile-plan':
                result = plan(args.repo, args.tooling, args.base, args.head)
            else:
                result = run(args.repo, args.tooling, args.base, args.head, args.workspace,
                             args.toolchain, args.dependencies)
            print(json.dumps(result, indent=2))
            return int(result.get('state') == 'error')
        except (ValueError, OSError, KeyError, SandboxError, subprocess.SubprocessError) as error:
            # JSON escaping keeps Git paths/diagnostics from becoming workflow commands.
            print(json.dumps({'state': 'error', 'reason': str(error)}))
            return 1
    try:
        project = parse_project(resource_text("sphereceti.toml"))
        policy = parse_policy(resource_text("automation.toml"))
        sources = parse_source_lock(resource_text("upstream-lock.toml"))
        operator_path = getattr(args, "operator_config", None)
        preferences = parse_operator(operator_path.read_text() if operator_path else "")
    except (ConfigError, OSError, tomllib.TOMLDecodeError) as error:
        parser.exit(2, f"sphereceti: configuration error: {error}\n")

    if args.command == "evaluation":
        try:
            report = run_evaluation(args, project, preferences)
        except (ValueError, OSError, KeyError, TypeError) as error:
            parser.exit(2, f"sphereceti: evaluation failed: {error}\n")
        print(json.dumps(report, indent=2) if args.json else render_evaluation(report, args.action))
        return 0

    if args.command == "archive":
        try:
            report = run_archive(args, project, preferences)
        except (ValueError, OSError, KeyError, TypeError) as error:
            parser.exit(2, f"sphereceti: archive operation failed ({type(error).__name__}): {error}\n")
        print(json.dumps(report, indent=2) if args.json else f"Archive: {report['state']}")
        return 0
    if args.command in ("merge-doctor", "merge-control"):
        try:
            report = run_controller(args, project)
        except (RecordError, ReviewError, GateError, ConfigError, OSError, ValueError, KeyError,
                TypeError, subprocess.SubprocessError) as error:
            reason = str(error) if isinstance(error, (RecordError, ConfigError, ReviewError)) else 'incomplete or unavailable controller evidence'
            parser.exit(2, f"sphereceti {args.command}: {reason}\n")
        print(json.dumps(report, indent=2))
        return 2 if report.get('state') == 'unconfirmed' else 0
    if args.command == 'maintenance':
        try:
            report = run_maintenance(args, project)
        except (RecordError, ReviewError, GateError, ConfigError, OSError, ValueError, KeyError,
                TypeError, subprocess.SubprocessError):
            report = {'state': 'error', 'reason': 'incomplete or unavailable lifecycle evidence',
                      'merge_allowed': False}
        # JSON escaping also protects logs from candidate-controlled workflow commands.
        print(json.dumps(report, indent=2))
        return int(report.get('state') in ('error', 'disabled'))

    if args.command == "merge-observe":
        try:
            report = observe(args, project)
        except (RecordError, ReviewError, GateError, ConfigError, OSError, ValueError, KeyError,
                TypeError, subprocess.SubprocessError) as error:
            reason = str(error) if isinstance(error, (RecordError, ConfigError, ReviewError)) else 'incomplete or unavailable observation evidence'
            parser.exit(2, f"sphereceti merge-observe: {reason}\n")
        print(json.dumps(report, indent=2) if args.json else
              f"PR #{args.pr}: {report['eligibility']}; " + '; '.join(report['reasons']) + '\nObservation only; merging is disabled.')
        return 0

    if args.command == "review":
        try:
            report = run_review(args, project, preferences)
        except (ReviewError, GateError, ConfigError, OSError, ValueError, KeyError,
                subprocess.SubprocessError) as error:
            reason = (str(error) if isinstance(error, (ReviewError, RecordError, ConfigError)) else
                      f"source/resource operation failed ({type(error).__name__}); check exact revisions and paths")
            parser.exit(2, f"sphereceti: {reason}\n")
        if args.json:
            print(json.dumps(report, indent=2))
        else:
            print(f"Local advisory review #{args.pr}: {report['completion']}")
            print(f"T={report['tooling']} H={report['head']} D={report['dependency_digest']}")
            print(f"Evidence and result: {report['output']}")
            print("This command does not authorize merging.")
            if report["missing_context"]:
                print("Missing approved context: " + ", ".join(report["missing_context"]))
            if "review_safe" in report:
                print("Authorized review evidence: " + ("current and approving" if report["review_safe"] else
                      "; ".join(report["reasons"])))
            if "publication" in report:
                posted = report["publication"]
                print(f"Published comment {posted['comment_id']}; API identity: {posted['identity']}; authorized: {posted['authorized']}")
        return 1 if report["completion"] == "error" else 0

    if args.command == "worker":
        try:
            report = run_worker(args, project, policy, preferences)
        except (WorkerError, ReviewError, RecordError, GateError, OSError, UnicodeError,
                subprocess.SubprocessError, KeyError, TypeError, ValueError) as error:
            reason = str(error) if isinstance(error, (WorkerError, ReviewError, RecordError)) else "worker operation failed; exact evidence remains unconfirmed"
            parser.exit(2, f"sphereceti worker: {reason}\n")
        print(json.dumps(report, indent=2) if args.json else render(report))
        return 1 if report.get("state") in ("error", "partial", "unconfirmed_publication") or report.get("state_publication", {}).get("state") == "unconfirmed" else 0
    if args.command == "progress":
        try:
            report = run_progress(args, project)
        except (OSError, ValueError, RuntimeError, KeyError, TypeError, subprocess.SubprocessError) as error:
            reason = str(error) if isinstance(error, ProgressError) else f"invalid or unavailable reporting evidence ({type(error).__name__})"
            parser.exit(2, f"sphereceti progress: {reason}\n")
        print(json.dumps(report, indent=2) if args.json else report.get("prompt", json.dumps(report, indent=2)))
        return 1 if report['state'] == 'missing_evidence' else 0

    config = {"project": asdict(project), "policy": asdict(policy), "sources": sources}
    report = {
        "schema_version": 1, "version": __version__, **config,
        "configuration_digest": hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest(),
        "operator": asdict(preferences),
        "roadmap": {"state": "approved" if project.roadmap_approved else "not_installed",
                    "reason": "Approved roadmap is not installed; an open PR is not approved specification."
                    if not project.roadmap_approved else "Profile records approved roadmap sources."},
        "capabilities": {name: {"implemented": name in ("posting", "merging"), "enabled": False,
                                "policy_requested": getattr(policy, name)}
                         for name in ("review_generation", "posting", "authoring", "reporting", "merging")},
        "worker": {"planning": True, "review_round": True, "execution_readiness": "unverified",
                   "mathematical_authoring": False},
        "local_review": {"implemented": True, "advisory_only": True, "publishing": True},
        "progress": {"implemented": True, "local_drafts": True, "publishing": False,
                     "production_evidence": "not_configured"},
        "merge_observation": {"implemented": True, "read_only": True, "activation_verified": False},
        "merge_controller": {"implemented": True, "enabled": False, "activation_verified": False},
        "maintenance": {"implemented": True, "labels_enabled": False, "automatic_closure": False},
        "queue": {"state": "not_checked", "pull_requests": None},
        "setup": {"state": "not_verified", "merging_ready": False,
                  "reason": "App installation, required checks, branch protection, and production adapter are not verified."},
    }
    exit_code = 0
    if not args.offline:
        try:
            report["queue"] = {"state": "available", "pull_requests": pull_requests(project.repository)}
        except QueueError as error:
            report["queue"] = {"state": "error", "pull_requests": None, "reason": str(error)}
            exit_code = 1
    if args.command == "doctor":
        report["executables"] = {name: shutil.which(name) for name in ("git", "gh", "lean", "lake")}
        if not all(report["executables"].values()):
            exit_code = 1
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(f"SphereCeti {__version__}: {project.repository} ({project.phase})")
        print(f"Mathematical destination: {project.implementation_repository}")
        print(report["roadmap"]["reason"])
        queue = report["queue"]
        print(f"Queue: {len(queue['pull_requests'])} open PR(s)" if queue["state"] == "available"
              else f"Queue: {queue.get('reason', 'not checked (offline)')}")
        print("Local review and explicit policy-gated posting are available. Automated review, authoring, reporting, and merging remain disabled.")
        print(f"Operational setup: {report['setup']['reason']}")
        if args.command == "doctor":
            for name, path in report["executables"].items():
                print(f"{name}: {path or 'missing'}")
        pending = [s["name"] for s in sources if s["license_status"] == "unresolved" and s["state"] == "planned"]
        if pending:
            print(f"Planned imports awaiting reuse terms: {', '.join(pending)}")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
