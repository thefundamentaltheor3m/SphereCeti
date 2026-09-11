"""Read-only project diagnostics. This command cannot author, post, review, or merge."""

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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", action="version", version=__version__)
    commands = parser.add_subparsers(dest="command", required=True)
    for command in ("doctor", "status"):
        sub = commands.add_parser(command)
        sub.add_argument("--json", action="store_true")
        sub.add_argument("--offline", action="store_true", help="do not query GitHub; queue remains unknown")
        sub.add_argument("--operator-config", type=Path, help="preferences only; cannot override repository policy")
    args = parser.parse_args(argv)
    try:
        project = parse_project(resource_text("sphereceti.toml"))
        policy = parse_policy(resource_text("automation.toml"))
        sources = parse_source_lock(resource_text("upstream-lock.toml"))
        preferences = parse_operator(args.operator_config.read_text() if args.operator_config else "")
    except (ConfigError, OSError, tomllib.TOMLDecodeError) as error:
        parser.exit(2, f"sphereceti: configuration error: {error}\n")

    config = {"project": asdict(project), "policy": asdict(policy), "sources": sources}
    report = {
        "schema_version": 1, "version": __version__, **config,
        "configuration_digest": hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest(),
        "operator": asdict(preferences),
        "roadmap": {"state": "approved" if project.roadmap_approved else "not_installed",
                    "reason": "Approved roadmap is not installed; an open PR is not approved specification."
                    if not project.roadmap_approved else "Profile records approved roadmap sources."},
        "capabilities": {name: {"implemented": False, "enabled": False,
                                "policy_requested": getattr(policy, name)}
                         for name in ("review_generation", "posting", "authoring", "reporting", "merging")},
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
        print("Authoring, review generation, posting, reporting, and merging: not implemented; disabled.")
        print(f"Operational setup: {report['setup']['reason']}")
        if args.command == "doctor":
            for name, path in report["executables"].items():
                print(f"{name}: {path or 'missing'}")
        pending = [s["name"] for s in sources if s["license_status"] == "unresolved"]
        if pending:
            print(f"Planned imports awaiting reuse terms: {', '.join(pending)}")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
