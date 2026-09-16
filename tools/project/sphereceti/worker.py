# SPDX-License-Identifier: Apache-2.0
"""Independently authored, advisory scheduling for SphereCeti's single roadmap.

Inputs are observations and effort estimates, never permission to execute work.
No TauCetiWorker implementation, prompts, or tests are incorporated here.
"""
from __future__ import annotations

from dataclasses import asdict
from datetime import datetime, timezone
import hashlib
import json
import re

from .config import COMMIT, ProjectConfig


class WorkerError(ValueError):
    """An incomplete observation cannot become an empty queue."""


STAGES = ("rebase", "dependency-repair", "progress", "ci-repair", "review-response",
          "review-assessment", "roadmap")
DEFERRED = {
    "dependency-repair": "Needs the coherent dependency-graph repair adapter.",
    "progress": "Needs the reporting adapter and its published evidence.",
    "review-response": "Needs authenticated current findings from the shared review engine.",
}
EFFORT = {"small": 0, "medium": 1, "large": 2, "unknown": 3}
MAX_PRS = 100
MAX_TARGETS = 25
MAX_ITEMS = 1000


def require(condition: bool, message: str) -> None:
    if not condition:
        raise WorkerError(message)


def fields(value, keys: set[str], context: str) -> None:
    require(isinstance(value, dict) and set(value) == keys, f"{context}: unexpected fields")


def text(value, context: str) -> str:
    require(isinstance(value, str) and 0 < len(value) <= 2000 and value.strip() == value
            and not any(ord(c) < 32 or ord(c) == 127 for c in value), f"{context}: invalid text")
    return value


def commit(value, context: str) -> str:
    require(isinstance(value, str) and COMMIT.fullmatch(value) is not None,
            f"{context}: expected a full commit")
    return value


def choice(value, values, context: str) -> None:
    require(isinstance(value, str) and value in values, f"{context}: unsupported value")


def timestamp(value: str) -> datetime:
    require(isinstance(value, str) and re.fullmatch(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", value)
            is not None, "expected UTC timestamp YYYY-MM-DDTHH:MM:SSZ")
    try:
        return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
    except ValueError as error:
        raise WorkerError("invalid UTC timestamp") from error


def fresh(value: str, now: datetime) -> None:
    require(0 <= (now - timestamp(value)).total_seconds() <= 900,
            "observation is future-dated or more than 15 minutes old; survey again")


def digest(value) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                     ensure_ascii=True).encode()).hexdigest()


def targets(values: list[str] | None) -> tuple[int, ...] | None:
    if values is None:
        return None
    result = set()
    for value in values:
        for part in value.split(","):
            require(re.fullmatch(r"#?[1-9][0-9]{0,8}", part) is not None,
                    "--pr requires positive PR numbers; empty or malformed targeting is an error")
            result.add(int(part.removeprefix("#")))
    require(0 < len(result) <= MAX_TARGETS, f"target between 1 and {MAX_TARGETS} PRs")
    return tuple(sorted(result))


def validate_snapshot(data, project: ProjectConfig, now: datetime) -> None:
    fields(data, {"schema", "repository", "actor", "observed_at", "scope", "pull_requests"}, "snapshot")
    require(data["schema"] == "sphereceti.worker-survey/v1", "unknown survey schema")
    require(data["repository"] == project.repository, "queue destination does not match the project")
    text(data["actor"], "actor")
    fresh(data["observed_at"], now)
    scope = data["scope"]
    require(scope is None or (isinstance(scope, list) and 0 < len(scope) <= MAX_TARGETS and
            all(type(n) is int and n > 0 for n in scope) and len(set(scope)) == len(scope)),
            "scope must be null (complete open queue) or distinct requested PR numbers")
    prs = data["pull_requests"]
    require(isinstance(prs, list) and len(prs) <= MAX_PRS, "queue exceeds the bounded survey limit")
    seen = set()
    for pr in prs:
        fields(pr, {"number", "title", "author", "head", "base", "updated_at", "state", "draft",
                    "mergeable", "ci"}, "pull request")
        n = pr["number"]
        require(type(n) is int and n > 0 and n not in seen, "invalid or duplicate pull request")
        seen.add(n)
        for key in ("title", "author"):
            text(pr[key], key)
        for key in ("head", "base"):
            commit(pr[key], key)
        require(timestamp(pr["updated_at"]) <= timestamp(data["observed_at"]), "PR update is in the future")
        choice(pr["state"], ("OPEN", "CLOSED", "MERGED"), "PR state")
        require(type(pr["draft"]) is bool, "draft must be boolean")
        choice(pr["mergeable"], ("MERGEABLE", "CONFLICTING", "UNKNOWN"), "mergeability")
        choice(pr["ci"], ("passed", "failed", "pending", "unknown"), "CI observation")
        require(scope is not None or pr["state"] == "OPEN", "complete queue contains a closed PR")
    require(scope is None or set(scope) == seen, "targeted survey is missing or adds a PR")


def validate_frontier(data, project: ProjectConfig, now: datetime) -> dict[str, dict]:
    fields(data, {"schema", "repository", "implementation_repository", "roadmap_revision",
                  "implementation_revision", "document", "targets", "observed_at", "items"}, "frontier")
    require(data["schema"] == "sphereceti.worker-frontier/v1", "unknown frontier schema")
    require(data["repository"] == project.repository and
            data["implementation_repository"] == project.implementation_repository,
            "frontier destination does not match the project")
    require(data["document"] == project.roadmap_document and data["targets"] == project.roadmap_targets,
            "frontier must describe the single configured roadmap")
    commit(data["roadmap_revision"], "roadmap revision")
    commit(data["implementation_revision"], "implementation revision")
    fresh(data["observed_at"], now)
    require(isinstance(data["items"], list) and len(data["items"]) <= MAX_ITEMS, "invalid frontier size")
    items = {}
    for item in data["items"]:
        fields(item, {"id", "summary", "reference", "status", "effort", "depends_on", "blocked_by"}, "work item")
        key = text(item["id"], "work id")
        require(re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,99}", key) is not None and key not in items,
                "invalid or duplicate work id")
        text(item["summary"], "work summary")
        text(item["reference"], "roadmap reference")
        require(item["reference"].startswith(project.roadmap_document + "#") and
                len(item["reference"]) > len(project.roadmap_document) + 1,
                "work must cite a heading in the single roadmap")
        choice(item["status"], ("remaining", "complete", "active"), "work status")
        choice(item["effort"], EFFORT, "effort estimate")
        deps = item["depends_on"]
        require(isinstance(deps, list) and all(isinstance(d, str) for d in deps) and
                len(deps) == len(set(deps)), "invalid or duplicate prerequisites")
        require(isinstance(item["blocked_by"], list), "invalid blockers")
        for blocker in item["blocked_by"]:
            text(blocker, "blocker")
        items[key] = item
    for key, item in items.items():
        require(all(d in items and d != key for d in item["depends_on"]), "unknown or self prerequisite")
    # Bounded iterative topological check, including completed/active nodes.
    pending = {key: set(item["depends_on"]) for key, item in items.items()}
    while pending:
        ready = {key for key, deps in pending.items() if not deps}
        require(bool(ready), "cyclic frontier prerequisites")
        pending = {key: deps - ready for key, deps in pending.items() if key not in ready}
    return items


def plan(snapshot, project: ProjectConfig, *, requested: tuple[int, ...] | None = None,
         frontier=None, now: datetime | None = None) -> dict:
    now = now or datetime.now(timezone.utc)
    validate_snapshot(snapshot, project, now)
    if requested is not None:
        require(isinstance(requested, tuple) and 0 < len(requested) <= MAX_TARGETS and
                all(type(n) is int and n > 0 for n in requested) and len(set(requested)) == len(requested),
                "invalid requested PR set")
    if snapshot["scope"] is not None:
        require(requested is not None and set(requested) <= set(snapshot["scope"]),
                "a targeted survey cannot become an unrestricted or wider plan")
    items = validate_frontier(frontier, project, now) if frontier is not None else {}
    candidates, diagnostics = [], []
    prs = [pr for pr in snapshot["pull_requests"] if requested is None or pr["number"] in requested]
    if requested:
        for number in sorted(set(requested) - {pr["number"] for pr in prs}):
            diagnostics.append({"pr": number, "reason": "Not in the observed open queue; no fallback."})
    for pr in prs:
        stage = None
        reason = "No supported maintenance recommendation."
        own = pr["author"].casefold() == snapshot["actor"].casefold()
        if pr["state"] != "OPEN":
            reason = "PR is closed or merged."
        elif own and pr["mergeable"] == "CONFLICTING":
            stage, reason = "rebase", "Resolve this operator's observed conflict before new work."
        elif own and pr["ci"] == "failed":
            stage, reason = "ci-repair", "Investigate this operator's failing CI before new work."
        elif pr["draft"]:
            reason = "Draft PR; review assessment waits."
        elif pr["mergeable"] != "MERGEABLE" or pr["ci"] != "passed":
            reason = "Review assessment waits for known mergeability and passing observed checks."
        else:
            stage, reason = "review-assessment", "Ask the shared engine whether current review work is needed."
        diagnostics.append({"pr": pr["number"], "reason": reason})
        if stage:
            candidates.append({"stage": stage, "pr": pr["number"], "head": pr["head"], "base": pr["base"],
                               "destination": project.repository, "reason": reason,
                               "updated_at": pr["updated_at"]})
    candidates.sort(key=lambda c: (STAGES.index(c["stage"]), c["updated_at"], c["pr"]))
    roadmap_reason = "An optional, revision-bound frontier has not been supplied."
    work = []
    if requested is not None:
        roadmap_reason = "Strict PR targeting excludes roadmap and other untargeted work."
    elif not project.roadmap_approved:
        roadmap_reason = "No approved roadmap is installed; an open PR is not specification."
    elif frontier is not None:
        roadmap_reason = "Operator estimates only; source approval, completeness and completion are not verified."
        for key, item in items.items():
            if (item["status"] == "remaining" and not item["blocked_by"] and
                    all(items[d]["status"] == "complete" for d in item["depends_on"])):
                work.append({"stage": "roadmap", "work_id": key, "summary": item["summary"],
                             "reference": item["reference"], "effort": item["effort"],
                             "destination": project.implementation_repository,
                             "roadmap_revision": frontier["roadmap_revision"],
                             "implementation_revision": frontier["implementation_revision"]})
        # Ready prerequisites first; effort ranks only the currently ready frontier.
        # Prefer more immediate dependents within the same effort class, then stable IDs.
        work.sort(key=lambda c: (EFFORT[c["effort"]],
                  -sum(c["work_id"] in item["depends_on"] and item["status"] == "remaining"
                       for item in items.values()), c["work_id"]))
    candidates.extend(work)
    return {"schema": "sphereceti.worker-plan/v1", "repository": project.repository,
            "actor": snapshot["actor"], "observed_at": snapshot["observed_at"],
            "requested_prs": list(requested) if requested is not None else None,
            "input_digest": digest({"project": asdict(project), "survey": snapshot, "frontier": frontier}),
            "advisory_only": True, "executable": False,
            "execution_reason": "No execution adapter is installed; a plan is never authorization.",
            "selected": candidates[0] if candidates else None, "candidates": candidates,
            "pull_requests": diagnostics,
            "roadmap": {"reason": roadmap_reason, "ready": len(work), "source_verified": False},
            "deferred_stages": DEFERRED}
