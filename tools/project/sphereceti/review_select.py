# SPDX-License-Identifier: Apache-2.0
"""Choose the one open PR a contributor's bare `sphereceti review` should review.

Selection reuses the worker's read-only survey and planner; it adds only the contributor's
filters (not their own PR, not already reviewed). It reads GitHub and the contributor's local
review store and never writes either. The chosen PR is then reviewed by the unchanged
`local_review.run_review`, bound to the head and base observed here.
"""
from __future__ import annotations

from datetime import datetime, timezone
import json
from pathlib import Path

from .carry_over import carried_records, describe as carry_status
from .local_review import ReviewError
from .review_claims import ClaimYielded, describe, live, note as claim_note, run_claimed
from .review_records import (ANY_DIRECTIVE, CONTEST, MARKER, RecordError, carried_contests, contests,
                             identity, intact, parse_record)
from .worker import plan, timestamp
from .worker_checks import NEEDS_REFRESH
from .worker_cli import survey
from .worker_leases import utcnow

SCHEMA = "sphereceti.review-selection/v1"
PRIORITY = ("Planner stage first (every eligible PR is at review-assessment, so they tie); "
            "then stack roots blocking the most descendants; "
            "then longest waiting by the PR's GitHub updatedAt, oldest first; then lowest PR number.")


def waiting(seconds: int) -> str:
    if seconds < 60:
        return "<1m"
    for unit, size in (("d", 86400), ("h", 3600), ("m", 60)):
        if seconds >= size:
            return f"{seconds // size}{unit}"


def readiness(pr) -> tuple[str, str]:
    """(code, reason) for a PR the planner does not offer for review assessment.

    Evidence that is merely not current yet (CI pending or unknown, or a trusted build that only
    needs refreshing on current main) is told apart from a real failure.
    """
    if pr["state"] != "OPEN":
        return "not_ready", "is not open"
    if pr["mergeable"] == "CONFLICTING":
        return "not_ready", "is not ready (conflicting)"
    if pr["mergeable"] != "MERGEABLE":  # GitHub recomputes it after main moves
        return "awaiting_github", "awaits GitHub's mergeability check"
    review_ci = pr.get("review_ci", pr["ci"])
    if review_ci in ("pending", "unknown"):
        return "awaiting_ci", f"awaits CI ({review_ci})"
    if pr.get("review_note") == NEEDS_REFRESH:
        return "awaiting_refresh", NEEDS_REFRESH
    return "not_ready", f"is not ready (CI {review_ci})"


def local_record(storage: Path, repository: str, number: int, head: str, base: str) -> str | None:
    """A complete commit/manual record this contributor produced locally for this exact head/base.

    Every executed review writes record.json in its run directory and captures it in the local
    archive journal, so runs with an explicit --output are found through the journal.
    """
    root = storage / repository.replace("/", "__")
    found = [(path, lambda value: value) for path in sorted(root.glob("runs/*/record.json"))]
    found += [(path, lambda value: value.get("review")) for path in
              sorted(root.glob("archive/journal/records/*.json"))]
    for path, review in found:
        try:
            record = review(json.loads(path.read_text()))
        except (OSError, ValueError, AttributeError):
            continue
        if (isinstance(record, dict) and record.get("repository") == repository
                and record.get("pr") == number and record.get("head") == head
                and record.get("base") == base and record.get("completion") == "complete"
                and record.get("execution_mode") in ("commit", "manual")):
            return str(path.parent if path.name == "record.json" else path)
    return None


def published(comments, repository, pr, actor_login):
    """Classify records on the PR for this head/base: accepted (authorized) and the actor's own."""
    accepted, yours = [], []
    for c in comments:
        body = c.get("body")
        if not isinstance(body, str) or MARKER not in body or not intact(c, repository, pr["number"]):
            continue
        try:
            r = parse_record(body)
        except (ValueError, TypeError):
            continue
        if (r["repository"] != repository or r["pr"] != pr["number"] or r["head"] != pr["head"]
                or r["base"] != pr["base"] or r["completion"] != "complete"
                or r["execution_mode"] not in ("commit", "manual")):
            continue
        login = (c.get("user") or {}).get("login")
        if isinstance(login, str) and login.casefold() == actor_login.casefold():
            yours.append(c["id"])
        if not r["advisory"]:
            accepted.append((c, r))
    return accepted, yours


def review_state(client, repository, pr, actor, policy, storage, *, force=False, now=None):
    """Return (code, reason) when this ready PR needs no review from you now, else None."""
    comments = client.comments(repository, pr["number"])
    if not isinstance(comments, list):
        raise RecordError("unknown review records")
    state = reviewed(client, comments, repository, pr, actor, policy, storage)
    if state or force:
        return state
    now = now or utcnow()
    context = {"repository": repository, "pr": pr["number"], "head": pr["head"]}
    foreign = [c for c in live(comments, context, now) if c["author"].casefold() != actor.casefold()]
    return ("claimed", describe(foreign[0], now)) if foreign else None


def reviewed(client, comments, repository, pr, actor, policy, storage):
    if any(isinstance(c.get("body"), str) and any(ANY_DIRECTIVE.match(line) for line in c["body"].splitlines())
           for c in comments):
        info = client.call(f"repos/{repository}/pulls/{pr['number']}")
        author = (info.get("user") or {}).get("id") if isinstance(info, dict) else None
        if type(author) is not int:
            raise RecordError("PR author identity is unavailable")
        if carried_contests(comments, {"repository": repository, "pr": pr["number"]}, policy, author):
            return None  # An unanswered author contest asks for another review, on any head.
    accepted, yours = published(comments, repository, pr, actor)
    if yours:
        return "reviewed_by_you", "you already published a complete review of this head"
    path = local_record(storage, repository, pr["number"], pr["head"], pr["base"])
    if path:
        return "reviewed_by_you", f"you already reviewed this head locally ({path})"
    carried = ""
    if not accepted:
        # Only update-branch merges since an older reviewed head, with the same change and no review
        # input changed on main: that review is current (carry_over), so no fresh review is needed.
        items, result = carried_records(client, comments, repository, pr["number"], pr["head"])
        if items:
            carried = carry_status(result)
            if any((c.get("user") or {}).get("login", "").casefold() == actor.casefold() for c, _ in items):
                return "reviewed_by_you", f"you already reviewed this change; {carried}"
            accepted = items
    accepted = {c["id"]: (c, r) for c, r in accepted if identity(c) in policy.authorized_reviewers}
    if not accepted:
        return None
    pending = []
    if any(isinstance(c.get("body"), str) and c["body"].startswith(CONTEST) for c in comments):
        info = client.call(f"repos/{repository}/pulls/{pr['number']}")
        author = (info.get("user") or {}).get("id") if isinstance(info, dict) else None
        if type(author) is not int:
            raise RecordError("PR author identity is unavailable")
        context = {"repository": repository, "pr": pr["number"], "head": pr["head"]}
        latest = {identity(c): r for _, (c, r) in sorted(accepted.items())}
        # As assess_records: a contest is resolved once its publisher's latest record has seen it.
        pending = [p for p in contests(comments, accepted, context, policy, author)
                   if latest[p["publisher"]]["contests_through"][p["rubric"]] < p["id"]]
    if pending:
        return None  # An authenticated contest newer than the record asks for another review.
    publisher = identity(accepted[max(accepted)][0])
    if carried:
        return "reviewed", f"already has an accepted review ({publisher}); {carried}"
    return "reviewed", f"already has an accepted review of this head ({publisher})"


def select(project, policy, prefs, *, api=None, client=None, now=None, force=False) -> dict:
    """Read-only selection. Unknown GitHub state raises; it never becomes an empty choice."""
    if client is None:
        from .review_post import GitHub
        client = GitHub()
    snapshot = survey(project, None, api=api)
    now = now or datetime.now(timezone.utc)
    planned = plan(snapshot, project, now=now)
    actor = snapshot["actor"]
    storage = Path(prefs.storage).expanduser().resolve()
    observed = timestamp(snapshot["observed_at"])
    ready = {c["pr"] for c in planned["candidates"] if c["stage"] == "review-assessment"}
    by_number = {pr["number"]: pr for pr in snapshot["pull_requests"]}
    skipped, candidates = [], []
    from .stacks import StackGate
    gate = StackGate(snapshot, project, policy, client, ready)

    def skip(pr, code, reason):
        # An informational readiness note (e.g. an older trusted build) never makes a PR not ready.
        note = pr.get("review_note") if code != "awaiting_refresh" else None
        skipped.append({"pr": pr["number"], "head": pr["head"], "code": code,
                        "reason": reason + (f" ({note})" if note else ""), "note": note})

    # The planner's order is the priority: stage, then oldest updatedAt, then PR number.
    order = [c["pr"] for c in planned["candidates"] if "pr" in c]
    order += sorted(n for n in by_number if n not in order)
    for number in order:
        pr = by_number[number]
        if pr["author"].casefold() == actor.casefold():
            skip(pr, "yours", "is yours")
        elif pr["draft"]:
            skip(pr, "draft", "is a draft")
        elif number not in ready:
            skip(pr, *readiness(pr))
        elif gate.waiting(number):
            skip(pr, "waiting_on_parent", gate.waiting(number)[1])
        else:
            state = review_state(client, project.repository, pr, actor, policy, storage, force=force)
            if state:
                skip(pr, state[0], state[1])
            else:
                seconds = max(0, int((observed - timestamp(pr["updated_at"])).total_seconds()))
                candidates.append({"pr": number, "title": pr["title"], "author": pr["author"],
                                   "head": pr["head"], "base": pr["base"], "updated_at": pr["updated_at"],
                                   "waiting_seconds": seconds, "ci": pr["ci"],
                                   "review_ci": pr.get("review_ci", pr["ci"]),
                                   "note": pr.get("review_note"), "unblocks": gate.descendants(number)})
    # Stack roots first: among equally eligible PRs, the one blocking the most descendants leads.
    candidates.sort(key=lambda c: -c["unblocks"])
    skipped.sort(key=lambda item: -item["pr"])  # Display order only: newest PR first.
    selected = candidates[0] if candidates else None
    main = None
    if any(item["code"] == "awaiting_refresh" for item in skipped):
        try:
            main = client.call(f"repos/{project.repository}/commits/{project.default_branch}").get("sha")
        except (RecordError, KeyError, AttributeError):
            main = None  # informational only
    return {"schema": SCHEMA, "main": main, "state": "selected" if selected else "nothing_to_review",
            "repository": project.repository, "actor": actor, "observed_at": snapshot["observed_at"],
            "priority": PRIORITY, "waiting_since": "updatedAt",
            "selected": selected, "candidates": candidates, "skipped": skipped,
            "rationale": None, "posting": None, "plan": None, "summary": None, "review": None}


def count(items, verb) -> str:
    return f"{len(items)} open PR {verb}s" if len(items) == 1 else f"{len(items)} open PRs {verb}"


def intent(args) -> str:
    if args.dry_run:
        return "nothing will be posted"
    if not args.post:
        return "will not post (--no-post)"
    return "will post if policy permits" if getattr(args, "post_default", False) else "will post"


def not_ready_summary(skipped, main=None) -> str:
    """Why nothing is ready: stale or pending evidence is summarized, real failures stay listed."""
    if not skipped:
        return "No PRs need your review: the open queue is empty."
    refresh = [i for i in skipped if i["code"] == "awaiting_refresh"]
    pending = [i for i in skipped if i["code"] == "awaiting_ci"]
    github = [i for i in skipped if i["code"] == "awaiting_github"]
    if not refresh and not pending and not github:
        return "No PRs need your review: " + "; ".join(f"#{i['pr']} {i['reason']}" for i in skipped) + "."
    parts = []
    if refresh:
        parts.append(f"{count(refresh, 'await')} a refreshed trusted build" +
                     (f" (main moved to {main[:7]})" if main else ""))
    if pending:
        parts.append(f"{count(pending, 'await')} CI")
    if github:
        parts.append(f"{count(github, 'await')} GitHub's mergeability check")
    yours = [i for i in skipped if i["code"] == "yours"]
    if yours:
        parts.append(f"{len(yours)} {'is' if len(yours) == 1 else 'are'} yours")
    parts += [f"#{i['pr']} {i['reason']}" for i in skipped
              if i["code"] not in ("awaiting_refresh", "awaiting_ci", "awaiting_github", "yours")]
    return "No PR is ready with current evidence: " + "; ".join(parts) + "."


def rationale(selection, *, dry_run=False, posting=None) -> str:
    s = selection["selected"]
    if s is None:
        return not_ready_summary(selection["skipped"], selection.get("main"))
    verb = "Previewing" if dry_run else "Reviewing"
    ready = "ready" if s["ci"] == s["review_ci"] else "ready (human-review scope)"
    if s.get("note"):
        ready = ready[:-1] + f"; {s['note']})" if ready.endswith(")") else f"ready ({s['note']})"
    unblocks = s.get("unblocks") or 0
    stack = f"; unblocks {unblocks} stacked PR{'s' if unblocks != 1 else ''}" if unblocks else ""
    return (f"{verb} #{s['pr']} (head {s['head'][:7]}): {ready}, not yours, no current review{stack}; "
            f"waiting {waiting(s['waiting_seconds'])}" + (f"; {posting}." if posting else "."))


def check_arguments(args) -> None:
    """Bare review chooses a GitHub PR; PR-specific inputs need an explicit number."""
    for flag, value in (("--local-sources", args.local_sources), ("--read-records", args.read_records),
                        ("--shadow", args.shadow), ("--replies-json", args.replies_json),
                        ("--head", args.head), ("--base", args.base),
                        ("--description-file", args.description_file),
                        ("--reply-file", args.reply_file), ("--reply-rubric", args.reply_rubric)):
        if value:
            raise ReviewError(f"{flag} requires an explicit PR number: sphereceti review N {flag} ...")
    if args.mode == "reply":
        raise ReviewError("reply mode requires an explicit PR number")


def run_bare(args, project, policy, prefs, *, api=None, client=None, announce=None, run=None):
    """Select, say why in one line (announced before a long review starts), then review.

    If another contributor's earlier claim wins the race for the chosen PR, the claim yields
    with nothing spent and the next candidate is tried, each with its own announced line.
    """
    from .local_review import posting_note
    from .review_summary import announcing, summarize
    check_arguments(args)
    force = getattr(args, "force_claim", False)
    selection = select(project, policy, prefs, api=api, client=client, force=force)
    output = args.output
    for attempt, candidate in enumerate(list(selection["candidates"])):
        selection["selected"] = candidate
        selection["rationale"] = rationale(selection, dry_run=args.dry_run, posting=intent(args))
        if announce:
            announce(selection["rationale"])
        args.pr = candidate["pr"]
        if output and attempt:
            args.output = output.with_name(f"{output.name}-pr{candidate['pr']}")  # --output must be new
        planned = {}
        try:
            selection["review"] = run_claimed(args, project, prefs, expect=candidate, run=run,
                                              wrap=lambda inner: announcing(prefs, announce, planned, inner=inner))
        except ClaimYielded as error:
            winner = error.winner
            selection["skipped"].append({"pr": candidate["pr"], "head": candidate["head"], "code": "claimed",
                                         "reason": f"review in progress by @{winner['author']} (yielded)"})
            continue
        selection["posting"] = posting_note(args, selection["review"])
        selection["plan"] = planned or None
        selection["summary"] = summarize(args, selection["review"], posting=selection["posting"])
        return selection
    selection.update(selected=None, state="nothing_to_review")
    selection["skipped"].sort(key=lambda item: -item["pr"])
    selection["rationale"] = rationale(selection)
    if announce:
        announce(selection["rationale"])
    return selection


def render(selection, args) -> list[str]:
    """The readable result after the announced rationale line."""
    report = selection["review"]
    if report is None:
        return []
    lines = []
    output = Path(report["output"])
    if report["completion"] == "dry_run":
        lines.append(f"Dry run: no model call. T={report['tooling']} H={report['head']}")
        lines.append(f"Evidence: {output / 'evidence.json'}")
    else:
        lines.append(f"Local advisory review #{report['pr']}: {report['completion']}")
        width = max(len(r) for r in report["verdicts"])
        lines += [f"  {rubric.ljust(width)}  {verdict}" for rubric, verdict in report["verdicts"].items()]
        lines.append(f"Record: {output / 'record.md'} (machine-readable: record.json)")
        archive = report.get("archive") or {}
        if archive.get("state") == "queued":
            lines.append(f"Archived locally as {archive['record']}.")
        elif archive:
            lines.append(f"Archive: {archive.get('state')}: {archive.get('reason', '')}".rstrip(": "))
    lines.append(selection["posting"])
    if report.get("claim"):
        lines.append(claim_note(report["claim"]))
    lines.append("This command does not authorize merging.")
    if selection.get("summary"):
        lines += [selection["summary"]["line"], "Next: " + selection["summary"]["next_action"]]
    return lines
