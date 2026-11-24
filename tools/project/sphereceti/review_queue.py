# SPDX-License-Identifier: Apache-2.0
"""A contributor's personal review queue (`sphereceti reviews`) and bounded review batches.

Adapted in design from TauCetiWorker's dashboard and review-only rounds
(https://github.com/TauCetiProject/TauCetiWorker#the-dashboard, #what-a-round-does): the previous
reviewer gets first chance at a revised PR. Independently written; no TauCetiWorker code is used.

The queue reuses the worker's survey and planner and bare selection's readiness and "already
reviewed" rules. One survey per listing; any failed GitHub lookup raises (exit 2), never a guess.
PRs ready to merge (ready_to_merge.py) are listed first.
"""
from __future__ import annotations

from datetime import datetime, timezone
import json
from pathlib import Path

from .carry_over import ApiSource, carry, describe as carry_status
from .local_review import ReviewError
from .review_records import CONTEST, MARKER, RecordError, intact, parse_record
from .review_claims import ClaimRefused, ClaimYielded, run_claimed
from .review_select import not_ready_summary, readiness, review_state, waiting
from .worker import WorkerError, plan, timestamp
from .worker_cli import survey

SCHEMA = "sphereceti.review-queue/v1"
BATCH_SCHEMA = "sphereceti.review-batch/v1"
SECTIONS = ("revised", "author_replied", "new", "waiting_on_author", "not_ready")
TITLES = {"revised": "Revised since your review", "author_replied": "Author replied",
          "new": "New to you", "waiting_on_author": "Waiting on the author"}
FOLLOW_UP = ("revised", "author_replied")  # yours first: you reviewed these before
MAX_LIMIT = 10
CHANGES = ("request_changes", "block")


def my_records(comments, repository, pr, actor):
    """Your posted, unedited review records on this PR (any head), oldest first."""
    found = []
    for c in comments:
        login = (c.get("user") or {}).get("login")
        body = c.get("body")
        if (not isinstance(login, str) or login.casefold() != actor.casefold() or not isinstance(body, str)
                or MARKER not in body or not intact(c, repository, pr)):
            continue
        try:
            record = parse_record(body)
        except (ValueError, TypeError):
            continue
        if (record["repository"] == repository and record["pr"] == pr
                and record["execution_mode"] in ("commit", "manual")):
            found.append((c, record))
    return sorted(found, key=lambda item: item[0]["id"])


def since(comments, after, author):
    """Author replies and contests newer than your latest record: (replies, contests)."""
    later = [c for c in comments if c["id"] > after]
    replies = [c for c in later if ((c.get("user") or {}).get("login") or "").casefold() == author.casefold()
               and not str(c.get("body", "")).startswith((CONTEST, MARKER))]
    contested = [c for c in later if str(c.get("body", "")).startswith(CONTEST)]
    return replies, contested


def link(repository, pr, comment):
    return comment.get("html_url") or f"https://github.com/{repository}/pull/{pr}#issuecomment-{comment['id']}"


def commits_since(client, repository, old, new):
    """(count, note) from the compare API; a rewritten history is reported, not guessed."""
    try:
        value = client.call(f"repos/{repository}/compare/{old}...{new}")
    except RecordError:
        return None, "the reviewed head is no longer in the history (force-pushed)"
    if not isinstance(value, dict) or type(value.get("ahead_by")) is not int:
        raise RecordError("incomplete compare response")
    if value.get("status") == "diverged":
        return value["ahead_by"], "history rewritten since your review"
    return value["ahead_by"], None


def entry(section, pr, observed, reason, **extra):
    seconds = max(0, int((observed - timestamp(pr["updated_at"])).total_seconds()))
    return {"section": section, "pr": pr["number"], "author": pr["author"], "title": pr["title"], "head": pr["head"],
            "base": pr["base"], "updated_at": pr["updated_at"], "waiting_seconds": seconds,
            "reason": reason, "note": pr.get("review_note"), **extra}


def queue(project, policy, prefs, *, api=None, client=None, now=None) -> dict:
    """Read-only classification of the open queue for the authenticated contributor."""
    if client is None:
        from .review_post import GitHub
        client = GitHub()
    from .ready_to_merge import HELD, Cached, held_reason, held_runs, ready_to_merge
    client = Cached(client)  # one comments read per PR for every section
    snapshot = survey(project, None, api=api)
    client.total = sum(1 for pr in snapshot["pull_requests"] if pr["state"] == "OPEN" and not pr["draft"])
    planned = plan(snapshot, project, now=now or datetime.now(timezone.utc))
    actor, repository = snapshot["actor"], project.repository
    storage = Path(prefs.storage).expanduser().resolve()
    observed = timestamp(snapshot["observed_at"])
    ready = {c["pr"] for c in planned["candidates"] if c["stage"] == "review-assessment"}
    order = [c["pr"] for c in planned["candidates"] if "pr" in c]
    by_number = {pr["number"]: pr for pr in snapshot["pull_requests"]}
    order += sorted(n for n in by_number if n not in order)
    sections = {name: [] for name in SECTIONS}
    main_sha = [None]  # read once, only when a record on an older head needs a carry-over check
    done, follow_ups = [], []
    from .stacks import StackGate
    gate = StackGate(snapshot, project, policy, client, ready)
    blocked = blocked_by_parent(gate, by_number, actor)
    blocked_numbers = {item["pr"] for group in blocked for item in group["items"]}

    def skip(pr, code, reason):
        note = pr.get("review_note") if code != "awaiting_refresh" else None
        held = held_reason(client, repository, pr) if code == "awaiting_ci" else None
        sections["not_ready"].append({"pr": pr["number"], "head": pr["head"], "code": code,
                                      "reason": (held or reason) + (f" ({note})" if note else ""), "note": note,
                                      **({"held": True} if held else {})})

    for number in order:
        pr = by_number[number]
        if pr["author"].casefold() == actor.casefold():
            skip(pr, "yours", "is yours")
            continue
        if pr["draft"]:
            skip(pr, "draft", "is a draft")
            continue
        comments = client.comments(repository, number)
        if not isinstance(comments, list):
            raise RecordError("unknown review records")
        mine = my_records(comments, repository, number, actor)
        latest = mine[-1] if mine else None
        carried = None
        if latest and latest[1]["head"] != pr["head"]:
            # Only update-branch merges since your review, with the same change and no review input
            # changed on main: your review is current (carry_over), not a revision to re-review.
            try:
                if main_sha[0] is None:
                    main_sha[0] = client.call(f"repos/{repository}/commits/{project.default_branch}").get("sha")
                result = carry(ApiSource(client, repository), latest[1]["head"], pr["head"], main_sha[0],
                               [latest[1]["tooling_revision"]])
            except (RecordError, AttributeError):
                result = {"carried": False}  # Unknown main: treat the PR as revised (fail closed).
            carried = carry_status(result) if result["carried"] else None
        if latest and (latest[1]["head"] == pr["head"] or carried):
            rubrics = [r for r, v in latest[1]["verdicts"].items() if v in CHANGES]
            if rubrics:
                verb = "blocked" if any(latest[1]["verdicts"][r] == "block" for r in rubrics) else "requested changes"
                replies, contested = since(comments, latest[0]["id"], pr["author"])
                if replies or contested:
                    # The author answered your findings on this same commit: your turn, not theirs.
                    newest = max(replies + contested, key=lambda c: c["id"])
                    parts = [f"you {verb} ({', '.join(rubrics)})"]
                    if replies:
                        parts.append(f"author replied {len(replies)}×")
                    if contested:
                        parts.append(f"{len(contested)} contest{'s' if len(contested) != 1 else ''}")
                    sections["author_replied"].append(entry(
                        "author_replied", pr, observed, "; ".join(parts) + f": {link(repository, number, newest)}",
                        rubrics=rubrics, record_comment=latest[0]["id"], author_replies=len(replies),
                        contests=len(contested), reply_url=link(repository, number, newest)))
                else:
                    sections["waiting_on_author"].append(entry(
                        "waiting_on_author", pr, observed, f"you {verb} ({', '.join(rubrics)}); " +
                        (f"no new change; {carried}" if carried else "no new head"),
                        rubrics=rubrics, record_comment=latest[0]["id"], carried=carried))
                continue
        if number not in ready:
            skip(pr, *readiness(pr))
            if latest:
                # Yours to follow up once its evidence is current: say so instead of hiding it.
                answered, contests_since = since(comments, latest[0]["id"], pr["author"])
                parts = ([f"revised {latest[1]['head'][:7]} → {pr['head'][:7]}"]
                         if latest[1]["head"] != pr["head"] else [])
                parts += [f"author replied {len(answered)}×"] * bool(answered)
                parts += [f"{len(contests_since)} contest(s)"] * bool(contests_since)
                if parts:
                    follow_ups.append({"pr": number, "head": pr["head"],
                                       "reason": f"{sections['not_ready'][-1]['reason']}; " + "; ".join(parts)})
            continue
        if number in blocked_numbers:
            continue  # listed under "Blocked by a parent": review its stack root first
        if latest and latest[1]["head"] != pr["head"] and not carried:
            old = latest[1]["head"]
            count, history = commits_since(client, repository, old, pr["head"])
            answered, contests_since = since(comments, latest[0]["id"], pr["author"])
            replies, contested = len(answered), len(contests_since)
            parts = [f"revised {old[:7]} → {pr['head'][:7]}" +
                     (f", {count} commit{'s' if count != 1 else ''}" if count is not None else "")]
            if history:
                parts.append(history)
            if replies:
                parts.append(f"author replied {replies}×")
            if contested:
                parts.append(f"{contested} contest{'s' if contested != 1 else ''}")
            sections["revised"].append(entry(
                "revised", pr, observed, "; ".join(parts), previous_head=old, commits_since=count,
                history=history, author_replies=replies, contests=contested, record_comment=latest[0]["id"]))
            continue
        state = review_state(client, repository, pr, actor, policy, storage)
        if state:
            done.append({"pr": number, "head": pr["head"], "code": state[0], "reason": state[1]})
            continue
        scope = "ready" if pr["ci"] == pr.get("review_ci", pr["ci"]) else "ready (human-review scope)"
        sections["new"].append(entry("new", pr, observed, scope + "; no review by you"))
    # You get first chance at PRs you reviewed before; within a section, stack roots that block the
    # most descendants first, then the oldest update.
    for name in ("revised", "author_replied", "new", "waiting_on_author"):
        for e in sections[name]:
            e["unblocks"] = gate.descendants(e["pr"])
            # Ready to review, but a fork's workflow runs may still be held (CI never ran): say so.
            pr = by_number[e["pr"]]
            e["held_workflows"] = ([] if pr.get("head_repo") == repository else
                                   held_runs(client, repository, pr["head"]))
            if e["held_workflows"]:
                e["reason"] += f"; CI held, {HELD} ({', '.join(e['held_workflows'])})"
        if name != "new":
            sections[name].sort(key=lambda e: (e["updated_at"], e["pr"]))
        sections[name].sort(key=lambda e: -e["unblocks"])
    sections["not_ready"].sort(key=lambda item: -item["pr"])
    main = None
    if any(i["code"] == "awaiting_refresh" for i in sections["not_ready"]):
        try:
            main = client.call(f"repos/{repository}/commits/{project.default_branch}").get("sha")
        except (RecordError, KeyError, AttributeError):
            main = None
    return {"schema": SCHEMA, "repository": repository, "actor": actor, "observed_at": snapshot["observed_at"],
            "ready_to_merge": ready_to_merge(client, project, policy, snapshot),
            "order": "ready to merge first; then revised, then author replied, then new; oldest update first",
            "sections": sections, "done": done,
            "follow_ups_not_ready": follow_ups, "blocked_by_parent": blocked,
            "main": main, "not_ready_summary": not_ready_summary(sections["not_ready"], main)
            if sections["not_ready"] else None}


def blocked_by_parent(gate, by_number, actor):
    """Stacked PRs whose ancestors are not review-satisfied, grouped by stack root."""
    groups = {}
    for number in sorted(by_number):
        pr = by_number[number]
        if pr["draft"]:
            continue
        waiting = gate.waiting(number)
        if not waiting:
            continue
        blocker, reason = waiting
        info = gate.info[number]
        # A base branch no PR heads has no root PR: group those by the branch instead.
        root = info["root"] if info["chain"] else f"branch {info['base_ref']}"
        groups.setdefault(root, []).append({
            "pr": number, "author": pr["author"], "title": pr["title"], "head": pr["head"],
            "parent": gate.info[number]["parent"], "blocker": blocker, "reason": reason,
            "yours": pr["author"].casefold() == actor.casefold()})
    out = [{"root": root if isinstance(root, int) else None,
            "branch": root[len("branch "):] if isinstance(root, str) else None,
            "root_title": by_number[root]["title"] if root in by_number else None,
            "unblocks": len(items), "items": items} for root, items in groups.items()]
    return sorted(out, key=lambda g: (g["root"] is None, -g["unblocks"], g["root"] or 0, g["branch"] or ""))


def render(report) -> str:
    from .ready_to_merge import render as render_ready
    lines = [f"Review queue for {report['actor']} ({report['repository']}, observed {report['observed_at']})"]
    lines += render_ready(report["ready_to_merge"])
    for name in ("revised", "author_replied", "new", "waiting_on_author"):
        items = report["sections"][name]
        lines.append(f"{TITLES[name]} ({len(items)}):" + ("" if items else " none"))
        for e in items:
            title = e["title"] if len(e["title"]) <= 60 else e["title"][:57] + "..."
            unblocks = f"; unblocks {e['unblocks']} stacked" if e.get("unblocks") else ""
            lines.append(f"  #{e['pr']} {e['author']} \"{title}\" {e['head'][:7]}: {e['reason']}{unblocks}; "
                         f"waiting {waiting(e['waiting_seconds'])}")
    groups = report.get("blocked_by_parent") or []
    count = sum(len(g["items"]) for g in groups)
    lines.append(f"Blocked by a parent ({count}):" + ("" if groups else " none"))
    for g in groups:
        head = f"stack #{g['root']} (unblocks {g['unblocks']})" if g["root"] else f"base branch {g['branch']}"
        lines.append(f"  {head}: " + "; ".join(
            f"#{i['pr']}{' (yours)' if i['yours'] else ''} {i['reason']}" for i in g["items"]))
    if report["follow_ups_not_ready"]:
        lines.append("Your follow-ups, not ready yet: " + "; ".join(
            f"#{f['pr']} {f['reason']}" for f in report["follow_ups_not_ready"]))
    if report["not_ready_summary"]:
        lines.append("Not ready: " + report["not_ready_summary"])
    if report["done"]:
        lines.append("Already reviewed: " + "; ".join(f"#{d['pr']} {d['reason']}" for d in report["done"]))
    return "\n".join(lines)


def add_parser(commands):
    p = commands.add_parser("reviews", help="read-only: PRs ready to merge, then your review queue (revised, "
                                            "author replied, new, waiting on the author)")
    p.add_argument("--json", action="store_true")
    p.add_argument("--quiet", action="store_true", help="no progress lines on stderr")
    p.add_argument("--operator-config", type=Path, help="preferences (default ~/.config/sphereceti/operator.toml)")
    return p


def section_items(report, section):
    """--revised takes your follow-ups (revised, then author replied); --all adds new PRs after them."""
    follow_up = report["sections"]["revised"] + report["sections"]["author_replied"]
    if section == "revised":
        return follow_up
    if section == "all":
        return follow_up + report["sections"]["new"]
    return report["sections"][section]


def spent_today(prefs, project) -> float:
    path = (Path(prefs.storage).expanduser().resolve() / project.repository.replace("/", "__")
            / "engine" / "ledger.json")
    try:
        days = json.loads(path.read_text()).get("days", {})
    except (OSError, ValueError, AttributeError):
        return 0.0
    value = days.get(datetime.now(timezone.utc).strftime("%Y-%m-%d"), 0.0)
    return float(value) if isinstance(value, (int, float)) else 0.0


def stop_reason(report, summary):
    """An execution failure stops the batch; a finding (block, requested changes) does not."""
    if report.get("completion") == "error":
        return f"provider failure on #{report['pr']} ({summary.get('stop') or 'engine error'})"
    if report.get("stop_reason"):
        return f"#{report['pr']}: {report['stop_reason'].replace('_', ' ')}"
    stop = summary.get("stop") or ""
    if stop.startswith("provider"):
        return f"provider failure on #{report['pr']} ({stop})"
    if stop == "budget or round limit reached":
        return f"#{report['pr']}: budget exhausted"
    if (report.get("publication") or {}).get("state") not in (None, "confirmed"):
        return f"#{report['pr']}: publication unconfirmed"
    return None


MOVED = ("review evidence or posting policy changed", "advanced during publication checks")


def outcome(result) -> str:
    verdicts = result.get("verdicts") or {}
    blocked = [r for r, v in verdicts.items() if v == "block"]
    changes = [r for r, v in verdicts.items() if v == "request_changes"]
    if blocked:
        return f"blocked ({', '.join(blocked)})"
    if changes:
        return f"changes ({', '.join(changes)})"
    if result.get("completion") == "complete":
        return "approved"
    if result.get("completion") == "dry_run":
        return "previewed (dry run)"
    return f"incomplete ({result.get('completion')})"


def run_batch(args, project, policy, prefs, *, api=None, client=None, announce=None, run=None, prepare=None,
              approval=None):
    """Review up to --limit distinct PRs from one queue section, one at a time.

    Before each item the queue is surveyed again and the review is bound to the head it selects.
    A finding ends only that PR's review; an execution failure stops the batch.
    """
    from .local_review import posting_note
    from .review_approval import note as approval_note
    from .review_select import check_arguments
    from .review_summary import announcing, summarize
    check_arguments(args)
    section = "revised" if args.revised else "new" if args.new else "all"
    limit = args.limit if args.limit is not None else 1
    if not 1 <= limit <= MAX_LIMIT:
        raise ReviewError(f"--limit must be between 1 and {MAX_LIMIT}")
    say = announce or (lambda line: None)
    budget = args.budget_usd if args.budget_usd is not None else prefs.budget_usd
    output, attempted, initial, untouched = args.output, [], [], []
    items, skipped, stopped = [], [], None
    while len(items) < limit and stopped is None:
        try:
            report = queue(project, policy, prefs, api=api, client=client)  # heads move: survey each time
        except (WorkerError, RecordError) as error:
            stopped = f"GitHub lookup failed: {error}"
            break
        current = section_items(report, section)
        initial = initial if attempted else [e["pr"] for e in current]
        # A PR that left the section since the batch began is skipped with its current reason.
        reasons = {i["pr"]: i["reason"] for name in ("not_ready", "waiting_on_author", "author_replied")
                   for i in report["sections"][name]} | {d["pr"]: d["reason"] for d in report["done"]}
        for number in initial:
            if (number not in attempted and number not in {e["pr"] for e in current}
                    and number not in {s["pr"] for s in skipped}):
                skipped.append({"pr": number, "head": None,
                                "reason": reasons.get(number, "no longer open or eligible")})
        pending = [e for e in current if e["pr"] not in attempted]  # distinct PRs only
        if not pending:
            stopped = "no more PRs in this section"
            break
        if not args.dry_run and budget and spent_today(prefs, project) + args.max_call_cost > budget:
            stopped = "daily budget exhausted"
            untouched = [e["pr"] for e in pending]
            break
        item = pending[0]
        attempted.append(item["pr"])
        say(f"[{len(items) + 1}/{limit}] #{item['pr']} {item['author']} {item['head'][:7]}: {item['reason']}")
        if prepare:  # first-run preferences, asked once, only when a review will really start
            prefs, prepare = prepare(), None
            budget = args.budget_usd if args.budget_usd is not None else prefs.budget_usd
        args.pr = item["pr"]
        if output and len(attempted) > 1:
            args.output = output.with_name(f"{output.name}-pr{item['pr']}")  # --output must be new
        planned = {}
        try:
            # As bare review: the claim guard rechecks the head right before inference and binds it.
            result = run_claimed(args, project, prefs, expect=item, run=run,
                                 wrap=lambda inner: announcing(prefs, announce, planned, inner=inner),
                                 approval=approval() if approval else None)
        except (ClaimRefused, ClaimYielded) as error:
            skipped.append({"pr": item["pr"], "head": item["head"], "reason": str(error).split(": ", 1)[-1]})
            say(f"  skipped #{item['pr']}: {skipped[-1]['reason']}")
            continue
        except (ReviewError, RecordError) as error:
            if "changed since it was selected" in str(error):
                skipped.append({"pr": item["pr"], "head": item["head"], "reason": "moved before review"})
                say(f"  skipped #{item['pr']}: moved before review")
                continue
            if any(text in str(error) for text in MOVED):
                # The head moved during the run: report it, and leave the new revision for later.
                items.append({"pr": item["pr"], "head": item["head"], "section": item["section"],
                              "outcome": "head moved during the review; new revision left for a later run",
                              "output": None, "completion": "moved", "posting": "Not posted: the PR moved.",
                              "posted": None, "plan": planned or None, "summary": None,
                              "approval": None})
                say(f"  #{item['pr']}: head moved during the review; left for a later run")
                continue
            stopped = f"#{item['pr']}: publication unconfirmed ({error})"
            items.append({"pr": item["pr"], "head": item["head"], "section": item["section"],
                          "outcome": "publication unconfirmed", "output": None, "completion": "error",
                          "posting": f"Not posted: {error}", "posted": None, "plan": planned or None,
                          "summary": None, "approval": None})
            untouched = [e["pr"] for e in pending[1:]]
            break
        posting = posting_note(args, result)
        summary = summarize(args, result, posting=posting)
        say(summary["line"])
        say("Next: " + summary["next_action"])
        approved = result.get("approval") or {}
        if approved:
            say(approval_note(approved))
        items.append({"pr": item["pr"], "head": result["head"], "section": item["section"],
                      "outcome": outcome(result) + ("; approval submitted" if approved.get("state") == "submitted"
                                                    else ""),
                      "output": result.get("output"), "completion": result["completion"], "posting": posting,
                      "posted": summary["posted"], "plan": planned or None, "summary": summary,
                      "approval": approved or None})
        stopped = stop_reason(result, summary)
        if stopped:
            untouched = [e["pr"] for e in pending[1:]]
    if stopped is None and len(items) >= limit:
        stopped = f"limit of {limit} reached"
    untouched = untouched[:max(0, limit - len(items))]
    posted = sum(1 for i in items if i["posted"])
    line = (f"Batch ({section}): {len(items)} reviewed, {posted} posted, {len(skipped)} skipped"
            f"; stopped: {stopped}" + (f"; untouched: {', '.join(f'#{n}' for n in untouched)}" if untouched else "")
            + ".")
    lines = [f"  #{i['pr']}: {i['outcome']}" + (f" · {i['posted']}" if i["posted"] else "") for i in items]
    lines += [f"  #{s['pr']}: skipped ({s['reason']})" for s in skipped]
    lines += [f"  #{n}: untouched" for n in untouched]
    return {"schema": BATCH_SCHEMA, "section": section, "limit": limit, "repository": project.repository,
            "items": items, "skipped": skipped, "untouched": untouched, "reviewed": len(items), "posted": posted,
            "stopped": stopped, "line": line, "lines": lines,
            "lookup_failed": bool(stopped and stopped.startswith("GitHub lookup failed")),
            "failed": any(i["completion"] == "error" for i in items)}
