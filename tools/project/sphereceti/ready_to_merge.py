# SPDX-License-Identifier: Apache-2.0
"""`sphereceti reviews`: open PRs a maintainer can approve and merge now, and the next step for each.

Read-only. A PR is ready to merge when all of these hold:

- its base is the default branch (it is not stacked);
- an accepted official record (authorized, intact, complete, non-advisory, contests answered) by
  someone other than the author approves all ten rubrics on the PR's current head;
- CI passes on the current head apart from the expected `trusted-scope` human-review result (the
  survey's review CI), and every check main's ruleset requires has completed and succeeded there. A
  cancelled run is not done. Workflow runs a fork PR is holding for a maintainer's approval
  ("action_required" on their latest attempt) are reported as such;
- GitHub reports it mergeable: not conflicting, and not blocked by a rule other than the missing
  approval or required check.

The next step is `approve + merge` without a current formal approval of this head by a non-author,
`merge` with one, and `waiting on CI (held: needs maintainer approval)` while runs are held. A PR
with an accepted 10/10 record that fails another condition is listed separately, with the reason.
"""
from __future__ import annotations

from .local_review import RUBRICS
from .review_records import (RecordError, answered, collect_records, contests, directive_contests, identity,
                             published_records)

HELD = "awaiting maintainer approval of workflow runs"
HELD_STEP = "waiting on CI (held: needs maintainer approval)"
DECISIVE = ("APPROVED", "CHANGES_REQUESTED", "DISMISSED")


class Cached:
    """One comments read per PR for the whole listing; other reads pass through unchanged."""

    def __init__(self, client, total=0):
        self.client, self.cache, self.total = client, {}, total

    def comments(self, repository, pr):
        if (repository, pr) not in self.cache:
            self.cache[(repository, pr)] = self.client.comments(repository, pr)
            from .feedback import current as progress
            progress().counter("reading comments", len(self.cache), max(self.total, len(self.cache)))
        return self.cache[(repository, pr)]

    def __getattr__(self, name):
        return getattr(self.client, name)


def pages(value, key):
    """Items from a `--paginate --slurp` listing whose pages are objects holding `key`."""
    if not isinstance(value, list) or not value or any(not isinstance(p, dict) or not isinstance(p.get(key), list)
                                                       for p in value):
        raise RecordError(f"incomplete {key.replace('_', ' ')} listing")
    items = [item for page in value for item in page[key]]
    if any(not isinstance(i, dict) or type(i.get("id")) is not int for i in items):
        raise RecordError(f"invalid {key.replace('_', ' ')} listing")
    return items


def held_runs(client, repository, head) -> list[str]:
    """Workflows whose latest run for this exact head waits for a maintainer to approve it."""
    runs = pages(client.call(f"repos/{repository}/actions/runs?head_sha={head}&per_page=100", paginate=True),
                 "workflow_runs")
    latest = {}
    for run in runs:
        if run.get("head_sha") != head:
            continue
        key = run.get("workflow_id", run.get("name"))
        if run["id"] > latest.get(key, {}).get("id", 0):
            latest[key] = run  # a run reports its latest attempt's status and conclusion
    return sorted(str(r.get("name") or r.get("workflow_id")) for r in latest.values()
                  if "action_required" in (r.get("status"), r.get("conclusion")))


def held_reason(client, repository, pr) -> str | None:
    """For readiness's "awaits CI": the held fork runs on the current head, if any."""
    if pr.get("head_repo") == repository:
        return None  # GitHub holds runs only for pull requests from forks
    held = held_runs(client, repository, pr["head"])
    return f"awaits CI: {HELD} ({', '.join(held)})" if held else None


def required_checks(client, repository, branch) -> list[dict]:
    """The status checks main's rulesets require: [{'context', 'integration_id' or None}]."""
    rules = client.call(f"repos/{repository}/rules/branches/{branch}")
    if not isinstance(rules, list) or any(not isinstance(r, dict) for r in rules):
        raise RecordError("incomplete branch rules")
    found = []
    for rule in rules:
        if rule.get("type") != "required_status_checks":
            continue
        checks = (rule.get("parameters") or {}).get("required_status_checks")
        if not isinstance(checks, list) or any(not isinstance(c, dict) or not isinstance(c.get("context"), str)
                                               for c in checks):
            raise RecordError("invalid required status checks")
        found += [{"context": c["context"], "integration_id": c.get("integration_id")} for c in checks]
    return found


def required_state(client, repository, head, required) -> dict:
    """{context: passed | pending | cancelled | failed | missing} for each required check on the head."""
    if not required:
        return {}
    runs = pages(client.call(f"repos/{repository}/commits/{head}/check-runs?per_page=100", paginate=True),
                 "check_runs")
    statuses = None
    states = {}
    for check in required:
        matching = [r for r in runs if r.get("name") == check["context"] and r.get("head_sha", head) == head
                    and (check["integration_id"] is None or (r.get("app") or {}).get("id") == check["integration_id"])]
        if matching:
            run = max(matching, key=lambda r: r["id"])  # a re-run is a newer check run
            if run.get("status") != "completed":
                states[check["context"]] = "pending"
            else:
                states[check["context"]] = {"success": "passed", "cancelled": "cancelled"}.get(
                    run.get("conclusion"), "failed")
            continue
        if statuses is None:
            statuses = client.call(f"repos/{repository}/commits/{head}/statuses?per_page=100")
            if not isinstance(statuses, list) or any(not isinstance(s, dict) or type(s.get("id")) is not int
                                                     for s in statuses):
                raise RecordError("incomplete commit statuses")
        named = [s for s in statuses if s.get("context") == check["context"]]
        state = max(named, key=lambda s: s["id"]).get("state") if named else None
        states[check["context"]] = ("missing" if state is None else "passed" if state == "success" else
                                    "pending" if state == "pending" else "failed")
    return states


def accepted_record(comments, repository, pr, policy, author_id):
    """(comment, record) of the newest accepted 10/10 record on the current head by a non-author."""
    context = {"repository": repository, "pr": pr["number"], "head": pr["head"]}
    records = collect_records(comments, context, policy)
    replies = contests(comments, records, context, policy, author_id)
    carried = [c for c in directive_contests(comments, published_records(comments, context), context, policy,
                                             author_id) if not answered(c, records)]
    latest = {}
    for cid, (c, r) in sorted(records.items()):
        if (r["head"] != pr["head"] or r["advisory"] or r["completion"] != "complete"
                or r["execution_mode"] not in ("commit", "manual")):
            continue
        latest[identity(c)] = (c, r)
    accepted = []
    for actor, (c, r) in latest.items():
        if actor == f"user:{author_id}" or any(r["verdicts"].get(rubric) != "approve" for rubric in RUBRICS):
            continue
        if any(reply["publisher"] == actor and r["contests_through"][reply["rubric"]] < reply["id"]
               for reply in replies) or any(item["publisher"] == actor for item in carried):
            continue  # an author contest this record has not answered
        accepted.append((c, r))
    return max(accepted, key=lambda item: item[0]["id"]) if accepted else None


def candidate(comments, repository, pr, policy, author_login):
    """Cheap pre-check before any extra read: the newest authorized complete 10/10 record on this
    head by someone whose login is not the author's, or None."""
    context = {"repository": repository, "pr": pr["number"], "head": pr["head"]}
    found = None
    for cid, (c, r) in sorted(collect_records(comments, context, policy).items()):
        login = ((c.get("user") or {}).get("login") or "").casefold()
        if (r["head"] == pr["head"] and not r["advisory"] and r["completion"] == "complete"
                and login != author_login.casefold()
                and all(r["verdicts"].get(rubric) == "approve" for rubric in RUBRICS)):
            found = (c, r)
    return found


def approvals(client, repository, number, head, author_id):
    """Current formal reviews, read as the merge controller reads them: each reviewer's latest
    APPROVED, CHANGES_REQUESTED or DISMISSED review is their state."""
    value = client.call(f"repos/{repository}/pulls/{number}/reviews?per_page=100", paginate=True)
    if not isinstance(value, list) or not value or any(not isinstance(p, list) for p in value):
        raise RecordError("incomplete PR review pages")
    reviews = [r for page in value for r in page]
    if any(not isinstance(r, dict) or type(r.get("id")) is not int or type((r.get("user") or {}).get("id")) is not int
           for r in reviews):
        raise RecordError("invalid PR reviews")
    latest = {}
    for review in sorted(reviews, key=lambda r: r["id"]):
        if review.get("state") in DECISIVE:
            latest[review["user"]["id"]] = review
    current, older, changes = [], [], []
    for user, review in sorted(latest.items()):
        if user == author_id:
            continue
        who = f"user:{user}"
        if review["state"] == "CHANGES_REQUESTED":
            changes.append(who)
        elif review["state"] == "APPROVED":
            entry = {"identity": who, "login": review["user"].get("login"), "review_id": review["id"],
                     "commit_id": review.get("commit_id"), "url": review.get("html_url")}
            (current if review.get("commit_id") == head else older).append(entry)
    return {"on_head": current, "older_heads": older, "changes_requested": changes}


def link(repository, number, comment):
    return comment.get("html_url") or f"https://github.com/{repository}/pull/{number}#issuecomment-{comment['id']}"


def assess(client, project, policy, pr, comments, required):
    """(item, None) when ready to merge, (None, item with `reason`) when not, (None, None) when the PR
    has no accepted 10/10 record on its head."""
    repository, number = project.repository, pr["number"]
    early = candidate(comments, repository, pr, policy, pr["author"])
    if early is None:
        return None, None
    if pr.get("base_ref", project.default_branch) != project.default_branch:
        # Not ready whatever else holds, so no further reads; the record is checked once it is on main.
        return None, {"pr": number, "author": pr["author"], "title": pr["title"], "head": pr["head"],
                      "record": link(repository, number, early[0]), "record_publisher": identity(early[0]),
                      "reason": f"stacked on {pr['base_ref']}; merge its parent first"}
    info = client.call(f"repos/{repository}/pulls/{number}")
    author_id = (info.get("user") or {}).get("id") if isinstance(info, dict) else None
    if type(author_id) is not int or not isinstance(info.get("head"), dict):
        raise RecordError("PR author identity is unavailable")
    if info["head"].get("sha") != pr["head"]:
        return None, {"pr": number, "head": pr["head"], "reason": "the head moved during this listing"}
    found = accepted_record(comments, repository, pr, policy, author_id)
    if found is None:
        return None, None
    c, r = found
    base = {"pr": number, "author": pr["author"], "title": pr["title"], "head": pr["head"],
            "record": link(repository, number, c), "record_publisher": identity(c)}

    def no(reason):
        return None, {**base, "reason": reason}

    if pr["mergeable"] == "CONFLICTING" or info.get("mergeable_state") == "dirty":
        return no("conflicting")
    if pr["mergeable"] != "MERGEABLE" or info.get("mergeable_state") in (None, "unknown"):
        return no("awaits GitHub's mergeability check")
    held = held_runs(client, repository, pr["head"])
    states = required_state(client, repository, pr["head"], required)
    review_ci = pr.get("review_ci", pr["ci"])
    cancelled = sorted(k for k, v in states.items() if v == "cancelled")
    if cancelled:
        return no(f"CI not done: {', '.join(cancelled)} was cancelled on this head; re-run it")
    if review_ci == "failed":
        return no("CI failed on this head")
    unfinished = {k: v for k, v in states.items() if v != "passed"}
    if not held and (review_ci != "passed" or unfinished):
        detail = ", ".join(f"{k} {v}" for k, v in sorted(unfinished.items())) or f"CI {review_ci}"
        return no(f"CI not done on this head ({detail})")
    formal = approvals(client, repository, number, pr["head"], author_id)
    if formal["changes_requested"]:
        return no("changes requested by " + ", ".join(formal["changes_requested"]))
    approved_somewhere = formal["on_head"] or formal["older_heads"]
    if info.get("mergeable_state") == "blocked" and approved_somewhere and not held and not unfinished:
        # Neither the approval nor a required check explains it: another rule, e.g. unresolved threads.
        return no("GitHub reports it blocked by another rule (for example unresolved review threads)")
    step = HELD_STEP if held else "merge" if formal["on_head"] else "approve + merge"
    return {**base, "next_step": step, "approval": formal, "held_workflows": held,
            "required_checks": states, "review_ci": review_ci, "note": pr.get("review_note"),
            "mergeable_state": info.get("mergeable_state")}, None


def ready_to_merge(client, project, policy, snapshot):
    """({'items', 'not_ready'}, required checks). Every read failure raises; nothing is guessed."""
    items, held_back, required = [], [], None
    for pr in sorted(snapshot["pull_requests"], key=lambda p: p["number"]):
        if pr["state"] != "OPEN" or pr["draft"]:
            continue
        comments = client.comments(project.repository, pr["number"])
        if not isinstance(comments, list):
            raise RecordError("unknown review records")
        if candidate(comments, project.repository, pr, policy, pr["author"]) is None:
            continue
        if required is None and pr.get("base_ref", project.default_branch) == project.default_branch:
            required = required_checks(client, project.repository, project.default_branch)
        item, other = assess(client, project, policy, pr, comments, required)
        if item:
            item["yours"] = pr["author"].casefold() == snapshot["actor"].casefold()
            items.append(item)
        elif other:
            held_back.append(other)
    order = {"merge": 0, "approve + merge": 1, HELD_STEP: 2}
    items.sort(key=lambda i: (order[i["next_step"]], i["pr"]))
    return {"items": items, "not_ready": held_back,
            "required_checks": [c["context"] for c in required or []]}


def render(section) -> list[str]:
    items = section["items"]
    lines = [f"Ready to merge ({len(items)}):" + ("" if items else " none")]
    for i in items:
        title = i["title"] if len(i["title"]) <= 60 else i["title"][:57] + "..."
        on_head = i["approval"]["on_head"]
        older = i["approval"]["older_heads"]
        approval = ("approved on this head by " + ", ".join(a["login"] or a["identity"] for a in on_head)
                    if on_head else "no approval on this head" +
                    (f" (older-head approval by {', '.join(a['login'] or a['identity'] for a in older)})"
                     if older else ""))
        held = f" ({', '.join(i['held_workflows'])})" if i["held_workflows"] else ""
        lines.append(f"  #{i['pr']} {i['author']}{' (yours)' if i.get('yours') else ''} \"{title}\" "
                     f"{i['head'][:7]}: {i['next_step']}{held}; {approval}; record {i['record']}")
    if section["not_ready"]:
        lines.append("Accepted 10/10 but not ready to merge: " + "; ".join(
            f"#{i['pr']} {i['reason']}" for i in section["not_ready"]))
    return lines
