# SPDX-License-Identifier: Apache-2.0
"""Advisory "review in progress" claims between contributors.

A posting review announces itself with one PR comment, confirms after posting that no other
contributor's live claim is earlier, and edits that same comment when it finishes. Claims only
avoid duplicate effort: they grant no review or merge authority, need no authorized_reviewers
entry, and are independent of the official worker's leases (worker_leases.py), whose marker,
identity check and post-then-confirm discipline they follow. Each ignores the other's marker.
"""
from __future__ import annotations

from contextlib import contextmanager
from datetime import timedelta
from pathlib import Path
import json
import math
import re
import signal
import sys
import uuid

from .local_review import RUN_TIMEOUT, ReviewError
from .review_records import RecordError, identity
from .review_summary import plan, receipt_runs
from .worker import WorkerError, commit, timestamp
from .worker_cli import load_json
from .worker_leases import stamp, utcnow

MARKER = "<!--sphereceti-review-claim:v1 "
TTL = RUN_TIMEOUT          # one claim covers the review's whole-run deadline (30 minutes)
SLACK = 60                 # tolerated clock difference between a client and GitHub, in seconds
STATES = ("in_progress", "finished", "abandoned", "yielded")
FIELDS = {"repository", "pr", "head", "base", "actor", "login", "claim", "started_at", "expires_at",
          "state", "detail"}
NOTE = "Advisory coordination between contributors; it grants no review or merge authority."


class ClaimRefused(ReviewError):
    """Another contributor's live claim; nothing was posted or spent."""


class ClaimYielded(ReviewError):
    """Our claim lost the race; it was edited to yielded and nothing was spent."""

    def __init__(self, message, winner):
        super().__init__(message)
        self.winner = winner


def clock(value: str) -> str:
    return value[11:16] + " UTC"


def render(data, usage="") -> str:
    who, head = f"@{data['login']}", data["head"][:7]
    text = {"in_progress": f"SphereCeti review in progress by {who} on head {head} "
                           f"(started {clock(data['started_at'])}, expires {clock(data['expires_at'])}).",
            "finished": f"SphereCeti review by {who} on head {head} finished: {data['detail']}",
            "abandoned": f"SphereCeti review by {who} on head {head} abandoned ({data['detail']}).",
            "yielded": f"SphereCeti review by {who} on head {head} yielded to @{data['detail']}."}[data["state"]]
    marker = MARKER + json.dumps(data, sort_keys=True, separators=(",", ":")) + "-->"
    return "\n".join([marker, text, *([usage] if usage else []), "", NOTE])


def final_usage(result, planned):
    """Show model attempts and the estimate for this run only, including retries."""
    runs = receipt_runs(result) if result.get("output") else []
    models = []
    for run in runs:
        for attempt in run.get("attempts") or [run]:
            model = attempt.get("model") or run.get("model")
            if model:
                models.append(f"{run['provider']}/{model}")
    model_text = "Models used: " + ", ".join(dict.fromkeys(models)) if models else planned
    estimate = "unavailable"
    if result.get("output") and not (result.get("engine_exit_code") or result.get("usage_unknown_rubrics")
                                     or result.get("stop_reason") == "usage_unknown"):
        directory = Path(result["output"]) / "engine-archive" / "records" / "rounds" / str(result["pr"])
        files = list(directory.glob("*.json"))
        if len(files) == 1:
            try:
                receipt = json.loads(files[0].read_text())
                cost = receipt["cost"]
                if (receipt["head_sha"] == result["head"] and isinstance(receipt["run_ids"], list)
                        and sorted(receipt["run_ids"]) == sorted(run["run_id"] for run in runs)
                        and all(run.get("cost_usd") is not None and run.get("usage_status") != "unknown"
                                for run in runs)
                        and type(cost) in (int, float) and math.isfinite(cost) and cost >= 0):
                    estimate = f"${cost:.2f}" if cost == 0 or cost >= 0.01 else "under $0.01"
            except (OSError, ValueError, TypeError, KeyError):
                pass
    if estimate != "unavailable" and (result.get("evaluation_request") or {}).get("auth") == "subscription":
        estimate += " (subscription list-price equivalent)"
    return f"{model_text} · Estimated usage cost: {estimate}"


def parse(comment, repository, pr):
    """A well-formed claim whose GitHub comment author is its declared actor, else None."""
    body = comment.get("body") if isinstance(comment, dict) else None
    if not isinstance(body, str) or not body.startswith(MARKER) or len(body) > 4000 or "-->" not in body:
        return None
    try:
        data = load_json(body[len(MARKER):body.index("-->")])
        if not isinstance(data, dict) or set(data) != FIELDS or data["state"] not in STATES:
            return None
        commit(data["head"], "claim head")
        commit(data["base"], "claim base")
        created, updated = timestamp(comment.get("created_at")), timestamp(comment.get("updated_at"))
        started, expires = timestamp(data["started_at"]), timestamp(data["expires_at"])
    except (WorkerError, TypeError, KeyError):
        return None
    if (data["repository"] != repository or data["pr"] != pr or data["actor"] != identity(comment)
            or not isinstance(data["login"], str) or not re.fullmatch(r"[0-9a-f]{32}", str(data["claim"]))
            or not (data["detail"] is None or isinstance(data["detail"], str))):
        return None  # Forged, misplaced or malformed: a claim proves nothing about anyone else.
    login = (comment.get("user") or {}).get("login")
    return {**data, "comment_id": comment["id"], "created": created, "updated": updated,
            "started": started, "expiry": expires,
            "author": login if isinstance(login, str) else data["login"]}


def live(comments, context, now):
    """Unexpired in-progress claims on this head, earliest first (comment ID, then created_at)."""
    if not isinstance(comments, list) or not all(
            isinstance(c, dict) and type(c.get("id")) is int and c["id"] > 0 for c in comments):
        raise RecordError("incomplete comment observation; review claims are unknown")
    if len({c["id"] for c in comments}) != len(comments):
        raise RecordError("duplicate comment observation; review claims are unknown")
    claims = []
    for comment in comments:
        claim = parse(comment, context["repository"], context["pr"])
        # GitHub's updated_at bounds the claimed expiry: no claim can outlive one run.
        if (claim and claim["state"] == "in_progress" and claim["head"] == context["head"]
                and now < claim["expiry"] <= claim["updated"] + timedelta(seconds=TTL + SLACK)):
            claims.append(claim)
    return sorted(claims, key=lambda c: (c["comment_id"], c["created"]))


def left(claim, now) -> str:
    return f"{max(1, math.ceil((claim['expiry'] - now).total_seconds() / 60))} min left"


def describe(claim, now) -> str:
    return f"review in progress by @{claim['author']}, {left(claim, now)}"


class ReviewClaim:
    """Run-scoped claim. `guard` plugs into run_review before any provider call."""

    def __init__(self, project, prefs, *, force=False, expect=None, now=utcnow):
        self.project, self.force, self.expect, self.now = project, force, expect, now
        self.client = self.data = self.comment_id = None
        self.closed = False
        self.prefs = prefs
        self.usage = ""

    @contextmanager
    def guard(self, args, report, policy, client):
        if self.expect and (report["head"] != self.expect["head"] or report["base"] != self.expect["base"]):
            raise ReviewError(f"PR #{report['pr']} changed since it was selected; run `sphereceti review` again")
        if args.post:
            planned = plan(args, self.prefs, report)
            self.models = "Selected model: " + ", ".join(
                f"{p}/{m}" for p, m in zip(planned["providers"], planned["models"]))
            self.usage = f"{self.models} · Estimated usage cost: pending"
            self.claim(report, client)
        yield None

    def comments(self):
        return self.client.comments(self.context["repository"], self.context["pr"])

    def claim(self, report, client):
        self.client = client
        self.context = {k: report[k] for k in ("repository", "pr", "head", "base")}
        user = client.call("user")
        actor = identity({"user": user}) if isinstance(user, dict) else None
        if actor is None or not actor.startswith("user:") or not isinstance(user.get("login"), str):
            raise ReviewError("your GitHub user identity is unavailable; no review claim was posted")
        now = self.now()
        claims = live(self.comments(), self.context, now)
        foreign = [c for c in claims if c["actor"] != actor]
        if foreign and not self.force:
            raise ClaimRefused(f"PR #{report['pr']}: {describe(foreign[0], now)}; "
                               "rerun with --force-claim to review anyway")
        self.data = {**self.context, "actor": actor, "login": user["login"], "claim": uuid.uuid4().hex,
                     "started_at": stamp(now), "expires_at": stamp(now + timedelta(seconds=TTL)),
                     "state": "in_progress", "detail": None}
        own = [c for c in claims if c["actor"] == actor]
        if own:
            # A re-run refreshes your earliest live claim in place: one comment, same position.
            self.comment_id = own[0]["comment_id"]
            self.edit("in_progress", None)
        else:
            body = render(self.data, self.usage)
            posted = client.call(f"repos/{self.context['repository']}/issues/{self.context['pr']}/comments",
                                 payload={"body": body})
            if not isinstance(posted, dict) or type(posted.get("id")) is not int:
                raise RecordError("review claim publication is unconfirmed; nothing was spent")
            self.comment_id = posted["id"]
            seen = client.call(f"repos/{self.context['repository']}/issues/comments/{posted['id']}")
            if not isinstance(seen, dict) or seen.get("body") != body or identity(seen) != actor:
                self.abandon("claim readback mismatch")
                raise RecordError("review claim readback mismatch; nothing was spent")
        # Post, then confirm: concurrent claimants converge on GitHub's earliest comment.
        try:
            claims = live(self.comments(), self.context, self.now())
        except RecordError:
            self.abandon("claims could not be confirmed")
            raise
        if not any(c["comment_id"] == self.comment_id and c["claim"] == self.data["claim"] for c in claims):
            self.abandon("claim not visible after posting")
            raise ReviewError("your review claim was not visible after posting; nothing was spent")
        winner = claims[0]
        if winner["actor"] != actor and not self.force:
            self.usage = f"{self.models} · No model calls"
            self.edit("yielded", winner["author"])
            self.closed = True
            raise ClaimYielded(f"PR #{report['pr']}: yielded to @{winner['author']}, whose claim is earlier; "
                               "nothing was spent", winner)

    def edit(self, state, detail):
        data = {**self.data, "state": state, "detail": detail}
        body = render(data, self.usage)
        seen = self.client.call(f"repos/{self.context['repository']}/issues/comments/{self.comment_id}",
                                payload={"body": body}, method="PATCH")
        if not isinstance(seen, dict) or seen.get("body") != body:
            raise RecordError("claim edit was not confirmed")
        self.data = data

    def close(self, state, detail) -> dict | None:
        if self.comment_id is None or self.closed:
            return None
        self.closed = True
        receipt = {"comment_id": self.comment_id, "state": state, "detail": detail,
                   "url": (f"https://github.com/{self.context['repository']}/pull/{self.context['pr']}"
                           f"#issuecomment-{self.comment_id}"), "expires_at": self.data["expires_at"]}
        try:
            self.edit(state, detail)
            receipt["edit"] = "confirmed"
        except (RecordError, ReviewError, OSError, ValueError) as error:
            receipt.update(edit="failed", reason=str(error) or type(error).__name__)
        return receipt

    def abandon(self, reason) -> dict | None:
        if self.comment_id is not None:
            self.usage = f"{self.models} · Estimated usage cost: unavailable"
        return self.close("abandoned", reason)

    def finish(self, result) -> dict | None:
        if self.comment_id is None:
            return None
        self.usage = final_usage(result, self.models)
        posted = result.get("publication") or {}
        link = (f"https://github.com/{result['repository']}/pull/{result['pr']}"
                f"#issuecomment-{posted['comment_id']}" if posted.get("state") == "confirmed" else None)
        if link and result.get("completion") == "complete" and not result.get("stop_reason"):
            return self.close("finished", link)
        reason = result.get("stop_reason") or (f"review {result.get('completion')}"
                                               if result.get("completion") != "complete" else "record not posted")
        return self.close("abandoned", reason + (f"; partial record {link}" if link else ""))


def note(receipt) -> str | None:
    if not receipt:
        return None
    if receipt["edit"] == "failed":
        return (f"Claim comment {receipt['comment_id']} could not be marked {receipt['state']} "
                f"({receipt['reason']}); it expires on its own at {clock(receipt['expires_at'])}.")
    return f"Claim {receipt['url']} marked {receipt['state']}."


def run_claimed(args, project, prefs, *, expect=None, run=None, wrap=None):
    """run_review with an advisory claim when it will post; abandon on any failure or signal."""
    from .local_review import run_review
    run = run or run_review
    claim = ReviewClaim(project, prefs, force=getattr(args, "force_claim", False), expect=expect)

    def interrupted(signum, frame):
        raise KeyboardInterrupt("review stopped")
    prior = signal.signal(signal.SIGTERM, interrupted)
    try:
        try:
            # `wrap` adds an outer guard (e.g. the plan line) around the claim's own guard.
            result = run(args, project, prefs, guard=wrap(claim.guard) if wrap else claim.guard)
        except BaseException as error:
            receipt = claim.abandon("interrupted" if isinstance(error, KeyboardInterrupt) else
                                    "review failed: " + (str(error) or type(error).__name__)[:200])
            if receipt and receipt["edit"] == "failed":
                print("sphereceti review: " + note(receipt), file=sys.stderr)
            raise
        receipt = claim.finish(result)
        if receipt:
            result["claim"] = receipt
        return result
    finally:
        signal.signal(signal.SIGTERM, prior)
