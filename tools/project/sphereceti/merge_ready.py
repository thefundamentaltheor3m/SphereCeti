# SPDX-License-Identifier: Apache-2.0
"""`sphereceti merge-ready`: the human route's merge sweep, as the invoking maintainer.

Candidates are Ready-to-merge PRs (ready_to_merge.py, found through the fast queue path) plus PRs
whose accepted 10/10 record carries over to their current head through update-branch merges
(carry_over.py). They are processed one at a time, stack roots first. For each, everything is read
again fresh (never the queue cache), then:

(a) behind main: `PUT pulls/N/update-branch` pinned to the reviewed head, wait for the new head,
    require that the record carries over to it, and wait (bounded) for its required checks;
(b) approve: one APPROVE pinned to the head, linking the record, unless you already approved this
    head; never on your own PR, never over your own CHANGES_REQUESTED;
(c) merge: `PUT pulls/N/merge`, squash, pinned to the head. A 405 or 409 is re-read and reported,
    never retried;
(d) the next PR is found from a fresh survey, since main has moved.

Before every merge, a live review-in-progress claim on any open PR pauses the sweep (bounded).
Any unexpected error or unconfirmed write stops the whole sweep. Without `--apply` nothing is
written: the plan is printed. Stacked, draft and conflicting PRs are never touched.
"""
from __future__ import annotations

from datetime import datetime, timezone
from pathlib import Path
import subprocess
import time

from .local_review import ReviewError
from .review_records import RecordError
from .worker import WorkerError

SCHEMA = "sphereceti.merge-ready/v1"
CI_POLL = 60          # seconds between required-check reads while waiting for CI
CLAIM_POLL = 60       # seconds between reads while a review is in progress
HEAD_POLL = 5         # seconds between reads while GitHub creates the update-branch merge
HEAD_WAIT = 180       # seconds GitHub gets to create it
UNEXPECTED = (RecordError, WorkerError, ReviewError, OSError, ValueError, KeyError, TypeError, AttributeError,
              subprocess.SubprocessError)


TRUSTED = {"trusted-build", "trusted-scope", "trusted-merge"}  # the trusted run posts all three


def name(check):
    return check.get("name") or check.get("context") or check.get("__typename") or "a check"


def finished(check):
    if check.get("__typename") == "CheckRun":
        return check.get("status") == "COMPLETED"
    return check.get("state") not in ("PENDING", "EXPECTED", None)


def failed(check):
    if check.get("__typename") == "CheckRun":
        return check.get("conclusion") in ("FAILURE", "TIMED_OUT", "CANCELLED", "ACTION_REQUIRED", "STARTUP_FAILURE",
                                           "STALE")
    return check.get("state") in ("FAILURE", "ERROR")


class Skip(Exception):
    """This PR is left alone, with the reason; the sweep goes on."""


class Stop(Exception):
    """The sweep stops here, with the reason; nothing further is written."""


def add_parser(commands):
    p = commands.add_parser("merge-ready", help="maintainers: update, approve and merge ready PRs one at a time "
                                                "(a dry run unless --apply)")
    p.add_argument("--apply", action="store_true", help="act; without it, only print the plan")
    p.add_argument("--limit", type=int, default=5, help="merge at most N PRs (default 5)")
    p.add_argument("--wait-ci", type=float, default=20, metavar="MIN",
                   help="minutes to wait for required checks after updating a branch (default 20)")
    p.add_argument("--wait-review", type=float, default=30, metavar="MIN",
                   help="minutes to wait for an in-progress review before merging (default 30)")
    p.add_argument("--retarget-children", action="store_true",
                   help="change the base of PRs stacked on a merged PR to main (no pushes)")
    p.add_argument("--json", action="store_true")
    p.add_argument("--quiet", action="store_true", help="no progress lines on stderr")
    p.add_argument("--operator-config", type=Path, help="preferences (default ~/.config/sphereceti/operator.toml)")
    return p


def short(sha):
    return (sha or "")[:7]


def minutes(seconds):
    from .feedback import duration
    return duration(seconds)


class Sweep:
    def __init__(self, project, policy, prefs, *, apply=False, limit=5, wait_ci=20, wait_review=30,
                 retarget=False, client=None, reader=None, carry=None, sleep=time.sleep, clock=time.monotonic,
                 now=None):
        from .feedback import current
        from .review_post import GitHub
        from .worker_cli import GitHub as Survey
        self.project, self.policy, self.prefs = project, policy, prefs
        self.apply, self.limit, self.retarget = apply, limit, retarget
        self.wait_ci, self.wait_review = wait_ci * 60, wait_review * 60
        self.client = client or GitHub()
        self.reader = reader or Survey  # a factory: each survey gets a fresh reader (and deadline)
        if carry is None:
            from .carry_over import carry
        self.carry, self.sleep, self.clock = carry, sleep, clock
        self.now = now or (lambda: datetime.now(timezone.utc))
        self.say = current().line
        self.repo, self.main_branch = project.repository, project.default_branch
        self.required = None
        self.me = None
        self.not_ready = []

    # -- reads -------------------------------------------------------------------------------

    def call(self, endpoint, **kwargs):
        return self.client.call(endpoint, **kwargs)

    def pull(self, number):
        info = self.call(f"repos/{self.repo}/pulls/{number}")
        if (not isinstance(info, dict) or not isinstance(info.get("head"), dict) or not isinstance(info.get("base"), dict)
                or type((info.get("user") or {}).get("id")) is not int):
            raise RecordError(f"incomplete pull request #{number}")
        return info

    def main_sha(self):
        value = self.call(f"repos/{self.repo}/commits/{self.main_branch}")
        sha = value.get("sha") if isinstance(value, dict) else None
        if not isinstance(sha, str) or len(sha) != 40:
            raise RecordError("current main is unavailable")
        return sha

    def whoami(self):
        if self.me is None:
            user = self.call("user")
            if not isinstance(user, dict) or type(user.get("id")) is not int or not isinstance(user.get("login"), str):
                raise RecordError("your GitHub identity is unavailable")
            self.me = user
        return self.me

    def discover(self, done):
        """Candidates in queue order (stack roots first), from the fast queue path; never acted on
        before they are read again fresh."""
        from .queue_cache import attach
        from .ready_to_merge import Cached, ready_to_merge
        from .stacks import stacks
        from .worker_cli import survey
        api = self.reader()
        cache = attach(api, self.prefs, self.project, enabled=True)
        client = Cached(self.client, cache=cache)
        snapshot = survey(self.project, None, api=api)
        client.bulk = getattr(api, "queue_comments", None) or {}
        client.total = sum(1 for pr in snapshot["pull_requests"] if pr["state"] == "OPEN" and not pr["draft"])
        section = ready_to_merge(client, self.project, self.policy, snapshot)
        found = {i["pr"]: {"pr": i["pr"], "title": i["title"], "head": i["head"], "record": i["record"],
                           "next_step": i["next_step"]} for i in section["items"]}
        self.not_ready = [{"pr": i["pr"], "reason": i["reason"]} for i in section["not_ready"]]
        listed = found.keys() | {i["pr"] for i in section["not_ready"]}
        for pr in snapshot["pull_requests"]:
            if (pr["number"] in listed or pr["draft"] or pr["state"] != "OPEN"
                    or pr.get("base_ref", self.main_branch) != self.main_branch):
                continue
            carried = self.carried_candidate(client, pr)
            if carried:
                found[pr["number"]] = carried
        if cache is not None:
            cache.save()
        info = stacks(snapshot, self.project, client=client)
        by_number = {pr["number"]: pr for pr in snapshot["pull_requests"]}
        order = sorted((n for n in found if n not in done),
                       key=lambda n: (-info.get(n, {}).get("descendants", 0), by_number[n]["updated_at"], n))
        return [found[n] for n in order], snapshot

    def carried_candidate(self, client, pr):
        """A PR whose newest accepted 10/10 record is on an older head that carries over to this one."""
        from .carry_over import ApiSource, older_records
        from .ready_to_merge import accepted_record, candidate, link
        comments = client.comments(self.repo, pr["number"])
        older = older_records(comments, self.repo, pr["number"], pr["head"])
        head = next((h for h in older if candidate(comments, self.repo, {"number": pr["number"], "head": h},
                                                   self.policy, pr["author"])), None)
        if head is None:
            return None
        author = self.pull(pr["number"])["user"]["id"]
        accepted = accepted_record(comments, self.repo, {"number": pr["number"], "head": head}, self.policy, author)
        if accepted is None:
            return None
        result = self.carry(ApiSource(client, self.repo), head, pr["head"], self.main_sha(),
                            [accepted[1]["tooling_revision"]])
        if not result.get("carried"):
            return None
        return {"pr": pr["number"], "title": pr["title"], "head": pr["head"],
                "record": link(self.repo, pr["number"], accepted[0]), "next_step": "carried", "carried_from": head}

    def record_for(self, number, head, author_id, client):
        """(record link, record head, tooling revision) of an accepted 10/10 record on this head, or on
        an older head that carries over to it; None otherwise. Read fresh."""
        from .carry_over import ApiSource, older_records
        from .ready_to_merge import accepted_record, link
        comments = self.client.comments(self.repo, number)
        found = accepted_record(comments, self.repo, {"number": number, "head": head}, self.policy, author_id)
        if found:
            return link(self.repo, number, found[0]), head, found[1]["tooling_revision"]
        for older in older_records(comments, self.repo, number, head):
            found = accepted_record(comments, self.repo, {"number": number, "head": older}, self.policy, author_id)
            if not found:
                continue
            result = self.carry(ApiSource(client, self.repo), older, head, self.main_sha(),
                                [found[1]["tooling_revision"]])
            if result.get("carried"):
                return link(self.repo, number, found[0]), older, found[1]["tooling_revision"]
            return None
        return None

    def ci(self, number, head):
        """('green' | 'pending' | 'held' | 'failed', detail) for this head.

        Every check on the head must have finished first, not only the required ones: the trusted
        run posts `trusted-scope` (the expected human-review failure) before `trusted-build` and
        `trusted-merge`, and while any check is unfinished the aggregate reads as failed. Once all
        are done the head is judged exactly as Ready to merge judges it: the authenticated scope
        exception is fine, held runs are held, and anything else that failed is named."""
        from .ready_to_merge import held_runs, required_checks, required_state
        from .worker_cli import PR_FIELDS, normalize
        api = self.reader()
        raw = api.read(["pr", "view", str(number), "--repo", "github.com/" + self.repo, "--json", PR_FIELDS])
        if not isinstance(raw, dict) or raw.get("headRefOid") != head:
            moved = raw.get("headRefOid") if isinstance(raw, dict) else None
            raise Skip(f"the head moved to {short(moved)} while its checks were read")
        held = held_runs(self.client, self.repo, head)
        if held:
            return "held", f"workflow runs await a maintainer's approval ({', '.join(held)})"
        if self.required is None:
            self.required = required_checks(self.client, self.repo, self.main_branch)
        states = required_state(self.client, self.repo, head, self.required)
        checks = raw.get("statusCheckRollup") or []
        unfinished = sorted({name(c) for c in checks if not finished(c)}
                            | {k for k, v in states.items() if v in ("pending", "missing")})
        contexts = {c.get("context") for c in checks if c.get("__typename") == "StatusContext"}
        if contexts & TRUSTED:
            unfinished += sorted(f"{context} (not posted yet)" for context in TRUSTED - contexts)
        if unfinished:
            return "pending", ", ".join(unfinished) + " not finished"
        observed = normalize(raw, self.project, api)
        review_ci = observed.get("review_ci", observed["ci"])
        cancelled = sorted(k for k, v in states.items() if v == "cancelled")
        if cancelled:
            return "failed", f"{', '.join(cancelled)} was cancelled"
        failing = sorted({name(c) for c in checks if failed(c)} | {k for k, v in states.items() if v == "failed"})
        if review_ci == "passed":
            return "green", None
        real = [n for n in failing if n != "trusted-scope"]
        if real:
            return "failed", f"{', '.join(real)} failed"
        if review_ci == "failed":
            note = observed.get("review_note")
            return "failed", ("trusted-scope failed and its human-review exception could not be authenticated"
                              + (f" ({note})" if note else ""))
        return "failed", f"CI is {review_ci} with every check finished ({', '.join(failing) or 'no failures'})"

    def reviews(self, number):
        value = self.call(f"repos/{self.repo}/pulls/{number}/reviews?per_page=100", paginate=True)
        if not isinstance(value, list) or not value or any(not isinstance(p, list) for p in value):
            raise RecordError("incomplete PR review pages")
        reviews = [r for page in value for r in page]
        if any(not isinstance(r, dict) or type(r.get("id")) is not int
               or type((r.get("user") or {}).get("id")) is not int for r in reviews):
            raise RecordError("invalid PR reviews")
        latest = {}
        for review in sorted(reviews, key=lambda r: r["id"]):
            if review.get("state") in ("APPROVED", "CHANGES_REQUESTED", "DISMISSED"):
                latest[review["user"]["id"]] = review  # each reviewer's current state, as GitHub reads it
        return latest

    def live_reviews(self):
        """[(PR, description)] of unexpired review-in-progress claims on any open PR, read fresh."""
        from .bulk import fetch
        from .review_claims import describe, live
        api = self.reader()
        _, raw, comments = fetch(api, self.repo)
        now = self.now()
        found = []
        for pr in raw:
            listed = comments.get(pr["number"])
            if listed is None:
                listed = self.client.comments(self.repo, pr["number"])
            claims = live(listed, {"repository": self.repo, "pr": pr["number"], "head": pr["headRefOid"]}, now)
            if claims:
                found.append((pr["number"], describe(claims[0], now)))
        return found

    # -- the sweep ---------------------------------------------------------------------------

    def run(self) -> dict:
        items, children, stopped, done = [], [], None, set()
        merged = 0
        candidates, snapshot = self.discover(done)
        while candidates and merged < self.limit:
            entry = candidates[0]
            done.add(entry["pr"])
            item = {"pr": entry["pr"], "title": entry["title"], "head": entry["head"], "record": entry["record"],
                    "actions": [], "outcome": None, "reason": None}
            items.append(item)
            try:
                self.process(entry, item, snapshot, children)
                merged += item["outcome"] in ("merged", "would merge")
            except Skip as reason:
                item.update(outcome="skipped", reason=str(reason))
                self.say(f"#{entry['pr']} skipped: {reason}")
            except Stop as reason:
                item.update(outcome="stopped", reason=str(reason))
                stopped = str(reason)
                break
            except UNEXPECTED as error:
                stopped = f"unexpected error on #{entry['pr']}: {error or type(error).__name__}; nothing further was written"
                item.update(outcome="stopped", reason=stopped)
                break
            if self.apply and item["outcome"] == "merged":
                try:
                    candidates, snapshot = self.discover(done)  # main moved: the rest may now be behind
                except UNEXPECTED as error:
                    stopped = f"the queue could not be read again after merging #{entry['pr']}: {error}"
                    break
            else:
                candidates = candidates[1:]
        counts = {k: sum(1 for i in items if k in i["actions"]) for k in ("updated", "approved")}
        counts["merged"] = sum(1 for i in items if i["outcome"] == "merged")
        counts["planned"] = sum(1 for i in items if i["outcome"] == "would merge")
        counts["skipped"] = sum(1 for i in items if i["outcome"] == "skipped")
        return {"schema": SCHEMA, "repository": self.repo, "apply": self.apply, "limit": self.limit,
                "items": items, "children": children, "stopped": stopped, "counts": counts,
                "not_ready": [i for i in self.not_ready if i["pr"] not in done],
                "observed_at": self.now().strftime("%Y-%m-%dT%H:%M:%SZ")}

    def process(self, entry, item, snapshot, children):
        from .ready_to_merge import Cached
        number = entry["pr"]
        client = Cached(self.client)  # immutable commit facts for this PR's carry-over; nothing stored
        if entry.get("next_step") == "waiting on CI (held: needs maintainer approval)":
            raise Skip("its workflow runs await a maintainer's approval in GitHub; approve them, then rerun")
        info = self.pull(number)
        head = info["head"].get("sha")
        if info.get("state") != "open" or info.get("merged"):
            raise Skip("no longer open")
        if info.get("draft"):
            raise Skip("is a draft")
        if info["base"].get("ref") != self.main_branch:
            raise Skip(f"stacked on {info['base'].get('ref')}; merge its parent first")
        if head != entry["head"]:
            raise Skip(f"the head moved since the listing ({short(entry['head'])} → {short(head)}); rerun")
        if info.get("mergeable") is False or info.get("mergeable_state") == "dirty":
            raise Skip("conflicting")
        author_id = info["user"]["id"]
        me = self.whoami()
        record = self.record_for(number, head, author_id, client)
        if record is None:
            raise Skip("no accepted 10/10 record on this head, or one that carries over to it")
        link, record_head, tooling = record
        item["record"] = link
        main = self.main_sha()
        compare = self.call(f"repos/{self.repo}/compare/{main}...{head}")
        behind = compare.get("behind_by") if isinstance(compare, dict) else None
        if type(behind) is not int:
            raise RecordError(f"incomplete compare of #{number} with main")
        if behind:
            if not self.apply:
                item["actions"].append("would update")
                self.say(f"#{number}: would update the branch ({behind} behind main), wait for CI and check "
                         "that the record carries over")
                item.update(outcome="would merge", reason=f"after updating the branch ({behind} behind main)")
                return self.plan_tail(number, head, author_id, me, item, provisional=True)
            head = self.update(number, head, record_head, tooling, client, item)
        else:
            state, detail = self.ci(number, head)
            if state != "green":
                raise Skip({"pending": f"CI not done on {short(head)} ({detail})", "held": detail,
                            "failed": f"CI on {short(head)}: {detail}"}[state])
        if not self.apply:
            return self.plan_tail(number, head, author_id, me, item)
        self.approve(number, head, author_id, me, link, record_head, item)
        self.wait_for_reviews(number)
        self.merge(number, head, item)
        self.stacked_children(number, info["head"].get("ref"), snapshot, children)

    def plan_tail(self, number, head, author_id, me, item, provisional=False):
        latest = self.reviews(number)
        decision = self.approval_decision(latest, head, author_id, me)
        if decision == "approve":
            item["actions"].append("would approve")
        item["actions"].append("would merge")
        live = self.live_reviews()
        if live:
            item["actions"].append(f"would wait: review in progress on #{live[0][0]}")
        item["outcome"] = "would merge"
        steps = ("update, approve and merge" if provisional and decision == "approve" else
                 "update and merge" if provisional else "approve and merge" if decision == "approve" else "merge")
        self.say(f"#{number} {short(head)}: would {steps}" + (f" (after #{live[0][0]}'s review finishes)" if live else ""))

    def approval_decision(self, latest, head, author_id, me):
        """'approve', 'approved' (nothing to write), or raises Skip with the reason."""
        others = [f"user:{u}" for u, r in latest.items()
                  if u not in (author_id, me["id"]) and r.get("state") == "CHANGES_REQUESTED"]
        if others:
            raise Skip(f"changes requested by {', '.join(others)}")
        if me["id"] == author_id:
            if not any(u != author_id and r.get("state") == "APPROVED" and r.get("commit_id") == head
                       for u, r in latest.items()):
                raise Skip(f"your own PR: it needs another maintainer's approval of {short(head)}")
            return "approved"
        mine = latest.get(me["id"])
        if mine and mine.get("state") == "CHANGES_REQUESTED":
            raise Skip("you requested changes on this PR; resolve or dismiss that review first")
        if mine and mine.get("state") == "APPROVED" and mine.get("commit_id") == head:
            return "approved"
        return "approve"

    def update(self, number, head, record_head, tooling, client, item):
        from .carry_over import ApiSource, describe
        from .review_claims import describe as claim, live
        comments = self.client.comments(self.repo, number)
        claims = live(comments, {"repository": self.repo, "pr": number, "head": head}, self.now())
        if claims:
            raise Skip(f"a review of this head is in progress ({claim(claims[0], self.now())}); rerun later")
        self.say(f"#{number}: updating the branch from main (pinned to {short(head)})…")
        from .review_post import HTTPError
        try:
            self.call(f"repos/{self.repo}/pulls/{number}/update-branch", payload={"expected_head_sha": head},
                      method="PUT")
        except HTTPError as error:
            if error.status == 422 and self.pull(number)["head"].get("sha") != head:
                raise Skip("the head moved before the update; rerun") from error
            raise Stop(f"update-branch of #{number} failed (HTTP {error.status}); nothing further was written") from error
        began = self.clock()
        while True:
            new = self.pull(number)["head"].get("sha")
            if new != head:
                break
            if self.clock() - began >= HEAD_WAIT:
                raise Stop(f"update-branch of #{number} was not confirmed: the head is still {short(head)}")
            self.sleep(HEAD_POLL)
        item["actions"].append("updated")
        item["updated_head"] = new
        self.say(f"#{number} updated: {short(head)} → {short(new)}")
        result = self.carry(ApiSource(client, self.repo), record_head, new, self.main_sha(), [tooling])
        if not result.get("carried"):
            raise Skip(f"needs a fresh review after update ({describe(result)})")
        began = self.clock()
        while True:
            state, detail = self.ci(number, new)
            if state == "green":
                self.say(f"#{number}: required checks passed on {short(new)} after {minutes(self.clock() - began)}")
                return new
            if state in ("failed", "held"):
                raise Skip(f"CI on the updated head {short(new)}: {detail}")
            waited = self.clock() - began
            if waited >= self.wait_ci:
                raise Skip(f"CI still running on {short(new)} after {minutes(waited)} ({detail}); rerun later")
            self.say(f"  #{number}: waiting for CI on {short(new)} ({detail}; {minutes(waited)} so far)")
            self.sleep(min(CI_POLL, max(1, self.wait_ci - waited)))

    def approve(self, number, head, author_id, me, link, record_head, item):
        decision = self.approval_decision(self.reviews(number), head, author_id, me)
        if decision != "approve":
            return
        if self.pull(number)["head"].get("sha") != head:
            raise Skip("the head moved before the approval; rerun")
        note = (f" (carried over from {short(record_head)} through update-branch merges)"
                if record_head != head else "")
        body = (f"Approving {short(head)}: the official review record {link} approves all ten rubrics"
                f"{note}. Submitted by `sphereceti merge-ready`.")
        posted = self.call(f"repos/{self.repo}/pulls/{number}/reviews",
                           payload={"commit_id": head, "event": "APPROVE", "body": body})
        if not isinstance(posted, dict) or posted.get("state") != "APPROVED" or posted.get("commit_id") != head:
            raise Stop(f"the approval of #{number} was not confirmed; check the PR before rerunning")
        item["actions"].append("approved")
        item["approval"] = posted.get("html_url")
        self.say(f"#{number} approved {short(head)}" + (f": {posted['html_url']}" if posted.get("html_url") else ""))

    def wait_for_reviews(self, number):
        """Never merge (and so move main) under a review in progress anywhere: pause, bounded."""
        began = self.clock()
        while True:
            live = self.live_reviews()
            if not live:
                return
            waited = self.clock() - began
            if waited >= self.wait_review:
                raise Stop(f"a review is in progress on #{live[0][0]}; rerun later")
            self.say(f"  before merging #{number}: a review is in progress on #{live[0][0]} ({live[0][1]}); "
                      f"waiting ({minutes(waited)} so far)")
            self.sleep(min(CLAIM_POLL, max(1, self.wait_review - waited)))

    def merge(self, number, head, item):
        from .review_post import HTTPError
        info = self.pull(number)
        if info["head"].get("sha") != head:
            raise Skip("the head moved before the merge; rerun")
        try:
            merged = self.call(f"repos/{self.repo}/pulls/{number}/merge",
                               payload={"merge_method": "squash", "sha": head}, method="PUT")
        except HTTPError as error:
            if error.status in (405, 409):
                now = self.pull(number)
                state = ("merged" if now.get("merged") else f"head {short(now['head'].get('sha'))}, "
                         f"mergeable state {now.get('mergeable_state')}")
                raise Skip(f"GitHub refused the merge (HTTP {error.status}); now: {state}") from error
            raise Stop(f"the merge of #{number} is unconfirmed (HTTP {error.status}); check the PR") from error
        confirmed = self.pull(number)
        if not (isinstance(merged, dict) and merged.get("merged") is True and confirmed.get("merged") is True):
            raise Stop(f"the merge of #{number} is unconfirmed; check the PR")
        item.update(outcome="merged", merge_commit=merged.get("sha") or confirmed.get("merge_commit_sha"))
        self.say(f"#{number} merged as {short(item['merge_commit'])}")

    def stacked_children(self, number, branch, snapshot, children):
        for pr in snapshot["pull_requests"]:
            if pr.get("base_ref") != branch or pr["number"] == number or pr["state"] != "OPEN":
                continue
            now = self.pull(pr["number"])
            child = {"pr": pr["number"], "parent": number, "branch": branch, "retargeted": False}
            if now["base"].get("ref") == self.main_branch:
                child["note"] = "GitHub already retargeted it to main"
            elif self.retarget:
                changed = self.call(f"repos/{self.repo}/pulls/{pr['number']}", payload={"base": self.main_branch},
                                    method="PATCH")
                if not isinstance(changed, dict) or (changed.get("base") or {}).get("ref") != self.main_branch:
                    raise Stop(f"retargeting #{pr['number']} to {self.main_branch} was not confirmed")
                child["retargeted"] = True
                child["note"] = f"retargeted to {self.main_branch}"
            else:
                child["note"] = f"retarget to {self.main_branch} (or rerun with --retarget-children)"
            children.append(child)
            self.say(f"#{pr['number']} is stacked on #{number} (now merged): {child['note']}")


def render(report) -> list[str]:
    mode = "applied" if report["apply"] else "dry run: nothing was written"
    lines = [f"Merge-ready sweep ({mode}; at most {report['limit']} merges)"]
    if not report["items"]:
        lines.append("  No open PR is ready to merge: none has an accepted 10/10 record on its head (or one "
                     "that carries over), green CI and a clean merge.")
    for item in report["items"]:
        if item["outcome"] == "skipped":
            lines.append(f"  #{item['pr']} skipped: {item['reason']}")
        elif item["outcome"] == "stopped":
            lines.append(f"  #{item['pr']} stopped: {item['reason']}")
        else:
            steps = [a for a in item["actions"]] + ([] if item["outcome"] == "would merge" else [item["outcome"]])
            lines.append(f"  #{item['pr']} {short(item.get('updated_head') or item['head'])}: " + ", ".join(steps)
                         + (f" ({item['reason']})" if item.get("reason") else "") + f"; record {item['record']}")
    for child in report["children"]:
        lines.append(f"  #{child['pr']} is stacked on #{child['parent']} (now merged): {child['note']}")
    if report["not_ready"]:
        lines.append("  Accepted 10/10 but not mergeable: " + "; ".join(
            f"#{i['pr']} {i['reason']}" for i in report["not_ready"]))
    c = report["counts"]
    parts = ([f"{c['merged']} merged", f"{c['updated']} updated", f"{c['approved']} approved"] if report["apply"]
             else [f"{c['planned']} would merge"]) + [f"{c['skipped']} skipped"]
    lines.append("Summary: " + ", ".join(parts) + (f"; stopped: {report['stopped']}" if report["stopped"] else ""))
    return lines
