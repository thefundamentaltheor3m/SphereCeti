# SPDX-License-Identifier: Apache-2.0
"""A maintainer's own formal GitHub approval after their all-green `sphereceti review`.

Only for a reviewer listed in the approved policy's `approving_reviewers`, with `approving` on and
the record posted. After the review the record must read back as accepted through the official
reader, and the read-only auto-approval decision must say `would_approve` for the exact head and
base. Only then is one APPROVE review submitted under the maintainer's own account. Nothing here
merges; a separate CI step does that.
"""
from __future__ import annotations

from argparse import Namespace
from contextlib import contextmanager
from pathlib import Path

from .local_review import RUBRICS
from .review_records import RecordError, assess_records, identity

ANNOUNCE = "If all rubrics approve and this PR qualifies, I'll submit your GitHub approval."


def decision(args, project):
    """The read-only `sphereceti auto-approve-check` decision, never hypothetical."""
    from .auto_approval import auto_approval
    options = Namespace(pr=args.pr, assume_proof_paths=None, json=True, source_repo=args.source_repo,
                        dependencies_dir=args.dependencies_dir, operator_config=None,
                        cache_dir=Path("~/.cache/sphereceti/merge-observation"))
    return auto_approval(options, project)


class Approval:
    """Decides applicability before inference (in the review guard) and acts after the review."""

    def __init__(self, project, *, announce=None, decide=decision):
        self.project, self.announce, self.decide = project, announce, decide
        self.reason = "not assessed"
        self.applicable = False
        self.client = self.policy = self.report = self.user = self.author = None

    @contextmanager
    def guard(self, args, report, policy, client):
        self.client, self.policy, self.report = client, policy, report
        self.reason = self.check(args, report, policy, client)
        self.applicable = self.reason is None
        if self.applicable and self.announce:
            self.announce(ANNOUNCE)
        yield None

    def check(self, args, report, policy, client):
        if getattr(args, "no_approve", False):
            return "--no-approve"
        if not args.post:
            return "the review record is not being posted"
        if policy is None or not report.get("tooling_approved"):
            return "approved repository policy is unavailable"
        if not getattr(policy, "approving", False):
            return "approving is off in the approved policy"
        user = client.call("user")
        self.user = identity({"user": user}) if isinstance(user, dict) else None
        if self.user is None or not self.user.startswith("user:"):
            return "your GitHub user identity is unavailable"
        if self.user not in getattr(policy, "approving_reviewers", ()):
            return f"you ({self.user}) are not opted in (approved policy approving_reviewers)"
        pr = client.call(f"repos/{report['repository']}/pulls/{report['pr']}")
        author = (pr.get("user") or {}).get("id") if isinstance(pr, dict) else None
        if type(author) is not int:
            return "the PR author is unknown"
        self.author = f"user:{author}"
        if self.author == self.user:
            return "you are the PR author"
        return None

    def after(self, args, result) -> dict:
        """Never raises: a refused or failed approval leaves the posted review untouched."""
        if not self.applicable:
            return {"state": "not_submitted", "reason": self.reason}
        try:
            return self.submit(args, result)
        except (RecordError, OSError, ValueError, KeyError, TypeError) as error:
            return {"state": "not_submitted", "reason": f"approval evidence unavailable: {error}"}

    def submit(self, args, result):
        report, client, repo, number = self.report, self.client, self.report["repository"], self.report["pr"]
        no = lambda reason, **extra: {"state": "not_submitted", "reason": reason, **extra}
        posted = result.get("publication") or {}
        if posted.get("state") != "confirmed" or posted.get("identity") != self.user:
            return no("the review record was not posted under your identity")
        if result.get("completion") != "complete" or result.get("stop_reason") or \
                any(result.get("verdicts", {}).get(r) != "approve" for r in RUBRICS):
            failing = [r for r in RUBRICS if result.get("verdicts", {}).get(r) != "approve"]
            return no("not all rubrics approve" + (f" ({', '.join(failing)})" if failing else ""))
        # 1. Confirmed readback through the official reader, for the exact head and base.
        comments = client.comments(repo, number)
        outcome = assess_records(comments, report, self.policy,
                                 lambda rev: client.approved_revision(repo, rev, report["tooling"]),
                                 int(self.author.split(":")[1]))
        if (not outcome["review_safe"] or outcome["head"] != report["head"]
                or outcome["selected_comments"].get(self.user) != posted["comment_id"]):
            return no("readback did not accept your record for this head and base: " +
                      ("; ".join(outcome["reasons"]) or "another record is selected"))
        pr = client.call(f"repos/{repo}/pulls/{number}")
        if pr["head"]["sha"] != report["head"] or pr["base"]["sha"] != report["base"]:
            return no("the PR head or base moved after the review")
        # 2. The read-only decision, for the same exact head and base.
        verdict = self.decide(args, self.project)
        if (verdict.get("would_approve") is not True or verdict.get("hypothetical") is not False
                or verdict.get("head") != report["head"] or verdict.get("base") != report["base"]):
            return no("the auto-approval decision refused", decision_reasons=verdict.get("reasons") or
                      ["decision was not for this exact head and base"])
        # 3. Idempotent: an existing APPROVE by you on this head means nothing to write.
        pages = client.call(f"repos/{repo}/pulls/{number}/reviews?per_page=100", paginate=True)
        if not isinstance(pages, list) or not pages or any(not isinstance(p, list) for p in pages):
            raise RecordError("incomplete PR review pages")
        for review in (r for page in pages for r in page):
            if (isinstance(review, dict) and (review.get("user") or {}).get("id") == int(self.user.split(":")[1])
                    and review.get("state") == "APPROVED" and review.get("commit_id") == report["head"]):
                return {"state": "existing", "review_id": review.get("id"), "url": review.get("html_url"),
                        "reason": "you already approved this head"}
        # 4. One formal APPROVE on the exact head. An ambiguous POST is reported, never retried.
        record = f"https://github.com/{repo}/pull/{number}#issuecomment-{posted['comment_id']}"
        body = (f"Approved after an all-green SphereCeti review of {report['head'][:7]} ({record}) "
                "and a passing auto-approval decision. Merging is a separate CI step.")
        try:
            review = client.call(f"repos/{repo}/pulls/{number}/reviews",
                                 payload={"commit_id": report["head"], "event": "APPROVE", "body": body})
        except RecordError as error:
            return no(f"approval submission is unconfirmed ({error}); check the PR before rerunning")
        if (not isinstance(review, dict) or review.get("state") != "APPROVED"
                or review.get("commit_id") != report["head"] or type(review.get("id")) is not int):
            return no("GitHub did not confirm an APPROVE on this head; check the PR before rerunning")
        return {"state": "submitted", "review_id": review["id"], "url": review.get("html_url"),
                "commit_id": report["head"]}


def note(approval) -> str | None:
    if not approval:
        return None
    if approval["state"] == "submitted":
        return f"Approval: submitted {approval.get('url') or approval['review_id']}"
    if approval["state"] == "existing":
        return f"Approval: not submitted: you already approved this head ({approval.get('url')})"
    reasons = approval.get("decision_reasons")
    return f"Approval: not submitted: {approval['reason']}" + (f" ({'; '.join(reasons)})" if reasons else "")
