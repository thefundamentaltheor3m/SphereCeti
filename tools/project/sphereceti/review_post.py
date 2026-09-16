"""Credential-bearing publication phase; never imported into a provider process.

Adapts TauCetiReview@afb424eda89e8ac96d9eb69f6a88972055a4cd1b runner/post.py's
confirmed-publication discipline (Apache-2.0, TauCetiReview contributors). SphereCeti uses
append-only issue comments, exact-body readback, API identity, and no legacy scoreboard parser.
"""
from __future__ import annotations

import json
import subprocess

from .review_records import RecordError, identity, intact, parse_record


class GitHub:
    def call(self, endpoint, *, payload=None, paginate=False, method=None):
        if method not in (None, "PATCH") or (method and payload is None):
            raise RecordError("unsupported GitHub method")
        command = ["gh", "api", "--hostname", "github.com", endpoint]
        if paginate:
            command += ["--paginate", "--slurp"]
        if payload is not None:
            command += ["--method", method or "POST", "--input", "-"]
        try:
            result = subprocess.run(command, input=json.dumps(payload) if payload is not None else None,
                                    capture_output=True, text=True, timeout=60)
        except (OSError, subprocess.SubprocessError) as error:
            raise RecordError("GitHub operation failed; publication is unconfirmed") from error
        if result.returncode:
            raise RecordError("GitHub operation failed; publication is unconfirmed")
        try:
            value = json.loads(result.stdout)
        except ValueError as error:
            raise RecordError("GitHub returned invalid JSON") from error
        return value

    def comments(self, repository, pr):
        pages = self.call(f"repos/{repository}/issues/{pr}/comments?per_page=100", paginate=True)
        if not isinstance(pages, list) or not pages or any(not isinstance(p, list) for p in pages):
            raise RecordError("incomplete comments response")
        comments = [c for page in pages for c in page]
        if any(not isinstance(c, dict) or type(c.get("id")) is not int for c in comments):
            raise RecordError("invalid comment response")
        if len({c['id'] for c in comments}) != len(comments):
            raise RecordError("duplicate comment pages; refresh before deciding")
        return comments

    def approved_revision(self, repository, revision, current):
        if revision == current:
            return True
        value = self.call(f"repos/{repository}/compare/{revision}...{current}")
        return (value.get("status") in ("ahead", "identical")
                and value.get("merge_base_commit", {}).get("sha") == revision)


def publish(client, rendered, record, policy, revalidate):
    """POST only after final evidence refresh; adoption/readback never trusts body identity.

    A timeout can leave a comment on GitHub. Retrying adopts an exact unedited authorized
    record. Cosmetic duplicates are possible across independent machines; they convey the
    same content ID and cannot clear a contest or change supersession semantics.
    """
    if not policy.posting:
        raise RecordError("posting is disabled by approved repository policy")
    repository, pr = record["repository"], record["pr"]
    existing = client.comments(repository, pr)
    for comment in existing:
        if (comment.get("body") == rendered and identity(comment) in policy.authorized_reviewers
                and intact(comment, repository, pr)):
            revalidate()
            return {"state": "confirmed", "comment_id": comment["id"], "identity": identity(comment),
                    "authorized": True, "adopted": True, "merge_eligible": False}
    revalidate()  # Head/base/context/policy can advance during a provider run or comment scan.
    posted = client.call(f"repos/{repository}/issues/{pr}/comments", payload={"body": rendered})
    if not isinstance(posted, dict) or type(posted.get("id")) is not int:
        raise RecordError("GitHub did not confirm a comment ID")
    comment = client.call(f"repos/{repository}/issues/comments/{posted['id']}")
    if (not isinstance(comment, dict) or comment.get("id") != posted["id"]
            or comment.get("body") != rendered or not intact(comment, repository, pr)):
        raise RecordError("published comment readback did not match; no authenticated receipt")
    if parse_record(comment["body"])["record_id"] != record["record_id"]:
        raise RecordError("published record content changed")
    actor = identity(comment)
    return {"state": "confirmed", "comment_id": comment["id"], "identity": actor,
            "authorized": actor in policy.authorized_reviewers, "adopted": False, "merge_eligible": False}
