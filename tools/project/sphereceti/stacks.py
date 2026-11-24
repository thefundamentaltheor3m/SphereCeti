# SPDX-License-Identifier: Apache-2.0
"""PR stacks: a PR whose base branch is not the default branch waits for the PR that branch heads.

Review effort goes to stack roots first: a stacked PR is worth reviewing only once every open
ancestor is review-satisfied (an accepted, complete, all-approving record on its current head),
and a root that unblocks more descendants ranks first among equally eligible PRs. Read-only.
"""
from __future__ import annotations

from .local_review import RUBRICS
from .review_records import MARKER, RecordError, identity, intact, parse_record


def stacks(snapshot, project, *, client=None) -> dict:
    """Per open PR: its parent (an open PR, `merged`, or unknown), ancestor chain, root, descendants.

    The parent is the open PR whose head branch is this PR's base branch. Same-repository heads are
    preferred; a fork head with that branch name counts when it is the only candidate. A base branch
    no open PR heads costs one read (closed PRs with that head) to tell a merged parent apart.
    """
    prs = {pr["number"]: pr for pr in snapshot["pull_requests"]}
    default = project.default_branch
    info = {}
    for number, pr in prs.items():
        base = pr.get("base_ref") or default
        entry = {"parent": None, "parent_state": "none", "base_ref": base}
        if base != default:
            candidates = [p for p in prs.values() if p["number"] != number and p.get("head_ref") == base]
            same = [p for p in candidates if p.get("head_repo") == project.repository]
            chosen = same if len(same) == 1 else candidates if len(candidates) == 1 else []
            if chosen:
                entry.update(parent=chosen[0]["number"], parent_state="open")
            elif candidates:
                entry["parent_state"] = "ambiguous"
            else:
                entry["parent_state"] = merged_parent(client, project, base)
        info[number] = entry
    for number, entry in info.items():
        chain, seen, cursor = [], {number}, entry["parent"]
        while cursor is not None and cursor not in seen:
            chain.append(cursor)
            seen.add(cursor)
            cursor = info[cursor]["parent"]
        entry["chain"] = chain  # nearest ancestor first
        entry["root"] = chain[-1] if chain else number
    for number, entry in info.items():
        entry["descendants"] = sum(1 for other in info.values() if number in other["chain"])
    return info


def merged_parent(client, project, branch) -> str:
    """`merged` when a closed PR with that head branch was merged, else `missing`."""
    if client is None:
        return "missing"
    owner = project.repository.split("/")[0]
    pages = client.call(f"repos/{project.repository}/pulls?state=closed&head={owner}:{branch}&per_page=10",
                        paginate=True)
    if not isinstance(pages, list) or any(not isinstance(p, list) for p in pages):
        raise RecordError("incomplete closed-PR listing for a stack parent")
    return "merged" if any(p.get("merged_at") for page in pages for p in page if isinstance(p, dict)) else "missing"


def approvals_on_head(comments, repository, pr, policy):
    """Approving rubrics in the latest accepted record on the PR's current head, or None."""
    latest = None
    for comment in sorted(comments, key=lambda c: c.get("id", 0)):
        body = comment.get("body")
        if (not isinstance(body, str) or MARKER not in body or identity(comment) not in policy.authorized_reviewers
                or not intact(comment, repository, pr["number"])):
            continue
        try:
            record = parse_record(body)
        except (ValueError, TypeError):
            continue
        if (record["repository"] == repository and record["pr"] == pr["number"] and record["head"] == pr["head"]
                and record["completion"] == "complete" and not record["advisory"]
                and record["execution_mode"] in ("commit", "manual")):
            latest = record
    if latest is None:
        return None
    return sum(1 for rubric in RUBRICS if latest["verdicts"].get(rubric) == "approve")


class StackGate:
    """Decides, with cached parent reads, whether a stacked PR waits on an ancestor."""

    def __init__(self, snapshot, project, policy, client, ready):
        self.project, self.policy, self.client, self.ready = project, policy, client, ready
        self.prs = {pr["number"]: pr for pr in snapshot["pull_requests"]}
        self.info = stacks(snapshot, project, client=client)
        self.cache = {}

    def descendants(self, number) -> int:
        return self.info.get(number, {}).get("descendants", 0)

    def satisfied(self, number):
        """None when review-satisfied, else why not: `not ready`, `k/10 on its head`, `no review on its head`."""
        if number not in self.cache:
            pr = self.prs[number]
            if number not in self.ready or pr["draft"]:
                self.cache[number] = "not ready"
            else:
                comments = self.client.comments(self.project.repository, number)
                if not isinstance(comments, list):
                    raise RecordError("unknown review records")
                approved = approvals_on_head(comments, self.project.repository, pr, self.policy)
                self.cache[number] = ("no review on its head" if approved is None else None
                                      if approved == len(RUBRICS) else f"{approved}/{len(RUBRICS)} on its head")
        return self.cache[number]

    def waiting(self, number):
        """(blocking ancestor or None, reason) when this PR waits on its stack, else None."""
        entry = self.info.get(number)
        if not entry or entry["parent_state"] == "none":
            return None
        if entry["parent_state"] == "merged" and not entry["chain"]:
            return None
        if entry["parent_state"] in ("missing", "ambiguous"):
            why = ("several open PRs head that branch" if entry["parent_state"] == "ambiguous"
                   else "no open or merged PR heads it")
            return None, f"waiting on base branch {entry['base_ref']} ({why})"
        for depth, ancestor in enumerate(entry["chain"]):
            reason = self.satisfied(ancestor)
            if reason:
                kind = "parent" if depth == 0 else "ancestor"
                return ancestor, f"waiting on {kind} #{ancestor} ({reason})"
        return None
