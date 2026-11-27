# SPDX-License-Identifier: Apache-2.0
"""The open queue in one read-only GraphQL pass: survey fields, comments and author ids.

`sphereceti reviews`, bare `review` and batches used to read every PR's comments with its own REST
call. This query returns, per page of open PRs, exactly the fields the survey reads from `gh pr
list --json` (same shapes, so `worker_cli.normalize` is unchanged) and each PR's issue comments
in the REST shape the record readers check (`id`, `user.id/type/login`, `issue_url`,
`created_at`, `updated_at`, `author_association`, `html_url`, `body`).

Fail closed: a PR whose comments exceed one page is marked incomplete, and its comments are read
through REST as before. A queue that changes between pages (a PR appears twice or vanishes from
the count) raises; nothing is guessed.
"""
from __future__ import annotations

from .worker import MAX_PRS, WorkerError, require

PAGE = 50          # PRs per GraphQL page (two pages for today's queue); comment bodies are large
COMMENTS = 100     # comments per PR in the bulk read; more are read through REST

FIELDS = """
        number title updatedAt state isDraft mergeable
        headRefOid baseRefOid baseRefName headRefName
        author { __typename login ... on User { id databaseId name } ... on Bot { id databaseId } }
        headRepository { id name nameWithOwner }
        commits(last: 1) { nodes { commit { statusCheckRollup { contexts(first: 100) { nodes {
          __typename
          ... on StatusContext { context state targetUrl createdAt }
          ... on CheckRun { name status conclusion startedAt completedAt detailsUrl
                            checkSuite { workflowRun { workflow { name } } } }
        } } } } } }"""
COMMENT_FIELDS = """
        number
        comments(first: %d) {
          totalCount
          nodes {
            databaseId body createdAt updatedAt url authorAssociation
            author { __typename login ... on User { databaseId } ... on Bot { databaseId } }
          }
        }""" % COMMENTS


def query(fields):
    return """
query($owner: String!, $name: String!, $cursor: String) {
  viewer { login }
  repository(owner: $owner, name: $name) {
    pullRequests(states: OPEN, first: %d, after: $cursor, orderBy: {field: CREATED_AT, direction: DESC}) {
      totalCount
      pageInfo { hasNextPage endCursor }
      nodes { %s
      }
    }
  }
}
""" % (PAGE, fields)


# GitHub computes mergeability and check rollups slowly; comments come fast. Two queries, read
# side by side, take about as long as the slower one alone.
QUERIES = (query(FIELDS), query(COMMENT_FIELDS))


ZERO_TIME = "0001-01-01T00:00:00Z"  # gh prints an unset time this way (Go's zero time)


def rollup(pr):
    """gh's `statusCheckRollup` JSON: the latest commit's contexts, flattened (gh's string fields
    print null as "")."""
    nodes = (pr.get("commits") or {}).get("nodes") or []
    status = ((nodes[0].get("commit") or {}).get("statusCheckRollup") if nodes else None) or {}
    out = []
    for node in (status.get("contexts") or {}).get("nodes") or []:
        if node.get("__typename") == "StatusContext":
            out.append({"__typename": "StatusContext", "context": node.get("context"),
                        "startedAt": node.get("createdAt") or ZERO_TIME, "state": node.get("state"),
                        "targetUrl": node.get("targetUrl") or ""})
        elif node.get("__typename") == "CheckRun":
            workflow = ((((node.get("checkSuite") or {}).get("workflowRun") or {}).get("workflow") or {})
                        .get("name") or "")
            out.append({"__typename": "CheckRun", "completedAt": node.get("completedAt") or ZERO_TIME,
                        "conclusion": node.get("conclusion") or "", "detailsUrl": node.get("detailsUrl") or "",
                        "name": node.get("name"), "startedAt": node.get("startedAt") or ZERO_TIME,
                        "status": node.get("status"), "workflowName": workflow})
        else:
            out.append(node)  # unknown kinds reach ci_summary, which refuses them as today
    return out


def user(author):
    """The REST `user` object for a GraphQL author (a deleted account is GitHub's `ghost`)."""
    if not author:
        return {"login": "ghost", "id": 10137, "type": "User"}
    kind = author.get("__typename")
    login = author.get("login")
    return {"login": login + "[bot]" if kind == "Bot" and login else login,
            "id": author.get("databaseId"), "type": kind if kind in ("User", "Bot") else kind}


def comment(node, repository, number):
    return {"id": node.get("databaseId"), "body": node.get("body"), "user": user(node.get("author")),
            "issue_url": f"https://api.github.com/repos/{repository}/issues/{number}",
            "html_url": node.get("url"), "created_at": node.get("createdAt"),
            "updated_at": node.get("updatedAt"), "author_association": node.get("authorAssociation")}


def survey_fields(pr):
    """One PR in `gh pr list --json` shape for worker_cli.PR_FIELDS."""
    author = pr.get("author") or {}
    return {"number": pr["number"], "title": pr["title"],
            "author": {"id": author.get("id"), "is_bot": author.get("__typename") == "Bot",
                       # gh lists an app's PRs as `app/<slug>`
                       "login": ("app/" if author.get("__typename") == "Bot" else "") + (author.get("login") or ""),
                       "name": author.get("name") or ""},
            "headRefOid": pr["headRefOid"], "baseRefOid": pr["baseRefOid"], "updatedAt": pr["updatedAt"],
            "state": pr["state"], "isDraft": pr["isDraft"], "mergeable": pr["mergeable"],
            "statusCheckRollup": rollup(pr), "headRepository": pr.get("headRepository"),
            "baseRefName": pr["baseRefName"], "headRefName": pr["headRefName"]}


CHANGED = "the open queue changed during the survey; rerun"


class QueueChanged(WorkerError):
    """The queue moved while it was being read (a PR merged, opened or closed): read it again."""


def changed(condition):
    if not condition:
        raise QueueChanged(CHANGED)


def listing(api, repository, text):
    """(actor, PR nodes, total) from every page of one query; a queue that moves between pages raises."""
    owner, name = repository.split("/")
    cursor, nodes, seen, actor, total = None, [], set(), None, None
    while True:
        args = ["api", "graphql", "--hostname", "github.com", "-f", "query=" + text,
                "-F", f"owner={owner}", "-F", f"name={name}"]
        if cursor:
            args += ["-F", f"cursor={cursor}"]
        page = api.read(args, limit=25_000_000)
        require(isinstance(page, dict) and not page.get("errors") and isinstance(page.get("data"), dict),
                "GitHub survey failed; queue is unknown (no fallback)")
        data = page["data"]
        actor = actor or ((data.get("viewer") or {}).get("login"))
        prs = ((data.get("repository") or {}).get("pullRequests")) or {}
        require(isinstance(prs.get("nodes"), list) and type(prs.get("totalCount")) is int,
                "incomplete open-PR listing; queue is unknown")
        require(prs["totalCount"] <= MAX_PRS, "open queue exceeds 100 PRs or is incomplete; use explicit --pr targeting")
        changed(total in (None, prs["totalCount"]))
        total = prs["totalCount"]
        for pr in prs["nodes"]:
            require(isinstance(pr, dict) and type(pr.get("number")) is int, "incomplete PR observation")
            changed(pr["number"] not in seen)
            seen.add(pr["number"])
            nodes.append(pr)
        info = prs.get("pageInfo") or {}
        if not info.get("hasNextPage"):
            break
        cursor = info.get("endCursor")
        require(isinstance(cursor, str) and cursor, "incomplete open-PR listing; queue is unknown")
    changed(len(nodes) == total)
    require(isinstance(actor, str) and actor, "missing authenticated actor")
    return actor, nodes, total


def fetch(api, repository):
    """(actor login, raw PRs in survey shape, {number: comments or None when incomplete})."""
    from .pool import concurrent, ordered
    (actor, prs, _), (_, listed, _) = ordered(lambda text: listing(api, repository, text), QUERIES,
                                              parallel=concurrent(api))
    changed([p["number"] for p in prs] == [p["number"] for p in listed])
    raw = [survey_fields(pr) for pr in prs]
    comments = {}
    for pr in listed:
        found = pr.get("comments") or {}
        nodes = found.get("nodes")
        complete = (isinstance(nodes, list) and type(found.get("totalCount")) is int
                    and found["totalCount"] == len(nodes)
                    and all(isinstance(n, dict) and type(n.get("databaseId")) is int for n in nodes))
        comments[pr["number"]] = (sorted((comment(n, repository, pr["number"]) for n in nodes),
                                         key=lambda c: c["id"]) if complete else None)
    return actor, raw, comments
