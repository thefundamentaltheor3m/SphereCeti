#!/usr/bin/env python3
"""Advisory intention claims on SphereCeti issues labelled `intention`.

Run by .github/workflows/intentions.yml from the default branch with the job's GITHUB_TOKEN
(`issues: write`). `comment` mode handles one `claim`, `claim N weeks` or `unclaim` comment from the
event file; `sweep` mode releases expired claims. Jobs run concurrently: each writes its marker,
re-reads the comments, and the replayed marker order decides (see `fold`), so no command is
dropped and no target is granted twice. Comment text is data only: it is read from the
event JSON, never executed or interpolated into a command. Intentions are advisory coordination for
human contributors and never affect merge eligibility.

The claim/expiry vocabulary follows leanprover-community/intentions as used by
TauCetiProject/TauCetiRoadmap (.github/workflows/intentions.yml at 5879d83); this is an independent
standard-library implementation that needs no Projects board or extra credential.
"""
from __future__ import annotations

from datetime import datetime, timedelta, timezone
import json
import os
import re
import sys
import urllib.request

LABEL = "intention"
MARKER = "<!--sphereceti-intention:v1 "
BOT = "github-actions[bot]"
DEFAULT_DAYS = 30
MAX_DAYS = 90
COMMAND = re.compile(r"(claim|unclaim|disclaim)(?:[ \t]+(.*?))?[ \t.!]*", re.I)
DURATION = re.compile(r"(\d{1,3})[ \t]*(d|days?|w|wks?|weeks?|mo|mths?|months?)", re.I)
UNIT_DAYS = {"d": 1, "w": 7, "m": 30}
MAINTAINERS = ("OWNER", "MEMBER", "COLLABORATOR")  # may release someone else's claim
USAGE = ("Comment `claim` (30 days), `claim 3 weeks` (up to 90 days) or `unclaim` on the first line "
         "of a comment.")
# Headings GitHub renders from .github/ISSUE_TEMPLATE/intention.yml; the keys are the form ids.
FIELDS = {"Target declaration": "target", "Roadmap item or layer": "roadmap_item",
          "Parent PR": "parent_pr", "Intended module": "module", "Expected duration": "duration"}


def parse_duration(text: str) -> int:
    """Days for `3 weeks`, `10d`, `2 months` (a month is 30 days); ValueError otherwise."""
    match = DURATION.fullmatch(text.strip())
    if not match:
        raise ValueError(f"cannot read the duration {text.strip()[:40]!r}")
    days = int(match[1]) * UNIT_DAYS[match[2][0].lower()]
    if not 1 <= days <= MAX_DAYS:
        raise ValueError(f"a claim lasts between 1 and {MAX_DAYS} days")
    return days


def parse_command(body: str):
    """(`claim`, days), (`unclaim`, None), (`invalid`, reason), or None for an ordinary comment."""
    first = (body or "").replace("\r\n", "\n").split("\n", 1)[0].strip()
    match = COMMAND.fullmatch(first)
    if not match:
        return None
    if match[1].lower() in ("unclaim", "disclaim"):
        return ("unclaim", None) if not match[2] else ("invalid", f"`{match[1].lower()}` takes no argument")
    if not match[2]:
        return "claim", DEFAULT_DAYS
    try:
        return "claim", parse_duration(match[2])
    except ValueError as error:
        return "invalid", str(error)


def stamp(moment: datetime) -> str:
    return moment.astimezone(timezone.utc).replace(microsecond=0).strftime("%Y-%m-%dT%H:%M:%SZ")


def trusted(comment) -> bool:
    user = comment.get("user") or {}
    return user.get("login") == BOT and user.get("type") == "Bot"


def markers(comments):
    """(comment, data) for this workflow's markers in comment order; anyone else's are ignored."""
    found = []
    for comment in sorted(comments, key=lambda c: c.get("id", 0)):
        body = comment.get("body") or ""
        if not trusted(comment) or not body.startswith(MARKER) or not isinstance(comment.get("created_at"), str):
            continue
        try:
            data = json.loads(body[len(MARKER):].split("-->", 1)[0])
        except ValueError:
            continue
        if isinstance(data, dict):
            found.append((comment, data))
    return found


def fold(comments):
    """Replay the markers in comment order: the single source of truth for who holds the claim.

    Comment IDs give one total order, so concurrent handlers that each write a marker and then
    re-read agree on the outcome: a claim is accepted only if the target was free, already held by
    the same person, or held by a claim that had expired when the marker was written. A release
    applies only to the current holder, and an expiry only to the exact claim it observed. Returns
    the state and, per marker comment ID, whether it was accepted.
    """
    state = {"holder": None, "expires": None, "marker": None}
    accepted = {}
    for comment, data in markers(comments):
        at, action, ok = comment["created_at"], data.get("action"), False
        if action in ("claim", "renew") and isinstance(data.get("holder"), str) and isinstance(data.get("expires"), str):
            ok = state["holder"] in (None, data["holder"]) or state["expires"] <= at
            if ok:
                state = {"holder": data["holder"], "expires": data["expires"], "marker": comment}
        elif action in ("release", "expire") and state["holder"] and data.get("released") == state["holder"]:
            ok = action == "release" or (data.get("observed") == state["expires"] and state["expires"] <= at)
            if ok:
                state = {"holder": None, "expires": None, "marker": comment}
        accepted[comment["id"]] = ok
    return state, accepted


def describe(state) -> str:
    link = (state.get("marker") or {}).get("html_url")
    return f"{state['holder']} holds it until {state['expires'][:10]}" + (f" ({link})" if link else "")


def reconcile(api, number, state, comments):
    """Make the assignees mirror the marker state: the holder assigned, earlier claimants not."""
    assignees = set(api.issue_assignees(number))
    claimants = {d["holder"] for _, d in markers(comments) if d.get("action") in ("claim", "renew")
                 and isinstance(d.get("holder"), str)}
    for login in sorted((claimants - {state["holder"]}) & assignees):
        api.remove_assignee(number, login)
    if state["holder"] and state["holder"] not in assignees:
        return state["holder"] in api.add_assignee(number, state["holder"])
    return True


def write(api, number, data, text) -> int:
    body = MARKER + json.dumps(data, sort_keys=True, separators=(",", ":")) + "-->\n" + text
    return api.comment(number, body)["id"]


def decide(api, event, now: datetime):
    """Read the live issue and markers; return ("ignored", why), ("reply", outcome, text) or ("write", data, text)."""
    issue, comment = event.get("issue") or {}, event.get("comment") or {}
    user = comment.get("user") or {}
    if issue.get("pull_request") or user.get("type") != "User" or str(user.get("login", "")).endswith("[bot]"):
        return ("ignored", "not a person's comment on an issue")
    command = parse_command(comment.get("body"))
    if command is None:
        return ("ignored", "no command")
    number, login = issue["number"], user["login"]
    live = api.issue(number)  # never the event payload: it may predate a concurrent claim
    if (live.get("pull_request") or live.get("state") != "open"
            or LABEL not in [label.get("name") for label in live.get("labels") or []]):
        return ("ignored", "not an open intention issue")
    if command[0] == "invalid":
        return ("reply", "invalid", f"Not changed: {command[1]}. {USAGE}")
    state, _ = fold(api.comments(number))
    active = state["holder"] and state["expires"] > stamp(now)
    if command[0] == "claim":
        if active and state["holder"] != login:
            return ("reply", "refused", f"Not changed: {describe(state)}. Please coordinate with them here. Intentions "
                             "are advisory, and the claim is released automatically when it expires.")
        expires = stamp(now + timedelta(days=command[1]))
        renew = bool(active)
        return ("write", {"action": "renew" if renew else "claim", "holder": login, "holder_id": user.get("id"),
                          "expires": expires, "comment": comment["id"]},
                f"{login} {'renewed' if renew else 'claimed'} this intention until **{expires[:10]}** (UTC). "
                "Comment `unclaim` to release it earlier. Intentions are advisory and do not affect merging.")
    maintainer = comment.get("author_association") in MAINTAINERS
    if not state["holder"]:
        return ("reply", "refused", "Not changed: this intention is not claimed.")
    if state["holder"] != login and not maintainer:
        return ("reply", "refused", f"Not changed: {describe(state)}. Only the holder or a maintainer can release it.")
    return ("write", {"action": "release", "released": state["holder"], "holder": None, "expires": None,
                      "by": login, "comment": comment["id"]},
            f"{login} released the claim by {state['holder']}. Anyone can comment `claim` to take it.")


def resolve(api, number, plan, marker_id) -> str:
    """After writing, re-read every marker; the replayed order decides, and a loser says so."""
    comments = api.comments(number)
    state, accepted = fold(comments)
    assigned = reconcile(api, number, state, comments)
    data = plan[1]
    if accepted.get(marker_id):
        if data["action"] != "release" and not assigned:
            api.comment(number, "GitHub did not accept the assignment, so the claim is recorded here only.")
        return {"claim": "claimed", "renew": "renewed", "release": "released"}[data["action"]]
    if data["action"] == "release":
        api.comment(number, f"Correction: the release above was not applied, because the claim changed "
                            f"first. {describe(state) if state['holder'] else 'It is not claimed.'}")
    else:
        holds = describe(state) if state["holder"] else "someone else claimed it first"
        api.comment(number, f"Correction: {data['holder']}'s claim above was not recorded, because another "
                            f"claim came first: {holds}. Please coordinate with them here.")
    return "lost"


def handle_comment(api, event, now: datetime) -> str:
    """Apply one comment command; returns what happened (for logs and tests)."""
    plan = decide(api, event, now)
    number = (event.get("issue") or {}).get("number")
    if plan[0] == "ignored":
        return "ignored: " + plan[1]
    if plan[0] == "reply":
        api.comment(number, plan[2])
        return plan[1]
    return resolve(api, number, plan, write(api, number, plan[1], plan[2]))


def sweep(api, now: datetime) -> list:
    """Release expired claims, with the same write-then-replay rule; a racing renewal survives."""
    released = []
    for issue in api.open_intentions():
        number = issue["number"]
        comments = api.comments(number)
        state, _ = fold(comments)
        if not state["holder"] or state["expires"] > stamp(now):
            reconcile(api, number, state, comments)  # heal a drifted assignee mirror
            continue
        marker_id = write(api, number, {"action": "expire", "released": state["holder"], "observed": state["expires"],
                                        "holder": None, "expires": None},
                          f"The claim by {state['holder']} expired on {state['expires'][:10]} and has been released. "
                          "Anyone can comment `claim` to take it; the previous holder can claim it again.")
        comments = api.comments(number)
        after, accepted = fold(comments)
        reconcile(api, number, after, comments)
        if accepted.get(marker_id):
            released.append(number)
        else:
            api.comment(number, f"Correction: the claim was renewed before it could expire, so it was not "
                                f"released: {describe(after)}.")
    return released


def parse_intention(body: str) -> dict:
    """Form fields of an intention issue body, by stable form id; None for an empty answer."""
    fields = {key: None for key in FIELDS.values()}
    parts = re.split(r"^### (.+?)[ \t]*$", (body or "").replace("\r\n", "\n"), flags=re.M)
    for heading, value in zip(parts[1::2], parts[2::2]):
        key = FIELDS.get(heading.strip())
        if key is None:
            continue
        value = value.strip()
        fence = re.fullmatch(r"(`{3,})[^\n]*\n([\s\S]*?)\n?\1", value)
        value = fence[2].strip() if fence else value
        fields[key] = None if value in ("", "_No response_") else value
    return fields


class GitHub:
    """Minimal REST client for the job token; every failure stops the job visibly."""
    def __init__(self, repository: str, token: str):
        self.base = f"https://api.github.com/repos/{repository}"
        self.token = token

    def request(self, method, path, payload=None):
        url = path if path.startswith("https://") else self.base + path
        request = urllib.request.Request(url, method=method, data=None if payload is None else json.dumps(payload).encode(),
                                         headers={"Authorization": f"Bearer {self.token}",
                                                  "Accept": "application/vnd.github+json",
                                                  "X-GitHub-Api-Version": "2022-11-28",
                                                  "User-Agent": "sphereceti-intentions"})
        with urllib.request.urlopen(request, timeout=30) as response:
            text = response.read().decode()
            links = re.findall(r'<([^>]+)>;\s*rel="next"', response.headers.get("Link") or "")
        return (json.loads(text) if text else None), (links[0] if links else None)

    def pages(self, path):
        items, url = [], path
        while url:
            page, url = self.request("GET", url)
            items += page
        return items

    def comments(self, number):
        return self.pages(f"/issues/{number}/comments?per_page=100")

    def comment(self, number, body):
        return self.request("POST", f"/issues/{number}/comments", {"body": body})[0]

    def issue(self, number):
        return self.request("GET", f"/issues/{number}")[0]

    def issue_assignees(self, number):
        return [a.get("login") for a in self.issue(number).get("assignees") or []]

    def add_assignee(self, number, login):
        issue, _ = self.request("POST", f"/issues/{number}/assignees", {"assignees": [login]})
        return [a.get("login") for a in (issue or {}).get("assignees") or []]

    def remove_assignee(self, number, login):
        self.request("DELETE", f"/issues/{number}/assignees", {"assignees": [login]})

    def open_intentions(self):
        return [i for i in self.pages(f"/issues?labels={LABEL}&state=open&per_page=100") if not i.get("pull_request")]


def main(argv) -> int:
    if len(argv) != 2 or argv[1] not in ("comment", "sweep"):
        print("usage: intentions.py comment|sweep", file=sys.stderr)
        return 2
    api = GitHub(os.environ["GITHUB_REPOSITORY"], os.environ["GITHUB_TOKEN"])
    now = datetime.now(timezone.utc)
    if argv[1] == "sweep":
        print("released:", sweep(api, now))
    else:
        with open(os.environ["GITHUB_EVENT_PATH"], encoding="utf-8") as handle:
            print(handle_comment(api, json.load(handle), now))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
