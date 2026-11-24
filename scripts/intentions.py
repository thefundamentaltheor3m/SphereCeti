#!/usr/bin/env python3
"""Advisory intention claims on SphereCeti issues labelled `intention`.

Run by .github/workflows/intentions.yml from the default branch with the job's GITHUB_TOKEN
(`issues: write`). `comment` mode handles one `claim`, `claim N weeks` or `unclaim` comment from the
event file; `sweep` mode releases expired claims. Comment text is data only: it is read from the
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


def instant(text: str) -> datetime:
    return datetime.strptime(text, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)


def trusted(comment) -> bool:
    user = comment.get("user") or {}
    return user.get("login") == BOT and user.get("type") == "Bot"


def marker_state(comments):
    """The latest state recorded by this workflow; markers in anyone else's comments are ignored."""
    for comment in sorted(comments, key=lambda c: c.get("id", 0), reverse=True):
        body = comment.get("body") or ""
        if not trusted(comment) or not body.startswith(MARKER):
            continue
        try:
            data = json.loads(body[len(MARKER):].split("-->", 1)[0])
        except ValueError:
            continue
        if isinstance(data, dict):
            return data
    return None


def holder(comments, assignees, now):
    """The current claim, or None. A claim counts while unexpired and its holder is still assigned."""
    state = marker_state(comments)
    if not state or not state.get("holder") or state["holder"] not in assignees:
        return None
    expired = instant(state["expires"]) <= now
    return {**state, "expired": expired}


def record(api, number, data, text):
    api.comment(number, MARKER + json.dumps(data, sort_keys=True, separators=(",", ":")) + "-->\n" + text)


def handle_comment(api, event, now: datetime) -> str:
    """Apply one comment command; returns what happened (for logs and tests)."""
    issue, comment = event.get("issue") or {}, event.get("comment") or {}
    user = comment.get("user") or {}
    if (issue.get("pull_request") or issue.get("state") != "open"
            or LABEL not in [label.get("name") for label in issue.get("labels") or []]):
        return "ignored: not an open intention issue"
    if user.get("type") != "User" or str(user.get("login", "")).endswith("[bot]"):
        return "ignored: not a person"
    command = parse_command(comment.get("body"))
    if command is None:
        return "ignored: no command"
    number, login = issue["number"], user["login"]
    if command[0] == "invalid":
        api.comment(number, f"Not changed: {command[1]}. {USAGE}")
        return "invalid"
    assignees = [a.get("login") for a in issue.get("assignees") or []]
    current = holder(api.comments(number), assignees, now)
    active = current if current and not current["expired"] else None
    if command[0] == "unclaim":
        if not active or active["holder"] != login:
            who = f"it is claimed by {active['holder']}" if active else "it is not claimed"
            api.comment(number, f"Not changed: {who}. Only the person holding a claim can release it; "
                                "a maintainer can also unassign them.")
            return "refused"
        api.remove_assignee(number, login)
        record(api, number, {"action": "release", "holder": None, "expires": None, "comment": comment["id"]},
               f"{login} released this intention. Anyone can comment `claim` to take it.")
        return "released"
    if active and active["holder"] != login:
        api.comment(number, f"Not changed: {active['holder']} holds this intention until "
                            f"{active['expires'][:10]}. Please coordinate with them here. Intentions are "
                            "advisory, and the claim is released automatically when it expires.")
        return "refused"
    if current and current["expired"] and current["holder"] != login:
        api.remove_assignee(number, current["holder"])  # an expiry the daily sweep has not reached yet
    expires = stamp(now + timedelta(days=command[1]))
    assigned = login in api.add_assignee(number, login)
    renewed = bool(active)
    note = "" if assigned else " GitHub did not accept the assignment, so the claim is recorded here only."
    record(api, number, {"action": "renew" if renewed else "claim", "holder": login, "holder_id": user.get("id"),
                         "expires": expires, "comment": comment["id"]},
           f"{login} {'renewed' if renewed else 'claimed'} this intention until **{expires[:10]}** (UTC).{note} "
           "Comment `unclaim` to release it earlier. Intentions are advisory and do not affect merging.")
    return "renewed" if renewed else "claimed"


def sweep(api, now: datetime) -> list:
    """Release every expired claim on open intention issues."""
    released = []
    for issue in api.open_intentions():
        assignees = [a.get("login") for a in issue.get("assignees") or []]
        current = holder(api.comments(issue["number"]), assignees, now)
        if not current or not current["expired"]:
            continue
        api.remove_assignee(issue["number"], current["holder"])
        record(api, issue["number"], {"action": "expire", "holder": None, "expires": None, "released": current["holder"]},
               f"The claim by {current['holder']} expired on {current['expires'][:10]} and has been released. "
               "Anyone can comment `claim` to take it; the previous holder can claim it again.")
        released.append(issue["number"])
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
        self.request("POST", f"/issues/{number}/comments", {"body": body})

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
