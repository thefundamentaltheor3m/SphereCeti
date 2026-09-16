"""Authenticated record rules adapted from TauCetiReview's post/scoreboard design.

TauCetiProject/TauCetiReview@afb424eda89e8ac96d9eb69f6a88972055a4cd1b,
runner/post.py and runner/merge_from_scoreboard.py, Apache-2.0, TauCetiReview contributors.
SphereCeti requires API identity and exact evidence; the upstream no-author-bar parser stays inactive.
"""
from __future__ import annotations

import base64
import hashlib
import json
import re

from .local_review import RUBRICS

MARKER = "<!--sphereceti-review:v1 "
CONTEST = "<!--sphereceti-contest:v1 "
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
BINDINGS = ("repository", "pr", "head", "base", "diff_base", "dependency_digest",
            "engine_digest", "effective_rubrics_digest", "installed_tooling_digest",
            "policy_digest", "review_context_digest", "description_digest")
FIELDS = {*BINDINGS, "schema_version", "tooling_revision", "completion", "execution_mode",
          "advisory", "verdicts", "contests_through", "body_sha256", "record_id"}


class RecordError(ValueError):
    pass


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def unique_object(pairs):
    result = {}
    for k, v in pairs:
        if k in result:
            raise RecordError("duplicate record field")
        result[k] = v
    return result


def parse_json(text):
    return json.loads(text, object_pairs_hook=unique_object)


def identity(comment):
    """Use immutable IDs supplied by GitHub, never login strings or the comment body."""
    user = comment.get("user") or {}
    if type(user.get("id")) is not int or user["id"] <= 0:
        return None
    if user.get("type") == "User":
        return f"user:{user['id']}"
    app = comment.get("performed_via_github_app") or {}
    if user.get("type") == "Bot" and type(app.get("id")) is int and app["id"] > 0:
        return f"app:{app['id']}"
    return None


def intact(comment, repository, pr):
    return (type(comment.get("id")) is int and comment["id"] > 0
            and comment.get("issue_url") == f"https://api.github.com/repos/{repository}/issues/{pr}"
            and isinstance(comment.get("created_at"), str) and bool(comment["created_at"])
            and comment.get("updated_at") == comment["created_at"])


def make_record(result):
    """A local record is an attestation proposal. Only API-authenticated publication can qualify."""
    lines = ["# SphereCeti review record", "", "Publication identity is verified from GitHub's API.",
             "This record alone never authorizes a merge.", ""]
    for rubric in RUBRICS:
        review = result.get("reviews", {}).get(rubric, {})
        lines += [f"## {rubric}: {result['verdicts'][rubric]}", "", str(review.get("summary") or ""), ""]
        for finding in review.get("findings") or []:
            lines += [canonical(finding), ""]
    # Provider prose cannot inject another machine marker, including inside code fences.
    body = "\n".join(lines).replace("<", "&lt;").replace(">", "&gt;")
    advisory = not (result["completion"] == "complete" and result["execution_mode"] in ("commit", "manual")
                    and result["tooling_approved"] and result["installed_tooling_matches_T"]
                    and not result["missing_context"] and not result["config_differences"])
    if advisory:
        body = "**Advisory: incomplete, prospective, or missing approved evidence.**\n\n" + body
    record = {k: result[k] for k in BINDINGS}
    record.update(schema_version=1, tooling_revision=result["tooling"],
                  completion=result["completion"], execution_mode=result["execution_mode"],
                  advisory=advisory, verdicts=result["verdicts"],
                  contests_through={r: result.get("reviews", {}).get(r, {}).get("last_reply_seen", 0) or 0
                                    for r in RUBRICS}, body_sha256=sha(body))
    record["record_id"] = sha(canonical(record))
    encoded = base64.b64encode(canonical(record).encode()).decode()
    rendered = MARKER + encoded + "-->\n\n" + body
    if len(rendered.encode()) > 60000:
        raise RecordError("review record exceeds the publication size limit; no truncated record is published")
    return record, rendered


def parse_record(body):
    if not isinstance(body, str) or len(body.encode()) > 60000 or body.count(MARKER) != 1:
        raise RecordError("missing, duplicate, or oversized review marker")
    match = re.fullmatch(re.escape(MARKER) + r"([A-Za-z0-9+/=]+)-->\n\n([\s\S]*)", body)
    if not match:
        raise RecordError("invalid review envelope")
    try:
        record = parse_json(base64.b64decode(match[1], validate=True).decode())
    except (ValueError, UnicodeError) as error:
        raise RecordError("invalid encoded record") from error
    if not isinstance(record, dict) or set(record) != FIELDS or type(record["schema_version"]) is not int or record["schema_version"] != 1:
        raise RecordError("unsupported record schema")
    if type(record["pr"]) is not int or record["pr"] <= 0 or not isinstance(record["repository"], str):
        raise RecordError("invalid repository/PR binding")
    for key in ("head", "base", "diff_base", "tooling_revision"):
        if not isinstance(record[key], str) or not HEX40.fullmatch(record[key]):
            raise RecordError("invalid source revision")
    for key in (*[k for k in BINDINGS if k.endswith("digest")], "body_sha256", "record_id"):
        if not isinstance(record[key], str) or not HEX64.fullmatch(record[key]):
            raise RecordError("invalid evidence digest")
    if (type(record["advisory"]) is not bool or record["completion"] not in ("complete", "partial", "error")
            or record["execution_mode"] not in ("commit", "manual", "reply", "shadow")):
        raise RecordError("invalid completion/mode")
    if not isinstance(record["verdicts"], dict) or set(record["verdicts"]) != set(RUBRICS):
        raise RecordError("incomplete verdict map")
    if any(v not in ("approve", "request_changes", "block", "absent", "error") for v in record["verdicts"].values()):
        raise RecordError("unknown verdict")
    marks = record["contests_through"]
    if not isinstance(marks, dict) or set(marks) != set(RUBRICS) or any(type(v) is not int or v < 0 for v in marks.values()):
        raise RecordError("invalid contest watermarks")
    if record["body_sha256"] != sha(match[2]) or record["record_id"] != sha(canonical({k:v for k,v in record.items() if k != "record_id"})):
        raise RecordError("record or rendered body digest mismatch")
    return record


def contests(comments, records, context, policy, author_id):
    """Only API-identified PR authors/authorized reviewers can contest a known current record."""
    found = []
    for c in comments:
        body = c.get("body", "")
        if not isinstance(body, str) or not body.startswith(CONTEST):
            continue
        match = re.match(re.escape(CONTEST) + r"([^\n]+)-->\n?([\s\S]*)", body)
        if not match or not intact(c, context["repository"], context["pr"]):
            continue
        actor = identity(c)
        if actor not in policy.authorized_reviewers and actor != f"user:{author_id}":
            continue
        try:
            data = parse_json(match[1])
            if (not isinstance(data, dict) or set(data) != {"comment", "record", "rubric"}
                    or type(data["comment"]) is not int):
                continue
            prior = records.get(data["comment"])
            if (not prior or data["rubric"] not in RUBRICS or c["id"] <= prior[0]["id"]
                    or prior[1]["head"] != context["head"] or prior[1]["record_id"] != data["record"]):
                continue
            found.append({"id": c["id"], "rubric": data["rubric"], "record": data["record"],
                          "publisher": identity(prior[0]), "by": actor, "body": match[2]})
        except (ValueError, TypeError, KeyError):
            continue
    return found


def collect_records(comments, context, policy):
    result = {}
    for c in comments:
        if identity(c) not in policy.authorized_reviewers or not intact(c, context["repository"], context["pr"]):
            continue
        try:
            r = parse_record(c.get("body"))
            if r["repository"] == context["repository"] and r["pr"] == context["pr"]:
                result[c["id"]] = (c, r)
        except (ValueError, TypeError):
            continue
    return result


def assess_records(comments, context, policy, approved_revision, author_id):
    """Review evidence only. Scope, trusted CI producer checks, and merging remain separate gates."""
    records = collect_records(comments, context, policy)
    replies = contests(comments, records, context, policy, author_id)
    latest = {}
    for c in sorted(comments, key=lambda c: c.get("id", 0)):
        actor = identity(c)
        if actor not in policy.authorized_reviewers or MARKER not in str(c.get("body", "")):
            continue
        if not intact(c, context["repository"], context["pr"]):
            latest[actor] = (c, None, ["edited or wrong-location record"])
            continue
        try:
            r = parse_record(c.get("body"))
        except (ValueError, TypeError):
            latest[actor] = (c, None, ["malformed authorized record"])
            continue
        if r["repository"] != context["repository"] or r["pr"] != context["pr"] or r["head"] != context["head"]:
            continue
        if r["advisory"] or r["completion"] != "complete" or r["execution_mode"] not in ("commit", "manual"):
            continue  # An advisory run cannot supersede an authorized decision.
        reasons = []
        if not intact(c, context["repository"], context["pr"]):
            reasons.append("edited or wrong-location record")
        reasons += [f"stale {k}" for k in BINDINGS if r[k] != context[k]]
        if not approved_revision(r["tooling_revision"]):
            reasons.append("unapproved tooling revision")
        if any(v != "approve" for v in r["verdicts"].values()):
            reasons.append("review requests changes or lacks an approval")
        if any(mark >= c["id"] for mark in r["contests_through"].values()):
            reasons.append("contest watermark is not older than the record")
        if any(reply["publisher"] == actor and r["contests_through"][reply["rubric"]] < reply["id"] for reply in replies):
            reasons.append("unresolved contest")
        latest[actor] = (c, r, reasons)
    reasons = []
    if not context["tooling_approved"] or not context["installed_tooling_matches_T"] or context["missing_context"] or context["config_differences"]:
        reasons.append("current approved evidence is incomplete")
    if not latest:
        reasons.append("no complete authorized review")
    for actor, (_, _, denied) in latest.items():
        reasons += [actor + ": " + reason for reason in denied]
    return {"review_safe": not reasons, "merge_eligible": False, "reasons": reasons,
            "selected_comments": {actor: item[0]["id"] for actor, item in latest.items()},
            "contests": replies, "repository": context["repository"], "pr": context["pr"], "head": context["head"]}
