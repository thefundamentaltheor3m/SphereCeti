"""Authenticated record rules adapted from TauCetiReview's post/scoreboard design.

TauCetiProject/TauCetiReview@afb424eda89e8ac96d9eb69f6a88972055a4cd1b,
runner/post.py and runner/merge_from_scoreboard.py, Apache-2.0, TauCetiReview contributors.
SphereCeti requires API identity and exact evidence; the upstream no-author-bar parser stays inactive.
The human-visible body follows runner/render.py's scoreboard table, icons and pinned rubric links.
"""
from __future__ import annotations

import base64
import hashlib
import json
import re

from .local_review import RUBRICS, UPSTREAM

MARKER = "<!--sphereceti-review:v1 "
CONTEST = "<!--sphereceti-contest:v1 "
HEX40 = re.compile(r"[0-9a-f]{40}\Z")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
BINDINGS = ("repository", "pr", "head", "base", "diff_base", "dependency_digest",
            "engine_digest", "effective_rubrics_digest", "installed_tooling_digest",
            "policy_digest", "review_context_digest", "description_digest")
FIELDS = {*BINDINGS, "schema_version", "tooling_revision", "completion", "execution_mode",
          "advisory", "verdicts", "contests_through", "body_sha256", "record_id"}
SIZE_LIMIT = 60000  # UTF-8 bytes of a whole record comment; GitHub allows 65536 characters.
RUBRIC_SOURCE = f"https://github.com/TauCetiProject/TauCetiReview/blob/{UPSTREAM}/rubrics/"
ICON = {"approve": "✅", "request_changes": "🟡", "block": "⛔", "error": "⚠️", "absent": "▫️"}
WORD = {"approve": "approved", "request_changes": "changes requested", "block": "blocked",
        "error": "error", "absent": "not run"}
SHORT = {"block": "block", "request_changes": "changes", "error": "error", "absent": "absent"}
FINDING_FIELDS = (("issue", "Issue"), ("fix", "Fix"), ("evidence", "Evidence"))
FIELD_CAPS = (None, 4000, 2000, 1000, 500, 250, 120)  # characters per rendered field, in order
LOCAL_COPY = "the publisher's local `result.json` for this run"
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


# Rendering is presentation only. Readers verify body_sha256 against the published text and
# never re-render it, so records from earlier renderers stay valid with the same schema.
PUNCTUATION = frozenset("!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~")
# GitHub ignores intraword underscores; leaving `_` and `-` keeps archive redaction patterns intact.
PROSE = str.maketrans({**{c: "\\" + c for c in "\\`*[]|~&"}, "<": "&lt;"})
REFERENCE = re.compile(
    r"(?<![\w/.\-])(?:[\w.\-]+/)*[\w\-][\w.\-]*?\.(?:lean|py|md|toml|json|ya?ml|txt|sh)\b"
    r"(?::\d+(?:[-–]\d+)?)?"                         # file or file:line(-line) reference
    r"|(?<![\w@`])@[A-Za-z0-9][\w\-]*(?:/[\w\-]+)?")  # a would-be @mention never notifies
FENCE = re.compile(r" {0,3}(`{3,}|~{3,})[ \t]*([^`\s]*)[^`]*")


def _clean(value):
    text = value if isinstance(value, str) else canonical(value)
    text = text.replace("\r\n", "\n").replace("\r", "\n")
    return re.sub(r"[\x00-\x08\x0b-\x1f\x7f]", "", text)


def _clip(text, cap):
    if cap is None or len(text) <= cap:
        return text, False
    return text[:cap].rstrip() + " …", True


def _code_spans(text):
    """Split one paragraph like CommonMark: backslash escapes, then exact-length backtick spans."""
    out, prose, i, n = [], [], 0, len(text)
    while i < n:
        if text[i] == "\\" and i + 1 < n and text[i + 1] in PUNCTUATION:
            prose.append(text[i + 1])
            i += 2
        elif text[i] == "`":
            j = i
            while j < n and text[j] == "`":
                j += 1
            close = next((m.start() for m in re.finditer(r"`+", text[j:]) if len(m[0]) == j - i), None)
            if close is None:
                prose.append(text[i:j])
                i = j
                continue
            if prose:
                out.append((False, "".join(prose)))
                prose = []
            code = text[j:j + close]
            if len(code) > 2 and code[0] == code[-1] == " " and code.strip():
                code = code[1:-1]
            out.append((True, code))
            i = j + close + (j - i)
        else:
            prose.append(text[i])
            i += 1
    if prose:
        out.append((False, "".join(prose)))
    return out


def code_span(text, table=False):
    """Literal inline code: no entities; the delimiter run never occurs inside the code."""
    runs = {len(r) for r in re.findall(r"`+", text)}
    n = next(k for k in range(1, len(runs) + 2) if k not in runs)
    pad = " " if text[:1] == "`" or text[-1:] == "`" or (text[:1] == text[-1:] == " " and text.strip()) else ""
    if table:
        text = text.replace("|", "\\|")  # GFM splits table cells before parsing code spans
    return "`" * n + pad + text + pad + "`" * n if text else ""


def inline(text, table=False):
    """One Markdown line: provider code stays literal; prose cannot open HTML, links or blocks."""
    out = []
    for is_code, part in _code_spans(re.sub(r"\s*\n\s*", " ", text).strip()):
        if is_code:
            out.append(code_span(part, table))
            continue
        last = 0
        for match in REFERENCE.finditer(part):
            out += [part[last:match.start()].translate(PROSE), code_span(match[0], table)]
            last = match.end()
        out.append(part[last:].translate(PROSE))
    line = "".join(out)
    number = re.match(r"\d{1,9}(?=[.)])", line)
    if number:
        return number[0] + "\\" + line[len(number[0]):]
    return "\\" + line if line[:1] in ("#", ">", "-", "+", "=") else line


def fenced(info, code, indent):
    longest = max((len(r) for r in re.findall(r"`+", code)), default=0)
    fence = "`" * max(3, longest + 1)
    lines = [fence + re.sub(r"[^\w+.\-]", "", info)[:24], *code.split("\n"), fence]
    return "\n".join(indent + line if line else "" for line in lines)


def field(value, cap, indent=""):
    """Paragraphs and fenced code from one provider field, continued at `indent`."""
    text, clipped = _clip(_clean(value), cap)
    chunks, prose, lines, i = [], [], text.split("\n"), 0  # (is_fence, text) pairs
    while i < len(lines):
        opener = FENCE.fullmatch(lines[i])
        if not opener:
            prose.append(lines[i])
            i += 1
            continue
        chunks.append((False, inline("\n".join(prose))))
        prose, code, i = [], [], i + 1
        closer = re.compile(r" {0,3}" + re.escape(opener[1][0]) + "{%d,}[ \t]*" % len(opener[1]))
        while i < len(lines) and not closer.fullmatch(lines[i]):
            code.append(lines[i])
            i += 1
        i += 1
        chunks.append((True, fenced(opener[2], "\n".join(code), indent)))
    chunks.append((False, inline("\n".join(prose))))
    if clipped:
        chunks.append((False, "*(truncated; the full text is in " + LOCAL_COPY + ")*"))
    out = ""
    for is_fence, chunk in (c for c in chunks if c[1]):
        if not out and not (is_fence and indent):
            out = chunk.lstrip(" ")  # the first paragraph continues the caller's line
        else:
            out += "\n\n" + (chunk if is_fence else indent + chunk)
    return out


def first_sentence(text, cap=200):
    text = re.sub(r"\s+", " ", _clean(text)).strip()
    for match in re.finditer(r"[.!?](?=\s+[A-Z0-9`(\[])", text):
        if text.count("`", 0, match.end()) % 2 == 0:
            text = text[:match.end()]
            break
    return _clip(text, cap)[0]


def advisory_reasons(result):
    reasons = []
    if result["completion"] != "complete":
        reasons.append(f"completion is {result['completion']}")
    if result["execution_mode"] not in ("commit", "manual"):
        reasons.append(f"{result['execution_mode']} mode")
    if not result["tooling_approved"]:
        reasons.append("the reviewed tooling is not approved")
    if not result["installed_tooling_matches_T"]:
        reasons.append("installed tooling differs from the approved revision")
    if result["missing_context"]:
        reasons.append("missing approved context: " + ", ".join(map(str, result["missing_context"])))
    if result["config_differences"]:
        reasons.append("candidate configuration differs: " + ", ".join(map(str, result["config_differences"])))
    return reasons or ["missing approved evidence"]


def overall(verdicts):
    approved = sum(verdicts.get(r) == "approve" for r in RUBRICS)
    if approved == len(RUBRICS):
        return f"✅ **All {len(RUBRICS)} rubrics approve.**"
    order = ("block", "request_changes", "error", "absent")
    pending = sorted((r for r in RUBRICS if verdicts.get(r) != "approve"),
                     key=lambda r: order.index(verdicts.get(r)) if verdicts.get(r) in order else len(order))
    items = ", ".join(f"{r} ({SHORT.get(verdicts.get(r), 'unknown')})" for r in pending)
    states = {verdicts.get(r) for r in pending}
    icon, headline = (("⛔", "Changes requested") if "block" in states else
                      ("🟡", "Changes requested") if "request_changes" in states else ("⚠️", "Incomplete"))
    return f"{icon} **{headline}:** {items}. {approved} of {len(RUBRICS)} rubrics approve."


def labelled(text):
    return text if text.startswith("\n") else " " + text


def finding_lines(number, finding, cap):
    if not isinstance(finding, dict):
        return [f"**Finding {number}**", "", "-" + labelled(field(finding, cap, "  ")), ""]
    where = ""
    if finding.get("file"):
        line = finding.get("line")
        where = _clean(finding["file"]) + (f":{_clean(line)}" if line not in (None, "", 0) else "")
        where = " · " + code_span(re.sub(r"\s+", " ", where)[:300])
    lines = [f"**Finding {number}**{where}", ""]
    labels = dict(FINDING_FIELDS)
    extra = sorted(k for k in finding if k not in labels and k not in ("file", "line"))
    for key in [k for k, _ in FINDING_FIELDS] + extra:
        if finding.get(key) not in (None, ""):
            label = labels.get(key) or str(key).translate(PROSE)
            lines.append(f"- **{label}:**" + labelled(field(finding[key], cap, "  ")))
    return lines + [""]


def render_body(result, advisory, cap=None, details=True):
    """Deterministic Markdown for one record: summary, table, then collapsible evidence."""
    verdicts, reviews = result["verdicts"], result.get("reviews") or {}
    lines = ["# SphereCeti review record", ""]
    if advisory:
        lines += ["> [!WARNING]", "> **Advisory record; it cannot count as an authorized review:** "
                  + inline("; ".join(advisory_reasons(result))) + ".", ""]
    lines += [overall(verdicts), "",
              "Publication identity is verified from GitHub's API; only a currently authorized "
              "publisher's record counts. This record alone never authorizes a merge.", "",
              "| | rubric | verdict | summary |", "|---|---|---|---|"]
    for rubric in RUBRICS:
        verdict = verdicts.get(rubric)
        summary = inline(first_sentence((reviews.get(rubric) or {}).get("summary") or ""), table=True)
        lines.append(f"| {ICON.get(verdict, '❔')} | [{rubric}]({RUBRIC_SOURCE}{rubric}.md) | "
                     f"{WORD.get(verdict, inline(str(verdict), table=True))} | {summary or '—'} |")
    shown = [r for r in RUBRICS if (reviews.get(r) or {}).get("summary") or (reviews.get(r) or {}).get("findings")]
    if shown and not details:
        lines += ["", "Reasoning and evidence are omitted to fit GitHub's comment size limit; "
                  f"they are in {LOCAL_COPY}."]
    elif shown:
        lines += ["", "### Details", ""]
        if cap is not None:
            lines += ["Long reasoning and evidence are shortened to fit GitHub's comment size limit; "
                      f"the full text is in {LOCAL_COPY}.", ""]
        for rubric in shown:
            review, verdict = reviews[rubric], verdicts.get(rubric)
            findings = review.get("findings") or []
            count = f" · {len(findings)} finding{'s' if len(findings) != 1 else ''}" if findings else ""
            lines += [f"<details><summary>{ICON.get(verdict, '❔')} <b>{rubric}</b>: "
                      f"{WORD.get(verdict, 'unknown')}{count}</summary>", ""]
            if review.get("summary"):
                lines += [field(review["summary"], cap), ""]
            for number, finding in enumerate(findings, 1):
                lines += finding_lines(number, finding, cap)
            lines += ["</details>", ""]
        lines.pop()
    head, base, repo = result["head"], result["diff_base"], result["repository"]
    revisions = f"head {code_span(str(head)[:7])} against diff base {code_span(str(base)[:7])}"
    if (isinstance(repo, str) and re.fullmatch(r"[\w.\-]+/[\w.\-]+", repo)
            and HEX40.fullmatch(str(head)) and HEX40.fullmatch(str(base))):
        revisions = f"[this diff](https://github.com/{repo}/compare/{base}...{head}) at " + revisions
    lines += ["", f"<sub>Reviewed {revisions} with tooling {code_span(str(result['tooling'])[:7])}; "
              f"completion {inline(str(result['completion']))}, mode {inline(str(result['execution_mode']))}. "
              f"Rubric links credit the pinned TauCetiReview source at {code_span(UPSTREAM[:7])}; "
              "SphereCeti's effective rubrics are bound by the record's `effective_rubrics_digest`.</sub>", ""]
    # Provider text can never form a machine marker, including inside code.
    return "\n".join(lines).replace("<!--", "<!\u200b--")


def make_record(result):
    """A local record is an attestation proposal. Only API-authenticated publication can qualify."""
    advisory = not (result["completion"] == "complete" and result["execution_mode"] in ("commit", "manual")
                    and result["tooling_approved"] and result["installed_tooling_matches_T"]
                    and not result["missing_context"] and not result["config_differences"])
    # Shorten provider fields deterministically, then drop details, until the comment fits.
    for cap, details in [*((cap, True) for cap in FIELD_CAPS), (None, False)]:
        body = render_body(result, advisory, cap, details)
        record = {k: result[k] for k in BINDINGS}
        record.update(schema_version=1, tooling_revision=result["tooling"],
                      completion=result["completion"], execution_mode=result["execution_mode"],
                      advisory=advisory, verdicts=result["verdicts"],
                      contests_through={r: result.get("reviews", {}).get(r, {}).get("last_reply_seen", 0) or 0
                                        for r in RUBRICS}, body_sha256=sha(body))
        record["record_id"] = sha(canonical(record))
        encoded = base64.b64encode(canonical(record).encode()).decode()
        rendered = MARKER + encoded + "-->\n\n" + body
        if len(rendered.encode()) <= SIZE_LIMIT:
            return record, rendered
    raise RecordError("review record exceeds the publication size limit even without details")


def parse_record(body):
    if not isinstance(body, str) or len(body.encode()) > SIZE_LIMIT or body.count(MARKER) != 1:
        raise RecordError("missing, duplicate, or oversized review marker")
    match = re.fullmatch(re.escape(MARKER) + r"([A-Za-z0-9+/=]+)-->\n\n([\s\S]*)", body)
    if not match:
        raise RecordError("invalid review envelope")
    try:
        record = parse_json(base64.b64decode(match[1], validate=True).decode())
    except (ValueError, UnicodeError) as error:
        raise RecordError("invalid encoded record") from error
    validate_metadata(record)
    if record["body_sha256"] != sha(match[2]):
        raise RecordError("rendered body digest mismatch")
    return record


def validate_metadata(record):
    """Check metadata integrity only; neither authenticate a publisher nor verify omitted prose."""
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
    if record["record_id"] != sha(canonical({k:v for k,v in record.items() if k != "record_id"})):
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
