"""The two generated file formats, and the validators the merge gate runs on them.

`STATUS.md` is a snapshot: rewritten whole on every update, headed by the commit it describes.
`PROGRESS.md` is an append-only log of windows, each section headed by the commit range it covers.

Both carry a machine-readable HTML-comment header followed by prose, following the
`tauceti-<kind>:v1 {json}` convention the rest of the project already uses for scoreboards and
target markers.

Everything here is pure: it takes and returns text, touches no network and no filesystem. That
matters because the merge gate in CI runs these same functions on an untrusted PR's blobs, and it
is the only thing standing between a model and a human-owned repository. The gate proves *shape*,
never truth -- see the trust-boundary section of README.md.
"""

import json
import re

# Marker names are part of the wire format; the gate rejects a model that emits any of them
# inside its prose, so bumping a version here is a coordinated change with the gate.
STATUS_MARKER = "tauceti-status:v1"
PROGRESS_MARKER = "tauceti-progress:v1"

# Any `tauceti-*:vN` marker at all. Model prose is checked against this, not just against the two
# markers above: prose that forges a *scoreboard* or *target* marker is equally unwanted, and a
# file that grows a second status header would confuse every later parse of it.
RESERVED_MARKER_RE = re.compile(r"<!--\s*tauceti-[a-z-]+:v\d+")

_HEADER_RE = re.compile(r"<!--\s*(tauceti-[a-z-]+:v\d+)\s*(\{.*?\})\s*-->", re.S)

# A short SHA is ambiguous and a 40-hex SHA is not, so the formats store full ones and abbreviate
# only for display.
_SHA_RE = re.compile(r"\A[0-9a-f]{40}\Z")

# Caps exist so a runaway model cannot commit a megabyte of prose, and so the gate's own work is
# bounded. A window's section is meant to be a few paragraphs; STATUS is a page.
MAX_STATUS_BYTES = 64 * 1024
MAX_SECTION_BYTES = 32 * 1024
MAX_PROGRESS_BYTES = 4 * 1024 * 1024

# STATUS is a selective snapshot, not a declaration inventory. The writing prompt targets 750
# words; this is a slightly larger fail-closed backstop so a modest overshoot can still land while
# the multi-thousand-word catalogues the old prompt produced cannot.
MAX_STATUS_WORDS = 900

# A floor as well as a ceiling. Without one, a file consisting of nothing but a well-formed header
# passed every structural check and merged -- a degenerate report that also announces an empty
# message to Zulip. The bar is deliberately low: a real section is several paragraphs, so this only
# catches output that is empty or a stub, never a terse but genuine report.
MIN_PROSE_CHARS = 200
# A ceiling on a single report, in words. The prompt asks for at most 300 and says explicitly that a
# quiet window deserves a shorter report; this is only the backstop, set with headroom so a slight
# overshoot does not waste a writing round while a catalogue is still caught.
#
# There is deliberately no lower bound beyond `MIN_PROSE_CHARS`. A window of five pull requests
# should produce a few sentences, and a floor would turn that into padding.
#
# It exists because the failure it prevents actually happened: the first report published ran to 932
# words, and the reader it was written for said it should have been three times shorter. A request
# in a prompt drifts; a check does not. Enforced in `validate_update`, so `apply` refuses on the
# worker before a pull request is opened rather than the gate refusing one that already exists.
MAX_SECTION_WORDS = 450

# Markdown that renders as nothing. An unclosed `<!--` swallows everything after it, so a body could
# clear the prose floor while displaying no report at all -- and the same comment hides the footer of
# the Zulip announcement. Generated prose has no legitimate use for an HTML comment (the machine
# headers are added by the renderer, outside the body), so any is refused.
HTML_COMMENT_RE = re.compile(r"<!--")

# Control characters other than newline and tab: invisible, and a stray CR can split a line in ways a
# reader does not see.
CONTROL_CHARS_RE = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")

# `ts` is interpolated verbatim into the canonical prefix, so it is restricted to the characters an
# ISO-8601 timestamp uses. Otherwise it could itself open an HTML comment and hide the disclaimer
# that follows it.
TS_RE = re.compile(r"\A[0-9A-Za-z:.+\- ]{0,40}\Z")

# The standing disclaimer every STATUS.md must carry. It is the only thing telling a reader that the
# prose below is machine-written and unverified, so the gate REQUIRES it verbatim: a generation that
# dropped it would read as reviewed roadmap content. Split into lines so wrapping cannot change it
# without changing this constant too.
STATUS_DISCLAIMER = (
    "It is generated, and its prose is not security-validated; see\n"
    "https://github.com/TauCetiProject/TauCetiProgress for what that means."
)

# Header schemas, closed rather than open. Unknown keys are refused so a future reader cannot be
# steered by a field this version silently ignored.
STATUS_KEYS = {"roadmap", "to_sha", "ts"}
SECTION_KEYS = {"roadmap", "from_sha", "to_sha", "prs"}


class FormatError(ValueError):
    """A generated file does not conform. Always fail closed on one of these: the gate refuses
    the PR rather than merging something it could not fully parse."""


def _require_sha(value, field):
    if not isinstance(value, str) or not _SHA_RE.match(value):
        raise FormatError(f"{field} must be a full 40-character lowercase hex SHA, got {value!r}")
    return value


def _require_keys(obj, allowed, marker):
    """A header carries exactly the fields this version knows about.

    Unknown keys are refused rather than ignored: a header is a wire format shared with the merge
    gate, and silently tolerating extra fields lets prose smuggle data past a reader that does look
    at them.
    """
    extra = sorted(set(obj) - set(allowed))
    if extra:
        raise FormatError(f"{marker} header has unknown field(s): {', '.join(extra)}")
    missing = sorted(set(allowed) - set(obj) - {"ts"})   # `ts` is display-only and optional
    if missing:
        raise FormatError(f"{marker} header is missing field(s): {', '.join(missing)}")
    return obj


def _require_pr_numbers(value):
    """`prs` must be a list of positive integers, verbatim.

    `int()` coercion accepted floats, bools and numeric strings, so a header could record `[true]`
    or `["1"]` and still parse. The list is what stops a pull request being reported twice, so it is
    validated rather than coerced.
    """
    if not isinstance(value, list) or not value:
        raise FormatError(f"prs must be a non-empty list, got {value!r}")
    out = []
    for n in value:
        if isinstance(n, bool) or not isinstance(n, int) or n <= 0:
            raise FormatError(f"prs must contain positive integers, got {n!r}")
        out.append(n)
    if len(set(out)) != len(out):
        raise FormatError(f"prs contains duplicates: {value!r}")
    return out


def _require_area(value, field):
    # Areas are directory names in the roadmap repo; keep this strict so an area can never
    # contain a path separator and escape its directory.
    if not isinstance(value, str) or not re.match(r"\A[A-Za-z0-9]+\Z", value):
        raise FormatError(f"{field} must be an alphanumeric roadmap area name, got {value!r}")
    return value


def parse_headers(text, marker):
    """Every `marker` header in `text`, in order, as a list of dicts.

    Used both to read one status header and to read every section header of a progress log.
    """
    out = []
    for found_marker, payload in _HEADER_RE.findall(text):
        if found_marker != marker:
            continue
        try:
            obj = json.loads(payload)
        except json.JSONDecodeError as exc:
            raise FormatError(f"malformed {marker} header JSON: {exc}") from exc
        if not isinstance(obj, dict):
            raise FormatError(f"{marker} header must be a JSON object, got {type(obj).__name__}")
        out.append(obj)
    return out


# ----- STATUS.md -------------------------------------------------------------------------------


def _require_ts(value):
    """`ts` is display-only, but it is interpolated verbatim into the canonical prefix, so it must not
    be able to open an HTML comment and hide the disclaimer that follows it."""
    if value is None:
        return ""
    if not isinstance(value, str) or not TS_RE.match(value):
        raise FormatError(f"ts must be a short ISO-8601-style string, got {value!r}")
    return value


def status_prefix(area, to_sha, ts):
    """The exact bytes a `STATUS.md` must begin with, given its own header values.

    Shared by the renderer and the validator so there is one definition. Checking a PREFIX rather
    than searching for substrings is what makes the framing canonical: with a substring check the
    heading and the disclaimer could sit anywhere, including inside a fenced code block, so a file
    could satisfy every check and still render as no report at all.
    """
    header = json.dumps(
        {"roadmap": _require_area(area, "roadmap"), "to_sha": _require_sha(to_sha, "to_sha"),
         "ts": _require_ts(ts)},
        sort_keys=True,
        separators=(",", ":"),
    )
    return (
        f"<!--{STATUS_MARKER} {header}-->\n"
        f"# Status: {area}\n\n"
        f"This file documents the status of the {area} roadmap up until "
        f"`{to_sha[:7]}` ({ts}). There may have been subsequent updates.\n\n"
        f"{STATUS_DISCLAIMER}\n\n"
    )


def render_status(area, to_sha, ts, body):
    """A whole `STATUS.md`. `body` is the model's prose, without any heading of its own.

    The prose is deliberately preceded by a standing note that the file may be out of date: it is
    updated asynchronously from the PRs it describes, so a reader must never take it as
    authoritative about the current tip.
    """
    return f"{status_prefix(area, to_sha, ts)}{body.strip()}\n"


def parse_status(text):
    """The header of a `STATUS.md`. Raises unless there is exactly one."""
    headers = parse_headers(text, STATUS_MARKER)
    if len(headers) != 1:
        raise FormatError(f"expected exactly one {STATUS_MARKER} header, found {len(headers)}")
    h = headers[0]
    _require_keys(h, STATUS_KEYS, STATUS_MARKER)
    return {
        "roadmap": _require_area(h.get("roadmap"), "roadmap"),
        "to_sha": _require_sha(h.get("to_sha"), "to_sha"),
        "ts": _require_ts(h.get("ts")),
    }


# ----- PROGRESS.md -----------------------------------------------------------------------------


def render_section(area, from_sha, to_sha, prs, window_label, body):
    """One `PROGRESS.md` section, ready to append.

    `prs` is the full PR-number list for the window. It is recorded so that a later run can refuse
    to report a PR twice even if its `roadmap/<Area>` label is changed after the fact -- labels are
    mutable metadata, and re-attribution must not silently double-count or drop work.
    """
    nums = sorted({int(n) for n in prs})
    if not nums:
        raise FormatError("a progress section must record at least one PR")
    header = json.dumps(
        {
            "roadmap": _require_area(area, "roadmap"),
            "from_sha": _require_sha(from_sha, "from_sha"),
            "to_sha": _require_sha(to_sha, "to_sha"),
            "prs": nums,
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return (
        f"\n<!--{PROGRESS_MARKER} {header}-->\n"
        f"## {area}: {window_label} (`{from_sha[:7]}` to `{to_sha[:7]}`)\n\n"
        f"{body.strip()}\n"
    )


def new_progress_file(area):
    """The preamble a fresh `PROGRESS.md` starts with, before its first section.

    Sections are appended below, oldest first, so that "this update only added text at the end" is
    checkable as a byte-prefix comparison. See `check_append_only`.
    """
    return (
        f"# Progress log: {area}\n\n"
        f"An append-only record of what landed on the {area} roadmap, one section per window of\n"
        f"merged pull requests, oldest first. Generated; the prose is not security-validated.\n"
        f"For a current snapshot instead, read `STATUS.md` beside this file.\n"
    )


def parse_sections(text):
    """Every section header of a `PROGRESS.md`, oldest first."""
    out = []
    for h in parse_headers(text, PROGRESS_MARKER):
        _require_keys(h, SECTION_KEYS, PROGRESS_MARKER)
        out.append(
            {
                "roadmap": _require_area(h.get("roadmap"), "roadmap"),
                "from_sha": _require_sha(h.get("from_sha"), "from_sha"),
                "to_sha": _require_sha(h.get("to_sha"), "to_sha"),
                "prs": _require_pr_numbers(h.get("prs")),
            }
        )
    return out


def cursor(text):
    """The reporting cursor: the `to_sha` of the newest section, or None for an empty log.

    This single value is the cursor for an area. `STATUS.md` carries a `to_sha` too, but only as a
    snapshot label -- treating it as a second cursor is what would let a STATUS-only update advance
    past a window whose prose was never written, leaving an unreportable gap.
    """
    sections = parse_sections(text)
    return sections[-1]["to_sha"] if sections else None


def reported_prs(text):
    """Every PR number any section of this log has already reported."""
    seen = set()
    for s in parse_sections(text):
        seen.update(s["prs"])
    return seen


# ----- validators the merge gate runs ----------------------------------------------------------


def check_append_only(old_text, new_text):
    """`new_text` must be `old_text` plus trailing bytes, and must actually add some.

    This is the whole reason sections append at the bottom: the property is one byte-prefix
    comparison, with no reasoning about diff hunks, line endings or whitespace. Newest-first
    ordering would be checkable too (old bytes as an unchanged suffix), but this is the version it
    is hardest to get subtly wrong.
    """
    if not isinstance(old_text, str) or not isinstance(new_text, str):
        raise FormatError("append-only check needs text on both sides")
    if not new_text.startswith(old_text):
        raise FormatError("PROGRESS.md was modified above the end; only appending is allowed")
    if len(new_text) == len(old_text):
        raise FormatError("PROGRESS.md is unchanged; an update must add a section")
    return new_text[len(old_text):]


def strip_one_header(text, marker):
    """Remove exactly ONE well-formed `marker` header from `text`, or raise.

    Used before scanning prose for reserved markers. The previous approach exempted anything whose
    prefix matched an allowed marker name, which let prose carrying `<!--tauceti-progress:v1 junk-->`
    through untouched -- a string that is not the parsed header at all. Removing the one canonical
    span and then scanning the remainder with NO exemptions is exact.
    """
    spans = [m.span() for m in _HEADER_RE.finditer(text)
             if _HEADER_RE.match(text, m.start()).group(1) == marker]
    if len(spans) != 1:
        raise FormatError(f"expected exactly one {marker} header, found {len(spans)}")
    start, end = spans[0]
    return text[:start] + text[end:]


def check_no_reserved_markers(body):
    """Refuse prose that contains any `tauceti-*:vN` marker.

    A model that emits one could forge a second status header, a fake scoreboard, or a target
    marker, and every later parse of the file would then see something the generator never intended.
    There is no exemption list: the caller removes the one legitimate header first.
    """
    m = RESERVED_MARKER_RE.search(body)
    if m:
        raise FormatError(f"prose contains a reserved marker at offset {m.start()}: {m.group(0)!r}")


def check_status_shape(text, area, to_sha, ts):
    """`STATUS.md` must begin with EXACTLY the canonical prefix for its own header values.

    A prefix comparison, not a set of substring searches. The looser version could be satisfied with
    the heading and the disclaimer buried anywhere in the file -- inside a fenced code block, say --
    so a document that rendered as no report at all still passed. Returns the body that follows.
    """
    expected = status_prefix(area, to_sha, ts)
    if not text.startswith(expected):
        # Say which part diverges; the whole prefix is too long to quote usefully.
        for label, probe in (
            ("its tauceti-status:v1 header", f"<!--{STATUS_MARKER} "),
            (f"its canonical '# Status: {area}' heading", f"# Status: {area}\n"),
            ("the standing 'not security-validated' disclaimer", STATUS_DISCLAIMER),
        ):
            if probe not in text:
                raise FormatError(f"STATUS.md is missing {label}")
        raise FormatError(
            "STATUS.md does not begin with the canonical header, heading and disclaimer, in that "
            "order and unmodified"
        )
    return text[len(expected):]


def check_section_shape(added, area, from_sha, to_sha):
    """The appended text must open with its section header and canonical heading. Returns the body.

    Anchored at the start of the addition, so nothing -- a code fence, stray prose -- can precede it.
    The heading must also name the same window the header declares.
    """
    pattern = re.compile(
        rf"\A\n?<!--{re.escape(PROGRESS_MARKER)} \{{.*?\}}-->\n"
        rf"## {re.escape(area)}: [^\n]*\(`{re.escape(from_sha[:7])}` to `{re.escape(to_sha[:7])}`\)\n\n",
        re.S,
    )
    m = pattern.match(added)
    if not m:
        raise FormatError(
            f"the new section must begin with its tauceti-progress:v1 header followed by a "
            f"'## {area}: ... (`{from_sha[:7]}` to `{to_sha[:7]}`)' heading"
        )
    return added[m.end():]


def check_visible(name, body):
    """Generated prose must actually render.

    Two ways it might not, both reproduced against an earlier version: an unclosed HTML comment
    swallows the remainder of the document (and, in the announcement, everything after the lead-in),
    and control characters are invisible. Neither has any legitimate use in a report body.
    """
    m = HTML_COMMENT_RE.search(body)
    if m:
        raise FormatError(
            f"{name} contains an HTML comment at offset {m.start()}; generated prose must render"
        )
    m = CONTROL_CHARS_RE.search(body)
    if m:
        raise FormatError(f"{name} contains a control character at offset {m.start()}")
    return True


def check_prose(name, body):
    """`body` -- the text AFTER the canonical framing -- must carry real prose.

    Measuring the extracted body rather than "whole file minus a scaffold length" matters: a length
    subtraction can be satisfied by padding the framing itself, which is exactly what a report
    wrapped in a code fence did.
    """
    prose = len("".join(body.split()))
    if prose < MIN_PROSE_CHARS:
        raise FormatError(
            f"{name} carries only {prose} characters of prose after its heading; "
            f"at least {MIN_PROSE_CHARS} are required"
        )
    return prose


def check_word_count(name, body, cap=MAX_SECTION_WORDS):
    """Refuse a report that has become a catalogue.

    Words rather than bytes: the byte cap is a safety limit measured in kilobytes, which a report
    can be four times too long without approaching. This one is about whether a person will read it.
    """
    words = len(body.split())
    if words > cap:
        raise FormatError(
            f"{name} is {words} words; the limit is {cap}. Reports are summaries, not catalogues -- "
            f"name what the work amounts to and cite a few pull requests, rather than listing them"
        )
    return words


def check_size(name, text, cap):
    n = len(text.encode("utf-8"))
    if n > cap:
        raise FormatError(f"{name} is {n} bytes, over the {cap}-byte cap")
    return n


def check_utf8(name, data):
    """`data` is bytes as GitHub returned them; reject anything that is not valid UTF-8."""
    if isinstance(data, str):
        return data
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise FormatError(f"{name} is not valid UTF-8: {exc}") from exc


def validate_update(area, old_status, new_status, old_progress, new_progress, expect_from_sha=None):
    """The full content gate for one generated update. Returns the new section's header.

    Checks, in order: both files parse; the status snapshot and the new section agree on area and
    `to_sha`; the progress log is a byte-exact append that adds exactly one section; the new
    section's `from_sha` continues the log (and matches `expect_from_sha` when the caller knows
    it); no reserved markers appear in the added prose; sizes are within caps.

    `old_status` may be None for an area's first update; `old_progress` may be None likewise, in
    which case `new_progress` must begin with a fresh preamble rather than a section.
    """
    check_size("STATUS.md", new_status, MAX_STATUS_BYTES)
    check_size("PROGRESS.md", new_progress, MAX_PROGRESS_BYTES)

    status = parse_status(new_status)
    if status["roadmap"] != area:
        raise FormatError(f"STATUS.md is for {status['roadmap']}, expected {area}")

    if old_progress is None:
        old_progress = new_progress_file(area)
    added = check_append_only(old_progress, new_progress)

    before = parse_sections(old_progress)
    after = parse_sections(new_progress)
    if len(after) != len(before) + 1:
        raise FormatError(
            f"expected exactly one new section, went from {len(before)} to {len(after)}"
        )
    section = after[-1]

    if section["roadmap"] != area:
        raise FormatError(f"new section is for {section['roadmap']}, expected {area}")
    if section["to_sha"] != status["to_sha"]:
        raise FormatError(
            f"STATUS.md is at {status['to_sha'][:7]} but the new section ends at "
            f"{section['to_sha'][:7]}; a snapshot must describe the window it ships with"
        )
    prior_cursor = before[-1]["to_sha"] if before else None
    if prior_cursor is not None and section["from_sha"] != prior_cursor:
        raise FormatError(
            f"new section starts at {section['from_sha'][:7]} but the log's cursor is "
            f"{prior_cursor[:7]}; windows must tile with no gap"
        )
    if expect_from_sha is not None and section["from_sha"] != expect_from_sha:
        raise FormatError(
            f"new section starts at {section['from_sha'][:7]}, expected {expect_from_sha[:7]}"
        )
    if section["from_sha"] == section["to_sha"]:
        raise FormatError("a window must be non-empty (from_sha equals to_sha)")
    if not section["prs"]:
        raise FormatError("new section records no PRs")

    check_size("the new section", added, MAX_SECTION_BYTES)
    check_word_count("the new section", strip_one_header(added, PROGRESS_MARKER))

    # Shape before content: both files must carry their canonical framing, so a generation cannot
    # drop the heading or the disclaimer and still parse. Each returns the body that follows it.
    status_body = check_status_shape(new_status, area, status["to_sha"], status["ts"])
    section_body = check_section_shape(added, area, section["from_sha"], section["to_sha"])

    # Remove the ONE legitimate header from each, then scan what is left with no exemptions.
    check_no_reserved_markers(strip_one_header(added, PROGRESS_MARKER))
    check_no_reserved_markers(strip_one_header(new_status, STATUS_MARKER))

    if old_status is not None:
        old = parse_status(old_status)
        if old["to_sha"] == status["to_sha"]:
            raise FormatError(f"STATUS.md still describes {status['to_sha'][:7]}; nothing advanced")

    # Last, so a more specific failure (an injected marker, an unadvanced snapshot) reports its own
    # reason rather than being masked by a complaint about length.
    check_visible("the new section", section_body)
    check_visible("STATUS.md", status_body)
    check_word_count("STATUS.md", status_body, MAX_STATUS_WORDS)
    check_prose("the new section", section_body)
    check_prose("STATUS.md", status_body)

    return section
