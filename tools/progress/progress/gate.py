"""The merge gate: decide whether a progress pull request may be merged, and refuse otherwise.

This is the security-critical module of the project, so it is worth being explicit about why.

TauCetiRoadmap's `main` ruleset requires an approving review from a code owner plus the `build`
check. A ruleset cannot scope that requirement to a path, so the only way a generated report can land
unattended is the roadmap App's `always` bypass -- and a bypass actor bypasses the *whole* ruleset,
including the status checks. Anyone may open a pull request against that repository, including from a
fork. Therefore:

    the checks in this file are the entire gate.

Everything is decided from data the caller fetched via the API; nothing here checks out or executes
pull-request content, and the caller must not mint a write token until `decide` has returned an
allow. The checks run cheapest-and-most-decisive first, so a hostile pull request is rejected on
provenance long before any content is parsed.

What this gate proves is *shape*: which paths changed, that the cursor continues, that the window
advances along real published history, that the append is byte-exact, and that the bytes validated are
the bytes that will land (the head is pinned, and it already contains current `main`). What it cannot
prove is that the prose is true. That limit is accepted deliberately and documented in README.md.

It proves nothing at all about *who* opened the pull request, and that is the design. Identity was
never what made this safe; the shape checks are. Anyone may publish a report, from a fork or
otherwise. The window check is what keeps that bounded rather than merely revertible: without it,
`to_sha` is free, and a chain of reports could walk the cursor anywhere while announcing each step.

The path restriction bounds the damage to two markdown files in one directory -- and to one Zulip
message, since every merged section is announced automatically. That second sink is part of the blast
radius and is named here so it is not overlooked.
"""

import datetime
import json
import re

from . import files

# Only these two basenames, and only inside ONE area directory.
ALLOWED_BASENAMES = ("STATUS.md", "PROGRESS.md")
BRANCH_RE = re.compile(r"\Aprogress/([0-9a-f]{7})-([0-9a-f]{7})/([A-Za-z0-9]+)\Z")
# Group 1 is the parent (an area lives under one or the other, never both), group 2 the area name,
# group 3 the basename. The parent is captured because an area name can legitimately exist under
# BOTH parents -- `Completed/` is where a finished roadmap is archived -- so matching on the area and
# basename alone would let one update write to two directories at once.
PATH_RE = re.compile(r"\A(TauCetiRoadmap|Completed)/([A-Za-z0-9]+)/(STATUS\.md|PROGRESS\.md)\Z")

# A blob mode other than a regular file means a symlink (120000), a gitlink/submodule (160000), or
# an executable. A symlink named STATUS.md pointing at something else is the classic way to make a
# path-restricted gate write outside its restriction, so modes are checked, not assumed.
REGULAR_MODES = {"100644"}

# The App permitted to report the required check. `build` in TauCetiRoadmap is a GitHub Actions
# check-run (app id 15368); any repository WRITER can POST a commit status or create a check-run
# under an arbitrary name, so an unauthenticated "something called build says success" is not
# evidence. Legacy commit statuses are not accepted here at all -- the roadmap repo publishes none.
GITHUB_ACTIONS_APP_ID = 15368

# A considered refusal is exit 3, distinct from both an allow (0) and a crash (anything else). The
# workflow relies on that distinction: a refusal is a normal outcome that leaves the pull request for
# a human, while an unexpected failure must go red rather than reading as a quiet "did not merge".
#
# Not 2: `argparse` exits 2 on a usage error, so a mistyped invocation would have been reported as a
# considered refusal. The workflow additionally requires the output to start with `REFUSED:`, so the
# two signals have to agree.
EX_REFUSED = 3

# The minimum gap between two reports for the SAME roadmap, enforced here rather than only in the
# planner. Kept below `plan.IDLE_HOURS` so it never refuses a report the planner considered due,
# while still capping how fast one roadmap can drive the announcement channel.
MIN_REPORT_INTERVAL_HOURS = 6.0


def _parse_iso(text):
    return datetime.datetime.fromisoformat(str(text).replace("Z", "+00:00"))


class Refused(Exception):
    """The pull request must not be merged. The message is posted for a human to read."""


def _refuse(reason):
    raise Refused(reason)


def check_provenance(pr, base_repo, base_branch="main"):
    """Provenance first: is this pull request even a candidate?

    Deliberately says nothing about *who* opened it, and accepts fork heads.

    Anyone may publish a progress report. What makes that safe is the shape of the diff, not the
    identity behind it: the checks below and in `check_files`/`check_content` permit exactly one
    roadmap's `STATUS.md` and `PROGRESS.md`, with the log append-only and the window advancing along
    real project history. Nothing else can be reached, no code is ever executed, and the worst
    outcome is prose someone has to revert. An author allowlist bought none of that and only excluded
    contributors.

    Accepting fork heads is safe for the same reason plus one more: no pull request content is ever
    checked out. Everything is read through the API at two immutable SHAs, and a fork's head commit
    and tree are replicated into the base repository, so the merge builds from exactly the bytes that
    were validated.
    """
    if pr.get("state") != "open":
        _refuse(f"pull request is {pr.get('state')}, not open")
    if pr.get("draft"):
        _refuse("pull request is a draft")
    base = pr.get("base") or {}
    if (base.get("ref") or "") != base_branch:
        _refuse(f"base branch is {base.get('ref')!r}, expected {base_branch!r}")
    if ((base.get("repo") or {}).get("full_name") or "") != base_repo:
        _refuse(f"base repository is {(base.get('repo') or {}).get('full_name')!r}")

    head = pr.get("head") or {}
    branch = head.get("ref") or ""
    m = BRANCH_RE.match(branch)
    if not m:
        _refuse(f"head branch {branch!r} is not a progress branch")
    return {
        "area": m.group(3),
        "from_prefix": m.group(1),
        "to_prefix": m.group(2),
        "head_sha": head.get("sha") or "",
    }


def check_files(changed_files, area):
    """Diff shape: exactly the two generated files, in exactly ONE `area` directory, as regular files.

    Requiring *both* is deliberate. A `STATUS.md`-only update would move the snapshot forward while
    the window's prose was never written, and because the reporting cursor is the last `PROGRESS.md`
    section, no later run could reconstruct the gap. "Either file" is unsafe; "both files" is not.

    Requiring exactly *two* files in *one* parent is equally deliberate, and was a real hole: keying
    only on the basename let a pull request change four paths -- `TauCetiRoadmap/<area>/{STATUS,
    PROGRESS}.md` **and** `Completed/<area>/{STATUS,PROGRESS}.md` -- and pass, because both basenames
    were present and every path matched the pattern. The content validators then inspected only one
    pair, so the other two would have merged unexamined.

    Returns `{basename: file}` plus the resolved parent directory.
    """
    if not changed_files:
        _refuse("no files changed")

    # First pass: every path must be an allowed generated file in the branch's own area, added or
    # modified, never renamed in.
    parsed = []
    for f in changed_files:
        path = f.get("filename") or ""
        m = PATH_RE.match(path)
        if not m:
            _refuse(f"path {path!r} is not an allowed generated file")
        parent, path_area, basename = m.group(1), m.group(2), m.group(3)
        if path_area != area:
            _refuse(f"path {path!r} is not in the {area} directory")
        status = f.get("status")
        if status not in ("added", "modified"):
            _refuse(f"path {path!r} has status {status!r}; only added or modified are allowed")
        # `previous_filename` present means a rename, which could move a file out of the area.
        if f.get("previous_filename"):
            _refuse(f"path {path!r} is a rename from {f['previous_filename']!r}")
        parsed.append((parent, basename, f))

    # Second pass, in order of how much the message tells a reader: one directory, then no
    # duplicates, then both files present.
    parents = {parent for parent, _, _ in parsed}
    if len(parents) != 1:
        _refuse(f"update spans {sorted(parents)}; it must change one directory, not several")
    seen = {}
    for _, basename, f in parsed:
        if basename in seen:
            _refuse(f"{basename} appears twice; an update changes each file once")
        seen[basename] = f
    missing = [name for name in ALLOWED_BASENAMES if name not in seen]
    if missing:
        _refuse(f"missing required file(s): {', '.join(missing)}; an update must change both")
    return seen, parents.pop()


def check_modes(tree_entries, required_paths):
    """Every changed blob must be an ordinary file: no symlink, submodule, or mode flip.

    `tree_entries` is `[{path, mode, type}]` read from the git TREE api at the head commit, which
    reports true modes (`100644`, `100755`, `120000`, `160000`). The TauCeti build workflow rejects
    symlinks for the same reason.

    `required_paths` must be supplied and every one of them must have an entry. Iterating only over
    whatever was handed in was a fail-OPEN hole: an empty list -- which `collect.py` produced whenever
    a per-path fetch failed -- passed vacuously, and the symlink defence is precisely the check that
    must never fail open.
    """
    by_path = {e.get("path"): e for e in tree_entries}
    for path in sorted(required_paths):
        entry = by_path.get(path)
        if entry is None:
            _refuse(f"no tree entry for {path!r}; cannot confirm it is a regular file")
        if entry.get("type") != "blob":
            _refuse(f"{path!r} is a {entry.get('type')!r}, not a file")
        if entry.get("mode") not in REGULAR_MODES:
            _refuse(f"{path!r} has mode {entry.get('mode')!r}, not a regular file")
    extra = sorted(set(by_path) - set(required_paths))
    if extra:
        _refuse(f"unexpected tree entries: {extra}")
    return True


def check_content(area, old_status, new_status_bytes, old_progress, new_progress_bytes,
                  expect_from_sha=None):
    """Content: both files parse, agree, and the log grew only at the end.

    Bytes in, so invalid UTF-8 is caught here rather than raising something unhelpful later.
    """
    new_status = files.check_utf8("STATUS.md", new_status_bytes)
    new_progress = files.check_utf8("PROGRESS.md", new_progress_bytes)
    try:
        return files.validate_update(
            area, old_status, new_status, old_progress, new_progress,
            expect_from_sha=expect_from_sha,
        )
    except files.FormatError as exc:
        _refuse(str(exc))


def check_up_to_date(compare_status, behind_by, head_sha, main_sha):
    """The head must already contain current `main`.

    This is what makes the merge safe to reason about. If the head is BEHIND main, merging it is a
    three-way merge, and the resulting bytes are a combination of the head and whatever landed on
    main since -- not the bytes that were validated. Requiring `ahead` with `behind_by == 0` means
    the head's tree IS the post-merge tree for the paths in question, so validating the head's blobs
    validates exactly what will land.

    A head that has fallen behind is not an error; the worker simply rebuilds the report against the
    newer main. Refusing is the correct outcome, not a failure.
    """
    if behind_by is None or compare_status is None:
        _refuse("could not determine whether the head contains current main")
    if int(behind_by) != 0 or compare_status != "ahead":
        _refuse(
            f"head {head_sha[:7]} is {compare_status} main {main_sha[:7]} and is behind by "
            f"{behind_by}; rebuild the report on current main so the merged bytes are the "
            f"validated bytes"
        )
    return True


def check_window(code_window, section):
    """The reported window must be a real stretch of TauCeti history that moves forward.

    This is the check that makes "anyone may publish" bounded rather than merely revertible, and it
    replaces the anti-abuse role an author allowlist was quietly playing.

    Cursor continuity alone is not enough. `from_sha` must equal the area's current cursor, but
    `to_sha` was otherwise free, so a report could name any 40-hex string, land, and leave the cursor
    at that value -- then do it again from there, indefinitely. Each link would advance the cursor
    past windows that could no longer be reported, and each would post to Zulip. Requiring `to_sha`
    to be a commit reachable from the documentation branch, strictly ahead of `from_sha`, bounds the
    whole thing to the project's own history: a bogus report costs exactly what a real one costs, and
    is revertible in the same way.

    Reachability is checked against `docgen` rather than equality with its tip on purpose. The tip
    moves whenever documentation is published, and demanding equality would refuse reports that were
    correct when the round started, throwing away the model's work over a race.
    """
    if not code_window:
        _refuse("the reported window could not be checked against TauCeti history")
    checked = code_window.get("to_sha") or ""
    if checked != section["to_sha"]:
        # The window was resolved from the same pinned blob the section was parsed from, so this can
        # only mean the two disagree about which bytes are under test.
        _refuse(
            f"the window checked against history ({checked[:7]}) is not the section's to_sha "
            f"({section['to_sha'][:7]})"
        )
    if (code_window.get("from_sha") or "") != section["from_sha"]:
        _refuse(
            f"the window checked against history starts at {(code_window.get('from_sha') or '')[:7]}, "
            f"not the section's from_sha ({section['from_sha'][:7]})"
        )
    if code_window.get("to_reachable") is not True:
        _refuse(
            f"to_sha {section['to_sha'][:7]} is not a commit reachable from TauCeti's "
            f"{code_window.get('ref', 'docgen')} branch, so it names no published history"
        )
    # `is not True`, never `is False`: a missing or null field would otherwise pass. The collector
    # leaves `advances` null when it did not get as far as asking.
    if code_window.get("advances") is not True:
        _refuse(
            f"to_sha {section['to_sha'][:7]} does not come after from_sha "
            f"{section['from_sha'][:7]}; a window must move forward"
        )
    return True


def check_area_exists(area_exists, parent, area):
    """The report must be for a roadmap that already exists.

    Without this the rate limit below is trivially escaped. It is keyed on the area, and a report for
    an area with no predecessor is always allowed, so an actor who can invent area names can invent
    unlimited first reports: `TauCetiRoadmap/Bogus1/`, `Bogus2/`, and so on, each creating a new
    directory of two files and each announcing itself. Requiring the directory to already hold a
    `README.md` on the base branch pins reports to roadmaps humans actually created -- the same rule
    that defines an area everywhere else in this tool.
    """
    if not area_exists:
        _refuse(
            f"{parent}/{area} is not a roadmap on the base branch (no README.md there); reports may "
            f"only be added to roadmaps that already exist"
        )
    return True


def check_rate(last_report_at, now, area, min_hours=MIN_REPORT_INTERVAL_HOURS):
    """An area may not be reported again until `min_hours` after its last report landed.

    The window check bounds where a report may point, but not how many may be sent. An area whose
    cursor is far behind the documentation branch has a lot of room in front of it -- over a thousand
    commits, for one never yet reported -- and that room can be cut into as many single-commit windows
    as there are commits. Every one of them would satisfy every other check here, and every one would
    post to Zulip. Bounding where without bounding how often leaves the announcement channel wide
    open.

    So the cadence is enforced on the server, not just in the planner that decides what to write. At
    most one report per area per interval, whoever sends it, which is the rate the project intends
    anyway. The first report for an area has no predecessor and is always allowed.

    `now` is the collector's own clock, not anything from the pull request.
    """
    if not last_report_at or not now:
        return True
    try:
        then = _parse_iso(last_report_at)
        current = _parse_iso(now)
    except ValueError:
        # An unreadable timestamp must not silently disable the limit.
        _refuse(f"could not read when {area} was last reported ({last_report_at!r})")
    hours = (current - then).total_seconds() / 3600.0
    if hours < min_hours:
        _refuse(
            f"{area} was reported {hours:.1f}h ago; reports for one roadmap are at least "
            f"{min_hours:g}h apart"
        )
    return True


def check_build(check_runs, head_sha, required="build", app_id=GITHUB_ACTIONS_APP_ID):
    """The `build` check must be a completed success, from the expected App, on the exact head.

    The merging App bypasses required status checks, so this is asserted rather than relied upon --
    the same reasoning as `decide_merge` in TauCetiReview.

    Three things this is strict about, each a way the looser version could be fooled:

    * **Provenance.** Any repository writer can create a check-run or POST a commit status under any
      name, so a result is only evidence if it came from the App that actually runs CI. Legacy commit
      statuses are refused outright -- the roadmap repo publishes none, and accepting them would open
      exactly that forgery route.
    * **Literal success.** `neutral` and `skipped` count as passing for ordinary branch protection,
      which means a workflow that skipped the build entirely would have satisfied this.
    * **No contradictions.** Every matching entry must agree; a success listed ahead of a failure
      used to win because the first match returned.
    """
    matching = [r for r in check_runs if (r.get("name") or "") == required]
    if not matching:
        _refuse(f"{required} has not reported on {head_sha[:7]}")
    for run in matching:
        # Every field is REQUIRED. Defaulting a missing field to the acceptable value meant a bare
        # {"name": "build", "conclusion": "SUCCESS"} passed: no app to check, status assumed
        # completed, head assumed to match. An absent field is unknown provenance, which is exactly
        # the thing this refuses.
        if run.get("source") != "check_run":
            _refuse(f"{required} on {head_sha[:7]} came from {run.get('source')!r}, not a check run")
        if run.get("head_sha") != head_sha:
            _refuse(f"{required} names head {run.get('head_sha')!r}, not {head_sha}")
        got_app = run.get("app_id")
        # Compared as an integer, not coerced into one: `int()` accepted "15368" and 15368.9 alike.
        if isinstance(got_app, bool) or not isinstance(got_app, int) or got_app != app_id:
            _refuse(f"{required} on {head_sha[:7]} was reported by app {got_app!r}, not {app_id}")
        if run.get("status") != "completed":
            _refuse(f"{required} is {run.get('status')!r} on {head_sha[:7]}, not completed")
        # Compared exactly, not case-folded: GitHub emits lowercase conclusions, so anything else is
        # not something GitHub wrote.
        if run.get("conclusion") != "success":
            _refuse(f"{required} concluded {run.get('conclusion')!r} on {head_sha[:7]}")
    return f"{len(matching)}x success"


def check_baseline_paths(old_paths, parent, area):
    """The append-only baseline must come from the directory the diff actually touches.

    An area can exist under both `TauCetiRoadmap/` and `Completed/`. A collector that probed a fixed
    order would hand a `Completed/` update the ACTIVE log as its baseline, and a wholesale
    replacement of the archived log would then look like a valid append. The paths the baseline was
    read from are therefore recorded and checked here rather than trusted.
    """
    if not old_paths:
        # No baseline at all is legitimate only for an area's first report; validate_update enforces
        # the rest (a first report starts from a fresh preamble).
        return True
    for name in ALLOWED_BASENAMES:
        got = old_paths.get(name)
        want = f"{parent}/{area}/{name}"
        if got != want:
            _refuse(f"baseline for {name} was read from {got!r}, expected {want!r}")
    return True


def decide(pr, changed_files, tree_entries, old_status, new_status_bytes, old_progress,
           new_progress_bytes, check_runs, base_repo,
           current_main_cursor=None, compare_status=None, behind_by=None, main_sha="",
           old_paths=None, code_window=None, last_report_at=None, now=None,
           area_exists=None, expected_bootstrap_from_sha=None):
    """Run the whole gate. Returns `{"area", "head_sha", "section"}` or raises `Refused`.

    `current_main_cursor` is the area's cursor read from **freshly fetched `main`**, not from the
    pull request's stale base. Passing it closes the window where `main` moved on (another report
    merged) after this pull request was opened.
    """
    prov = check_provenance(pr, base_repo)
    area, head_sha = prov["area"], prov["head_sha"]
    if not head_sha:
        _refuse("pull request has no head sha")

    check_up_to_date(compare_status, behind_by, head_sha, main_sha)
    seen, parent = check_files(changed_files, area)
    check_area_exists(area_exists, parent, area)
    check_baseline_paths(old_paths or {}, parent, area)
    # A roadmap's FIRST report has no cursor on `main` to continue from, so its `from_sha` has to be
    # pinned some other way or whoever files it also chooses where that roadmap's history begins --
    # and because windows only move forward, everything earlier becomes unreportable for good.
    #
    # The collector computes the one legitimate answer (the first parent of the merge commit of the
    # area's earliest labelled pull request) and it is required exactly. Refusing first reports
    # outright would have been safe and useless: thirteen of the fourteen roadmaps have never been
    # reported, so almost nothing would be left for automation to do.
    # A roadmap's FIRST report has no cursor on `main` to continue from, so its starting point is
    # pinned against the code repository instead: the collector clones it and asks git, using the same
    # functions the planner uses over the same data, so the two agree by construction.
    #
    # Three earlier versions tried to answer this through the REST API -- by lowest pull request
    # number, by merge timestamp, and by walking the commits endpoint -- and all three were wrong,
    # because the question is about position on the first-parent chain and the API expresses neither
    # first-parent traversal nor any ordering guarantee. A fourth refused first reports outright,
    # which was sound but made a person merge fourteen of them by hand.
    if not current_main_cursor:
        expect = expected_bootstrap_from_sha or ""
        if not expect:
            _refuse(
                f"{parent}/{area} has no reported history yet, and where that history begins could "
                f"not be determined, so a first report cannot be checked"
            )
        current_main_cursor = expect
    check_modes(tree_entries, [f"{parent}/{area}/{name}" for name in ALLOWED_BASENAMES])
    section = check_content(
        area, old_status, new_status_bytes, old_progress, new_progress_bytes,
        expect_from_sha=current_main_cursor,
    )
    check_build(check_runs, head_sha)
    check_window(code_window, section)
    check_rate(last_report_at, now, area)

    # The branch name encodes the window it reports, and `apply` derives it from the same plan that
    # produced the header. Requiring them to agree binds the branch to its content, so a branch
    # cannot be reused to carry a different window's update.
    #
    # This is emphatically not an identity check. Anyone may open the pull request, from a fork or
    # otherwise, and whoever owns the head branch may replace it at any time. That is fine: the head
    # is pinned to one immutable SHA and every check below reads that SHA, so a replaced head is a
    # different head and gets validated on its own terms or not at all.
    if not section["from_sha"].startswith(prov["from_prefix"]):
        _refuse(
            f"branch says the window starts at {prov['from_prefix']} but the section says "
            f"{section['from_sha'][:7]}"
        )
    if not section["to_sha"].startswith(prov["to_prefix"]):
        _refuse(
            f"branch says the window ends at {prov['to_prefix']} but the section says "
            f"{section['to_sha'][:7]}"
        )
    return {"area": area, "head_sha": head_sha, "main_sha": main_sha, "section": section}


def summary(result):
    return (
        f"{result['area']}: window {result['section']['from_sha'][:7]}.."
        f"{result['section']['to_sha'][:7]}, {len(result['section']['prs'])} PR(s), "
        f"head {result['head_sha'][:7]}"
    )


def main(argv=None):
    """CLI used by the reusable workflow: reads a JSON bundle, prints a verdict, exits 0 or 1.

    The workflow fetches every input with the read-only default token and hands them over as one
    file, so this process needs no credentials at all.
    """
    import argparse
    import pathlib
    import sys

    ap = argparse.ArgumentParser(description="Decide whether a progress PR may be merged.")
    ap.add_argument("--bundle", required=True, help="JSON file with the fetched pull-request data")
    args = ap.parse_args(argv)

    data = json.loads(pathlib.Path(args.bundle).read_text(encoding="utf-8"))
    try:
        result = decide(
            pr=data["pr"],
            changed_files=data["changed_files"],
            tree_entries=data.get("tree_entries") or [],
            old_status=data.get("old_status"),
            new_status_bytes=data["new_status"].encode("utf-8", "surrogateescape"),
            old_progress=data.get("old_progress"),
            new_progress_bytes=data["new_progress"].encode("utf-8", "surrogateescape"),
            check_runs=data.get("check_runs") or [],
            base_repo=data["base_repo"],
            # `.get`, but the gate refuses when it is absent: a bundle from an older collector must
            # not silently skip the window check.
            code_window=data.get("code_window"),
            area_exists=data.get("area_exists"),
            expected_bootstrap_from_sha=data.get("expected_bootstrap_from_sha"),
            last_report_at=data.get("last_report_at"),
            now=data.get("collected_at"),
            current_main_cursor=data.get("current_main_cursor"),
            compare_status=data.get("compare_status"),
            behind_by=data.get("behind_by"),
            main_sha=data.get("main_sha") or "",
            old_paths=data.get("old_paths") or {},
        )
    except Refused as exc:
        print(f"REFUSED: {exc}")
        return EX_REFUSED
    print(f"ALLOWED: {summary(result)}")
    return 0
