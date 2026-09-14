"""Tests for the merge gate.

These are the most important tests here. The roadmap App bypasses the whole ruleset, so this gate is
the only thing preventing an unwanted change to a human-owned repository. Every check therefore has
an explicit negative test, and the default expectation is refusal.
"""

import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from progress import files, gate  # noqa: E402
from progress.gate import Refused  # noqa: E402

failures = []


def check(name, fn):
    try:
        fn()
    except Exception as exc:  # noqa: BLE001
        failures.append(name)
        print(f"FAIL {name}: {type(exc).__name__}: {exc}")
    else:
        print(f"ok   {name}")


def refuses(fn, needle=None):
    try:
        fn()
    except Refused as exc:
        if needle and needle not in str(exc):
            raise AssertionError(f"refused for the wrong reason: {str(exc)!r}") from None
        return str(exc)
    raise AssertionError("expected a refusal, the gate ALLOWED this")


REPO = "TauCetiProject/TauCetiRoadmap"
FROM = "1f1d752" + "0" * 33
TO = "3f41440" + "0" * 33
HEAD = "f" * 40
AREA = "ReductiveGroups"
BRANCH = f"progress/{FROM[:7]}-{TO[:7]}/{AREA}"


def make_pr(**over):
    pr = {
        "state": "open",
        "draft": False,
        "user": {"id": 477956, "login": "kim-em"},
        "base": {"ref": "main", "repo": {"full_name": REPO}},
        "head": {"ref": BRANCH, "sha": HEAD, "repo": {"full_name": REPO}},
    }
    pr.update(over)
    return pr


def make_files(area=AREA, names=("STATUS.md", "PROGRESS.md"), status="modified", **over):
    out = []
    for n in names:
        f = {"filename": f"TauCetiRoadmap/{area}/{n}", "status": status}
        f.update(over)
        out.append(f)
    return out


def make_tree(area=AREA, mode="100644"):
    return [
        {"path": f"TauCetiRoadmap/{area}/STATUS.md", "mode": mode, "type": "blob"},
        {"path": f"TauCetiRoadmap/{area}/PROGRESS.md", "mode": mode, "type": "blob"},
    ]


PROSE = "Harnack's inequality landed for a nonnegative harmonic function on a planar disc, in both the two-sided comparison with the centre value and the pairwise form on a closed subdisc with the sharp constant. The supporting mean-value machinery was extracted along the way, and the remaining Layer 2 targets are untouched."


def make_content(from_sha=FROM, to_sha=TO, prs=(1, 2, 3), area=AREA, prose=None):
    prose = PROSE if prose is None else prose
    old_progress = files.new_progress_file(area)
    new_progress = old_progress + files.render_section(area, from_sha, to_sha, list(prs), "w", prose)
    new_status = files.render_status(area, to_sha, "2026-07-30T00:00:00Z", PROSE)
    return None, new_status, old_progress, new_progress


def build_run(**over):
    """A fully-specified check-run. Every field is required by the gate, so fixtures state them all."""
    run = {"name": "build", "head_sha": HEAD, "conclusion": "success",
           "status": "completed", "app_id": gate.GITHUB_ACTIONS_APP_ID, "source": "check_run"}
    run.update(over)
    return run


CHECKS_OK = [build_run()]


MAIN = "9a9a9a9" + "0" * 33


def make_window(**over):
    """A window that really is a forward stretch of documented TauCeti history."""
    w = {"repo": "TauCetiProject/TauCeti", "ref": "docgen", "from_sha": FROM, "to_sha": TO,
         "to_reachable": True, "advances": True}
    w.update(over)
    return w


NOW = "2026-07-30T12:00:00Z"


def call(pr=None, changed=None, tree=None, content=None, checks=None, cursor=FROM, window=-1,
         compare_status="ahead", behind_by=0, old_paths=None, last_report_at=None, now=NOW,
         area_exists=True, expected_bootstrap=None):
    old_status, new_status, old_progress, new_progress = content or make_content()
    return gate.decide(
        pr=pr or make_pr(),
        changed_files=changed if changed is not None else make_files(),
        tree_entries=tree if tree is not None else make_tree(),
        old_status=old_status,
        new_status_bytes=new_status.encode(),
        old_progress=old_progress,
        new_progress_bytes=new_progress.encode(),
        check_runs=checks if checks is not None else CHECKS_OK,
        base_repo=REPO,
        code_window=make_window() if window == -1 else window,
        last_report_at=last_report_at,
        now=now,
        area_exists=area_exists,
        expected_bootstrap_from_sha=expected_bootstrap,
        current_main_cursor=cursor,
        compare_status=compare_status,
        behind_by=behind_by,
        main_sha=MAIN,
        old_paths=old_paths if old_paths is not None else {
            n: f"TauCetiRoadmap/{AREA}/{n}" for n in ("STATUS.md", "PROGRESS.md")
        },
    )


# ----- the happy path (exactly one) -------------------------------------------------------------


def test_allows_a_well_formed_update():
    result = call()
    assert result["area"] == AREA
    assert result["head_sha"] == HEAD
    assert result["section"]["prs"] == [1, 2, 3]
    assert AREA in gate.summary(result)


# ----- provenance ------------------------------------------------------------------------------


def test_allows_a_fork():
    """Anyone may publish, which in practice means from a fork: no PR content is ever checked out."""
    pr = make_pr(head={"ref": BRANCH, "sha": HEAD, "repo": {"full_name": "someone/TauCetiRoadmap"}})
    assert call(pr=pr)["area"] == AREA


def test_the_author_is_irrelevant():
    """Identity is deliberately not a criterion. The shape of the diff is what makes this safe."""
    for user in ({"id": 999999, "login": "stranger"}, {"id": 1, "login": "kim-em"}, {}):
        assert call(pr=make_pr(user=user))["area"] == AREA


def test_refuses_a_fabricated_to_sha():
    """The attack the window check exists to stop.

    Cursor continuity pins `from_sha`, but `to_sha` was otherwise free. A report naming an invented
    commit would land and leave the cursor at that value, and the next one could start from there:
    an unbounded walk, each step burning a window that could never afterwards be reported and each
    step posting to Zulip. A fabricated sha is not reachable from the documentation branch.
    """
    refuses(lambda: call(window=make_window(to_reachable=False, advances=None)),
            "names no published history")


def test_refuses_a_window_that_does_not_move_forward():
    refuses(lambda: call(window=make_window(advances=False)), "must move forward")


def test_refuses_when_the_window_could_not_be_checked():
    """A bundle from an older collector must not silently skip the check."""
    refuses(lambda: call(window=None), "could not be checked")
    refuses(lambda: call(window={}), "could not be checked")


def test_refuses_when_the_checked_window_is_not_the_reported_one():
    """The window is resolved from the same pinned blob the section is parsed from; they must agree."""
    refuses(lambda: call(window=make_window(to_sha="b" * 40)), "is not the section's to_sha")


def test_a_fork_that_force_pushes_after_opening_gains_nothing():
    """Now that fork heads are accepted, the head branch is under someone else's control.

    That is fine, because every check reads one pinned SHA. Replacing the branch produces a different
    head, and evidence gathered for the old one no longer applies: here the build success names a
    commit that is not the pinned head, which is exactly what a force-push leaves behind.
    """
    pr = make_pr(head={"ref": BRANCH, "sha": HEAD, "repo": {"full_name": "someone/TauCetiRoadmap"}})
    refuses(lambda: call(pr=pr, checks=[build_run(head_sha="0" * 40)]), "names head")


def test_a_first_report_must_start_where_the_roadmap_starts():
    """A bootstrap has no cursor to continue from, so it would otherwise pick its own start, and
    windows only move forward -- anything before it is unreportable for good.

    The collector clones the code repository and asks git, using the same functions the planner uses
    over the same data, so the two agree by construction rather than by luck. Three earlier versions
    tried to answer this through the REST API and all three were wrong.
    """
    assert call(cursor=None, expected_bootstrap=FROM)["area"] == AREA
    refuses(lambda: call(cursor=None, expected_bootstrap="e" * 40), "expected eeeeeee")


def test_a_first_report_is_refused_when_the_start_is_unknown():
    refuses(lambda: call(cursor=None, expected_bootstrap=None), "could not be determined")


def test_refuses_an_invented_roadmap():
    """Otherwise the cadence limit is trivially escaped.

    It is keyed on the area, and an area with no previous report is always allowed, so inventing area
    names would give unlimited exempt "first reports" -- Bogus1, Bogus2 -- each creating a directory
    and each announcing itself.
    """
    refuses(lambda: call(area_exists=False), "is not a roadmap on the base branch")


def test_refuses_a_second_report_for_the_same_roadmap_too_soon():
    """Bounding WHERE a report may point does not bound HOW MANY may be sent.

    An area whose cursor is far behind the documentation branch has over a thousand commits of room
    in front of it, and that room can be cut into as many single-commit windows as there are commits.
    Every one would pass every other check, and every one would post to Zulip. The cadence is
    therefore enforced here as well as in the planner.
    """
    refuses(lambda: call(last_report_at="2026-07-30T09:00:00Z"), "reported 3.0h ago")


def test_allows_a_report_once_the_interval_has_passed():
    assert call(last_report_at="2026-07-29T00:00:00Z")["area"] == AREA


def test_a_first_report_for_an_area_has_no_predecessor():
    assert call(last_report_at=None)["area"] == AREA


def test_an_unreadable_last_report_time_does_not_disable_the_limit():
    refuses(lambda: call(last_report_at="whenever"), "could not read when")


def test_refuses_a_draft():
    refuses(lambda: call(pr=make_pr(draft=True)), "draft")


def test_refuses_a_closed_pr():
    refuses(lambda: call(pr=make_pr(state="closed")), "not open")


def test_refuses_a_wrong_base_branch():
    pr = make_pr(base={"ref": "gh-pages", "repo": {"full_name": REPO}})
    refuses(lambda: call(pr=pr), "base branch")


def test_refuses_a_non_progress_branch():
    pr = make_pr(head={"ref": "patch-1", "sha": HEAD, "repo": {"full_name": REPO}})
    refuses(lambda: call(pr=pr), "not a progress branch")


def test_refuses_a_branch_whose_area_is_not_alphanumeric():
    pr = make_pr(head={"ref": f"progress/{FROM[:7]}-{TO[:7]}/../../etc", "sha": HEAD,
                       "repo": {"full_name": REPO}})
    refuses(lambda: call(pr=pr), "not a progress branch")


def test_refuses_a_head_behind_main():
    """If the head is behind main, merging is a three-way merge and the resulting bytes are NOT the
    validated bytes. Refusing makes the worker rebuild on current main."""
    refuses(lambda: call(compare_status="diverged", behind_by=3), "is behind by 3")
    refuses(lambda: call(compare_status="behind", behind_by=1), "is behind by 1")


def test_refuses_an_unknown_comparison():
    refuses(lambda: call(compare_status=None, behind_by=None), "could not determine")


# ----- diff shape ------------------------------------------------------------------------------


def test_refuses_an_extra_path():
    changed = make_files() + [{"filename": f"TauCetiRoadmap/{AREA}/README.md", "status": "modified"}]
    refuses(lambda: call(changed=changed), "not an allowed generated file")


def test_refuses_a_workflow_path():
    changed = make_files() + [{"filename": ".github/workflows/evil.yml", "status": "added"}]
    refuses(lambda: call(changed=changed), "not an allowed generated file")


def test_refuses_status_only():
    """The motivating case for requiring both files: the cursor would advance past unwritten prose."""
    refuses(lambda: call(changed=make_files(names=("STATUS.md",))), "missing required file")


def test_refuses_progress_only():
    refuses(lambda: call(changed=make_files(names=("PROGRESS.md",))), "missing required file")


def test_refuses_files_from_another_area():
    changed = make_files(area="PDE")
    refuses(lambda: call(changed=changed), "not in the ReductiveGroups directory")


def test_refuses_a_deletion():
    refuses(lambda: call(changed=make_files(status="removed")), "only added or modified")


def test_refuses_a_rename():
    changed = make_files()
    changed[0]["previous_filename"] = "TauCetiRoadmap/PDE/STATUS.md"
    refuses(lambda: call(changed=changed), "rename")


def test_refuses_no_change():
    refuses(lambda: call(changed=[]), "no files changed")


def test_refuses_writing_into_two_parent_directories():
    """An area name can exist under BOTH `TauCetiRoadmap/` and `Completed/` (that is where a finished
    roadmap is archived). Keying only on the basename let a PR change all FOUR paths and pass, because
    both basenames were present and every path matched; the content validators then looked at only one
    pair, so the other two would have merged unexamined."""
    changed = make_files() + [
        {"filename": f"Completed/{AREA}/STATUS.md", "status": "modified"},
        {"filename": f"Completed/{AREA}/PROGRESS.md", "status": "modified"},
    ]
    refuses(lambda: call(changed=changed), "one directory")


def test_refuses_a_duplicated_path():
    changed = make_files() + [{"filename": f"TauCetiRoadmap/{AREA}/STATUS.md", "status": "modified"}]
    refuses(lambda: call(changed=changed), "appears twice")


def test_refuses_more_files_than_allowed():
    """Belt and braces alongside the both-files check: a repeated path is caught too."""
    changed = make_files()
    changed.append({"filename": f"TauCetiRoadmap/{AREA}/STATUS.md", "status": "added"})
    refuses(lambda: call(changed=changed), "appears twice")


def test_refuses_a_baseline_from_the_wrong_parent():
    """An area can exist under both parents. A collector probing a fixed order would hand a
    Completed/ update the ACTIVE log as its baseline, making a wholesale replacement of the archived
    log look like a valid append."""
    wrong = {n: f"Completed/{AREA}/{n}" for n in ("STATUS.md", "PROGRESS.md")}
    refuses(lambda: call(old_paths=wrong), "expected 'TauCetiRoadmap/")


def test_refuses_a_partial_baseline():
    half = {"STATUS.md": f"TauCetiRoadmap/{AREA}/STATUS.md"}
    refuses(lambda: call(old_paths=half), "baseline for PROGRESS.md")


# ----- modes -----------------------------------------------------------------------------------


def test_refuses_when_a_tree_entry_is_missing():
    """FAIL-CLOSED. Iterating only over the entries handed in meant an EMPTY list passed vacuously --
    and the collector produced exactly that whenever a per-path fetch failed, so the symlink defence
    (the one check that must never fail open) could be skipped by making a fetch fail."""
    refuses(lambda: call(tree=[]), "no tree entry")
    partial = [{"path": f"TauCetiRoadmap/{AREA}/STATUS.md", "mode": "100644", "type": "blob"}]
    refuses(lambda: call(tree=partial), "no tree entry")


def test_refuses_an_executable_mode():
    """The contents api reports a 100755 blob as plain type "file", so modes now come from the tree
    api. Harmless in itself for markdown, but the gate claimed to check modes and did not."""
    refuses(lambda: call(tree=make_tree(mode="100755")), "not a regular file")


def test_refuses_unexpected_tree_entries():
    tree = make_tree() + [{"path": "README.md", "mode": "100644", "type": "blob"}]
    refuses(lambda: call(tree=tree), "unexpected tree entries")


def test_refuses_a_symlink():
    """A symlink named STATUS.md is the classic way to escape a path restriction."""
    refuses(lambda: call(tree=make_tree(mode="120000")), "not a regular file")


def test_refuses_a_submodule():
    tree = make_tree()
    tree[0] = {"path": tree[0]["path"], "mode": "160000", "type": "commit"}
    refuses(lambda: call(tree=tree), "not a file")


# ----- content ---------------------------------------------------------------------------------


def test_refuses_an_injected_marker_in_prose():
    content = make_content(prose=PROSE + ' <!--tauceti-status:v1 {"roadmap":"PDE"}-->')
    refuses(lambda: call(content=content), "reserved marker")


def test_refuses_a_rewritten_log():
    """PROGRESS.md must grow only at the end."""
    old_status, new_status, old_progress, new_progress = make_content()
    tampered = "EDITED " + new_progress
    refuses(lambda: call(content=(old_status, new_status, old_progress, tampered)),
            "above the end")


def test_refuses_a_cursor_that_does_not_continue_current_main():
    """`main` may have moved on since the PR was opened; validating against a stale base would let
    the same window land twice."""
    refuses(lambda: call(cursor="9" * 40), "expected")


def test_allows_when_the_cursor_matches_current_main():
    result = call(cursor=FROM)
    assert result["section"]["from_sha"] == FROM


def test_refuses_mismatched_status_and_section():
    old_progress = files.new_progress_file(AREA)
    new_progress = old_progress + files.render_section(AREA, FROM, TO, [1], "w", PROSE)
    # Snapshot claims a different commit than the window ends at.
    new_status = files.render_status(AREA, "c" * 40, "t", PROSE)
    refuses(lambda: call(content=(None, new_status, old_progress, new_progress)), "must describe")


def test_refuses_invalid_utf8():
    old_status, new_status, old_progress, new_progress = make_content()
    bad = new_progress.encode()[:-3] + b"\xff\xfe"
    try:
        gate.decide(
            pr=make_pr(), changed_files=make_files(), tree_entries=make_tree(),
            old_status=old_status, new_status_bytes=new_status.encode(),
            old_progress=old_progress, new_progress_bytes=bad,
            check_runs=CHECKS_OK, base_repo=REPO, code_window=make_window(),
            area_exists=True, now=NOW, current_main_cursor=FROM,
            compare_status="ahead", behind_by=0, main_sha=MAIN,
        )
    except (Refused, files.FormatError) as exc:
        assert "UTF-8" in str(exc), str(exc)
        return
    raise AssertionError("expected a refusal")


def test_refuses_an_area_mismatch_between_branch_and_content():
    """The branch says ReductiveGroups; the files say PDE."""
    content = make_content(area="PDE")
    changed = make_files(area="PDE")
    refuses(lambda: call(changed=changed, content=content), "not in the ReductiveGroups directory")


def test_refuses_bare_headers_with_no_prose():
    """A file consisting of nothing but a well-formed header passed every structural check and would
    have merged -- and then announced an empty message to Zulip. The floor is measured against what
    the renderer emits for an EMPTY body, so it tracks the boilerplate rather than a magic number."""
    bare_status = '<!--tauceti-status:v1 {"roadmap":"%s","to_sha":"%s","ts":"t"}-->' % (AREA, TO)
    old_progress = files.new_progress_file(AREA)
    bare_section = ('\n<!--tauceti-progress:v1 {"roadmap":"%s","from_sha":"%s","to_sha":"%s",'
                    '"prs":[1]}-->' % (AREA, FROM, TO))
    refuses(lambda: call(content=(None, bare_status, old_progress, old_progress + bare_section)),
            "missing")


def test_refuses_a_stub_section_under_a_real_status():
    old_progress = files.new_progress_file(AREA)
    stub = files.render_section(AREA, FROM, TO, [1], "w", "Some things landed.")
    status = files.render_status(AREA, TO, "t", PROSE)
    refuses(lambda: call(content=(None, status, old_progress, old_progress + stub)),
            "characters of prose")


def test_refuses_a_status_missing_the_disclaimer():
    """The disclaimer is the only thing telling a reader the prose is machine-written and
    unverified, so a generation that drops it must not merge as ordinary roadmap content."""
    old_progress = files.new_progress_file(AREA)
    new_progress = old_progress + files.render_section(AREA, FROM, TO, [1], "w", PROSE)
    good = files.render_status(AREA, TO, "t", PROSE)
    stripped = good.replace(files.STATUS_DISCLAIMER, "")
    refuses(lambda: call(content=(None, stripped, old_progress, new_progress)), "disclaimer")


def test_refuses_a_status_whose_header_is_not_first():
    """parse_headers finds a header anywhere; a file that buried it under other content would parse
    yet read as something else."""
    old_progress = files.new_progress_file(AREA)
    new_progress = old_progress + files.render_section(AREA, FROM, TO, [1], "w", PROSE)
    good = files.render_status(AREA, TO, "t", PROSE)
    moved = "Preamble a reader sees first.\n\n" + good
    refuses(lambda: call(content=(None, moved, old_progress, new_progress)), "does not begin with")


def test_refuses_a_section_without_its_heading():
    old_progress = files.new_progress_file(AREA)
    section = files.render_section(AREA, FROM, TO, [1], "w", PROSE)
    headless = section.replace(f"## {AREA}: ", "Some other line ")
    status = files.render_status(AREA, TO, "t", PROSE)
    refuses(lambda: call(content=(None, status, old_progress, old_progress + headless)), "must begin with")


def test_refuses_junk_pr_numbers():
    """`prs` is what stops a PR being reported twice, so it is validated, not coerced. int() used to
    accept booleans, floats and numeric strings."""
    old_progress = files.new_progress_file(AREA)
    status = files.render_status(AREA, TO, "t", PROSE)
    for junk in ('["1"]', "[true]", "[1.5]", "[-3]", "[]", "[1,1]"):
        bad = ('\n<!--tauceti-progress:v1 {"roadmap":"%s","from_sha":"%s","to_sha":"%s","prs":%s}-->\n'
               '## %s: w\n\n%s\n' % (AREA, FROM, TO, junk, AREA, PROSE))
        refuses(lambda b=bad: call(content=(None, status, old_progress, old_progress + b)), "prs")


def test_refuses_a_report_wrapped_in_a_code_fence():
    """The substring version of the shape check let the heading and disclaimer live anywhere,
    including inside a fenced block, so a document that rendered as no report at all still passed.
    The framing is now an exact prefix, and the prose floor measures the extracted body."""
    old_progress = files.new_progress_file(AREA)
    good_status = files.render_status(AREA, TO, "t", PROSE)
    fenced_status = f"```\n{good_status}\n```\n"
    good_section = files.render_section(AREA, FROM, TO, [1], "w", PROSE)
    fenced_section = f"```\n{good_section}\n```\n"
    refuses(lambda: call(content=(None, fenced_status, old_progress, old_progress + good_section)),
            "does not begin with")
    refuses(lambda: call(content=(None, good_status, old_progress, old_progress + fenced_section)),
            "must begin with")


def test_refuses_a_heading_naming_the_wrong_window():
    """The heading must name the same window the header declares, so the two cannot disagree."""
    old_progress = files.new_progress_file(AREA)
    status = files.render_status(AREA, TO, "t", PROSE)
    section = files.render_section(AREA, FROM, TO, [1], "w", PROSE)
    wrong = section.replace(f"(`{FROM[:7]}` to `{TO[:7]}`)", "(`0000000` to `1111111`)")
    refuses(lambda: call(content=(None, status, old_progress, old_progress + wrong)), "must begin with")


def test_refuses_padded_framing_with_no_real_body():
    """A length subtraction could be satisfied by padding the framing itself; measuring the extracted
    body cannot."""
    old_progress = files.new_progress_file(AREA)
    status = files.render_status(AREA, TO, "t", PROSE)
    section = files.render_section(AREA, FROM, TO, [1], "w", "tiny")
    refuses(lambda: call(content=(None, status, old_progress, old_progress + section)),
            "characters of prose")


def test_refuses_an_unclosed_html_comment_in_the_body():
    """An unclosed `<!--` swallows the rest of the document, so a body could clear the prose floor
    while rendering nothing -- and the same comment hides the footer of the Zulip announcement."""
    hidden = "<!-- " + ("padding text that is never seen " * 12)
    old_progress = files.new_progress_file(AREA)
    status = files.render_status(AREA, TO, "t", PROSE)
    section = files.render_section(AREA, FROM, TO, [1], "w", hidden)
    refuses(lambda: call(content=(None, status, old_progress, old_progress + section)),
            "must render")
    bad_status = files.render_status(AREA, TO, "t", hidden)
    good_section = files.render_section(AREA, FROM, TO, [1], "w", PROSE)
    refuses(lambda: call(content=(None, bad_status, old_progress, old_progress + good_section)),
            "must render")


def test_refuses_control_characters_in_the_body():
    old_progress = files.new_progress_file(AREA)
    status = files.render_status(AREA, TO, "t", PROSE)
    section = files.render_section(AREA, FROM, TO, [1], "w", PROSE + "\x00hidden")
    refuses(lambda: call(content=(None, status, old_progress, old_progress + section)),
            "control character")


def test_refuses_a_ts_that_could_open_a_comment():
    """`ts` is interpolated verbatim into the canonical prefix, so it must not be able to open an
    HTML comment and hide the disclaimer that follows it."""
    try:
        files.render_status(AREA, TO, "<!-- ", PROSE)
    except files.FormatError as exc:
        assert "ISO-8601" in str(exc), str(exc)
        return
    raise AssertionError("expected a FormatError")


def test_refuses_a_string_app_id():
    """`int()` coercion accepted "15368" and 15368.9 alike."""
    refuses(lambda: call(checks=[build_run(app_id="15368")]), "reported by app")
    refuses(lambda: call(checks=[build_run(app_id=15368.9)]), "reported by app")


def test_refuses_unknown_header_fields():
    """Headers are a closed schema shared with the gate; an ignored field is a field a later reader
    might not ignore."""
    old_progress = files.new_progress_file(AREA)
    new_progress = old_progress + files.render_section(AREA, FROM, TO, [1], "w", PROSE)
    odd = ('<!--tauceti-status:v1 {"roadmap":"%s","to_sha":"%s","ts":"t","evil":"x"}-->\n\n%s\n'
           % (AREA, TO, PROSE))
    refuses(lambda: call(content=(None, odd, old_progress, new_progress)), "unknown field")


# ----- build ------------------------------------------------------------------------------------


def test_refuses_a_failing_build():
    checks = [build_run(conclusion="failure")]
    refuses(lambda: call(checks=checks), "concluded 'failure'")


def test_refuses_a_build_from_another_app():
    """Any repository WRITER can create a check-run or POST a commit status under any name, so a
    result is evidence only if it came from the App that actually runs CI."""
    checks = [build_run(app_id=99999)]
    refuses(lambda: call(checks=checks), "reported by app")


def test_refuses_a_legacy_commit_status():
    checks = [build_run(source="status")]
    refuses(lambda: call(checks=checks), "not a check run")


def test_refuses_a_skipped_or_neutral_build():
    """Both count as passing for ordinary branch protection, so a workflow that skipped the build
    entirely would otherwise have satisfied this."""
    for concl in ("skipped", "neutral"):
        refuses(lambda c=concl: call(checks=[build_run(conclusion=c)]), "concluded " + repr(concl))


def test_refuses_an_incomplete_build():
    checks = [build_run(conclusion=None, status="in_progress")]
    refuses(lambda: call(checks=checks), "in_progress")


def test_refuses_a_branch_whose_window_disagrees_with_the_section():
    """The branch encodes the window it reports; requiring agreement stops a branch being reused to
    carry a different window's update."""
    other = make_pr(head={"ref": f"progress/aaaaaaa-{TO[:7]}/{AREA}", "sha": HEAD,
                          "repo": {"full_name": REPO}})
    refuses(lambda: call(pr=other), "branch says the window starts at")
    other2 = make_pr(head={"ref": f"progress/{FROM[:7]}-bbbbbbb/{AREA}", "sha": HEAD,
                           "repo": {"full_name": REPO}})
    refuses(lambda: call(pr=other2), "branch says the window ends at")


def test_refuses_a_pending_build():
    checks = [build_run(conclusion=None)]
    refuses(lambda: call(checks=checks), "concluded None")


def test_refuses_a_missing_build():
    refuses(lambda: call(checks=[]), "has not reported")


def test_refuses_a_failing_build_listed_after_a_success():
    """A head can carry BOTH a check-run and a commit status named `build` (the collector appends
    check-runs, then statuses). Returning on the first match let a success hide a later failure."""
    checks = [build_run(), build_run(conclusion="failure")]
    refuses(lambda: call(checks=checks), "concluded 'failure'")


def test_allows_when_every_build_entry_is_green():
    checks = [build_run(), build_run()]
    assert call(checks=checks)["area"] == AREA


def test_refuses_a_build_for_another_commit():
    """A green build on an earlier commit says nothing about the head being merged."""
    refuses(lambda: call(checks=[build_run(head_sha="0" * 40)]), "names head")


def test_refuses_a_build_with_missing_provenance():
    """Defaulting an absent field to the acceptable value meant a bare
    {"name": "build", "conclusion": "SUCCESS"} passed: no app to check, status assumed completed."""
    refuses(lambda: call(checks=[{"name": "build", "conclusion": "SUCCESS"}]), "not a check run")
    refuses(lambda: call(checks=[build_run(app_id=None)]), "reported by app")
    refuses(lambda: call(checks=[build_run(status=None)]), "not completed")
    # Case matters: GitHub emits lowercase, so anything else was not written by GitHub.
    refuses(lambda: call(checks=[build_run(conclusion="SUCCESS")]), "concluded")


for _name, _fn in sorted(globals().items()):
    if _name.startswith("test_") and callable(_fn):
        check(_name, _fn)

print()
if failures:
    print(f"{len(failures)} failure(s): {', '.join(failures)}")
    sys.exit(1)
print("all tests passed")
