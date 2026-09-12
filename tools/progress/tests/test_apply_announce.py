"""Tests for the pure parts of `apply` and `announce`: naming, bodies, idempotency, sanitising.

The git and network paths are exercised by the live verification steps in the plan, not here; what
is unit-tested is everything that decides *what* those paths will do.
"""

import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from progress import announce, apply as apply_mod, files, zulip  # noqa: E402

failures = []


def check(name, fn):
    try:
        fn()
    except Exception as exc:  # noqa: BLE001
        failures.append(name)
        print(f"FAIL {name}: {type(exc).__name__}: {exc}")
    else:
        print(f"ok   {name}")


A = "a1b2c3d" + "0" * 33
B = "b9c8d7e" + "0" * 33

PROSE = "Harnack's inequality landed for a nonnegative harmonic function on a planar disc, in both the two-sided comparison with the centre value and the pairwise form on a closed subdisc with the sharp constant. The supporting mean-value machinery was extracted along the way, and the remaining Layer 2 targets are untouched."

PLAN = {
    "roadmap": "ContourIntegration",
    "rel_dir": "TauCetiRoadmap/ContourIntegration",
    "from_sha": A,
    "to_sha": B,
    "prs": [1464, 966, 1244],
    "from_date": "2026-07-28T09:11:00+00:00",
    "to_date": "2026-07-30T11:34:41+00:00",
    "status_path": "TauCetiRoadmap/ContourIntegration/STATUS.md",
    "progress_path": "TauCetiRoadmap/ContourIntegration/PROGRESS.md",
}


# ----- apply: naming ---------------------------------------------------------------------------


def test_branch_name_is_a_pure_function_of_the_window():
    b1 = apply_mod.branch_name(PLAN)
    b2 = apply_mod.branch_name(dict(PLAN))
    assert b1 == b2 == "progress/a1b2c3d-b9c8d7e/ContourIntegration", b1
    # Two workers computing the same window compute the same branch, which is what lets the second
    # find the first one's work instead of duplicating it.
    other = dict(PLAN, to_sha="c" * 40)
    assert apply_mod.branch_name(other) != b1


def test_branch_name_area_is_the_last_segment():
    """plan.build_plan reads the area back off an open PR's branch as the last path segment."""
    branch = apply_mod.branch_name(PLAN)
    assert branch.split("/")[-1] == PLAN["roadmap"]


def test_pr_title_carries_the_due_check_prefix():
    title = apply_mod.pr_title(PLAN)
    # A squash merge turns the title into the commit subject, and `due` finds the last update by
    # scanning subjects for exactly this prefix. If these drift, the cadence check goes blind.
    from progress import plan as plan_mod
    assert title.startswith(plan_mod.COMMIT_PREFIX), title
    assert "ContourIntegration" in title and "2026-07-30" in title


def test_pr_body_records_the_window_and_prs():
    body = apply_mod.pr_body(PLAN, {}, version="deadbee")
    assert "a1b2c3d..b9c8d7e" in body
    assert "#966" in body and "#1464" in body
    assert "deadbee" in body
    assert "not\nsecurity-validated" in body or "not security-validated" in body
    assert "🤖 Prepared with Claude Code" in body


# ----- apply: rendering and validation ---------------------------------------------------------


def test_render_update_produces_a_valid_pair():
    status, progress, header = apply_mod.render_update(
        PLAN, PROSE, PROSE, None, None
    )
    assert header["prs"] == sorted(PLAN["prs"])
    assert header["from_sha"] == A and header["to_sha"] == B
    # The progress file is the fresh preamble plus exactly one section.
    assert progress.startswith("# Progress log: ContourIntegration")
    assert len(files.parse_sections(progress)) == 1


def test_render_update_appends_to_an_existing_log():
    old_log = files.new_progress_file("ContourIntegration") + files.render_section(
        "ContourIntegration", "9" * 40, A, [12], "earlier", PROSE
    )
    old_status = files.render_status("ContourIntegration", A, "t", PROSE)
    status, progress, header = apply_mod.render_update(
        PLAN, PROSE + " Now.", PROSE + " Also.", old_status, old_log
    )
    assert progress.startswith(old_log), "must be a pure append"
    assert len(files.parse_sections(progress)) == 2
    assert header["from_sha"] == A


def test_render_update_rejects_a_window_that_does_not_continue():
    """The generated section must continue the log, or the gate would refuse it later anyway."""
    old_log = files.new_progress_file("ContourIntegration") + files.render_section(
        "ContourIntegration", "9" * 40, "8" * 40, [12], "earlier", PROSE
    )
    try:
        apply_mod.render_update(PLAN, PROSE, PROSE, None, old_log)
    except files.FormatError as exc:
        assert "tile with no gap" in str(exc), str(exc)
        return
    raise AssertionError("expected a FormatError")


def test_render_update_rejects_injected_marker():
    evil = PROSE + ' <!--tauceti-status:v1 {"roadmap":"PDE"}-->'
    try:
        apply_mod.render_update(PLAN, PROSE, evil, None, None)
    except files.FormatError as exc:
        assert "reserved marker" in str(exc)
        return
    raise AssertionError("expected a FormatError")


# ----- announce --------------------------------------------------------------------------------


def make_section():
    return files.render_section("PDE", A, B, [1299, 1300], "2026-07-29 to 2026-07-30",
                                "Harnack's inequality landed, with the sharp constant.")


def test_split_section_handles_a_first_report_with_its_preamble():
    """Regression: the appended text of an area's FIRST report is the file preamble PLUS the section,
    so a splitter that assumed the text began at the marker leaked the preamble and a raw
    `<!--tauceti-progress:v1 ...-->` marker into the Zulip post."""
    added = files.new_progress_file("PDE") + files.render_section(
        "PDE", A, B, [1], "w", "Harnack landed."
    )
    header, prose = announce.split_section(added)
    assert header["roadmap"] == "PDE"
    assert prose == "Harnack landed.", repr(prose)
    assert "append-only record" not in prose
    assert "tauceti-progress:v1" not in prose
    msg = announce.render_message(header, prose)
    assert "# Progress log" not in msg
    assert "tauceti-progress:v1" not in msg


def test_split_section_strips_machine_furniture():
    header, prose = announce.split_section(make_section())
    assert header["roadmap"] == "PDE"
    assert prose.startswith("Harnack"), prose
    assert "tauceti-progress:v1" not in prose
    assert not prose.startswith("##")


def test_section_id_is_stable_and_window_scoped():
    header, _ = announce.split_section(make_section())
    assert announce.section_id(header) == f"PDE-{A[:7]}-{B[:7]}"


def test_message_contains_the_id_and_a_link():
    header, prose = announce.split_section(make_section())
    msg = announce.render_message(header, prose)
    assert f"{announce.ID_PREFIX}PDE-{A[:7]}-{B[:7]}" in msg
    assert "PROGRESS.md" in msg
    assert "STATUS.md" in msg
    assert "[Current roadmap status](" in msg
    assert "2 merged pull requests" in msg


def test_message_links_completed_roadmaps_under_completed():
    header, prose = announce.split_section(make_section())
    msg = announce.render_message(header, prose, roadmap_parent="Completed")
    assert "/Completed/PDE/PROGRESS.md" in msg
    assert "/Completed/PDE/STATUS.md" in msg
    assert "/TauCetiRoadmap/PDE/" not in msg


def test_message_is_capped():
    header, _ = announce.split_section(make_section())
    msg = announce.render_message(header, "x " * 20000)
    assert len(msg) < announce.MAX_MESSAGE_CHARS + 500
    assert "truncated" in msg


def test_already_posted_requires_an_exact_id_match():
    """Zulip search is word-based, so a near match must not count as already-announced."""
    sid = "PDE-aaaaaaa-bbbbbbb"

    class FakeClient:
        def __init__(self, contents):
            self.contents = contents

        def search(self, channel, topic, query):
            return [{"id": i, "content": c} for i, c in enumerate(self.contents)]

    near = FakeClient([f"{announce.ID_PREFIX}PDE-aaaaaaa-ccccccc"])
    assert announce.already_posted(near, "c", "t", sid) is None
    exact = FakeClient(["unrelated", f"text {announce.ID_PREFIX}{sid} more"])
    assert announce.already_posted(exact, "c", "t", sid) is not None


# ----- Zulip sanitising ------------------------------------------------------------------------


def test_sanitize_defuses_mentions_and_bare_hashes():
    out = zulip.sanitize("ping @all and see #1234")
    assert "@​" in out
    assert "#​1234" in out


def test_sanitize_keeps_repo_linkifiers():
    """Kim asked for `TauCeti#NNN` linkifiers rather than markdown links, so these must survive --
    including the all-lowercase `mathlib4#NNNNN` form."""
    out = zulip.sanitize("added in TauCeti#966 and mathlib4#33505")
    assert "TauCeti#966" in out, out
    assert "mathlib4#33505" in out, out


def test_sanitize_leaves_headings_and_plain_hashes_alone():
    """Defusing every `#` would corrupt a markdown heading in the generated prose."""
    assert zulip.sanitize("## Highlights") == "## Highlights"
    assert zulip.sanitize("C# is not relevant here") == "C# is not relevant here"



# ----- publishing without push access ----------------------------------------------------------


def test_push_target_prefers_the_canonical_repo():
    """No fork to keep alive, and the branch is deleted after the merge."""
    orig = apply_mod.gh.gh
    apply_mod.gh.gh = lambda args, **kw: "true\n"
    try:
        remote, owner = apply_mod.push_target("/nonexistent")
    finally:
        apply_mod.gh.gh = orig
    assert (remote, owner) == ("origin", None)


def test_push_target_falls_back_to_a_fork():
    """Publishing is open to anyone, so most operators will not have push access.

    The stubs below return exactly what `gh` prints, raw and unquoted, because that detail is the
    whole reliability of this path.
    """
    calls = []
    orig_gh, orig_run = apply_mod.gh.gh, apply_mod._run

    def fake_gh(args, **kw):
        calls.append(args)
        if args[:2] == ["api", "repos/TauCetiProject/TauCetiRoadmap"]:
            return "false\n"
        if args[0] == "api" and any("/forks" in a for a in args):
            # The jq already filtered on `.parent.full_name`, so a hit means a genuine fork.
            return "someone/roadmap-fork\n"
        if args[:2] == ["api", "user"]:
            # Exactly what `gh api user --jq .login` prints: a raw, UNQUOTED login. An earlier
            # version parsed this as JSON, which raises -- on the one path that needs it to work.
            return "someone\n"
        return ""

    class P:
        returncode = 1
    apply_mod.gh.gh = fake_gh
    apply_mod._run = lambda *a, **kw: P()
    try:
        remote, owner = apply_mod.push_target("/nonexistent")
    finally:
        apply_mod.gh.gh, apply_mod._run = orig_gh, orig_run
    assert (remote, owner) == ("fork", "someone")
    assert ["repo", "fork", "TauCetiProject/TauCetiRoadmap", "--clone=false", "--remote=false"] in calls


# ----- a stranger must not be able to lock a window ---------------------------------------------


def _with_pr_rows(rows):
    orig = apply_mod.gh.gh
    def fake(args, **kw):
        if args[:2] == ["api", "user"]:
            return "kim-em\n"
        return json.dumps(rows)
    apply_mod.gh.gh = fake
    try:
        return apply_mod.own_pr("progress/a1b2c3d-b9c8d7e/PDE", states=("closed",))
    finally:
        apply_mod.gh.gh = orig


def test_a_strangers_closed_pr_does_not_lock_the_window():
    """The attack: branch names are a pure function of the window, so anyone can open and instantly
    close a pull request on that name. Honouring it would stop the window ever being published."""
    rows = [{"number": 1, "state": "CLOSED", "url": "u", "mergedAt": None,
             "headRepositoryOwner": {"login": "stranger"}}]
    assert _with_pr_rows(rows) is None


def test_our_own_closed_pr_still_locks_the_window():
    """A report we filed and someone rejected must not come back by itself every day."""
    for owner in ("kim-em", "TauCetiProject"):
        rows = [{"number": 1, "state": "CLOSED", "url": "u", "mergedAt": None,
                 "headRepositoryOwner": {"login": owner}}]
        assert _with_pr_rows(rows) is not None, owner


def test_a_merged_pr_is_not_treated_as_a_rejection():
    rows = [{"number": 1, "state": "MERGED", "url": "u", "mergedAt": "2026-07-30T00:00:00Z",
             "headRepositoryOwner": {"login": "kim-em"}}]
    assert _with_pr_rows(rows) is None


def test_a_strangers_open_pr_does_not_block_us():
    """Otherwise anyone could freeze a roadmap by opening one pull request a day."""
    rows = [{"number": 1, "state": "OPEN", "url": "u", "mergedAt": None,
             "headRepositoryOwner": {"login": "stranger"}}]
    orig = apply_mod.gh.gh
    def fake(args, **kw):
        if args[:2] == ["api", "user"]:
            return "kim-em\n"
        return json.dumps(rows)
    apply_mod.gh.gh = fake
    try:
        assert apply_mod.own_pr("progress/a1b2c3d-b9c8d7e/PDE", states=("open",)) is None
    finally:
        apply_mod.gh.gh = orig


def test_push_target_requires_the_fork_to_be_a_fork_of_this_repo():
    """A repository that merely shares the name is not a fork; pushing a report there is wrong."""
    orig_gh, orig_run = apply_mod.gh.gh, apply_mod._run

    def fake_gh(args, **kw):
        if args[:2] == ["api", "repos/TauCetiProject/TauCetiRoadmap"]:
            return "false\n"
        if args[:2] == ["api", "user"]:
            return "someone\n"
        if args[0] == "api" and any("/forks" in a for a in args):
            return ""            # not in the fork listing
        if args[0] == "api":
            return "\n"          # `.parent.full_name` empty: an unrelated same-named repo
        return ""

    class P:
        returncode = 1
    apply_mod.gh.gh, apply_mod._run = fake_gh, lambda *a, **kw: P()
    try:
        apply_mod.push_target("/nonexistent")
    except RuntimeError as exc:
        assert "could not identify a fork" in str(exc)
    else:
        raise AssertionError("an unrelated same-named repository must not be used")
    finally:
        apply_mod.gh.gh, apply_mod._run = orig_gh, orig_run

for _name, _fn in sorted(globals().items()):
    if _name.startswith("test_") and callable(_fn):
        check(_name, _fn)

print()
if failures:
    print(f"{len(failures)} failure(s): {', '.join(failures)}")
    sys.exit(1)
print("all tests passed")
