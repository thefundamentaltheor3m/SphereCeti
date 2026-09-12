"""Tests for window arithmetic and the plan decision.

The git-touching parts are exercised against a real throwaway repository built in a temp dir, so
the ancestry and half-open-range behaviour is tested against actual git rather than a mock that
could encode the same mistake twice.
"""

import datetime
import os
import pathlib
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from progress import files, plan, window  # noqa: E402

failures = []


def check(name, fn):
    try:
        fn()
    except Exception as exc:  # noqa: BLE001
        failures.append(name)
        print(f"FAIL {name}: {type(exc).__name__}: {exc}")
    else:
        print(f"ok   {name}")


def raises(exc_type, fn, needle=None):
    try:
        fn()
    except exc_type as exc:
        if needle and needle not in str(exc):
            raise AssertionError(f"expected {needle!r} in {str(exc)!r}") from None
        return
    raise AssertionError(f"expected {exc_type.__name__}, none raised")


# ----- subject parsing -------------------------------------------------------------------------


def test_pr_number_of_subject():
    assert window.pr_number_of_subject("feat: add products (#1433)") == 1433
    assert window.pr_number_of_subject("Merge pull request #62 from TauCetiProject/x") == 62
    assert window.pr_number_of_subject("chore: no number here") is None
    # A number in the middle is not a merge marker; only the trailing form counts.
    assert window.pr_number_of_subject("fix: handle (#12) in parser") is None


def test_pr_numbers_from_log_dedupes_and_keeps_order():
    log = "feat: a (#3)\nfix: b (#2)\nfeat: c (#3)\nchore: none\nMerge pull request #1 from x\n"
    assert window.pr_numbers_from_log(log) == [3, 2, 1]


# ----- a real git repo -------------------------------------------------------------------------


def make_repo(tmp, subjects):
    """A repo whose mainline is one commit per subject, oldest first. Returns [sha] aligned to it."""
    subprocess.run(["git", "init", "-q", "-b", "main", tmp], check=True, capture_output=True)
    # Inherit the real environment (git must stay on PATH) and only pin identity and dates, so
    # commit SHAs are reproducible without breaking the tool lookup.
    env = {
        **os.environ,
        "GIT_AUTHOR_NAME": "T", "GIT_AUTHOR_EMAIL": "t@e",
        "GIT_COMMITTER_NAME": "T", "GIT_COMMITTER_EMAIL": "t@e",
        "GIT_AUTHOR_DATE": "2026-01-01T00:00:00Z", "GIT_COMMITTER_DATE": "2026-01-01T00:00:00Z",
    }
    shas = []
    for i, subject in enumerate(subjects):
        (pathlib.Path(tmp) / f"f{i}").write_text(str(i))
        subprocess.run(["git", "-C", tmp, "add", "-A"], check=True, capture_output=True, env=env)
        subprocess.run(["git", "-C", tmp, "commit", "-q", "-m", subject],
                       check=True, capture_output=True, env=env)
        shas.append(window.git(["rev-parse", "HEAD"], tmp).strip())
    return shas


def test_window_is_half_open_and_excludes_from_sha():
    with tempfile.TemporaryDirectory() as tmp:
        shas = make_repo(tmp, ["init", "a (#1)", "b (#2)", "c (#3)"])
        # (shas[1], shas[3]] must contain #2 and #3, and must NOT contain #1.
        got = window.window_prs(tmp, shas[1], shas[3])
        assert got == [3, 2], got
        # The whole history from the root's parent is not expressible, which is exactly why
        # bootstrap uses first_parent_before on the earliest *merge*, not on the root.
        got_all = window.window_prs(tmp, shas[0], shas[3])
        assert got_all == [3, 2, 1], got_all


def test_bootstrap_parent_includes_the_first_pr():
    with tempfile.TemporaryDirectory() as tmp:
        shas = make_repo(tmp, ["init", "a (#1)", "b (#2)"])
        merge = window.find_merge_commit(tmp, 1, ref="main")
        assert merge == shas[1], merge
        from_sha = window.first_parent_before(tmp, merge)
        assert from_sha == shas[0]
        # With the parent as cursor, #1 is reported. With the merge itself, it would be lost.
        assert window.window_prs(tmp, from_sha, shas[2]) == [2, 1]
        assert window.window_prs(tmp, merge, shas[2]) == [2]


def test_ancestry_is_asserted():
    with tempfile.TemporaryDirectory() as tmp:
        shas = make_repo(tmp, ["init", "a (#1)"])
        assert window.is_ancestor(tmp, shas[0], shas[1]) is True
        assert window.is_ancestor(tmp, shas[1], shas[0]) is False
        # A cursor that is not an ancestor means rewritten history or a foreign cursor. Refuse.
        raises(window.GitError, lambda: window.window_prs(tmp, shas[1], shas[0]), "not an ancestor")


def test_consecutive_windows_tile_with_no_gap_or_overlap():
    with tempfile.TemporaryDirectory() as tmp:
        shas = make_repo(tmp, ["init", "a (#1)", "b (#2)", "c (#3)", "d (#4)"])
        w1 = window.window_prs(tmp, shas[0], shas[2])
        w2 = window.window_prs(tmp, shas[2], shas[4])
        assert w1 == [2, 1], w1
        assert w2 == [4, 3], w2
        assert not set(w1) & set(w2), "windows must not overlap"
        assert set(w1) | set(w2) == {1, 2, 3, 4}, "windows must leave no gap"


def test_head_sha_and_commit_date():
    with tempfile.TemporaryDirectory() as tmp:
        shas = make_repo(tmp, ["init", "a (#1)"])
        assert window.head_sha(tmp, ref="main") == shas[-1]
        assert window.commit_date(tmp, shas[-1]).startswith("2026-")


# ----- cadence ---------------------------------------------------------------------------------


NOW = datetime.datetime(2026, 7, 30, 12, 0, tzinfo=datetime.timezone.utc)


def test_cadence_never_updated():
    reason = plan.check_cadence([("2026-07-30T11:00:00Z", "feat: something else (#1)")], now=NOW)
    assert "ever" in reason, reason


def test_cadence_too_recent_raises():
    commits = [("2026-07-30T09:00:00Z", "progress: PDE 2026-07-30 (#9)")]
    raises(plan.NotDue, lambda: plan.check_cadence(commits, now=NOW), "3.0h ago")


def test_cadence_old_enough_passes():
    commits = [("2026-07-28T12:00:00Z", "progress: PDE (#9)")]
    reason = plan.check_cadence(commits, now=NOW)
    assert "48.0h" in reason, reason


def test_cadence_ignores_non_progress_commits():
    commits = [
        ("2026-07-30T11:00:00Z", "doc: sharpen a target (#91)"),
        ("2026-07-27T12:00:00Z", "progress: PDE (#9)"),
    ]
    reason = plan.check_cadence(commits, now=NOW)
    assert "72.0h" in reason, reason


# ----- area discovery --------------------------------------------------------------------------


def test_discover_areas_matches_canonical_rule():
    """Shaped after the real origin/main tree: nested RepresentationTheory, a Completed area, a
    references/ dir that must NOT count, and an area with no Suggested.lean."""
    with tempfile.TemporaryDirectory() as tmp:
        root = pathlib.Path(tmp)
        for rel in [
            "TauCetiRoadmap/PDE",
            "TauCetiRoadmap/ContourIntegration",
            "TauCetiRoadmap/OneParameterSemigroups",     # README only, no Suggested.lean
            "TauCetiRoadmap/RepresentationTheory",
            "TauCetiRoadmap/RepresentationTheory/RootSystems",   # nested: not a top-level area
            "TauCetiRoadmap/GeometricTopology",
            "TauCetiRoadmap/GeometricTopology/references",       # has a README but is not an area
            "Completed/EffectiveBounds",
        ]:
            (root / rel).mkdir(parents=True)
            (root / rel / "README.md").write_text("#")
        (root / "TauCetiRoadmap/PDE/Suggested.lean").write_text("-- x")
        # A directory with no README is not an area.
        (root / "TauCetiRoadmap/NotAnArea").mkdir()

        areas = plan.discover_areas(root)
        assert set(areas) == {
            "PDE", "ContourIntegration", "OneParameterSemigroups", "RepresentationTheory",
            "GeometricTopology", "EffectiveBounds",
        }, sorted(areas)
        assert areas["PDE"] == "TauCetiRoadmap/PDE"
        assert areas["EffectiveBounds"] == "Completed/EffectiveBounds"
        assert "RootSystems" not in areas, "nested sub-roadmaps are not separate labelled areas"
        assert "references" not in areas


def test_read_area_files_missing_is_none():
    with tempfile.TemporaryDirectory() as tmp:
        root = pathlib.Path(tmp)
        (root / "TauCetiRoadmap/PDE").mkdir(parents=True)
        s, p = plan.read_area_files(root, "TauCetiRoadmap/PDE")
        assert s is None and p is None
        (root / "TauCetiRoadmap/PDE/PROGRESS.md").write_text("hi")
        s, p = plan.read_area_files(root, "TauCetiRoadmap/PDE")
        assert s is None and p == "hi"


# ----- attribution and duplicate rejection -----------------------------------------------------


def test_area_window_is_git_range_intersect_label_set():
    """Attribution is an intersection: git says which PRs are in the range, one label query per
    area says which PRs belong to it. #2 here is `roadmap/none`, so it is absent from the set."""
    with tempfile.TemporaryDirectory() as tmp:
        shas = make_repo(tmp, ["init", "a (#1)", "b (#2)", "c (#3)"])
        area_prs = {1, 3}
        got = plan.area_window(tmp, area_prs, shas[0], shas[3])
        assert got == [3, 1], got
        # A PR labelled for the area but outside the window must not appear.
        got_narrow = plan.area_window(tmp, area_prs, shas[2], shas[3])
        assert got_narrow == [3], got_narrow


def test_already_reported_prs_are_excluded():
    """A relabel after a section landed must not double-report. The section header records the PR
    numbers, and `reported_prs` is the authority."""
    log = files.new_progress_file("PDE") + files.render_section("PDE", "a" * 40, "b" * 40, [1, 2],
                                                                "w", "x")
    assert files.reported_prs(log) == {1, 2}
    fresh = [n for n in [3, 2, 1] if n not in files.reported_prs(log)]
    assert fresh == [3], fresh



def test_earliest_merged_is_by_merge_order_not_by_number():
    """The bug this exists to prevent, reproduced exactly.

    Numbers are assigned when a pull request is OPENED. If #100 opens first but merges after #101,
    starting a roadmap from the commit before #100's merge puts the cursor past #101 -- and windows
    only move forward, so #101 becomes unreportable for good. Two of the fourteen live roadmaps had
    this shape (RepresentationTheory #1227 vs #1228, OneParameterSemigroups #273 vs #276).
    """
    import tempfile, subprocess, os
    with tempfile.TemporaryDirectory() as d:
        def run(*args):
            subprocess.run(args, cwd=d, check=True, capture_output=True)
        env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e",
                   GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@e")
        subprocess.run(["git", "init", "-q", "-b", "main"], cwd=d, check=True, capture_output=True)
        for subject in ("root", "feat: later-numbered merges first (#101)",
                        "feat: lower-numbered merges second (#100)"):
            subprocess.run(["git", "commit", "-q", "--allow-empty", "-m", subject],
                           cwd=d, check=True, capture_output=True, env=env)
        got = window.earliest_merged(d, [100, 101], ref="main")
        assert got is not None and got[0] == 101, got
        # And the cursor derived from it is the commit BEFORE #101, so #101 is inside the window.
        cursor = window.first_parent_before(d, got[1])
        assert 101 in window.window_prs(d, cursor, "main")
        assert 100 in window.window_prs(d, cursor, "main")


def test_earliest_merged_ignores_unlabelled_pull_requests():
    import tempfile, subprocess, os
    with tempfile.TemporaryDirectory() as d:
        env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e",
                   GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@e")
        subprocess.run(["git", "init", "-q", "-b", "main"], cwd=d, check=True, capture_output=True)
        for subject in ("root", "chore: unrelated (#7)", "feat: ours (#9)"):
            subprocess.run(["git", "commit", "-q", "--allow-empty", "-m", subject],
                           cwd=d, check=True, capture_output=True, env=env)
        assert window.earliest_merged(d, [9], ref="main")[0] == 9
        assert window.earliest_merged(d, [], ref="main") is None
        assert window.earliest_merged(d, [12345], ref="main") is None


def test_a_labelled_pr_with_no_number_in_its_subject_fails_closed():
    """The hazard: `earliest_merged` finds pull requests by matching numbers in commit subjects.

    One whose merge subject omits its number is invisible, so the cursor would be computed from a
    LATER merge and skip it, permanently. Two implementations agreeing does not catch this -- they
    share the omission, which is how three earlier versions of this check passed review while wrong.
    """
    import os, subprocess, tempfile
    from progress import gh as gh_mod, plan as plan_mod
    with tempfile.TemporaryDirectory() as d:
        env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e",
                   GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@e")
        subprocess.run(["git", "init", "-q", "-b", "main"], cwd=d, check=True, capture_output=True)
        for subject in ("root", "feat: no number here at all", "feat: later one (#20)"):
            subprocess.run(["git", "commit", "-q", "--allow-empty", "-m", subject],
                           cwd=d, check=True, capture_output=True, env=env)
        # #10 merged as the numberless commit; resolve it the way the real check does.
        numberless = subprocess.run(["git", "rev-parse", "HEAD~1"], cwd=d,
                                    capture_output=True, text=True).stdout.strip()
        orig = gh_mod.gh
        gh_mod.gh = lambda args, **kw: numberless + "\n"
        try:
            assert plan_mod.unaccounted_prs(d, [10, 20], ref="main") == [10]
            raises(window.GitError,
                   lambda: plan_mod.bootstrap_from_sha(d, "PDE", [10, 20], ref="main"),
                   "no pull request number")
        finally:
            gh_mod.gh = orig


def test_a_merge_commit_this_checkout_never_fetched_is_not_fatal():
    """Hit for real while verifying this change: a pull request merged between the checkout's last
    fetch and the plan. `merge-base` FAILS on a commit it has never seen rather than answering "no",
    and that failure aborted the whole plan — every area — over one freshly merged pull request."""
    import os, subprocess, tempfile
    from progress import gh as gh_mod, plan as plan_mod
    with tempfile.TemporaryDirectory() as d:
        env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e",
                   GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@e")
        subprocess.run(["git", "init", "-q", "-b", "main"], cwd=d, check=True, capture_output=True)
        for subject in ("root", "feat: ours (#5)"):
            subprocess.run(["git", "commit", "-q", "--allow-empty", "-m", subject],
                           cwd=d, check=True, capture_output=True, env=env)
        assert not window.has_commit(d, "0" * 40)
        assert window.has_commit(d, window.head_sha(d, ref="main"))
        orig = gh_mod.gh
        gh_mod.gh = lambda args, **kw: "0" * 40 + "\n"  # GitHub names a commit we have not fetched
        try:
            assert plan_mod.unaccounted_prs(d, [5, 99], ref="main") == []
        finally:
            gh_mod.gh = orig


def test_a_labelled_pr_merged_after_the_tip_is_not_flagged():
    """Benign: it is not in this history yet, and a later window will cover it."""
    import os, subprocess, tempfile
    from progress import gh as gh_mod, plan as plan_mod
    with tempfile.TemporaryDirectory() as d:
        env = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@e",
                   GIT_COMMITTER_NAME="t", GIT_COMMITTER_EMAIL="t@e")
        subprocess.run(["git", "init", "-q", "-b", "main"], cwd=d, check=True, capture_output=True)
        for subject in ("root", "feat: ours (#5)"):
            subprocess.run(["git", "commit", "-q", "--allow-empty", "-m", subject],
                           cwd=d, check=True, capture_output=True, env=env)
        orig = gh_mod.gh
        gh_mod.gh = lambda args, **kw: "\n"        # no merge commit we can see
        try:
            assert plan_mod.unaccounted_prs(d, [5, 99], ref="main") == []
        finally:
            gh_mod.gh = orig


# ----- an area ahead of the published documentation --------------------------------------------


def make_roadmap(root, areas):
    """A roadmap checkout: `{area: progress_text_or_None}` under `TauCetiRoadmap/`."""
    for area, progress_text in areas.items():
        d = pathlib.Path(root) / "TauCetiRoadmap" / area
        d.mkdir(parents=True)
        (d / "README.md").write_text(f"# {area}\n", encoding="utf-8")
        if progress_text is not None:
            (d / "PROGRESS.md").write_text(progress_text, encoding="utf-8")


def plan_against(code_dir, roadmap_dir, docs_sha, area_prs, **kw):
    """`build_plan` with the network stubbed: a fixed documented build and fixed area labels."""
    from progress import gh as gh_mod, plan as plan_mod
    orig_docs, orig_labels = plan_mod.docs_source_commit, gh_mod.merged_prs_for_area
    plan_mod.docs_source_commit = lambda: docs_sha
    gh_mod.merged_prs_for_area = lambda area, **_: list(area_prs.get(area, []))
    try:
        return plan_mod.build_plan(
            roadmap_dir, code_dir,
            commits=[{"commit": {"committedDate": "2026-01-01T00:00:00Z"},
                      "messageHeadline": "progress: X (2026-01-01)"}],
            open_prs=[], ref="main", min_prs=1, **kw)
    finally:
        plan_mod.docs_source_commit, gh_mod.merged_prs_for_area = orig_docs, orig_labels


def test_an_area_newer_than_the_documented_build_is_skipped_not_fatal():
    """The outage this prevents: a roadmap whose first pull request merged after the last
    documentation deploy bootstraps to a cursor ahead of `to_sha`. `window_prs` refuses on that,
    and the exception aborted the WHOLE plan -- so one new roadmap stopped every area's reporting
    until a human read the traceback. The new area waits; the others must still be reportable."""
    with tempfile.TemporaryDirectory() as code, tempfile.TemporaryDirectory() as roadmap:
        shas = make_repo(code, ["init", "old: a (#1)", "old: b (#2)", "later", "new: c (#3)"])
        make_roadmap(roadmap, {"Old": None, "New": None})
        # The documentation was built at shas[2]. New bootstraps to the parent of #3's merge,
        # shas[3], which is newer than that -- exactly the shape a roadmap added this week has.
        got = plan_against(code, roadmap, shas[2], {"Old": [1, 2], "New": [3]})
        assert got["roadmap"] == "Old", got["roadmap"]
        assert got["prs"] == [2, 1], got["prs"]
        assert any("New" in s and "not published yet" in s for s in got["skipped"]), got["skipped"]


def test_docs_catching_up_reports_the_waiting_area_with_no_history_stranded():
    """The skip must defer an area, not drop it. Once the documentation reaches the commit, the same
    area reports, and its FIRST pull request is inside that first window."""
    with tempfile.TemporaryDirectory() as code, tempfile.TemporaryDirectory() as roadmap:
        shas = make_repo(code, ["init", "old: a (#1)", "old: b (#2)", "later", "new: c (#3)"])
        make_roadmap(roadmap, {"Old": None, "New": None})
        got = plan_against(code, roadmap, shas[4], {"Old": [1, 2], "New": [3]}, only_area="New")
        assert got["roadmap"] == "New", got["roadmap"]
        assert got["prs"] == [3], got["prs"]


def test_a_recorded_cursor_ahead_of_the_docs_says_so_plainly():
    """A cursor written by an earlier report, now ahead of the published build: the documentation
    rolled back. Skipping is right — a backwards window would be nonsense — but a reader must not be
    told this is the ordinary "not published yet" case."""
    with tempfile.TemporaryDirectory() as code, tempfile.TemporaryDirectory() as roadmap:
        shas = make_repo(code, ["init", "a (#1)", "b (#2)", "c (#3)"])
        make_roadmap(roadmap, {"Old": files.new_progress_file("Old") + files.render_section(
            "Old", shas[0], shas[3], [1, 2, 3], "2026-01-01", "prose " * 60)})
        raises(plan.NotDue, lambda: plan_against(code, roadmap, shas[1], {"Old": [1, 2, 3]}),
               "went backwards")


def test_a_cursor_in_no_history_at_all_is_still_refused():
    """The skip is narrow on purpose. A cursor that is in neither the documented history nor the
    branch is the rewritten-branch case, and staying loud there is the whole point of the check."""
    with tempfile.TemporaryDirectory() as code, tempfile.TemporaryDirectory() as roadmap:
        shas = make_repo(code, ["init", "a (#1)", "b (#2)"])
        # A commit off the mainline: reachable as an object, on no branch. That is what a cursor
        # written before a rewrite looks like, and it is an ancestor of nothing we report from.
        subprocess.run(["git", "-C", code, "checkout", "-q", "--detach", shas[0]],
                       check=True, capture_output=True)
        subprocess.run(["git", "-C", code, "commit", "-q", "--allow-empty", "-m", "rewritten (#9)"],
                       check=True, capture_output=True,
                       env={**os.environ, "GIT_AUTHOR_NAME": "T", "GIT_AUTHOR_EMAIL": "t@e",
                            "GIT_COMMITTER_NAME": "T", "GIT_COMMITTER_EMAIL": "t@e"})
        orphan = window.git(["rev-parse", "HEAD"], code).strip()
        subprocess.run(["git", "-C", code, "checkout", "-q", "main"], check=True, capture_output=True)
        # The cursor is the newest section's `to_sha`, and this one names history we cannot reach.
        make_roadmap(roadmap, {"Old": files.new_progress_file("Old") + files.render_section(
            "Old", shas[0], orphan, [1], "2026-01-01", "prose " * 60)})
        raises(window.GitError,
               lambda: plan_against(code, roadmap, shas[2], {"Old": [1, 2]}),
               "not an ancestor")


for _name, _fn in sorted(globals().items()):
    if _name.startswith("test_") and callable(_fn):
        check(_name, _fn)

print()
if failures:
    print(f"{len(failures)} failure(s): {', '.join(failures)}")
    sys.exit(1)
print("all tests passed")
