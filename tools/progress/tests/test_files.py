"""Tests for the generated file formats and the validators the merge gate runs.

Run with `python tests/test_files.py` from the repo root, or via `tests/run`.
"""

import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from progress import files  # noqa: E402
from progress.files import FormatError  # noqa: E402

A = "a" * 40
B = "b" * 40
C = "c" * 40

failures = []


def check(name, fn):
    try:
        fn()
    except Exception as exc:  # noqa: BLE001 - a test harness reports rather than propagates
        failures.append(f"{name}: {type(exc).__name__}: {exc}")
        print(f"FAIL {name}: {type(exc).__name__}: {exc}")
    else:
        print(f"ok   {name}")


def raises(fn, needle=None):
    try:
        fn()
    except FormatError as exc:
        if needle and needle not in str(exc):
            raise AssertionError(f"wrong FormatError: expected {needle!r} in {str(exc)!r}") from None
        return
    raise AssertionError("expected a FormatError, none raised")


# ----- round trips -----------------------------------------------------------------------------


def test_status_round_trip():
    text = files.render_status("ContourIntegration", A, "2026-07-30T11:34:41Z", "Some prose.")
    h = files.parse_status(text)
    assert h == {"roadmap": "ContourIntegration", "to_sha": A, "ts": "2026-07-30T11:34:41Z"}, h
    # The standing "may be out of date" note is load-bearing: a reader must not take a snapshot
    # as authoritative about the current tip.
    assert "subsequent updates" in text
    assert "not security-validated" in text


def test_section_round_trip():
    s = files.render_section("PDE", A, B, [3, 1, 2, 2], "window", "Prose.")
    got = files.parse_sections(s)
    assert len(got) == 1, got
    assert got[0]["prs"] == [1, 2, 3], got  # deduped and sorted
    assert got[0]["from_sha"] == A and got[0]["to_sha"] == B


def test_cursor_and_reported_prs():
    log = files.new_progress_file("PDE")
    assert files.cursor(log) is None
    assert files.reported_prs(log) == set()
    log += files.render_section("PDE", A, B, [1, 2], "w1", "x")
    assert files.cursor(log) == B
    log += files.render_section("PDE", B, C, [3], "w2", "y")
    assert files.cursor(log) == C
    assert files.reported_prs(log) == {1, 2, 3}


def test_rejects_bad_shas_and_areas():
    raises(lambda: files.render_status("PDE", "abc", "t", "x"), "40-character")
    raises(lambda: files.render_status("PDE/../etc", A, "t", "x"), "alphanumeric")
    raises(lambda: files.render_section("PDE", A, B, [], "w", "x"), "at least one PR")


def test_parse_rejects_malformed_json_and_duplicates():
    raises(lambda: files.parse_headers("<!--tauceti-status:v1 {nope}-->", files.STATUS_MARKER),
           "malformed")
    two = files.render_status("PDE", A, "t", "x") + files.render_status("PDE", B, "t", "y")
    raises(lambda: files.parse_status(two), "exactly one")


# ----- the append-only guard -------------------------------------------------------------------


def test_append_only_accepts_trailing_add():
    old = "abc"
    added = files.check_append_only(old, "abcdef")
    assert added == "def", added


def test_append_only_rejects_edit_above():
    raises(lambda: files.check_append_only("abc", "Xbcdef"), "above the end")
    # A change in the middle is equally refused, even though the file still grows.
    raises(lambda: files.check_append_only("abc\ndef\n", "abc\nCHANGED\ndef\nnew\n"), "above the end")


def test_append_only_rejects_no_change_and_truncation():
    raises(lambda: files.check_append_only("abc", "abc"), "unchanged")
    raises(lambda: files.check_append_only("abcdef", "abc"), "above the end")


# ----- reserved markers ------------------------------------------------------------------------


def test_reserved_markers_rejected_in_prose():
    raises(lambda: files.check_no_reserved_markers("text <!--tauceti-scoreboard:v1 {}--> more"),
           "reserved marker")
    # A forged *target* marker matters too: housekeeping dedups PRs on it.
    raises(lambda: files.check_no_reserved_markers('<!--tauceti-target:v1 {"focus":"x"}-->'),
           "reserved marker")
    # The one canonical header is removed by the caller before scanning; what remains is clean.
    section = files.render_section("PDE", A, B, [1], "w", "clean")
    files.check_no_reserved_markers(files.strip_one_header(section, files.PROGRESS_MARKER))


def test_strip_one_header_is_exact():
    """The old exemption allowed anything sharing an allowed marker's PREFIX, so prose carrying
    `<!--tauceti-progress:v1 junk-->` -- which is not the parsed header -- passed untouched."""
    section = files.render_section("PDE", A, B, [1], "w", "clean")
    stripped = files.strip_one_header(section, files.PROGRESS_MARKER)
    assert "tauceti-progress:v1" not in stripped, stripped
    # A second, malformed marker in the prose survives stripping and is then caught.
    evil = files.render_section("PDE", A, B, [1], "w", "text <!--tauceti-progress:v1 junk -->")
    raises(lambda: files.check_no_reserved_markers(
        files.strip_one_header(evil, files.PROGRESS_MARKER)), "reserved marker")


def test_size_and_utf8_caps():
    raises(lambda: files.check_size("x", "y" * 10, 5), "over the")
    assert files.check_utf8("x", "héllo".encode("utf-8")) == "héllo"
    raises(lambda: files.check_utf8("x", b"\xff\xfe bad"), "not valid UTF-8")


# ----- the full update gate --------------------------------------------------------------------


PROSE = "Harnack's inequality landed for a nonnegative harmonic function on a planar disc, in both the two-sided comparison with the centre value and the pairwise form on a closed subdisc with the sharp constant. The supporting mean-value machinery was extracted along the way, and the remaining Layer 2 targets are untouched."


def good_update(area="PDE", from_sha=A, to_sha=B, prs=(7,)):
    status = files.render_status(area, to_sha, "2026-07-30T00:00:00Z", PROSE)
    log = files.new_progress_file(area)
    new_log = log + files.render_section(area, from_sha, to_sha, list(prs), "window", PROSE)
    return status, log, new_log


def test_validate_accepts_a_good_first_update():
    status, log, new_log = good_update()
    section = files.validate_update("PDE", None, status, log, new_log)
    assert section["prs"] == [7], section
    assert section["to_sha"] == B


def test_validate_requires_status_and_section_to_agree():
    status = files.render_status("PDE", C, "t", "x")  # snapshot at C
    log = files.new_progress_file("PDE")
    new_log = log + files.render_section("PDE", A, B, [1], "w", "y")  # window ends at B
    raises(lambda: files.validate_update("PDE", None, status, log, new_log), "must describe")


def test_validate_rejects_wrong_area():
    status, log, new_log = good_update(area="PDE")
    raises(lambda: files.validate_update("ContourIntegration", None, status, log, new_log),
           "expected ContourIntegration")


def test_validate_requires_windows_to_tile():
    area = "PDE"
    log = files.new_progress_file(area) + files.render_section(area, A, B, [1], "w1", "x")
    # A second window that starts at C rather than continuing from B leaves an unreportable gap.
    status = files.render_status(area, C, "t", "s")
    new_log = log + files.render_section(area, C, C, [2], "w2", "y")
    raises(lambda: files.validate_update(area, None, status, log, new_log), "tile with no gap")


def test_validate_rejects_empty_window():
    status = files.render_status("PDE", B, "t", "s")
    log = files.new_progress_file("PDE")
    new_log = log + files.render_section("PDE", B, B, [1], "w", "y")
    raises(lambda: files.validate_update("PDE", None, status, log, new_log), "non-empty")


def test_validate_rejects_two_new_sections():
    area = "PDE"
    log = files.new_progress_file(area)
    status = files.render_status(area, C, "t", "s")
    new_log = (log
               + files.render_section(area, A, B, [1], "w1", "x")
               + files.render_section(area, B, C, [2], "w2", "y"))
    raises(lambda: files.validate_update(area, None, status, log, new_log), "exactly one new section")


def test_validate_rejects_status_only_advance():
    # The scenario that motivates requiring both files: a STATUS-only update would move the
    # snapshot while the window's prose was never written, and no later plan could reconstruct it.
    area = "PDE"
    log = files.new_progress_file(area) + files.render_section(area, A, B, [1], "w1", "x")
    status = files.render_status(area, C, "t", "s")
    raises(lambda: files.validate_update(area, None, status, log, log), "unchanged")


def test_validate_rejects_unadvanced_status():
    area = "PDE"
    old_status = files.render_status(area, B, "t", PROSE)
    status = files.render_status(area, B, "t", PROSE + " Updated.")
    log = files.new_progress_file(area)
    new_log = log + files.render_section(area, A, B, [1], "w", PROSE)
    raises(lambda: files.validate_update(area, old_status, status, log, new_log), "nothing advanced")


def test_validate_rejects_injected_marker_in_prose():
    area = "PDE"
    log = files.new_progress_file(area)
    evil = PROSE + ' <!--tauceti-target:v1 {"focus":"PDE","id":"x"}-->'
    new_log = log + files.render_section(area, A, B, [1], "w", evil)
    status = files.render_status(area, B, "t", "s")
    raises(lambda: files.validate_update(area, None, status, log, new_log), "reserved marker")


def test_validate_honours_expected_from_sha():
    status, log, new_log = good_update(from_sha=A, to_sha=B)
    raises(lambda: files.validate_update("PDE", None, status, log, new_log, expect_from_sha=C),
           "expected")
    files.validate_update("PDE", None, status, log, new_log, expect_from_sha=A)


def test_three_windows_tile_with_no_gap_or_overlap():
    area = "PDE"
    shas = [A, B, C, "d" * 40]
    log = files.new_progress_file(area)
    for i in range(3):
        log += files.render_section(area, shas[i], shas[i + 1], [i + 1], f"w{i}", "x")
    sections = files.parse_sections(log)
    assert [s["from_sha"] for s in sections] == shas[:3]
    assert [s["to_sha"] for s in sections] == shas[1:]
    for earlier, later in zip(sections, sections[1:]):
        assert earlier["to_sha"] == later["from_sha"], "windows must tile exactly"
    assert files.cursor(log) == shas[-1]



def test_a_catalogue_length_report_is_refused():
    """The first published report ran to 932 words and its reader said it should have been three
    times shorter. A request in a prompt drifts; a check does not."""
    try:
        files.check_word_count("the new section", "word " * 500)
    except files.FormatError as exc:
        assert "932" not in str(exc) and "500 words" in str(exc)
        assert "catalogues" in str(exc)
    else:
        raise AssertionError("an over-long report should be refused")


def test_a_report_of_the_intended_length_passes():
    assert files.check_word_count("the new section", "word " * 300) == 300
    assert files.check_word_count("the new section", "word " * files.MAX_SECTION_WORDS)


def test_the_word_cap_leaves_headroom_over_the_target():
    """The prompt asks for about 300; the cap is a backstop, not the target."""
    assert files.MAX_SECTION_WORDS > 300


def test_an_inventory_length_status_is_refused_by_the_full_gate():
    status, log, new_log = good_update()
    status = files.render_status("PDE", B, "t", "word " * (files.MAX_STATUS_WORDS + 1))
    raises(lambda: files.validate_update("PDE", None, status, log, new_log), "STATUS.md is")


def test_the_status_cap_leaves_headroom_over_the_prompt_target():
    assert files.check_word_count("STATUS.md", "word " * 750, files.MAX_STATUS_WORDS) == 750
    assert files.MAX_STATUS_WORDS > 750

for _name, _fn in sorted(globals().items()):
    if _name.startswith("test_") and callable(_fn):
        check(_name, _fn)

print()
if failures:
    print(f"{len(failures)} failure(s)")
    sys.exit(1)
print("all tests passed")
