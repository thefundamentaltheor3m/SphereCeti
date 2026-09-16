"""Tests for resolving a reported window against real TauCeti history.

Anyone may open a progress pull request, so this is what keeps that bounded: `to_sha` must name a
commit the project actually published, strictly after `from_sha`. Without it a chain of reports could
walk the cursor to arbitrary values, announcing every step.
"""

import importlib.util
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

_spec = importlib.util.spec_from_file_location("collect", ROOT / ".github" / "scripts" / "collect.py")
collect = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(collect)

from progress import files  # noqa: E402

failures = []


def check(name, fn):
    try:
        fn()
    except Exception as exc:  # noqa: BLE001
        failures.append(name)
        print(f"FAIL {name}: {type(exc).__name__}: {exc}")
    else:
        print(f"ok   {name}")


AREA = "PDE"
FROM = "a" * 40
TO = "b" * 40
TIP = "d" * 40  # what `docgen` resolves to; pinned once per run, never re-read
PROSE = ("Harnack's inequality landed for a nonnegative harmonic function on a planar disc, in both "
         "the two-sided comparison with the centre value and the pairwise form on a closed subdisc "
         "with the sharp constant. The supporting mean-value machinery was extracted along the way.")


def progress_with(from_sha=FROM, to_sha=TO):
    return files.new_progress_file(AREA) + files.render_section(
        AREA, from_sha, to_sha, [1, 2, 3], "w", PROSE)


def with_statuses(mapping, tip=TIP):
    """Stub the two network calls from a `{(base, head): status}` map; anything absent is a 404."""
    orig_cmp, orig_rev = collect.compare_status, collect.rev_parse
    collect.compare_status = lambda repo, base, head: mapping.get((base, head))
    collect.rev_parse = lambda repo, ref: tip
    try:
        return collect.resolve_window(progress_with())
    finally:
        collect.compare_status, collect.rev_parse = orig_cmp, orig_rev


def test_a_real_forward_window_resolves():
    w = with_statuses({(TO, TIP): "ahead", (FROM, TO): "ahead"})
    assert w["to_reachable"] is True and w["advances"] is True
    assert w["from_sha"] == FROM and w["to_sha"] == TO


def test_the_documentation_tip_itself_is_reachable():
    """`identical` means to_sha IS the tip, which is the common case for a fresh report."""
    w = with_statuses({(TO, TIP): "identical", (FROM, TO): "ahead"})
    assert w["to_reachable"] is True and w["advances"] is True


def test_a_fabricated_to_sha_is_not_reachable():
    """A 404 from compare is exactly what an invented commit looks like."""
    w = with_statuses({(FROM, TO): "ahead"})
    assert w["to_reachable"] is False


def test_a_to_sha_off_the_documentation_branch_is_not_reachable():
    for status in ("behind", "diverged"):
        w = with_statuses({(TO, TIP): status, (FROM, TO): "ahead"})
        assert w["to_reachable"] is False, status


def test_a_backwards_window_does_not_advance():
    for status in ("behind", "diverged", "identical"):
        w = with_statuses({(TO, TIP): "ahead", (FROM, TO): status})
        assert w["advances"] is False, status


def test_an_empty_window_does_not_advance():
    """from_sha == to_sha compares as `identical`, and an empty window reports nothing."""
    w = with_statuses({(TO, TIP): "ahead", (FROM, TO): "identical"})
    assert w["advances"] is False


def test_reachability_is_checked_before_advancement():
    """No point asking whether an invented commit moves forward, and it saves a request."""
    seen = []
    orig_cmp, orig_rev = collect.compare_status, collect.rev_parse
    collect.compare_status = lambda repo, base, head: seen.append((base, head)) or None
    collect.rev_parse = lambda repo, ref: TIP
    try:
        w = collect.resolve_window(progress_with())
    finally:
        collect.compare_status, collect.rev_parse = orig_cmp, orig_rev
    assert seen == [(TO, TIP)], seen
    assert w["advances"] is None


def test_the_branch_is_pinned_to_one_snapshot():
    """`docgen` is mutable. Resolving it once and comparing against that SHA closes the gap in which
    it could move between the question and the answer, and records what was consulted."""
    w = with_statuses({(TO, TIP): "ahead", (FROM, TO): "ahead"})
    assert w["ref_sha"] == TIP


def test_an_unreadable_branch_refuses_rather_than_passing():
    orig_cmp, orig_rev = collect.compare_status, collect.rev_parse
    collect.compare_status = lambda repo, base, head: "ahead"
    collect.rev_parse = lambda repo, ref: None
    try:
        w = collect.resolve_window(progress_with())
    finally:
        collect.compare_status, collect.rev_parse = orig_cmp, orig_rev
    assert w["to_reachable"] is False and w["ref_sha"] is None


def test_an_unparseable_log_resolves_to_nothing():
    """The content checks report a malformed log properly; this must not mask them."""
    assert collect.resolve_window("not a progress file") is None
    assert collect.resolve_window("") is None
    assert collect.resolve_window(None) is None


def test_the_newest_section_is_the_one_checked():
    """A pull request appends one section; an older section's window is already history."""
    text = progress_with() + files.render_section(AREA, TO, "c" * 40, [4], "w", PROSE)
    orig_cmp, orig_rev = collect.compare_status, collect.rev_parse
    collect.compare_status = lambda repo, base, head: "ahead"
    collect.rev_parse = lambda repo, ref: TIP
    try:
        w = collect.resolve_window(text)
    finally:
        collect.compare_status, collect.rev_parse = orig_cmp, orig_rev
    assert w["from_sha"] == TO and w["to_sha"] == "c" * 40



for _name, _fn in sorted(globals().items()):
    if _name.startswith("test_") and callable(_fn):
        check(_name, _fn)

print()
if failures:
    print(f"{len(failures)} failure(s): {', '.join(failures)}")
    sys.exit(1)
print("all tests passed")
