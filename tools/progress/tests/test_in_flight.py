"""Tests for in-flight marking: an open report blocks its area, but a stuck one must not block forever."""

import datetime
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from progress import plan  # noqa: E402

failures = []


def check(name, fn):
    try:
        fn()
    except Exception as exc:  # noqa: BLE001
        failures.append(name)
        print(f"FAIL {name}: {type(exc).__name__}: {exc}")
    else:
        print(f"ok   {name}")


NOW = datetime.datetime(2026, 7, 30, 12, 0, 0, tzinfo=datetime.timezone.utc)


OURS = "TauCetiProject"


def pr(number=1, area="PDE", hours_old=1.0, created=True, owner=OURS):
    row = {"number": number, "headRefName": f"progress/a1b2c3d-b9c8d7e/{area}",
           "headRepositoryOwner": {"login": owner}}
    if created:
        stamp = NOW - datetime.timedelta(hours=hours_old)
        row["createdAt"] = stamp.strftime("%Y-%m-%dT%H:%M:%SZ")
    return row


def test_a_fresh_pr_marks_its_area_in_flight():
    blocked, stale = plan.in_flight_areas([pr(hours_old=2)], now=NOW, owners={OURS})
    assert set(blocked) == {"PDE"} and stale == []


def test_the_area_is_the_last_branch_segment():
    blocked, _ = plan.in_flight_areas([pr(area="ReductiveGroups")], now=NOW, owners={OURS})
    assert set(blocked) == {"ReductiveGroups"}


def test_a_stuck_pr_stops_blocking_after_the_cutoff():
    """The whole point: a permanently-refused report must not freeze its roadmap for everyone."""
    blocked, stale = plan.in_flight_areas([pr(number=115, hours_old=72)], now=NOW, owners={OURS})
    assert blocked == {}, "a three-day-old report is not in flight"
    assert len(stale) == 1 and "#115" in stale[0] and "3.0 days" in stale[0]


def test_the_stale_note_says_what_to_do():
    _, stale = plan.in_flight_areas([pr(hours_old=100)], now=NOW, owners={OURS})
    assert "close it if it is dead" in stale[0]


def test_the_cutoff_boundary_still_blocks():
    blocked, _ = plan.in_flight_areas([pr(hours_old=8.0)], now=NOW, stale_hours=8.0, owners={OURS})
    assert set(blocked) == {"PDE"}, "exactly at the cutoff is still in flight"
    blocked, _ = plan.in_flight_areas([pr(hours_old=8.1)], now=NOW, stale_hours=8.0, owners={OURS})
    assert blocked == {}


def test_a_pr_without_a_timestamp_keeps_blocking():
    """Age is the only evidence of being stuck; absent it, waiting beats opening a duplicate."""
    blocked, stale = plan.in_flight_areas([pr(created=False)], now=NOW, owners={OURS})
    assert set(blocked) == {"PDE"} and stale == []


def test_an_unparseable_timestamp_keeps_blocking():
    row = pr()
    row["createdAt"] = "not a date"
    blocked, stale = plan.in_flight_areas([row], now=NOW, owners={OURS})
    assert set(blocked) == {"PDE"} and stale == []


def test_a_non_progress_branch_shape_is_ignored():
    rows = [{"number": 9, "headRefName": "progress/oops", "headRepositoryOwner": {"login": OURS}}]
    blocked, stale = plan.in_flight_areas(rows, now=NOW, owners={OURS})
    assert blocked == {} and stale == []


def test_only_the_stale_area_is_released():
    rows = [pr(number=1, area="PDE", hours_old=1), pr(number=2, area="Exchangeability", hours_old=99)]
    blocked, stale = plan.in_flight_areas(rows, now=NOW, owners={OURS})
    assert set(blocked) == {"PDE"}
    assert len(stale) == 1 and "Exchangeability" in stale[0]


def test_the_default_cutoff_matches_the_cadence():
    """A report that has not merged within a full cadence period is stuck, not pending."""
    assert plan.STALE_PR_HOURS == plan.IDLE_HOURS


def test_the_server_side_limit_never_refuses_a_report_the_planner_thinks_due():
    """The gate's per-roadmap gap must stay under the planner's cadence, or reports are generated
    and then refused."""
    from progress import gate
    assert gate.MIN_REPORT_INTERVAL_HOURS < plan.IDLE_HOURS



def test_a_strangers_pull_request_does_not_mark_an_area_in_flight():
    """Anyone may open one on a `progress/*` branch. If a stranger's counted, they could freeze a
    roadmap indefinitely by opening one a day -- staleness bounds a single one, not a stream."""
    blocked, stale = plan.in_flight_areas([pr(owner="stranger")], now=NOW, owners={OURS})
    assert blocked == {} and stale == []


def test_our_own_fork_still_marks_an_area_in_flight():
    blocked, _ = plan.in_flight_areas([pr(owner="kim-em")], now=NOW, owners={OURS, "kim-em"})
    assert set(blocked) == {"PDE"}


for _name, _fn in sorted(globals().items()):
    if _name.startswith("test_") and callable(_fn):
        check(_name, _fn)

print()
if failures:
    print(f"{len(failures)} failure(s): {', '.join(failures)}")
    sys.exit(1)
print("all tests passed")
