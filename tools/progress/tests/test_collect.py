"""Tests for the collector's parsing, which runs on attacker-influenced GitHub responses.

`collect.py` is not importable as a package module (it lives under .github/scripts and is invoked as
a script), so it is loaded by path here.
"""

import importlib.util
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

_spec = importlib.util.spec_from_file_location("collect", ROOT / ".github" / "scripts" / "collect.py")
collect = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(collect)

failures = []


def check(name, fn):
    try:
        fn()
    except Exception as exc:  # noqa: BLE001
        failures.append(name)
        print(f"FAIL {name}: {type(exc).__name__}: {exc}")
    else:
        print(f"ok   {name}")


class FakeProc:
    def __init__(self, out, rc=0):
        self.returncode, self.stdout, self.stderr = rc, out, ""


def with_output(payload, rc=0):
    """Run gh_api_paged against a canned `gh` response."""
    orig = subprocess.run
    subprocess.run = lambda *a, **k: FakeProc(payload, rc)
    try:
        return collect.gh_api_paged("x")
    finally:
        subprocess.run = orig


def test_single_page():
    assert with_output(json.dumps([{"filename": "a.md"}])) == [{"filename": "a.md"}]


def test_empty_output():
    assert with_output("") == []


def test_concatenated_pages_are_flattened():
    payload = json.dumps([{"n": 1}]) + json.dumps([{"n": 2}]) + json.dumps([{"n": 3}])
    assert with_output(payload) == [{"n": 1}, {"n": 2}, {"n": 3}]


def test_pages_separated_by_whitespace():
    payload = json.dumps([{"n": 1}]) + "\n" + json.dumps([{"n": 2}])
    assert with_output(payload) == [{"n": 1}, {"n": 2}]


def test_bracket_pair_inside_a_string_value_survives():
    """The regression this file exists for.

    `gh api --paginate` concatenates one array per page, and the old code spliced them by replacing
    the literal `][`. That sequence can occur inside a STRING -- the files endpoint carries a `patch`
    field holding the diff, and generated prose may contain brackets -- so the replacement silently
    rewrote data instead of failing. A filename containing it would have been mangled into a path
    that no longer matched, and a `patch` into something that was never sent.
    """
    payload = (json.dumps([{"filename": "a.md", "patch": "prose containing ][ brackets"}])
               + json.dumps([{"filename": "b.md"}]))
    got = with_output(payload)
    assert got[0]["patch"] == "prose containing ][ brackets", got[0]["patch"]
    assert [g["filename"] for g in got] == ["a.md", "b.md"], got


def test_bracket_pair_inside_a_filename_survives():
    payload = json.dumps([{"filename": "weird][name.md"}])
    assert with_output(payload)[0]["filename"] == "weird][name.md"


def test_malformed_output_fails_closed():
    try:
        with_output("not json at all")
    except SystemExit as exc:
        assert "could not parse" in str(exc), str(exc)
        return
    raise AssertionError("expected SystemExit")


def test_non_list_page_fails_closed():
    try:
        with_output(json.dumps({"message": "Not Found"}))
    except SystemExit as exc:
        assert "expected a list" in str(exc), str(exc)
        return
    raise AssertionError("expected SystemExit")


def test_gh_failure_fails_closed():
    try:
        with_output("", rc=1)
    except SystemExit as exc:
        assert "failed" in str(exc)
        return
    raise AssertionError("expected SystemExit")


for _name, _fn in sorted(globals().items()):
    if _name.startswith("test_") and callable(_fn):
        check(_name, _fn)

print()
if failures:
    print(f"{len(failures)} failure(s): {', '.join(failures)}")
    sys.exit(1)
print("all tests passed")
