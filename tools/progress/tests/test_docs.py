"""Tests for reading doc-gen4's published output.

The fixture is a verbatim slice of a real module page, so these test the markup as it actually is
rather than as it was imagined. If doc-gen4 changes its markup these fail loudly, which is the point:
silently extracting nothing would mean reports that quietly stop naming results.
"""

import json
import os
import pathlib
import sys
import tempfile
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from progress import docs as docs_mod  # noqa: E402
from progress.docs import Docs, DocsError  # noqa: E402

FIXTURES = pathlib.Path(__file__).parent / "fixtures"
failures = []


def check(name, fn):
    try:
        fn()
    except Exception as exc:  # noqa: BLE001
        failures.append(name)
        print(f"FAIL {name}: {type(exc).__name__}: {exc}")
    else:
        print(f"ok   {name}")


def make(pages, cache=None, ttl=None, fetched=None):
    """A Docs whose transport serves canned responses and never touches the network.

    `fetched` collects the site-relative paths that actually reached the transport, so a test can
    assert a cache hit or miss rather than inferring one from the content.
    """
    def opener(url):
        rel = url.split("/docs/", 1)[1]
        if fetched is not None:
            fetched.append(rel)
        if rel not in pages:
            raise DocsError(f"no such page: {rel}")
        return pages[rel]
    return Docs(base="https://example.test/docs", cache_dir=cache or "/nonexistent",
                opener=opener, ttl=ttl)


PAGE = (FIXTURES / "module-page.html").read_text(encoding="utf-8")
INDEX = json.dumps({
    "declarations": {
        "TauCeti.IsFredholm": {"docLink": "./TauCeti/Analysis/Fredholm/Basic.html#TauCeti.IsFredholm",
                               "kind": "structure"},
    },
    "modules": {},
})


def test_declarations_are_read_from_real_markup():
    d = make({"TauCeti/Analysis/Fredholm/Basic.html": PAGE})
    got = d.declarations("TauCeti/Analysis/Fredholm/Basic.html")
    assert "TauCeti.IsFredholm" in got, sorted(got)
    e = got["TauCeti.IsFredholm"]
    assert e["kind"] == "structure", e
    assert e["file"] == "TauCeti/Analysis/Fredholm/Basic.lean", e
    assert e["start"] == 61 and e["end"] == 73, e
    assert len(e["commit"]) == 40, e
    assert e["url"].endswith("Basic.html#TauCeti.IsFredholm"), e


def test_every_declaration_block_is_found():
    d = make({"p.html": PAGE})
    got = d.declarations("p.html")
    assert len(got) == PAGE.count('<div class="decl" id="'), (len(got), PAGE.count('<div class="decl" id="'))


def test_source_commit_comes_from_the_page():
    d = make({"TauCeti/Analysis/Fredholm/Basic.html": PAGE, docs_mod.INDEX_PATH: INDEX})
    assert d.source_commit() == "ed837d596f81c587c5b9696efed02a869f945e7e", d.source_commit()


def test_index_is_parsed_and_maps_names_to_pages():
    d = make({docs_mod.INDEX_PATH: INDEX})
    assert d.module_of("TauCeti.IsFredholm") == "TauCeti/Analysis/Fredholm/Basic.html"
    assert d.module_of("Nope.Missing") is None


def test_a_malformed_index_is_refused():
    for bad in ("not json", json.dumps({"declarations": {}}), json.dumps({"modules": {}})):
        d = make({docs_mod.INDEX_PATH: bad})
        try:
            d.index()
        except DocsError:
            continue
        raise AssertionError(f"expected a DocsError for {bad[:30]!r}")


def test_a_page_with_no_declarations_yields_nothing():
    d = make({"empty.html": "<html><body>nothing here</body></html>"})
    assert d.declarations("empty.html") == {}


def test_markup_that_stops_matching_is_visible():
    """A page whose decl blocks carry no source link still lists the declarations, without a
    position -- so the caller cannot decide they are new, rather than guessing that they are."""
    d = make({"p.html": '<div class="decl" id="A.b"><span class="decl_kind">theorem</span></div>'})
    got = d.declarations("p.html")
    assert got["A.b"]["start"] is None and got["A.b"]["commit"] is None, got


# ----- the disk cache expires ------------------------------------------------------------------


def test_a_fresh_cache_entry_is_reused():
    with tempfile.TemporaryDirectory() as tmp:
        fetched = []
        make({"p.html": "one"}, cache=tmp, fetched=fetched)._get("p.html")
        make({"p.html": "two"}, cache=tmp, fetched=fetched)._get("p.html")
        # Second reader is a different process's worth of state; it must not refetch.
        assert fetched == ["p.html"], fetched


def test_an_expired_cache_entry_is_refetched_and_replaced():
    """The outage this prevents: an index cached days earlier pinned `source_commit()` to a build
    that had long since been superseded, and every window `plan` could close ended there."""
    with tempfile.TemporaryDirectory() as tmp:
        fetched = []
        first = make({"p.html": "one"}, cache=tmp, ttl=0, fetched=fetched)
        assert first._get("p.html") == "one"
        second = make({"p.html": "two"}, cache=tmp, ttl=0, fetched=fetched)
        assert second._get("p.html") == "two", "a stale entry must not be served"
        assert fetched == ["p.html", "p.html"], fetched
        # The refetch replaced the stale bytes rather than accumulating beside them.
        assert (pathlib.Path(tmp) / "p.html").read_text(encoding="utf-8") == "two"


def test_a_url_is_read_once_per_run():
    """The in-process memo. It makes one URL stable within a run — and NOTHING more: two different
    URLs still cross their TTLs independently, which is what `declarations` has to police."""
    with tempfile.TemporaryDirectory() as tmp:
        pages = {"p.html": "one"}
        fetched = []
        d = make(pages, cache=tmp, ttl=0, fetched=fetched)
        assert d._get("p.html") == "one"
        pages["p.html"] = "two"
        assert d._get("p.html") == "one", "a run must not change build under itself"
        assert fetched == ["p.html"], fetched


def test_a_positive_ttl_expires_too():
    """Backdate the entry rather than setting ttl=0, so an implementation that special-cases 0 while
    caching every positive TTL for ever — the bug being fixed — cannot pass this."""
    with tempfile.TemporaryDirectory() as tmp:
        fetched = []
        make({"p.html": "one"}, cache=tmp, ttl=3600, fetched=fetched)._get("p.html")
        entry = pathlib.Path(tmp) / "p.html"
        os.utime(entry, (0, time.time() - 7200))
        assert make({"p.html": "two"}, cache=tmp, ttl=3600, fetched=fetched)._get("p.html") == "two"
        assert fetched == ["p.html", "p.html"], fetched


def test_an_mtime_in_the_future_is_not_fresh():
    """A corrected clock or a skewed shared filesystem makes the age negative, and `age < ttl` alone
    would then call the entry fresh for as long as the skew lasts — the immortal cache, rebuilt."""
    with tempfile.TemporaryDirectory() as tmp:
        fetched = []
        make({"p.html": "one"}, cache=tmp, ttl=3600, fetched=fetched)._get("p.html")
        entry = pathlib.Path(tmp) / "p.html"
        os.utime(entry, (0, time.time() + 86400))
        assert make({"p.html": "two"}, cache=tmp, ttl=3600, fetched=fetched)._get("p.html") == "two"
        assert fetched == ["p.html", "p.html"], fetched


def test_an_unreadable_cache_entry_falls_back_to_the_transport():
    with tempfile.TemporaryDirectory() as tmp:
        cache = pathlib.Path(tmp) / "c"
        cache.mkdir()
        (cache / "p.html").mkdir()  # fresh by mtime, and not a file we can read
        assert make({"p.html": "live"}, cache=cache, ttl=3600)._get("p.html") == "live"


def test_a_cache_write_is_atomic_and_leaves_no_litter():
    """A concurrent reader must see the old file or the whole new one, never a truncated page: a
    half-written module page parses as zero declarations, which reads as an honest empty result."""
    with tempfile.TemporaryDirectory() as tmp:
        d = make({"p.html": "x" * 5000}, cache=tmp, ttl=3600)
        d._get("p.html")
        entry = pathlib.Path(tmp) / "p.html"
        assert entry.read_text(encoding="utf-8") == "x" * 5000
        assert [p.name for p in pathlib.Path(tmp).iterdir()] == ["p.html"], "temp files were left behind"


# ----- one build per run ---------------------------------------------------------------------


def page_at(commit, name="A.b"):
    return (
        f'<div class="decl" id="{name}"><span class="decl_kind">theorem</span>'
        f'<div class="gh_link"><a href="https://github.com/o/r/blob/{commit}/TauCeti/A.lean#L1-L2">src</a>'
        f"</div></div>"
    )


OLD, NEW = "a" * 40, "b" * 40
TWO_PAGE_INDEX = json.dumps({"declarations": {
    "A.b": {"docLink": "./probe.html#A.b", "kind": "theorem"},
    "C.d": {"docLink": "./other.html#C.d", "kind": "theorem"},
}, "modules": {}})


def test_a_page_from_another_build_is_refetched():
    """The straddle: the probe expires and fixes `source_commit()` at the new build while another
    page is still served, in-TTL, from the old one. `facts` would then read line spans from one
    build and blame them at the other's commit."""
    with tempfile.TemporaryDirectory() as tmp:
        pages = {docs_mod.INDEX_PATH: TWO_PAGE_INDEX, "probe.html": page_at(OLD), "other.html": page_at(OLD)}
        make(pages, cache=tmp, ttl=3600)._get("other.html")  # the old build's page, now cached
        pages["probe.html"] = page_at(NEW)
        pages["other.html"] = page_at(NEW)
        d = make(pages, cache=tmp, ttl=3600)
        assert d.source_commit() == NEW, "the probe is fetched fresh here, so it names the new build"
        got = d.declarations("other.html")
        assert got["A.b"]["commit"] == NEW, got["A.b"]["commit"]


def test_a_site_redeploying_under_a_run_is_refused():
    """If the page still disagrees after a re-fetch the deploy is in flight. Refusing is the honest
    outcome: `plan` treats DocsError as "not due" and the next run closes the window cleanly."""
    with tempfile.TemporaryDirectory() as tmp:
        pages = {docs_mod.INDEX_PATH: TWO_PAGE_INDEX, "probe.html": page_at(NEW), "other.html": page_at(OLD)}
        d = make(pages, cache=tmp, ttl=3600)
        assert d.source_commit() == NEW
        try:
            d.declarations("other.html")
        except DocsError as exc:
            assert "redeploying" in str(exc), str(exc)
        else:
            raise AssertionError("expected a DocsError for a page from another build")


for _name, _fn in sorted(globals().items()):
    if _name.startswith("test_") and callable(_fn):
        check(_name, _fn)

print()
if failures:
    print(f"{len(failures)} failure(s): {', '.join(failures)}")
    sys.exit(1)
print("all tests passed")
