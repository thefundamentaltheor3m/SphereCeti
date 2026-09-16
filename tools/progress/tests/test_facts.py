"""Tests for the factual spine.

Declaration names, kinds, links and source positions come from doc-gen4; git blame decides what
belongs to the window. Neither requires understanding Lean, which is the point -- an earlier version
tried to derive names by tracking `namespace`/`section`/`end` in Python and got them subtly wrong,
which is the worst outcome for something whose output becomes a link.

The documentation is stubbed here with a fake `Docs` so the tests are hermetic; the parsing of real
doc-gen4 markup is covered in test_docs.py against a captured page.
"""

import json
import os
import pathlib
import subprocess
import sys
import tempfile

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from progress import cli, facts, window  # noqa: E402
from progress.facts import FactsError  # noqa: E402

failures = []


def check(name, fn):
    try:
        fn()
    except Exception as exc:  # noqa: BLE001
        failures.append(name)
        print(f"FAIL {name}: {type(exc).__name__}: {exc}")
    else:
        print(f"ok   {name}")


ENV = {
    **os.environ,
    "GIT_AUTHOR_NAME": "T", "GIT_AUTHOR_EMAIL": "t@e",
    "GIT_COMMITTER_NAME": "T", "GIT_COMMITTER_EMAIL": "t@e",
    "GIT_AUTHOR_DATE": "2026-01-01T00:00:00Z", "GIT_COMMITTER_DATE": "2026-01-01T00:00:00Z",
}


def commit(tmp, subject, files):
    for rel, text in files.items():
        p = pathlib.Path(tmp) / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
    subprocess.run(["git", "-C", tmp, "add", "-A"], check=True, capture_output=True, env=ENV)
    subprocess.run(["git", "-C", tmp, "commit", "-q", "-m", subject],
                   check=True, capture_output=True, env=ENV)
    return window.git(["rev-parse", "HEAD"], tmp).strip()


class FakeDocs:
    """Stands in for the published documentation.

    `pages` maps a module page to `{full_name: (kind, file, start, end)}`, which is exactly what the
    real reader extracts from doc-gen4's markup.
    """

    base = "https://docs.example/docs"

    def __init__(self, pages, source_commit):
        self._pages = pages
        self._commit = source_commit

    def source_commit(self):
        return self._commit

    def declarations(self, page):
        out = {}
        for name, (kind, file, start, end) in self._pages.get(page, {}).items():
            out[name] = {
                "kind": kind, "file": file, "start": start, "end": end,
                "commit": self._commit, "url": f"{self.base}/{page}#{name}",
            }
        return out


ALPHA = """namespace TauCeti
/-- **Alpha's theorem.** It states alpha. And more besides. -/
theorem alpha : True := trivial
end TauCeti
"""

ALPHA_AND_BETA = """namespace TauCeti
/-- **Alpha's theorem.** It states alpha. And more besides. -/
theorem alpha : True := trivial

/-- **Beta's theorem.** It states beta. -/
theorem beta : True := trivial
end TauCeti
"""


def repo_with_two_prs(tmp):
    """Root, then a PR adding `alpha`, then a PR adding `beta` to the same file."""
    subprocess.run(["git", "init", "-q", "-b", "main", tmp], check=True, capture_output=True)
    root = commit(tmp, "init", {"README.md": "x"})
    first = commit(tmp, "feat: alpha (#101)", {"TauCeti/A.lean": ALPHA})
    second = commit(tmp, "feat: beta (#102)", {"TauCeti/A.lean": ALPHA_AND_BETA})
    return root, first, second


# `alpha` occupies lines 2-3 in both versions; `beta` occupies lines 5-6 of the second.
PAGE = "TauCeti/A.html"


def docs_for(commit_sha, with_beta=True):
    decls = {"TauCeti.alpha": ("theorem", "TauCeti/A.lean", 2, 3)}
    if with_beta:
        decls["TauCeti.beta"] = ("theorem", "TauCeti/A.lean", 5, 6)
    return FakeDocs({PAGE: decls}, commit_sha)


def test_names_kinds_and_urls_come_from_the_documentation():
    """Nothing is derived from the source text: the qualified name, the kind and the link are all
    what doc-gen4 published."""
    with tempfile.TemporaryDirectory() as tmp:
        root, first, second = repo_with_two_prs(tmp)
        got = facts.collect(tmp, root, second, docs=docs_for(second))
        by = {d["name"]: d for d in got["declarations"]}
        assert set(by) == {"TauCeti.alpha", "TauCeti.beta"}, sorted(by)
        assert by["TauCeti.alpha"]["kind"] == "theorem"
        assert by["TauCeti.alpha"]["url"] == "https://docs.example/docs/TauCeti/A.html#TauCeti.alpha"


def test_blame_attributes_each_declaration_to_its_pull_request():
    with tempfile.TemporaryDirectory() as tmp:
        root, first, second = repo_with_two_prs(tmp)
        got = facts.collect(tmp, root, second, docs=docs_for(second))
        by = {d["name"]: d for d in got["declarations"]}
        assert by["TauCeti.alpha"]["pr"] == 101, by["TauCeti.alpha"]
        assert by["TauCeti.beta"]["pr"] == 102, by["TauCeti.beta"]


def test_declarations_predating_the_window_are_not_reported():
    """`alpha` was written before this window opens, so it is real but not news."""
    with tempfile.TemporaryDirectory() as tmp:
        root, first, second = repo_with_two_prs(tmp)
        got = facts.collect(tmp, first, second, docs=docs_for(second))
        names = {d["name"] for d in got["declarations"]}
        assert names == {"TauCeti.beta"}, sorted(names)


def test_the_pr_filter_is_honoured():
    with tempfile.TemporaryDirectory() as tmp:
        root, first, second = repo_with_two_prs(tmp)
        got = facts.collect(tmp, root, second, pr_numbers=[101], docs=docs_for(second))
        names = {d["name"] for d in got["declarations"]}
        assert names == {"TauCeti.alpha"}, sorted(names)


def test_docstrings_are_read_from_a_known_line():
    """doc-gen4's source range BEGINS at the docstring, so it is read from a position the
    documentation supplied rather than found by parsing."""
    with tempfile.TemporaryDirectory() as tmp:
        root, first, second = repo_with_two_prs(tmp)
        got = facts.collect(tmp, root, second, docs=docs_for(second))
        by = {d["name"]: d for d in got["declarations"]}
        assert by["TauCeti.alpha"]["doc"] == "**Alpha's theorem.** It states alpha.", by
        assert by["TauCeti.beta"]["doc"] == "**Beta's theorem.** It states beta."


def test_a_declaration_with_no_docstring_reports_none():
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(["git", "init", "-q", "-b", "main", tmp], check=True, capture_output=True)
        root = commit(tmp, "init", {"README.md": "x"})
        head = commit(tmp, "feat: bare (#7)", {"TauCeti/A.lean": "theorem bare : True := trivial\n"})
        docs = FakeDocs({PAGE: {"bare": ("theorem", "TauCeti/A.lean", 1, 1)}}, head)
        got = facts.collect(tmp, root, head, docs=docs)
        assert got["declarations"][0]["doc"] == ""


def test_an_undocumented_module_contributes_nothing():
    """A file added after the documentation was built has no page, so nothing in it can be linked --
    and claiming it landed with a dead link would be worse than silence."""
    with tempfile.TemporaryDirectory() as tmp:
        root, first, second = repo_with_two_prs(tmp)
        empty = FakeDocs({}, second)
        got = facts.collect(tmp, root, second, docs=empty)
        assert got["declarations"] == []
        assert got["counts"]["declarations"] == 0


def test_revised_declarations_are_marked_not_new():
    """A declaration whose lines are only partly from this window existed before and was revised."""
    with tempfile.TemporaryDirectory() as tmp:
        subprocess.run(["git", "init", "-q", "-b", "main", tmp], check=True, capture_output=True)
        root = commit(tmp, "init", {"README.md": "x"})
        before = "/-- Doc. -/\ntheorem t : True := by\n  trivial\n"
        first = commit(tmp, "feat: add (#1)", {"TauCeti/A.lean": before})
        after = "/-- Doc. -/\ntheorem t : True := by\n  exact trivial\n"
        second = commit(tmp, "refactor: tweak (#2)", {"TauCeti/A.lean": after})
        docs = FakeDocs({PAGE: {"t": ("theorem", "TauCeti/A.lean", 2, 3)}}, second)
        got = facts.collect(tmp, root, second, docs=docs)
        assert got["declarations"][0]["new"] is True, "written entirely within the window"
        got2 = facts.collect(tmp, first, second, docs=docs)
        assert got2["declarations"][0]["new"] is False, "only the body line is from this window"


def test_documentation_behind_the_window_end_anchors_to_the_documented_commit():
    """The docs deploy independently of the branch that nominates them. Anchoring to the branch tip
    would produce dead links for anything newer, so the documented commit wins and is reported."""
    with tempfile.TemporaryDirectory() as tmp:
        root, first, second = repo_with_two_prs(tmp)
        third = commit(tmp, "feat: later (#103)", {"TauCeti/B.lean": "theorem later : True := trivial\n"})
        # The documentation is still at `second`.
        got = facts.collect(tmp, root, third, docs=docs_for(second))
        assert got["docs_sha"] == second
        assert got["to_sha"] == third
        names = {d["name"] for d in got["declarations"]}
        assert names == {"TauCeti.alpha", "TauCeti.beta"}, sorted(names)


def test_documentation_from_a_foreign_history_is_refused():
    with tempfile.TemporaryDirectory() as tmp:
        root, first, second = repo_with_two_prs(tmp)
        try:
            facts.collect(tmp, root, second, docs=docs_for("0" * 40))
        except (FactsError, window.GitError) as exc:
            assert "0000000" in str(exc) or "not an ancestor" in str(exc), str(exc)
            return
        raise AssertionError("expected a refusal")


def test_module_page_for_file():
    assert facts.module_page_for_file("TauCeti/Analysis/Fredholm/Basic.lean") == \
        "TauCeti/Analysis/Fredholm/Basic.html"
    assert facts.module_page_for_file("scripts/x.py") is None
    assert facts.module_page_for_file("TauCeti/A.txt") is None


def test_cli_facts_passes_the_plan_filter():
    """Regression: the CLI once dropped the filter, so a one-roadmap report was grounded in every
    roadmap's work in the range. The failure is silent -- the output merely gets bigger."""
    with tempfile.TemporaryDirectory() as tmp:
        root, first, second = repo_with_two_prs(tmp)
        plan = {"roadmap": "Algebra", "from_sha": root, "to_sha": second, "prs": [101]}
        plan_file = pathlib.Path(tmp) / "plan.json"
        out_file = pathlib.Path(tmp) / "facts.json"
        plan_file.write_text(json.dumps(plan))
        # Point the reader at a stub by monkeypatching the module the CLI imports.
        import progress.docs as docs_mod
        real = docs_mod.Docs
        docs_mod.Docs = lambda *a, **k: docs_for(second)
        try:
            rc = cli.main(["facts", "--plan", str(plan_file), "--code-dir", tmp,
                           "--out", str(out_file)])
        finally:
            docs_mod.Docs = real
        assert rc == 0, rc
        got = json.loads(out_file.read_text())
        names = {d["name"] for d in got["declarations"]}
        assert names == {"TauCeti.alpha"}, f"filter dropped: got {sorted(names)}"


for _name, _fn in sorted(globals().items()):
    if _name.startswith("test_") and callable(_fn):
        check(_name, _fn)

print()
if failures:
    print(f"{len(failures)} failure(s): {', '.join(failures)}")
    sys.exit(1)
print("all tests passed")
