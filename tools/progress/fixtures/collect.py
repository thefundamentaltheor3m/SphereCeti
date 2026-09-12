#!/usr/bin/env python3
"""Fetch everything the merge gate needs into one JSON bundle, using only a read-only token.

Separating collection from decision keeps `progress.gate` a pure function of data, which is what
makes it testable against several dozen hostile inputs. This script does the untrusted I/O.

EVERYTHING IS PINNED TO TWO IMMUTABLE SHAs. That is the whole design, and it was the original
version's blocker. `GET /pulls/{n}/files` reports whatever the head is *at the moment of the call*,
with no way to pin it, so a collector that read the pull request, then its files, then its tree,
could observe three different commits: force-push a benign `B`, let the file list be read from `B`,
restore `A`, and the gate would validate `B` while the merge took `A` -- whose diff was never
inspected. `--match-head-commit` does not help; it only pins the head between validation and merge.

So the head SHA and the current `main` SHA are each read ONCE, and every later request names one of
them explicitly:

* `GET /compare/{main_sha}...{head_sha}` gives the changed paths and their blob SHAs, computed
  between exactly those two commits.
* The comparison must be `ahead` with `behind_by == 0`. That means the head already contains current
  `main`, so merging it is a fast-forward of content: the post-merge bytes are the head's bytes,
  which are the bytes validated. A head *behind* main would be squashed by a three-way merge whose
  result is not what was checked, so it is refused rather than merged.
* Blobs are fetched by the SHA the comparison reported.
* Modes come from `GET /git/trees/{head_sha}?recursive=1`, which reports true git modes; the contents
  api reports only a coarse type, may dereference symlinks, and gives no mode at all.
* The previous contents of the two files are read at `main_sha`, not from a working checkout that
  could have drifted.

Run as: collect.py --repo O/R --pr N --out bundle.json
"""

import argparse
import base64
import datetime
import json
import pathlib
import re
import subprocess
import tempfile
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2]))

from progress import files, gate, gh as gh_mod, plan as plan_mod, window  # noqa: E402

# Where the reported window has to live. `to_sha` is checked for reachability from this branch, which
# tracks the newest TauCeti commit with published documentation.
CODE_REPO = "TauCetiProject/TauCeti"
CODE_REF = "docgen"
ROADMAP_LABEL_PREFIX = "roadmap/"

# `compare` returns at most 300 files. More than that cannot be a progress report, and a truncated
# list could HIDE a path from the gate, so anything approaching the limit is refused outright rather
# than partially inspected.
MAX_COMPARE_FILES = 300


class CollectError(SystemExit):
    """Collection could not produce a trustworthy bundle. Always fatal: the gate must never run on
    data that might be incomplete."""


def gh_api(path):
    proc = subprocess.run(["gh", "api", path], capture_output=True, text=True)
    if proc.returncode != 0:
        raise CollectError(f"gh api {path} failed: {proc.stderr.strip()}")
    return json.loads(proc.stdout)


def gh_api_paged(path):
    """Every page of a list endpoint, flattened.

    `gh api --paginate` emits one JSON array per page, concatenated (`[...][...]`). Splicing that
    back together by replacing the literal `][` is wrong: the sequence can occur inside a *string
    value* -- a `patch` field carries the diff, and generated prose may contain brackets -- and the
    replacement silently rewrites the data rather than failing. Decode the documents properly
    instead, which is exact and does not depend on the `gh` version having `--slurp`.
    """
    proc = subprocess.run(["gh", "api", "--paginate", path], capture_output=True, text=True)
    if proc.returncode != 0:
        raise CollectError(f"gh api --paginate {path} failed: {proc.stderr.strip()}")
    text = proc.stdout.strip()
    if not text:
        return []
    decoder = json.JSONDecoder()
    out, idx = [], 0
    while idx < len(text):
        try:
            page, end = decoder.raw_decode(text, idx)
        except json.JSONDecodeError as exc:
            raise CollectError(f"could not parse paginated output of {path}: {exc}") from exc
        if not isinstance(page, list):
            raise CollectError(f"{path} returned a {type(page).__name__}, expected a list")
        out.extend(page)
        idx = end
        while idx < len(text) and text[idx].isspace():
            idx += 1
    return out


def gh_api_paged_field(path, field):
    """Every page of an endpoint that wraps its list in an object, flattened.

    `/check-runs` answers `{"total_count": N, "check_runs": [...]}` rather than a bare array, so the
    pages are concatenated JSON *objects*. Same decoding discipline as `gh_api_paged`; only the
    unwrapping differs.
    """
    proc = subprocess.run(["gh", "api", "--paginate", path], capture_output=True, text=True)
    if proc.returncode != 0:
        raise CollectError(f"gh api --paginate {path} failed: {proc.stderr.strip()}")
    text = proc.stdout.strip()
    if not text:
        return []
    decoder = json.JSONDecoder()
    out, idx = [], 0
    while idx < len(text):
        try:
            page, end = decoder.raw_decode(text, idx)
        except json.JSONDecodeError as exc:
            raise CollectError(f"could not parse paginated output of {path}: {exc}") from exc
        if not isinstance(page, dict):
            raise CollectError(f"{path} returned a {type(page).__name__}, expected an object")
        out.extend(page.get(field) or [])
        idx = end
        while idx < len(text) and text[idx].isspace():
            idx += 1
    return out


def blob_text(repo, sha):
    """A blob's contents, by SHA. Empty string when there is no SHA."""
    if not sha:
        return ""
    obj = gh_api(f"repos/{repo}/git/blobs/{sha}")
    if obj.get("encoding") == "base64":
        raw = base64.b64decode(obj.get("content") or "")
        # Decode leniently; the gate re-checks UTF-8 validity and refuses if it is broken.
        return raw.decode("utf-8", "surrogateescape")
    return obj.get("content") or ""


def file_at(repo, ref, path):
    """A file's text at an exact ref, or None when it does not exist there."""
    proc = subprocess.run(
        ["gh", "api", f"repos/{repo}/contents/{path}?ref={ref}", "--jq", ".content,.encoding"],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        if "Not Found" in (proc.stderr or ""):
            return None
        raise CollectError(f"reading {path} at {ref[:7]} failed: {proc.stderr.strip()}")
    lines = proc.stdout.strip().splitlines()
    if len(lines) < 2:
        return None
    content, encoding = "\n".join(lines[:-1]), lines[-1]
    if encoding == "base64":
        return base64.b64decode(content).decode("utf-8", "surrogateescape")
    return content


def last_commit_date(repo, ref, path):
    """When `path` was last changed on `ref`, or None if never.

    Used to enforce the per-roadmap reporting cadence on the server. Read from the base branch, so it
    reflects reports that actually landed rather than anything the pull request claims.
    """
    proc = subprocess.run(
        ["gh", "api", f"repos/{repo}/commits?sha={ref}&path={path}&per_page=1",
         "--jq", ".[0].commit.committer.date"],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        raise CollectError(f"reading the history of {path} failed: {proc.stderr.strip()}")
    out = proc.stdout.strip()
    return out if out and out != "null" else None


def rev_parse(repo, ref):
    """Resolve a ref to an immutable commit SHA, or None if it cannot be read."""
    proc = subprocess.run(
        ["gh", "api", f"repos/{repo}/commits/{ref}", "--jq", ".sha"],
        capture_output=True, text=True,
    )
    return proc.stdout.strip() or None if proc.returncode == 0 else None


def bootstrap_cursor(area, repo=CODE_REPO, ref=CODE_REF):
    """The one legitimate `from_sha` for a roadmap's FIRST report, or None if it cannot be computed.

    A first report has no cursor on `main` to continue from, so its starting point has to be pinned
    some other way, or whoever files it also decides where that roadmap's history begins -- and
    windows only move forward, so everything earlier becomes unreportable for good.

    Three earlier attempts tried to answer this through the REST API, by lowest pull request number,
    by merge timestamp, and by walking the commits endpoint, and all three were wrong. The question is
    about position on the first-parent chain; the API offers neither first-parent traversal nor any
    ordering guarantee, and this history is not linear, so ancestry checks cannot recover it.

    So do not ask the API. Clone the code repository and ask git, which is what the planner does, with
    the SAME functions over the same data -- so the two agree by construction rather than by luck,
    which is what the previous attempts got wrong.

    `--filter=blob:none --no-checkout` fetches commits without file contents: about a second and three
    megabytes, since only commit subjects are read. This is not a checkout of pull-request content --
    it is the upstream code repository, nothing from the pull request reaches it, and nothing in it is
    executed.
    """
    proc = subprocess.run(
        ["gh", "pr", "list", "--repo", repo, "--state", "merged",
         "--label", f"{ROADMAP_LABEL_PREFIX}{area}", "--limit", "100000", "--json", "number"],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        return None
    try:
        labelled = [int(r["number"]) for r in json.loads(proc.stdout)]
    except (json.JSONDecodeError, KeyError, TypeError, ValueError):
        return None
    if not labelled:
        return None

    with tempfile.TemporaryDirectory() as tmp:
        clone = pathlib.Path(tmp) / "code"
        cloned = subprocess.run(
            ["git", "clone", "--filter=blob:none", "--no-checkout", "--single-branch",
             "--branch", ref, "-q", f"https://github.com/{repo}", str(clone)],
            capture_output=True, text=True,
        )
        if cloned.returncode != 0:
            return None
        try:
            # The same refusal the planner makes, from the same helper: a labelled pull request that
            # is in this history but unrecognised in it would otherwise move the cursor past itself.
            if plan_mod.unaccounted_prs(clone, labelled, ref=ref):
                return None
            found = window.earliest_merged(clone, labelled, ref=ref)
            if found is None:
                return None
            return window.first_parent_before(clone, found[1])
        except (window.GitError, gh_mod.GhError):
            return None


def compare_status(repo, base, head):
    """`status` from a two-dot-three comparison, or None when either end is not a commit.

    A 404 here is a *finding*, not an error: it is exactly what a fabricated `to_sha` looks like, and
    the caller turns it into a refusal.
    """
    proc = subprocess.run(
        ["gh", "api", f"repos/{repo}/compare/{base}...{head}", "--jq", ".status"],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        err = proc.stderr or ""
        if "Not Found" in err or "404" in err:
            return None
        raise CollectError(f"comparing {base[:7]}...{head[:7]} in {repo} failed: {err.strip()}")
    return proc.stdout.strip() or None


def resolve_window(new_progress, repo=CODE_REPO, ref=CODE_REF):
    """Check the newly-appended section's window against real TauCeti history.

    Without this, `to_sha` is unconstrained. Cursor continuity pins `from_sha` to the area's current
    cursor, but nothing stopped a report naming an arbitrary 40-hex `to_sha`, landing, and leaving the
    cursor there -- then repeating from that value indefinitely, walking the cursor past windows that
    could never afterwards be reported and announcing every step to Zulip.

    Two questions, both answered against `ref`:

    * is `to_sha` a commit reachable from the documentation branch?
    * does it come strictly after `from_sha`?

    Reachability rather than equality with the tip, because the tip advances whenever documentation is
    published and equality would refuse a report that was correct when its round began.

    Returns None when the section cannot be parsed; the content checks report that failure properly.
    """
    try:
        sections = files.parse_sections(new_progress or "")
    except files.FormatError:
        return None
    if not sections:
        return None
    section = sections[-1]
    from_sha, to_sha = section["from_sha"], section["to_sha"]

    # `to_sha...ref` is `ahead` when ref has commits to_sha does not, and `identical` when to_sha IS
    # the tip. Both mean to_sha is reachable. `behind` or `diverged` mean it is off the branch.
    # Resolve the branch to an immutable SHA first and compare against that. `docgen` is a mutable
    # ref: comparing against the name leaves a gap in which it could move between the question and
    # the answer, and records nothing about what was actually consulted.
    tip = rev_parse(repo, ref)
    if tip is None:
        return {"repo": repo, "ref": ref, "ref_sha": None, "from_sha": from_sha, "to_sha": to_sha,
                "to_reachable": False, "advances": None}
    reach = compare_status(repo, to_sha, tip)
    to_reachable = reach in ("ahead", "identical")

    advances = None
    if to_reachable:
        # Only `ahead` advances: `identical` is an empty window, and `behind`/`diverged` go backwards
        # or sideways.
        advances = compare_status(repo, from_sha, to_sha) == "ahead"

    return {"repo": repo, "ref": ref, "ref_sha": tip, "from_sha": from_sha, "to_sha": to_sha,
            "to_reachable": to_reachable, "advances": advances}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", required=True)
    ap.add_argument("--pr", required=True, type=int)
    ap.add_argument("--base-branch", default="main")
    ap.add_argument("--out", required=True)
    args = ap.parse_args(argv)

    # ----- the two anchors, read once ----------------------------------------------------------
    pr = gh_api(f"repos/{args.repo}/pulls/{args.pr}")
    head_sha = ((pr.get("head") or {}).get("sha")) or ""
    if not head_sha:
        raise CollectError("pull request has no head sha")
    main_sha = gh_api(f"repos/{args.repo}/commits/{args.base_branch}").get("sha") or ""
    if not main_sha:
        raise CollectError(f"could not resolve {args.base_branch}")


    # The area comes from the branch and is validated by the gate's own pattern. Reading it here with
    # the gate's regex keeps the two from disagreeing.
    branch = (pr.get("head") or {}).get("ref") or ""
    m = gate.BRANCH_RE.match(branch)
    area = m.group(3) if m else ""

    # ----- the diff, between exactly those two commits -----------------------------------------
    cmp_data = gh_api(f"repos/{args.repo}/compare/{main_sha}...{head_sha}?per_page={MAX_COMPARE_FILES}")
    changed = cmp_data.get("files") or []
    if len(changed) >= MAX_COMPARE_FILES:
        raise CollectError(
            f"{len(changed)} files changed, at or over the {MAX_COMPARE_FILES}-file comparison "
            f"limit; the list may be truncated, so it cannot be trusted"
        )
    behind = cmp_data.get("behind_by")
    status = cmp_data.get("status")

    tree = gh_api(f"repos/{args.repo}/git/trees/{head_sha}?recursive=1")
    if tree.get("truncated"):
        raise CollectError("the head tree was truncated; modes cannot be confirmed")
    wanted = {f.get("filename") or "" for f in changed if gate.PATH_RE.match(f.get("filename") or "")}
    tree_entries = [
        {"path": e.get("path"), "mode": e.get("mode"), "type": e.get("type"), "sha": e.get("sha")}
        for e in (tree.get("tree") or [])
        if e.get("path") in wanted
    ]

    by_path = {}
    for f in changed:
        path = f.get("filename") or ""
        if gate.PATH_RE.match(path):
            by_path[path] = f

    def blob_for(basename):
        for path, f in by_path.items():
            if path.endswith("/" + basename):
                return blob_text(args.repo, f.get("sha"))
        return ""

    new_status = blob_for("STATUS.md")
    new_progress = blob_for("PROGRESS.md")

    # ----- the previous contents, at main_sha, from the parent THIS DIFF TOUCHES ---------------
    #
    # The parent is derived from the changed paths, never probed in a fixed order. Probing
    # `TauCetiRoadmap/` first was a real hole: an area can exist under both parents, so a pull request
    # changing `Completed/<area>/` would be handed the ACTIVE log as its append-only baseline, and a
    # wholesale replacement of the archived log then looked like a valid append.
    old_status = old_progress = last_report_at = None
    area_exists = False
    expected_bootstrap = None
    old_paths = {}
    current_cursor = None
    parents = {gate.PATH_RE.match(p).group(1) for p in by_path}
    if len(parents) > 1:
        # The gate refuses this too, but collecting a baseline would mean choosing one arbitrarily.
        raise CollectError(f"the diff spans {sorted(parents)}; it must touch one directory")
    if area and parents:
        parent = parents.pop()
        old_paths = {
            "STATUS.md": f"{parent}/{area}/STATUS.md",
            "PROGRESS.md": f"{parent}/{area}/PROGRESS.md",
        }
        old_status = file_at(args.repo, main_sha, old_paths["STATUS.md"])
        old_progress = file_at(args.repo, main_sha, old_paths["PROGRESS.md"])
        # When this roadmap was last reported, for the server-side cadence limit.
        last_report_at = last_commit_date(args.repo, main_sha, old_paths["PROGRESS.md"])
        # A roadmap is a directory with a README.md, the same rule the planner uses. Reports may only
        # be added to one that already exists, or invented area names would give unlimited
        # "first reports", each exempt from the cadence limit.
        area_exists = file_at(args.repo, main_sha, f"{parent}/{area}/README.md") is not None
        if old_progress:
            try:
                current_cursor = files.cursor(old_progress)
            except files.FormatError:
                # An unparseable log on main is a real problem, but saying so is the gate's job.
                current_cursor = None
        if current_cursor is None and area_exists:
            # Only for a first report, so at most once per roadmap ever.
            expected_bootstrap = bootstrap_cursor(area)

    # Only check-runs, and only from the head we pinned. Commit statuses are deliberately NOT
    # collected: any repository writer can POST one under any context, so they are not evidence, and
    # the gate refuses them if they somehow appear.
    check_runs = []
    runs = gh_api_paged_field(f"repos/{args.repo}/commits/{head_sha}/check-runs?per_page=100",
                              "check_runs")
    for run in runs:
        check_runs.append({
            "name": run.get("name"),
            "head_sha": head_sha,
            "conclusion": run.get("conclusion"),
            "status": run.get("status"),
            "app_id": ((run.get("app") or {}).get("id")),
            "source": "check_run",
        })

    bundle = {
        "base_repo": args.repo,
        "code_window": resolve_window(new_progress),
        "area_exists": area_exists,
        "expected_bootstrap_from_sha": expected_bootstrap,
        "last_report_at": last_report_at,
        # The collector's own clock, never anything from the pull request.
        "collected_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "pr": pr,
        "area": area,
        "head_sha": head_sha,
        "main_sha": main_sha,
        "compare_status": status,
        "behind_by": behind,
        "changed_files": changed,
        "tree_entries": tree_entries,
        "new_status": new_status,
        "new_progress": new_progress,
        "old_status": old_status,
        "old_progress": old_progress,
        # Recorded so the gate can confirm the baseline came from the directory being changed.
        "old_paths": old_paths,
        "current_main_cursor": current_cursor,
        "check_runs": check_runs,
    }
    pathlib.Path(args.out).write_text(json.dumps(bundle, indent=2), encoding="utf-8")
    print(f"collected: area={area or '(none)'} head={head_sha[:7]} main={main_sha[:7]} "
          f"status={status} behind={behind} files={len(changed)} checks={len(check_runs)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
