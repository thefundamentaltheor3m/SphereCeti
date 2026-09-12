"""The GitHub reads this tool needs, via the `gh` CLI.

Two design points worth stating, because both were defects in an earlier draft:

* **No global PR cap.** `TauCeti/scripts/loc_roadmap_graph.py` fetches merged PRs with
  `--limit 2000`, which is fine for a chart that only needs recent history. Here a cap would start
  silently dropping the oldest PRs of a quiet area: at ~36 merges a day the project passes 2000
  within weeks of writing this. Labels are therefore looked up for an explicit set of PR numbers
  taken from a commit range, so the query size is bounded by the window, not by project age.

* **Failures raise.** A GitHub hiccup must never read as "nothing to report" -- that would let a
  transient error advance a cursor past real work. Every caller turns a raise into "cannot decide
  right now".
"""

import json
import subprocess
import time

ROADMAP_REPO = "TauCetiProject/TauCetiRoadmap"
CODE_REPO = "TauCetiProject/TauCeti"

ROADMAP_LABEL_PREFIX = "roadmap/"
# Labels that exist but name no roadmap: infra/refactor/bump work, and new mathematics whose
# citation could not be parsed. Neither is reported, by design.
NON_AREA_LABELS = {"roadmap/none", "roadmap/Unknown"}


class GhError(RuntimeError):
    """A `gh` invocation failed."""


def gh(args, retries=3):
    """Run `gh` and return stdout, retrying transient failures.

    Every call here is a read, so a retry is always safe. This mirrors the retry helper in
    `TauCeti/scripts/roadmap_label.py`.
    """
    last = ""
    for attempt in range(retries):
        proc = subprocess.run(["gh", *args], capture_output=True, text=True)
        if proc.returncode == 0:
            return proc.stdout
        last = proc.stderr.strip()
        if attempt + 1 < retries:
            time.sleep(2 ** attempt)
    raise GhError(f"gh {' '.join(args)} failed after {retries} attempts: {last}")


def _api(path, jq=None):
    args = ["api", path]
    if jq:
        args += ["--jq", jq]
    return gh(args)


def recent_roadmap_commits(limit=30, repo=ROADMAP_REPO):
    """`[(iso_date, subject)]` for the newest commits on the roadmap repo's default branch.

    One request, no clone. This is the whole of the `due` check: progress updates are the only
    commits whose subject starts with the reserved prefix, so the newest such commit's date is the
    last time any area was updated.
    """
    out = _api(
        f"repos/{repo}/commits?per_page={int(limit)}",
        '.[] | [.commit.committer.date, (.commit.message | split("\\n")[0])] | @tsv',
    )
    rows = []
    for line in out.splitlines():
        date, _, subject = line.partition("\t")
        if date:
            rows.append((date.strip(), subject.strip()))
    return rows


def merged_prs_for_area(area, repo=CODE_REPO):
    """Every merged PR number labelled `roadmap/<area>`, newest first.

    Attribution is done per *area*, not per PR. The obvious alternative -- ask each PR in the
    window for its labels -- costs one request per PR, and an area's first window covers its whole
    history, so bootstrapping the project would have meant well over a thousand requests. One
    request per area (fourteen today) answers the same question, and the result doubles as the
    bootstrap lookup for an area's earliest PR.

    `--limit` is set far above the project's total deliberately rather than left at the default:
    the oldest entries are exactly what bootstrap needs, so a cap that silently truncated old
    history would lose work. (`TauCeti/scripts/loc_roadmap_graph.py` caps at 2000 because a chart
    only needs recent history; that would be the wrong choice here.)
    """
    out = gh([
        "pr", "list", "--repo", repo, "--state", "merged",
        "--label", f"{ROADMAP_LABEL_PREFIX}{area}",
        "--limit", "100000", "--json", "number",
    ])
    try:
        rows = json.loads(out)
    except json.JSONDecodeError as exc:
        raise GhError(f"could not parse gh pr list output: {exc}") from exc
    return sorted((int(r["number"]) for r in rows), reverse=True)


def pr_details(numbers, repo=CODE_REPO):
    """`[{number, title, body, merged_at, url}]` for an explicit set of PR numbers.

    Bodies are commentary for the writing model, not ground truth: they are self-reported, and a
    body can claim more than its diff delivers. `facts` supplies the ground truth instead.
    """
    out = []
    for n in numbers:
        raw = _api(f"repos/{repo}/pulls/{int(n)}")
        obj = json.loads(raw)
        out.append(
            {
                "number": int(n),
                "title": obj.get("title") or "",
                "body": obj.get("body") or "",
                "merged_at": obj.get("merged_at"),
                "url": obj.get("html_url") or f"https://github.com/{repo}/pull/{n}",
            }
        )
    return out


def open_progress_prs(repo=ROADMAP_REPO, branch_prefix="progress/"):
    """Open PRs on the roadmap repo whose head branch is a progress branch.

    An open progress PR *is* the in-flight marker for its area. Until it merges, the area's cursor
    in `main` still points at the old window, so recomputing would produce the same window again;
    treating the PR as in-flight is what stops a duplicate being opened every day.

    `headRepositoryOwner` comes back so callers can tell whose work a pull request is. Anyone may
    open one on a `progress/*` branch, and branch names are a pure function of the window, so
    treating every one of them as an in-flight marker would let a stranger freeze a roadmap by
    opening one pull request a day.

    `createdAt` comes back too, because "in flight" has to expire. A pull request the merge check
    refuses permanently never merges and never closes itself, and without an age it would mark its
    area in flight forever, silently stopping that roadmap's reporting for every operator.
    """
    out = gh([
        "pr", "list", "--repo", repo, "--state", "open",
        "--limit", "200", "--json",
        "number,headRefName,title,url,createdAt,headRepositoryOwner",
    ])
    rows = json.loads(out)
    return [r for r in rows if (r.get("headRefName") or "").startswith(branch_prefix)]
