"""Publish a saved local review run's record once, without running inference again.

A run whose publication was interrupted, kept local by policy, or run with --no-post keeps an
exact attestation proposal in record.md. This command revalidates it against current evidence
and publishes those exact bytes through the same confirmed publisher as `review --post`.
It never imports the engine bridge or starts a provider.
"""
from __future__ import annotations

import json
from pathlib import Path
import re
import tempfile
from types import SimpleNamespace

from .config import parse_policy
from .local_review import BUDGET_STOP_NOTE, ReviewError, poster_identity, prepare, revisions, store_lock, write_json
from .review_records import BINDINGS, RecordError, identity, intact, parse_json, parse_record
from .review_post import GitHub, publish

PUBLISHABLE = ("complete", "partial")
RUN_ID = re.compile(r"[0-9a-f]{32}")
NAMES = {"dependency_digest": "the dependency manifest", "engine_digest": "the review engine",
         "effective_rubrics_digest": "the effective rubrics", "installed_tooling_digest": "the installed tooling",
         "policy_digest": "the approved policy", "review_context_digest": "the approved review context",
         "description_digest": "the PR title or description", "diff_base": "the diff base"}


class PublishRefused(ReviewError):
    def __init__(self, reasons):
        self.reasons = list(reasons)
        super().__init__("; ".join(self.reasons))


def add_parser(commands):
    p = commands.add_parser("review-publish",
                            help="publish a saved review run's record once, without running the review again")
    target = p.add_mutually_exclusive_group(required=True)
    target.add_argument("run", nargs="?", help="run id under the operator's review storage, or a run directory")
    target.add_argument("--latest", type=int, metavar="PR", help="the most recent saved run for this PR")
    p.add_argument("--json", action="store_true")
    p.add_argument("--operator-config", type=Path, help="operator preferences (default ~/.config/sphereceti/operator.toml)")
    p.add_argument("--source-repo", type=Path, help="read exact objects from this Git repository")
    p.add_argument("--dependencies-dir", type=Path, help="local Git dependency stores, named by manifest package")
    return p


def find_run(args, storage: Path) -> Path:
    runs = storage / "runs"
    if args.latest is not None:
        found = []
        for result in sorted(runs.glob("*/result.json")) if runs.is_dir() else ():
            try:
                saved = json.loads(result.read_text())
            except (OSError, ValueError):
                continue
            if (isinstance(saved, dict) and saved.get("pr") == args.latest
                    and (result.parent / "record.md").is_file()):
                found.append((str(saved.get("finished_at") or ""), result.parent.name, result.parent))
        if not found:
            raise PublishRefused([f"no saved review run with a record for PR #{args.latest} under {runs}"])
        return max(found)[2]  # The latest run only; an older run is never chosen silently.
    if RUN_ID.fullmatch(args.run) and (runs / args.run).is_dir():
        return runs / args.run
    path = Path(args.run).expanduser()
    if not path.is_dir():
        raise PublishRefused([f"{args.run} is neither a run id under {runs} nor a run directory"])
    return path.resolve()


def load_run(directory: Path, repository: str):
    """The saved result and the exact record it produced, cross-checked as the archive does."""
    try:
        result = parse_json((directory / "result.json").read_text())
        rendered = (directory / "record.md").read_text()
        saved = parse_json((directory / "record.json").read_text())
    except (OSError, ValueError) as error:
        raise PublishRefused([f"{directory} has no readable result.json, record.json and record.md"]) from error
    record = parse_record(rendered)
    if saved != record:
        raise PublishRefused(["record.json and record.md disagree"])
    if not isinstance(result, dict) or any(result.get(k) != record[k] for k in
                                           (*BINDINGS, "completion", "execution_mode", "verdicts")):
        raise PublishRefused(["result.json and the saved record disagree"])
    if record["repository"] != repository:
        raise PublishRefused([f"the run reviews {record['repository']}, not {repository}"])
    return result, record, rendered


def eligibility(result, record) -> list[str]:
    """Only a run that `review --post` could have published, and that was not already published."""
    reasons = []
    if result.get("stop_reason") == "daily_budget":
        reasons.append(BUDGET_STOP_NOTE)
    if result.get("source_mode") != "github":
        reasons.append("the run used local sources; only a live GitHub review can be published")
    if not result.get("tooling_approved"):
        reasons.append("the run used a prospective --tooling revision, not approved main")
    if record["execution_mode"] not in ("commit", "manual"):
        reasons.append(f"{record['execution_mode']} runs are never published")
    if record["completion"] not in PUBLISHABLE:
        reasons.append(f"the run's completion is {record['completion']}; it has no review to publish")
    inputs = result.get("contest_inputs")
    if inputs == "local":
        reasons.append("the run used local reply inputs, which cannot attest to GitHub contests")
    elif inputs is None and any(record["contests_through"].values()) and "publication" not in result:
        reasons.append("the run predates recorded contest provenance and carries contest watermarks")
    receipt = result.get("publication") or {}
    if receipt.get("state") == "confirmed":
        reasons.append(f"the run was already published as comment {receipt.get('comment_id')}; "
                       "a record missing from the PR is never published again")
    return reasons


def existing(comments, record, rendered, actor):
    """This identity's comment carrying this record (same body, hence the same record ID)."""
    for comment in comments:
        if identity(comment) != actor:
            continue
        body = comment.get("body")
        if body == rendered:
            return comment
        try:
            if isinstance(body, str) and parse_record(body)["record_id"] == record["record_id"]:
                return comment
        except (ValueError, TypeError):
            continue
    return None


def live_refs(client, repository, record, result):
    """Cheap current-state checks before any source is materialized."""
    pr = client.call(f"repos/{repository}/pulls/{record['pr']}")
    if not isinstance(pr, dict) or pr.get("number") != record["pr"]:
        raise PublishRefused(["GitHub returned another PR"])
    reasons = []
    if pr.get("state") != "open":
        reasons.append(f"PR #{record['pr']} is {pr.get('state') or 'not open'}")
    head, base = pr["head"]["sha"], pr["base"]["sha"]
    if head != record["head"]:
        reasons.append(f"the PR head moved from {record['head'][:7]} to {head[:7]}; the saved run "
                       "reviews an older head and cannot be published as current: run a new review")
    if base != record["base"]:
        reasons.append(f"the PR base moved from {record['base'][:7]} to {base[:7]}; run a new review")
    return reasons


def revalidate(args, project, record, result, client, storage, scratch):
    """Re-derive every bound evidence digest from current GitHub state, as `review --post` does."""
    fresh = SimpleNamespace(pr=record["pr"], tooling=None, head=None, base=None, description_file=None,
                            local_sources=False, source_repo=args.source_repo and args.source_repo.resolve(),
                            dependencies_dir=args.dependencies_dir and args.dependencies_dir.resolve())
    refs = revisions(fresh, project)
    current = prepare(fresh, project, refs, storage / "git", scratch / "workspace", scratch / "engine")
    policy_path = scratch / "workspace/approved/policy/automation.toml"
    policy = parse_policy(policy_path.read_text()) if policy_path.is_file() else None
    reasons = []
    if policy is None or not policy.posting:
        reasons.append("posting is disabled by approved repository policy")
    if not client.approved_revision(record["repository"], record["tooling_revision"], current["tooling"]):
        reasons.append(f"the run's tooling {record['tooling_revision'][:7]} is not an ancestor of approved main")
    reasons += [f"{NAMES.get(k, k)} changed since the review" for k in BINDINGS
                if k not in ("repository", "pr", "head", "base") and current[k] != record[k]]
    if current["installed_tooling_matches_T"] != result["installed_tooling_matches_T"]:
        reasons.append("whether the installed tooling matches approved main changed since the review")
    if reasons:
        raise PublishRefused(reasons)

    def final_check():  # Immediately before the single POST.
        again = revisions(fresh, project)
        if any(again[k] != refs[k] for k in ("tooling", "head", "base")):
            raise ReviewError("PR or approved context advanced during publication checks")
    return policy, final_check


def publish_saved(args, project, prefs, *, client=None) -> dict:
    storage = Path(prefs.storage).expanduser().resolve() / project.repository.replace("/", "__")
    directory = find_run(args, storage)
    result, record, rendered = load_run(directory, project.repository)
    report = {"schema": "sphereceti.review-publish/v1", "run": str(directory), "repository": record["repository"],
              "pr": record["pr"], "head": record["head"], "record_id": record["record_id"],
              "completion": record["completion"], "advisory": record["advisory"], "merge_eligible": False}
    reasons = eligibility(result, record)
    if reasons:
        raise PublishRefused(reasons)
    client = client or GitHub()
    actor = poster_identity(client)
    if actor is None:
        raise PublishRefused(["the gh identity is unknown or not a personal account"])
    report["identity"] = actor
    recorded = result.get("poster_identity") or (result.get("publication") or {}).get("identity")
    if recorded and recorded != actor:
        raise PublishRefused([f"the run belongs to {recorded}; gh is authenticated as {actor}"])
    comments = client.comments(record["repository"], record["pr"])
    found = existing(comments, record, rendered, actor)
    if found:  # Never post twice: report the record already on the PR and write nothing.
        report.update(state="already_published", comment_id=found["id"],
                      intact=intact(found, record["repository"], record["pr"]))
        return report
    reasons = live_refs(client, record["repository"], record, result)
    if reasons:
        raise PublishRefused(reasons)
    with store_lock(storage / "engine"), tempfile.TemporaryDirectory(prefix="publish-", dir=directory) as scratch:
        policy, final_check = revalidate(args, project, record, result, client, storage, Path(scratch))
        from .archive_store import capture
        result["archive"] = capture(directory, storage / "archive", record["repository"])  # idempotent
        try:
            receipt = publish(client, rendered, record, policy, final_check)
        except (RecordError, ReviewError) as error:
            # One POST at most: an ambiguous write is reported, never retried.
            receipt = {"state": "unconfirmed", "reason": str(error), "identity": actor, "merge_eligible": False}
    result["publication"] = {**receipt, "via": "review-publish"}
    write_json(directory / "result.json", result)
    report.update(state="published" if receipt["state"] == "confirmed" else "unconfirmed",
                  publication=receipt, archive=result["archive"])
    return report


def render(report, run_argument) -> list[str]:
    url = (f"https://github.com/{report['repository']}/pull/{report['pr']}"
           f"#issuecomment-{report.get('comment_id') or report.get('publication', {}).get('comment_id')}")
    if report["state"] == "already_published":
        edited = "" if report["intact"] else " It was edited, so readers treat it as a barrier."
        return [f"Already published: {url} (record {report['record_id'][:12]}, {report['identity']}). "
                f"Nothing was written.{edited}"]
    if report["state"] == "published":
        receipt = report["publication"]
        who = ("authorized reviewer" if receipt.get("authorized") else
               f"advisory: {receipt.get('identity')} is not an authorized reviewer")
        return [f"Published the saved review of #{report['pr']} (head {report['head'][:7]}): {url} ({who}).",
                "No review was run again."]
    return [f"Not posted: publication unconfirmed ({report['publication']['reason']}).",
            "The comment may exist. Do not post it by hand: run "
            f"`sphereceti review-publish {run_argument}` again; it looks for this record on the PR first "
            "and never posts it twice."]
