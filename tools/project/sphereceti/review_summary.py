# SPDX-License-Identifier: Apache-2.0
"""What will a review do, and what happened? One line before inference, one summary after.

Before inference it also says when the installed sphereceti is not approved main (the prepared
evidence's `installed_tooling_matches_T`), because such a review is advisory, not official.

Everything here reads the prepared evidence, the run's result and its local engine receipt
(`engine-archive/records/runs`). It never calls GitHub or a provider.
"""
from __future__ import annotations

from contextlib import contextmanager
import json
import os
from pathlib import Path
import re
import sys

from .local_review import RUBRICS

PUBLISH = "sphereceti review-publish RUN"  # #82: RUN is a run id under the store's runs/, or a run directory
PROVIDER_DOWN = {  # the engine's provider-down kinds (runner/review.py PROVIDER_DOWN_KINDS)
    "not_authenticated": "sign in to {provider} again (e.g. `{login}`), then rerun",
    "quota_exhausted": "wait for {provider}'s usage window to reset, then rerun",
    "rate_limited": "{provider} is rate limiting this account; rerun later",
}
LOGIN = {"codex": "codex login", "claude": "claude /login", "sonnet": "claude /login", "kiro": "kiro-cli login"}


def engine_defaults() -> dict:
    """Default models, read from the packaged engine's pricing table (no import of engine code)."""
    from .review_resources import review_files
    text = review_files()["runner/pricing.py"].decode()
    values = dict(re.findall(r'^([A-Z_]+_MODEL) = "([^"]+)"', text, re.M))
    for name, default in re.findall(r'"(deepseek|minimax|grok)": \(.*?or "([^"]+)"\)', text, re.S):
        values[name] = default
    return values


def effective_models(args, providers) -> list[str]:
    """The model each selected provider will use, after the engine's defaults."""
    defaults = engine_defaults()
    out = []
    for provider in providers:
        if provider == "codex":
            out.append(getattr(args, "codex_model", None) or f"{defaults.get('CODEX_MODEL')} "
                       f"(falls back to {defaults.get('CODEX_FALLBACK_MODEL')})")
        elif provider == "claude":
            out.append(getattr(args, "claude_model", None) or defaults.get("CLAUDE_MODEL"))
        elif provider == "sonnet":
            out.append(defaults.get("SONNET_MODEL"))
        elif provider == "kiro":
            out.append(getattr(args, "kiro_model", None) or defaults.get("KIRO_MODEL"))
        else:
            env = os.environ.get(f"TAUCETI_{provider.upper()}_MODEL") or os.environ.get(f"{provider.upper()}_MODEL")
            out.append(env or defaults.get(provider) or "unknown")
    return out


def plan(args, prefs, report) -> dict:
    providers = [p for p in (getattr(args, "provider", None) or prefs.provider).split(",") if p]
    if args.dry_run:
        outcome = "dry run: no model call, nothing posted"
    else:
        outcome = ("will post" if args.post else "will not post (--no-post)" if getattr(args, "no_post", False)
                   else "will not post (approved policy disables posting)" if getattr(args, "post_default", False)
                   else "will not post")
    try:
        models = effective_models(args, providers)
    except (KeyError, OSError, UnicodeError):
        models = ["unknown"] * len(providers)
    effort = getattr(args, "codex_effort", None)
    pairs = ", ".join(f"{p} {m}" + (f" ({effort})" if p == "codex" and effort else "")
                      for p, m in zip(providers, models)) or "no provider selected"
    line = (f"Review #{report['pr']}: head {report['head'][:7]}, base {report['base'][:7]} · "
            f"{pairs} · {outcome}")
    try:
        from .provenance import review_notice
        notice = review_notice(report, report.get("repository") or "thefundamentaltheor3m/SphereCeti")
    except Exception:  # The notice is informational; it never blocks or changes a review.
        notice = None
    return {"line": line, "pr": report["pr"], "head": report["head"], "base": report["base"],
            "providers": providers, "models": models, "codex_effort": effort if "codex" in providers else None,
            "posting": outcome, "tooling_notice": notice}


def announcing(prefs, announce, sink=None, inner=None):
    """A run_review guard that states the plan before any provider call.

    When the installed sphereceti is not approved main the review can only be advisory: on a
    terminal it asks first (before any claim or model call) unless --allow-advisory; elsewhere, and
    in batches, it continues and says so once per invocation."""
    @contextmanager
    def guard(args, report, policy, client):
        planned = plan(args, prefs, report)
        notice = planned.get("tooling_notice")
        shown = False
        batch = any(getattr(args, name, False) for name in ("new", "revised", "all"))
        if (notice and announce and not args.dry_run and not batch and not getattr(args, "allow_advisory", False)
                and sys.stdin.isatty() and sys.stdout.isatty()):
            announce(notice)
            shown = True
            if not ask("Continue with an advisory review? [y/N] "):
                from .local_review import ReviewError
                raise ReviewError("advisory review declined; nothing was claimed, run or posted. Reinstall "
                                  "sphereceti from main, or pass --allow-advisory")
        with (inner(args, report, policy, client) if inner else _null()):
            if sink is not None:
                sink.update(planned)
            if announce:
                announce(planned["line"])
                if notice and not shown and not getattr(args, "advisory_noticed", False):
                    announce(notice)
                    args.advisory_noticed = True  # a batch reuses its arguments: once per batch
            yield None
    return guard


@contextmanager
def _null():
    yield None


def receipt_runs(report) -> list[dict]:
    """This run's engine run records, if any (the local receipt)."""
    root = Path(report.get("output") or "") / "engine-archive" / "records" / "runs"
    runs = []
    for path in sorted(root.glob("*/*.json")) if root.is_dir() else ():
        try:
            value = json.loads(path.read_text())
        except (OSError, ValueError):
            continue
        if isinstance(value, dict) and value.get("head_sha") == report.get("head"):
            runs.append(value)
    return runs


def startup_failure(runs) -> bool:
    """Every run ended without a verdict and without the model touching a file: the provider could
    not start its sandboxed session (the case `review-check-sandbox` diagnoses)."""
    failed = [r for r in runs if r.get("verdict") in (None, "error")]
    return bool(runs) and len(failed) == len(runs) and all(
        not r.get("tool_trace") and all(a.get("error_kind") in ("unknown_error", "no_verdict")
                                        for a in r.get("attempts") or [{}])
        for r in failed)


def provider_down(runs):
    kinds = [a.get("error_kind") for r in runs for a in r.get("attempts") or []]
    return next((k for k in reversed(kinds) if k in PROVIDER_DOWN), None)


def advisory_why(report, publication) -> list[str]:
    """Why a posted record is advisory, from the record's own fields (review_records.is_advisory) and
    the publisher's authorization; empty when it is official. Never authorization alone."""
    reasons = []
    if report.get("completion") != "complete":
        reasons.append(str(report.get("completion")))
    if report.get("execution_mode") not in ("commit", "manual"):
        reasons.append(f"{report.get('execution_mode')} mode")
    if not report.get("tooling_approved"):
        reasons.append("reviewed tooling is not approved main")
    if not report.get("installed_tooling_matches_T"):
        reasons.append("installed tooling is not approved main; reinstall")
    if report.get("missing_context"):
        reasons.append("missing approved context")
    if report.get("config_differences"):
        reasons.append("candidate configuration differs")
    if not publication.get("authorized"):
        reasons.append("not an authorized reviewer")
    return reasons


def ask(question: str) -> bool:
    """A yes/no question on the terminal; anything but y/yes is no."""
    sys.stderr.write(question)
    sys.stderr.flush()
    try:
        return input().strip().lower() in ("y", "yes")
    except EOFError:
        return False


def summarize(args, report, *, posting=None) -> dict:
    """The summary line, its fields, and one concrete next action."""
    verdicts = report.get("verdicts") or {}
    requested = report.get("requested_rubrics") or list(RUBRICS)
    reviewed = [r for r in requested if verdicts.get(r) in ("approve", "request_changes", "block")]
    blocks = [r for r in RUBRICS if verdicts.get(r) == "block"]
    blocking = blocks[0] if blocks else None
    changes = [r for r in RUBRICS if verdicts.get(r) == "request_changes"]
    # Every rubric the author must address, blocks first, as the summary line lists them.
    findings = blocks + changes
    first = findings[0] if findings else None
    runs = receipt_runs(report)
    down = provider_down(runs)
    startup = report.get("completion") != "dry_run" and not reviewed and startup_failure(runs)
    complete = len(reviewed) == len(requested)
    stop = None
    if report.get("completion") == "dry_run":
        pass  # nothing ran, so nothing stopped
    elif report.get("stop_reason"):
        stop = report["stop_reason"].replace("_", " ")
    elif down:
        stop = f"provider unavailable ({down.replace('_', ' ')})"
    elif startup:
        stop = "provider failed to start"
    elif not complete and blocking:
        stop = f"blocked on {blocking}"
    elif not complete and report.get("completion") == "error":
        stop = f"engine error (exit {report.get('engine_exit_code')})"
    elif not complete:
        stop = "budget or round limit reached"

    publication = report.get("publication") or {}
    url = (f"https://github.com/{report['repository']}/pull/{report['pr']}#issuecomment-{publication['comment_id']}"
           if publication.get("state") == "confirmed" else None)
    advisory = advisory_why(report, publication) if url else []
    if url:
        posted = f"posted {url} · " + (f"advisory ({'; '.join(advisory)})" if advisory else "official")
    elif publication:
        posted = "publication interrupted"
    else:
        posted = "not posted: " + ((posting or "Not posted: local review").split(": ", 1)[-1].rstrip("."))

    if report.get("completion") == "dry_run":
        head, posted = "dry run", "not posted: dry run"
    elif complete and not first:
        head = f"{len(reviewed)}/{len(requested)} approve"
    else:
        head = f"{len(reviewed)}/{len(requested)} reviewed"
    parts = ([head] + ([f"stopped: {stop}"] if stop else []) +
             ([f"blocked: {', '.join(blocks)}"] if blocks and not stop else []) +
             ([f"changes requested: {', '.join(changes)}"] if changes and not stop else []) + [posted])
    provider = (getattr(args, "provider", None) or "").split(",")[0] or "the provider"
    output = Path(report.get("output") or "RUN")
    # A run under the operator store's runs/ is named by its id; an --output run by its directory.
    run = output.name if output.parent.name == "runs" else str(output)
    if report.get("completion") == "dry_run":
        action = "run again without --dry-run to review"
    elif publication and not url:
        action = f"publication was interrupted; run `{PUBLISH.replace('RUN', run)}`"
    elif startup:
        action = "run `sphereceti review-check-sandbox --compare-path --compare-tmpdir`"
    elif down:
        action = PROVIDER_DOWN[down].format(provider=provider, login=LOGIN.get(provider, "the provider's login"))
    elif report.get("stop_reason") == "usage_unknown":
        action = "check the provider's usage for the unreported attempt, then rerun"
    elif first:
        action = f"author: address {', '.join(findings)} (see record); rerun after the head changes"
    elif not complete:
        action = "rerun to finish the remaining rubrics (raise budget_usd with `--budget-usd` if needed)"
    elif not url and getattr(args, "no_post", False):
        action = "rerun without --no-post to publish the record"
    elif not url:
        action = f"none: every rubric approves; the record stays local ({posted.split(': ', 1)[-1]})"
    else:
        action = "none: every rubric approves"
    return {"line": " · ".join(parts), "reviewed": len(reviewed), "total": len(requested),
            "first_blocking": first, "findings": findings, "stop": stop, "posted": url, "official": bool(url) and not advisory,
            "advisory_reasons": advisory,
            "next_action": action}
