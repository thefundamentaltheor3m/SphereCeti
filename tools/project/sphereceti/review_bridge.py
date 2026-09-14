"""Private subprocess bridge to the one imported engine; never a publishing command.

Run in a fresh interpreter so TauCetiReview's flat sibling imports and mutable registries
cannot collide with the project CLI or another review. Provider adapters remain upstream's.
"""
from __future__ import annotations

import contextlib
import io
import json
from pathlib import Path
import sys


def bound_shadow_budget(review, allowance):
    """Constrain the isolated engine at its actual day-balance read, without resetting spend."""
    original_load = review.Ledger.__init__
    def bounded_ledger(ledger, path):
        original_load(ledger, path)
        original_days = ledger.data['days']
        class BudgetDays(dict):
            def get(self, day, default=0):
                spent = super().get(day, default)
                # review.py reads the day's balance once before dispatch. Its parsed
                # args hold the daily cap, so constrain that cap at this exact read.
                review_args.daily_budget = min(review_args.daily_budget, spent + allowance)
                return spent
        ledger.data['days'] = BudgetDays(original_days)
    original_parse = review.argparse.ArgumentParser.parse_args
    review_args = None
    def parse_args(parser, *args, **kwargs):
        nonlocal review_args
        review_args = original_parse(parser, *args, **kwargs)
        return review_args
    review.argparse.ArgumentParser.parse_args = parse_args
    review.Ledger.__init__ = bounded_ledger


def main() -> int:
    request = json.loads(Path(sys.argv[1]).read_text())
    runner = Path(request["engine"]) / "runner"
    sys.path.insert(0, str(runner))
    import review
    import reviewers

    # Add approved evidence as runner context, never inside the author-provided PR description.
    original_prompt = review.build_prompt
    context = request["context"]
    review.build_prompt = lambda rubrics, angle, candidate, marker: original_prompt(
        rubrics, angle, context + "\n\n" + candidate, marker)

    # Upstream subscription fallback can reuse a personal HOME/config. Refuse that fallback;
    # retain its provider-specific credential copying and read-only tool restrictions.
    original_env = review.reviewer_env

    def isolated_env(*args, **kwargs):
        env, home = original_env(*args, **kwargs)
        for name in ("HOME", "CODEX_HOME", "KIRO_HOME", "XDG_DATA_HOME"):
            if name in env and not Path(env[name]).resolve().is_relative_to(Path(home).resolve()):
                reviewers.cleanup_rev_home(home)
                raise RuntimeError("subscription credential could not be isolated; use API authentication")
        return env, home

    review.reviewer_env = isolated_env
    if request.get("shared_budget_ledger"):
        # Persist each shadow attempt's spend to the shared ledger as it occurs, keeping its
        # normal case files intact. The inherited store lock also survives a parent interruption.
        shared = Path(request["shared_budget_ledger"])
        original_persist = review.Ledger.persist

        def persist_shadow(ledger):
            original_persist(ledger)
            parent = json.loads(shared.read_text())
            parent["days"] = ledger.data["days"]
            temporary = shared.with_suffix(".tmp")
            temporary.write_text(json.dumps(parent, indent=2) + "\n")
            temporary.replace(shared)

        review.Ledger.persist = persist_shadow
    if request.get("shadow_budget_usd") is not None:
        bound_shadow_budget(review, request["shadow_budget_usd"])
    allowed = set(request["executables"])

    def guard(event, args):
        if event == "subprocess.Popen":
            executable, argv, cwd, env = args
            if str(executable) not in allowed or str(cwd) != request["workspace"]:
                raise RuntimeError("review engine attempted a non-provider subprocess")
        elif event.startswith(("socket.", "os.exec", "os.spawn", "os.posix_spawn")) or event in (
            "os.system", "os.fork", "os.forkpty",
        ):
            raise RuntimeError("review engine attempted external I/O outside a provider adapter")

    sys.addaudithook(guard)
    sys.argv = ["review", *request["arguments"]]
    # Raw provider errors can contain credentials. Keep neither engine console stream in artifacts.
    try:
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            review.main()
        return 0
    except SystemExit as error:
        return error.code if type(error.code) is int else 1
    except Exception:
        return 1


if __name__ == "__main__":
    sys.exit(main())
