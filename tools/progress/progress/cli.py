"""The `tauceti-progress` command line.

Subcommands, in the order a round uses them:

    due       is an update due at all? one API call, no clone. exit 75 when not.
    plan      pick the roadmap and the PR window. exit 75 when nothing qualifies.
    facts     what mathematics actually landed in the window (ground truth for the model)
    prompt    print a writing prompt for the worker to fill in and hand to a model
    apply     write the files and open the PR (resumable)
    announce  post a new section to Zulip (idempotent)

Exit codes follow the worker's convention: 0 did something, 75 (`EX_NOPROGRESS`) nothing to do,
1 a real error. The distinction matters because a round must fall through to other work on 75 but
must not silently treat an error as "nothing to do" -- that would let a transient GitHub failure
advance a cursor past real work.
"""

import argparse
import json
import pathlib
import sys

EX_NOPROGRESS = 75


def _load_plan(path):
    return json.loads(pathlib.Path(path).read_text(encoding="utf-8"))


PROMPT_DIR = pathlib.Path(__file__).resolve().parent / "prompts"


def cmd_prompt(args):
    """Print a writing prompt.

    The prompts live here rather than in the worker so that the words a model is given and the checks
    its output must pass are one versioned thing, pinned by the same SHA. They were duplicated once,
    the two copies drifted, and a fix was very nearly made to the dead one.

    The worker substitutes its own `__PLACEHOLDERS__` after fetching, so this deliberately prints the
    template unchanged.
    """
    path = PROMPT_DIR / f"{args.name}.md"
    if not path.is_file():
        print(f"no such prompt: {args.name}", file=sys.stderr)
        return 1
    sys.stdout.write(path.read_text(encoding="utf-8"))
    return 0


def cmd_due(args):
    from . import gh, plan

    commits = gh.recent_roadmap_commits(limit=args.limit)
    try:
        reason = plan.check_cadence(commits, idle_hours=args.idle_hours)
    except plan.NotDue as exc:
        print(f"not due: {exc}")
        return EX_NOPROGRESS
    print(f"due: {reason}")
    return 0


def cmd_plan(args):
    from . import plan

    try:
        result = plan.build_plan(
            roadmap_dir=args.roadmap_dir,
            code_dir=args.code_dir,
            ref=args.ref,
            idle_hours=args.idle_hours,
            min_prs=args.min_prs,
            only_area=args.area,
        )
    except plan.NotDue as exc:
        print(f"not due: {exc}", file=sys.stderr)
        return EX_NOPROGRESS
    out = plan.plan_json(result)
    if args.out:
        pathlib.Path(args.out).write_text(out + "\n", encoding="utf-8")
        print(f"wrote {args.out}: {result['roadmap']}, {len(result['prs'])} PR(s)")
    else:
        print(out)
    return 0


def cmd_facts(args):
    from . import facts

    p = _load_plan(args.plan)
    # The plan's PR list is the area filter. Without it `collect` would walk every merged PR in the
    # commit range, so a report on one roadmap would be grounded in every roadmap's work.
    result = facts.collect(args.code_dir, p["from_sha"], p["to_sha"], pr_numbers=p["prs"])
    out = json.dumps(result, indent=2, sort_keys=True)
    if args.out:
        pathlib.Path(args.out).write_text(out + "\n", encoding="utf-8")
        print(f"wrote {args.out}: {len(result['declarations'])} declaration(s) "
              f"in {len(result['files'])} file(s)")
    else:
        print(out)
    return 0


def cmd_apply(args):
    from . import apply as apply_mod

    p = _load_plan(args.plan)
    return apply_mod.run(
        plan=p,
        status_body_file=args.status_body,
        section_body_file=args.section_body,
        roadmap_dir=args.roadmap_dir,
        dry_run=args.dry_run,
        version=args.version,
    )


def cmd_announce(args):
    from . import announce as announce_mod

    return announce_mod.run(
        section_file=args.section,
        topic=args.topic,
        channel=args.channel,
        roadmap_parent=args.roadmap_parent,
        dry_run=args.dry_run,
    )


def build_parser():
    ap = argparse.ArgumentParser(prog="tauceti-progress", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    d = sub.add_parser("due", help="is an update due? (one API call, no clone)")
    d.add_argument("--idle-hours", type=float, default=None,
                   help="hours of quiet required (default 8)")
    d.add_argument("--limit", type=int, default=30,
                   help="how many roadmap commits to inspect (default 30)")
    d.set_defaults(fn=cmd_due)

    p = sub.add_parser("plan", help="pick the roadmap and the PR window")
    p.add_argument("--roadmap-dir", required=True, help="a TauCetiRoadmap checkout")
    p.add_argument("--code-dir", required=True, help="a full-history TauCeti checkout")
    p.add_argument("--ref", default=None,
                   help="the code ref to read (default: the docs-tracking branch, origin/docgen)")
    p.add_argument("--idle-hours", type=float, default=None)
    p.add_argument("--min-prs", type=int, default=None)
    p.add_argument("--area", default=None, help="force a single area (testing)")
    p.add_argument("--out", default=None, help="write the plan JSON here instead of stdout")
    p.set_defaults(fn=cmd_plan)

    f = sub.add_parser("facts", help="what declarations landed in the window")
    f.add_argument("--plan", required=True)
    f.add_argument("--code-dir", required=True)
    f.add_argument("--out", default=None)
    f.set_defaults(fn=cmd_facts)

    a = sub.add_parser("apply", help="write the files and open the PR")
    a.add_argument("--plan", required=True)
    a.add_argument("--status-body", required=True, help="file holding the model's STATUS prose")
    a.add_argument("--section-body", required=True, help="file holding the model's section prose")
    a.add_argument("--roadmap-dir", required=True, help="a writable TauCetiRoadmap clone")
    a.add_argument("--version", default=None, help="the TauCetiProgress SHA to record in the PR")
    a.add_argument("--dry-run", action="store_true", help="produce the commit, push nothing")
    a.set_defaults(fn=cmd_apply)

    pr = sub.add_parser("prompt", help="print a writing prompt, for the worker to fill in")
    # A plain string, not `choices=`: that would enumerate the directory at import time, so a build
    # that shipped no prompts would fail while merely parsing `--help`. `cmd_prompt` reports a
    # missing prompt properly.
    pr.add_argument("name", help="which prompt (progress, status)")
    pr.set_defaults(fn=cmd_prompt)

    n = sub.add_parser("announce", help="post a section to Zulip")
    n.add_argument("--section", required=True, help="file holding the rendered section")
    n.add_argument("--channel", default=None)
    n.add_argument("--topic", default=None)
    n.add_argument(
        "--roadmap-parent",
        choices=("TauCetiRoadmap", "Completed"),
        default="TauCetiRoadmap",
        help="parent directory containing the roadmap in TauCetiRoadmap",
    )
    n.add_argument("--dry-run", action="store_true")
    n.set_defaults(fn=cmd_announce)
    return ap


def main(argv=None):
    args = build_parser().parse_args(argv)
    # Defaults live in plan.py so there is one source of truth for the thresholds.
    from . import plan as plan_mod

    if getattr(args, "idle_hours", None) is None:
        args.idle_hours = plan_mod.IDLE_HOURS
    if getattr(args, "min_prs", None) is None:
        args.min_prs = plan_mod.MIN_PRS
    if getattr(args, "ref", None) is None:
        args.ref = plan_mod.CODE_REF
    try:
        return args.fn(args)
    except KeyboardInterrupt:
        return 130


if __name__ == "__main__":
    sys.exit(main())
