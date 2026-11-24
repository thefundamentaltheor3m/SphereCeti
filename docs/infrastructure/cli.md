# Project CLI and configuration

The `sphereceti` command supplies project diagnostics and the adapters credited in the
[architecture plan](../../INFRASTRUCTURE-PLAN.md). Available command families are:

| Command | Guide |
|---|---|
| `--version` | [Which build am I running?](#which-build-am-i-running) |
| `doctor`, `status` | Project identity, policy and queue diagnostics (below) |
| `review` | [Choose the PR that most needs your review](local-review.md#choosing-what-to-review) |
| `reviews` | [Your review queue: ready to merge, revised, author replied, new, waiting on the author, blocked by a parent](local-review.md#your-review-queue-and-bounded-batches) |
| `review --new / --revised / --all --limit N` | [Bounded review batches](local-review.md#your-review-queue-and-bounded-batches) |
| `review N` | [Local review, posted by default](local-review.md#posting-by-default) |
| `review --force-claim` | [Advisory review-in-progress claims](local-review.md#review-in-progress-claims) |
| `review --read-records / --no-post` | [Authenticated records and publication](review-records.md) |
| `review-publish RUN` | [Publish a saved run without reviewing again](local-review.md#publishing-a-saved-run) |
| `review-check-sandbox` | [Credential-free Codex sandbox diagnostic](local-review.md#codex-sandbox-diagnostic) |
| `archive` | [Durable review records](review-archive.md) |
| `worker plan` | [Worker planning](worker.md) |
| `worker run` | [Guarded execution and leases](worker-execution.md) |
| `worker run --expect-head SHA` | [Binding a run to the authorized head](worker-execution.md#binding-a-run-to-the-authorized-head) |
| `evaluation` | [Costs and shadow comparisons](evaluation.md) |
| `worker run --loop` | [Bounded review loops](worker-loop.md) |
| `progress` | [Local reporting drafts](progress-reporting.md) |
| `merge-observe` | [Merge eligibility observations](merge-observation.md) |
| `auto-approve-check` | [Read-only auto-approval decision](merge-observation.md#auto-approval-decision) |
| `merge-doctor / merge-control` | [Controller diagnostics and gated action](merge-controller.md) |
| `maintenance` | [Lifecycle diagnostics and labels](lifecycle.md) |
| `profile-plan / profile-run` | [Advisory profiling](profiling.md) |
| `intentions`, `intend TARGET` | [Work underway on proof targets, and registering an intention](intentions-cli.md) |
| `verify` | [Check a proof branch the way CI does, before opening the PR](#verifying-a-proof-branch) |

For installation smoke tests, one-PR review rehearsal, and the boundary between contributor
credentials and official merge workers, see the [rollout guide](rollout.md).

From this checkout:

```bash
uv sync --locked
uv run --locked sphereceti doctor --offline
uv run --locked sphereceti status --json
```

After landing, installation from the canonical repository uses:

```bash
uv tool install git+https://github.com/thefundamentaltheor3m/SphereCeti
sphereceti doctor
sphereceti status --json
```

## Which build am I running?

`sphereceti --version` prints the package version and the installed commit, for example
`0.1.0 (main@90b0860)`. The commit and the requested revision come from the installation's
PEP 610 `direct_url.json`, which uv writes for Git installs. A local, path or editable install, or
a source tree on `PYTHONPATH`, prints `(local build)`, followed by `, checkout <commit>` when the
package sits in a Git checkout (read with `git rev-parse`). Missing metadata never fails the command.

Only a build of current approved main makes a review official. `doctor` checks this:

```text
installed: main@90b0860 · up to date with approved main
installed: main@90b0860 · 3 commits behind approved main (90b0860 → abc1234); update with: uv tool install --force --refresh git+https://github.com/thefundamentaltheor3m/SphereCeti@main
```

"Up to date" is the review path's own test, `installed_tooling_matches_T`: every installed tooling
file has the same Git blob ID at approved main T, resolved as `repos/{repo}/commits/main`.
`doctor` reads T's tree through the API rather than fetching it. The compare API only counts
commits. An install that is behind main but whose tooling is unchanged is still current for
reviews, and doctor says so. `--json` adds `installed` with `installed_commit`, `approved_main`,
`behind_by`, `up_to_date` and `state`. With `--offline`, doctor prints only the installed build.
A GitHub failure here reports `state = error` and does not change doctor's exit code. When the
installed tooling is not approved main, `sphereceti review` says so before any model call:
`Your sphereceti is not current main (installed main@X, approved main Y): this review will be
advisory, not official. Update with: …`.

Without `--offline`, both commands read the canonical repository's open PR queue through `gh`.
They never post, create branches, spend provider credits, or change repository settings.
A failed query exits 1 and reports `queue.state = error` with `pull_requests = null`.
An offline run reports `not_checked`, also with a null list. A confirmed empty queue alone
has `state = available` and an empty list. JSON reports have schema version 1.

`doctor` additionally locates git, gh, Lean, and Lake; a missing executable exits 1. Exit 0
means diagnostics succeeded, not that automation is ready. App installation, required checks,
branch protections, and the production adapter are explicitly unverified. Activation requires verified live configuration. The profile proposes the installed roadmap state; authoritative execution still requires
that profile and the source revision to be approved on the canonical branch. Capability diagnostics separate implementation, requested policy, and readiness.
`enabled = false` means diagnostics have not verified activation; it does not prove a live off switch.
Review posting (the default for a live `review`) requires approved live policy; without it the
record stays local.
`local_review` separately reports the available advisory adapter.

The installed package includes these configuration resources:

| File | Role |
|---|---|
| `sphereceti.toml` | Canonical identity, mathematical destination, source paths, dependency pins, state branch names |
| `policy/automation.toml` | Repository-owned operational switches and acceptance inputs |
| `policy/reporting.toml` | Approved documentation endpoint (initially empty), report scope and cadence |
| `policy/merge-checks.toml` | Approved workflow and status-producer IDs, initially unconfigured |
| `policy/merge-controller.toml` | Controller workflow and required-check IDs, initially unconfigured; the executor is the workflow's job token |
| `tools/ci/merge-controller.yml` | Packaged copy of the installed read-only `.github/workflows/merge-controller.yml`, for exact-byte comparison |
| `policy/archive.toml` | Private archive capture and remote sync policy |
| `policy/lifecycle.toml` | Managed labels and lifecycle thresholds |
| `tools/upstream-lock.toml` | Exact upstream source revisions/paths, adaptation status, reuse terms |

The CLI loads these from its installed package, or from its own source tree during development.
It does not discover policy in the caller's working directory. Installing code from an
unreviewed branch does not establish trust: [PR #6](https://github.com/thefundamentaltheor3m/SphereCeti/pull/6) supplies approved tooling selection for
server checks. The configuration digest is diagnostic provenance, not a review approval.

`--operator-config PATH` accepts only these preferences:

```toml
provider = "none"
budget_usd = 0
storage = "~/.local/state/sphereceti"
```

Preferences cannot change repository identity, source selection, authorization, or automation
switches. Diagnostics only validate/report them. Explicit `review` uses private storage;
local subscription reviews (bare `review` and `review N`, posting or not) read
`~/.config/sphereceti/operator.toml` when no `--operator-config` is supplied. Inference requires
a selected provider and positive budget. `review N --dry-run` verifies the exact evidence without
invoking a provider; bare `review --dry-run` also previews which PR it would choose. See [local review usage and limits](local-review.md).
Unknown fields, floating source commits, traversal paths, and unsupported schema versions fail.
A source-lock component cannot move from planned to adapted/imported while its reuse terms
remain unresolved. The Worker entry is now `reference-only`: its source import was cancelled in favor of an
independently authored Apache-2.0 implementation. This status grants no reuse rights; the
upstream license remains unresolved. The planned Data import remains inactive.

The wheel bundles the same project resources as the source installation. CI builds and installs
both distributions into separate temporary environments and tests them from a foreign directory
containing an untrusted `sphereceti.toml` and policy file. Review resources (engine, rubrics,
references, project overlays, source manifest, and license) are also bundled; both installations
run dry and full advisory reviews with a fake provider.

## Verifying a proof branch

Run `sphereceti verify` in your SphereCeti checkout before opening or updating a proof PR:

```bash
lake exe cache get          # once per dependency pin; verify exits 2 without the Mathlib cache
sphereceti verify           # or: uv run --locked sphereceti verify
```

It checks the working tree, including uncommitted and untracked files, against its merge base
with `origin/main` (`--base REF` to change it; run `git fetch origin` first). Each step runs
what CI already runs, from your checkout:

| Step | What runs | Fails when |
|---|---|---|
| `changes` | `git diff` against the merge base, plus untracked files; or `--module M` (repeatable) | the base or a named module does not exist (exit 2) |
| `roadmap` | `python3 -I scripts/check_roadmap.py` (CI's "Check roadmap contracts") | a static contract fails |
| `build` | `lake build +Module` for each changed library/roadmap module; `lake build @/SphereCeti` when `SphereCeti.lean` changed or a module was deleted; bare `lake build` when no Lean source changed or the dependency configuration changed | Lean reports an error; each is listed as `file:line:column` |
| `boundaries` | `lake env python3 -I scripts/check_modules.py --json` (CI's "Check module boundaries") | an import crosses the library/roadmap boundary |
| `root_imports` | `SphereCeti.lean` is compared with the merge base. Proof PRs leave it alone and import topic modules directly; the `SphereCeti.*` Lake glob builds every module, and the root keeps its existing re-exports | the root changed; the message gives the `git checkout <merge-base> -- SphereCeti.lean` that restores it |
| `audit` | `lake env python3 -I scripts/check_audits.py` (CI's "Build and audit every classified source"), with its verdict read back | a new `sorryAx` dependency (listed as a new admission), roadmap ledger drift, an unapproved axiom, lint finding, or empty module, or a warning in a library module |

Each step prints one line: `PASS`, `FAIL` or `SKIPPED` with the reason. Then come the verdict
and the next action. A skipped step is never a pass: `--skip-audit`, a failed build or a failed
boundary check skips the audit, and the verdict is then `incomplete` or `fail`. A change to
`policy/audits.json` is flagged, because the trusted build applies main's policy.

A `WARNING:` line, which never changes the verdict or exit code, says when the branch is stacked:
its open PR targets a branch other than `main` (read with `gh pr view --json baseRefName`; any gh
failure skips this), or its merge base is not the tip of `--base`. The line reads
`stacked on <base>: proofs stacked on unmerged PRs wait for their parents; start from main when you can`.

| Exit | Verdict |
|---|---|
| 0 | `pass`: every step passed |
| 1 | `fail` (a check failed) or `incomplete` (a step was skipped) |
| 2 | `environment_error`: not a SphereCeti checkout, no `lake`, base missing, dependencies not at the manifest pins, or no Mathlib cache. The message names the fix, usually `lake exe cache get` |

`--json` prints exactly one JSON document on stdout; progress and Lake's log go to stderr. The
document has `schema` `sphereceti.verify/v1`, `verdict`, `exit_code`, `next_action`, `root`, `head`,
`base` (`ref`, `merge_base`), `environment`, `modules` (changed paths, library/roadmap/deleted/new
modules, build targets), `steps` (each with `name`, `status`, `summary`, `seconds`, `command`,
`failures`, `details`), a flattened `failures` list (`step`, `message`, and `file`, `line`,
`column` where known), `warnings` and the total `seconds`.

`verify` is advisory. It runs your checkout's own scripts, as the ordinary `CI` workflow does,
not approved main's tooling in the sandbox, so `trusted-build` remains the merge evidence. It does
not fetch, push, post or call a model provider; its only network read is the optional `gh pr view`.
It never writes to the repository.
With the Mathlib cache present, the first run on main took about 100 seconds, and later runs about 40 seconds.
