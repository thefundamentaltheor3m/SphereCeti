# Project CLI and configuration

The `sphereceti` command supplies project diagnostics and the adapters credited in the
[architecture plan](../../INFRASTRUCTURE-PLAN.md). Available command families are:

| Command | Guide |
|---|---|
| `doctor`, `status` | Project identity, policy and queue diagnostics (below) |
| `review` | [Choose the PR that most needs your review](local-review.md#choosing-what-to-review) |
| `reviews` | [Your review queue: revised, author replied, new, waiting on the author](local-review.md#your-review-queue-and-bounded-batches) |
| `review --new / --revised / --all --limit N` | [Bounded review batches](local-review.md#your-review-queue-and-bounded-batches) |
| `review N` | [Local review, posted by default](local-review.md#posting-by-default) |
| `review N --no-approve` | [Opted-in maintainers: review without submitting the GitHub approval](local-review.md#approvals-by-opted-in-maintainers) |
| `review --force-claim` | [Advisory review-in-progress claims](local-review.md#review-in-progress-claims) |
| `review --read-records / --no-post` | [Authenticated records and publication](review-records.md) |
| `review-publish RUN` | [Publish a saved run without reviewing again](local-review.md#publishing-a-saved-run) |
| `setup` | [First-run and changed review preferences](local-review.md#first-run-and-sphereceti-setup) |
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
a selected provider and positive budget; on a terminal the first review asks for them and saves
the file, and `sphereceti setup` changes them later. `review N --dry-run` verifies the exact evidence without
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
