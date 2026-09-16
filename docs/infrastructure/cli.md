# Project CLI and configuration

The `sphereceti` command supplies project diagnostics and the adapters credited in the
[architecture plan](../../INFRASTRUCTURE-PLAN.md). Available command families are:

| Command | Guide |
|---|---|
| `doctor`, `status` | Project identity, policy and queue diagnostics (below) |
| `review` | [Local advisory review](local-review.md) |
| `review --read-records / --post` | [Authenticated records and explicit publication](review-records.md) |
| `archive` | [Durable review records](review-archive.md) |
| `worker plan` | [Worker planning](worker.md) |

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
branch protections, and the production adapter are explicitly unverified. Activation requires verified live configuration. The current scaffold has no approved roadmap; PR #1 is not silently
used as specification. Automatic capabilities remain disabled; explicit posting is implemented but requires
approved live policy. `local_review`
separately reports the available advisory adapter.

The installed package includes these configuration resources:

| File | Role |
|---|---|
| `sphereceti.toml` | Canonical identity, mathematical destination, source paths, dependency pins, state branch names |
| `policy/automation.toml` | Repository-owned operational switches and acceptance inputs |
| `policy/archive.toml` | Private archive capture and remote sync policy |
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
inference requires a selected provider and positive budget. `review N --dry-run` verifies
the exact evidence without invoking a provider. See [local review usage and limits](local-review.md).
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
