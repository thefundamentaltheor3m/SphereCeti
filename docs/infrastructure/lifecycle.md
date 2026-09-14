# Lifecycle maintenance

**Adapted from the [TauCeti contributors](https://github.com/TauCetiProject/TauCeti),
Apache-2.0, at [b743b60](https://github.com/TauCetiProject/TauCeti/tree/b743b607ce3e9742b18026ad79082e5d15badff5).**
The exact sources are
[`scripts/pr_status/core.py`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/pr_status/core.py),
[`labels.py`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/pr_status/labels.py),
[`conflicts.py`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/pr_status/conflicts.py),
[`stuck_alerts.py`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/pr_status/stuck_alerts.py), and
[`scripts/housekeeping.py`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/housekeeping.py),
with their corresponding tests recorded in `tools/upstream-lock.toml`.
Shared authenticated observation comes from
[TauCetiReview](https://github.com/TauCetiProject/TauCetiReview) at
[afb424e](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b)
through [SphereCeti #15](https://github.com/thefundamentaltheor3m/SphereCeti/pull/15).

## Review and dependency boundary

The preceding stack layers supply merge observation and the inactive controller. Review the
shared decision/API contract, then `lifecycle.py`, `lifecycle_api.py`, the policy, and the tests.
All infrastructure lands before roadmap #1; lifecycle diagnostics do not enable the controller.

The selected port covers main health, quiet-work diagnostics, housekeeping recommendations,
and managed status/conflict labels. It uses #15's observation directly and never parses an
upstream scoreboard or interprets a label as proof, review, or merge authority. It does not
implement automatic PR closure, budget retirement, target-marker deduplication, empty-diff
closure, branch deletion/rebasing, scheduler control, or external notifications. Those actions
need separately reviewed ownership and lifecycle contracts; they are not implied by enabling
these labels. No workflow or repository setting is activated on landing.

## Local diagnostics

```bash
sphereceti maintenance --health-only --json
sphereceti maintenance --pr 123 --json
sphereceti maintenance --sweep --json
```

All output is JSON, including when `--json` is omitted. `--source-repo /path/to/repo` can supply
local immutable Git objects; authority still comes from exact remote `main`. Otherwise the
adapter fetches objects into `--cache-dir` (default `~/.cache/sphereceti/lifecycle`). Mathematical
PR observations reuse #15's source evidence and optional `--dependencies-dir`; protected,
draft, held, closed, and stacked PRs do not need a review environment. The command never invokes
a provider. Main-health-only needs no local source checkout and does not fetch a dependency graph.

Preview reads current GitHub state, the approved-main policy if installed, and complete label
inventories. Missing approved policy produces explicit setup blockers and uses the installed
age defaults for advisory diagnostics only. It cannot enable publication. A sweep enumerates
at most 50 PRs, serially; oversized, duplicate, or incomplete inventories fail. One PR's unknown
state or API error is reported without suppressing diagnostics for the remaining PRs.

| Observation | Managed status label |
| --- | --- |
| Human review required | `sphereceti:human-review` |
| Shared decision blocked | `sphereceti:blocked` |
| Eligible at this observation | `sphereceti:observed-eligible` |

These are display labels. The merger continues to obtain its own fresh evidence and does not
consume them. Conflict is independent: `sphereceti:conflict` accompanies any status. GitHub's
`mergeable: null` stays unknown and does not remove an existing conflict label. Publication
skips that PR entirely until its state becomes known. A later invocation reads it again;
there is no retry loop or stale-event replay.

Draft PRs, PRs carrying `keep`, `hold`, `wip`, `human`, `do-not-close`, or `blocked` (case
insensitive), existing human auto-merge requests, and PRs targeting a stack branch are left
untouched. Closed/merged PRs selected explicitly can have managed labels cleared; their
unrelated labels remain intact. Open-PR sweeps do not revisit terminal PRs automatically.

`eligible_now_but_quiet` means the current shared observation is eligible and the PR has no
recorded update for at least 24 hours. It does **not** claim continuous eligibility or a broken
controller: activation may still be disabled. A blocked PR quiet for 168 hours receives a
`human_review_of_quiet_blocked_pr` recommendation, never an automatic close. Labels/comments
can update GitHub's activity timestamp, so these conservative diagnostics can under-report
staleness. Neither upstream's lifetime review budget nor target-body markers are adopted.

## Main-health contract

The adapter reads the exact main tip and the newest 30 `ci.yml` runs filtered to main/push.
It validates workflow/repository/event/path identities, duplicate IDs, and window completeness.
The most recently created conclusive run determines the last known result. A queued, running,
cancelled, neutral, or skipped run does not clear a previous failure. A newer success does.

`green` requires that successful run to name the current tip; an older success is `pending_tip`.
An older failure remains `red` while the tip advances without a newer success. An entirely
inconclusive/empty window is `unknown`, never a healthy empty result. Disabled CI is reported
as `disabled`. The source revision and last conclusive run are retained in the report. These
are operational diagnostics, not trusted-build attestations or a substitute for #15's checks.

## Explicit label publication (disabled)

```bash
sphereceti maintenance --pr 123 --apply-labels --json
```

Future setup must deliberately enable both `policy/lifecycle.toml`'s `labels_enabled` and
`policy/automation.toml`'s `posting` on approved main, configure `writer_user_id`, install the
matching CLI/resources, and precreate the four managed label names. The selected code and
packaged resources must match exact main. Operator preferences and a conflicting working
directory cannot override these checks. Keep the separate `SPHERECETI_MAINTENANCE_TOKEN` in
the trusted operator/runner environment, with only the repository permissions needed to write
issue labels. Its user ID/type is checked; token custody and least privilege remain setup
responsibilities. No scheduler or credential setup is included in this PR.

The writer token is removed from the inherited environment before any reader/Git process is
started. The writer receives a minimal environment and only issues identity GET, a one-label
POST, or a DELETE for one of the fixed managed names. It cannot change PR state or write
comments through the exposed reconciliation path. Labels are not created or globally edited.

The stop switches are checked before enumerating work. Immediately before a label change,
the adapter rereads approved-main setup and the entire PR observation, including holds, labels,
head/base, and shared evidence. Changed evidence cancels that PR's action. It makes at most
**one label mutation per invocation**, including sweeps. Obsolete status labels are removed
first; a later fresh invocation adds the replacement. Thus a transition may temporarily have
no status label. Repeated invocations converge without clobbering unrelated labels.

Readback reports whether the desired label presence was observed, including after an ambiguous
transport error. It does not claim exclusive authorship of that state. No uncertain mutation
is retried in the same run, and no saved plan can be replayed. `reconcile_again` means one write
was observed and another fresh invocation can finish the set; `disabled` and unknown/failed
evidence return nonzero. Ordinary advisory findings such as main being red do not imply a
transport error. A PR with unknown state remains an error even if another PR is processed.

GitHub label writes have no expected-head precondition. A final concurrent push, hold, or stop
change can race the last read; a label may briefly be stale. This is a metadata-only boundary,
and the next fresh reconciliation corrects it. Run a single trusted reconciler for predictable
convergence. A stopped switch cannot recall an already in-flight label request.

## Validation

`tests/test_lifecycle.py` adapts upstream conflict/unknown/hold, label convergence, main-red
recovery, quiet-work, and per-detector failure cases. It adds exact shared-observation binding,
policy/identity/resource checks, head and policy races, one-write limits, and ambiguous readback.
`tests/lifecycle_fixture.py` exercises the actual installed/source CLI against exact Git policy
and a GET-only GitHub stub: preview, disabled apply, token stripping, and API failure. Both wheel
and source installs run it from a foreign directory. The existing trusted-build/compiled-audit
CI remains the mathematical check; this PR changes no Lean source or dependency pin.
