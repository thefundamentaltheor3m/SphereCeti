# Activating the merge controller

Everything the controller needs is installed with every switch **off**. Activation is a short,
ordered sequence: one administrator setting, then two tiny reviewed PRs. This page lists the exact
lines, the order, and what each step should print. Background: [merge controller](merge-controller.md).

## Order of operations

1. **Carry-over is merged.** Reviews and formal approvals carry over to "Update branch" heads
   (decision 2 on #100). Without it, strict up-to-date checks would invalidate every review on each
   update.
2. **An administrator turns strict on** ([ruleset change](#1-ruleset-change-administrator)).
3. **The activation flips PR lands** ([flips](#2-activation-flips-one-tiny-pr)), with the schedule
   still commented out. Only a maintainer's manual dispatch can now merge.
4. **The live race probe passes** ([probe](#3-live-race-probe)).
5. **The schedule PR lands** ([schedule](#4-schedule-one-tiny-pr)). Unattended merging is on.

Merging also needs the policy prerequisites that land separately: a nonempty `mathematical_paths`
(for example #149) and an opted-in maintainer in `approving_reviewers` (#154/#155).

## 1. Ruleset change (administrator)

On ruleset **21449770** (`main`), in the `required_status_checks` rule, set
`strict_required_status_checks_policy` to `true` and change nothing else. `build` stays required
from integration 15368, and `do_not_enforce_on_create` stays `false`. In the UI: Settings → Rules →
Rulesets → main → "Require status checks to pass" → tick "Require branches to be up to date before
merging".

Verify read-only:

```bash
gh api repos/thefundamentaltheor3m/SphereCeti/rules/branches/main \
  --jq '.[] | select(.type=="required_status_checks") | .parameters'
# {"do_not_enforce_on_create":false,"required_status_checks":[{"context":"build","integration_id":15368}],
#  "strict_required_status_checks_policy":true}
gh api repos/thefundamentaltheor3m/SphereCeti/rulesets/21449770 --jq '.enforcement, .updated_at'
# active, and a fresh timestamp
gh api repos/thefundamentaltheor3m/SphereCeti/pulls/<N> --jq .mergeable_state
# "behind" for an open PR whose head lacks current main
```

`sphereceti merge-doctor --json` then lists `PR branches must be up to date with main before merging`
under `protection.verified`, and the strict item leaves `protection.missing`.
`protection.tested_tree_enforced` becomes `true` only once `checks_app_id` is set by the flips below.

## 2. Activation flips (one tiny PR)

**Workflow.** `.github/workflows/merge-controller.yml` and its packaged copy
`tools/ci/merge-controller.yml` change identically, because `merge-doctor` requires them to be
byte-identical. The lines are marked `ACTIVATION` in the file:

```diff
-          CONTROLLER: doctor
+          CONTROLLER: apply
-  contents: read
-  pull-requests: read
-  actions: read
-  issues: read
+  contents: write
+  pull-requests: write
+  actions: write
+  issues: write
```

| Permission | Why |
|---|---|
| `contents: write` and `pull-requests: write` | The head-pinned squash merge |
| `actions: write` | Dispatching a trusted refresh of `pr-build.yml` |
| `issues: write` | Opening the halt issue after an unexpected refusal |

**Controller policy.** `policy/merge-controller.toml`:

```diff
-workflow_id = 0
+workflow_id = 428151597
-checks_app_id = 0
+checks_app_id = 15368
```

`428151597` is the ID GitHub reported for `.github/workflows/merge-controller.yml` in probe runs
45238596085 and 45274799597. `15368` is the GitHub Actions App that `build` is bound to.

**Stop switch.** `policy/automation.toml`:

```diff
-merging = false
+merging = true
```

The schedule stays commented out in this PR. A test in `tests/test_activation_prep.py` applies
exactly these workflow flips and checks that nothing else changes.

**Expected:** a manual dispatch with no inputs runs `merge-control --apply --sweep`. Its `setup`
shows `ready: true`, `executor.token_view: "never"`, `protection.tested_tree_enforced: true`, and no
`halt`. Each PR gets an action, and nothing merges unless a PR fully qualifies.

## 3. Live race probe

Run [the live procedure](merge-controller.md#tested-tree-through-the-merge): dispatch the controller
on main with `pr=<B>` and `probe=race`. B must fully qualify. While the run holds, a maintainer
squash-merges a disposable PR A.

The run log prints, in order:

```text
probe race: final check passed: merge #B head <H>; main <M0>; tested tree <tree>
probe race: waiting up to 20 minutes for main to move
probe race: main moved to <M1>; sending the head-pinned squash PUT
probe race: PROOF: GitHub refused the stale combination {"status": "405", "message": "..."}
```

The JSON shows `probe.proof: true` and `outcome: "rejected_stale"`. B stays open, and `main_after`
is `M1`. If main does not move within 20 minutes, the result is `probe_timeout` and no PUT is sent.
Any other outcome is not a proof: keep the schedule off, investigate, and repeat. A
`rejected_unexpected` also opens a halt issue, which a maintainer acknowledges with
`/sphereceti acknowledge-halt` after investigating.

## 4. Schedule (one tiny PR)

Only after the probe's proof:

```diff
-  # schedule:
-  #   - cron: '17 * * * *'
+  schedule:
+    - cron: '17 * * * *'
```

The same change goes in both workflow copies. The probe stays impossible in scheduled runs: the
controller refuses `--probe` unless the API reports a `workflow_dispatch` run.

## Stopping

Set `merging = false` to stop new attempts at the next run. To stop at once, also disable the
workflow in the Actions tab. An unexpected refusal halts runs by itself, until a maintainer
acknowledges it.
