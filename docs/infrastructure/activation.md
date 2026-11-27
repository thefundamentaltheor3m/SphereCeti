# Activating the merge controller

Activation is a short, ordered sequence: one administrator setting, then two tiny reviewed PRs.
This page lists the exact lines, the order, and what each step should print. Background:
[merge controller](merge-controller.md).

## Status (2026-11-25)

- [x] Carry-over to "Update branch" heads is merged (#156).
- [x] Strict up-to-date checks are on for ruleset 21449770 (`strict_required_status_checks_policy:
  true`, `build` required), verified read-only.
- [x] The activation flips are merged (this PR): `CONTROLLER: apply`, write permissions,
  `workflow_id = 428151597`, `checks_app_id = 15368`, `merging = true`, `approving = true`, and all
  seven authorized reviewers in `approving_reviewers` (each opted in on 2026-11-25). The schedule
  stays commented out: only a maintainer's manual `workflow_dispatch` can merge.
- [ ] **Next: the live race probe** ([procedure](#3-live-race-probe)), dispatched with
  `probe=race`.
- [ ] **Then:** the schedule PR ([schedule](#4-schedule-one-tiny-pr)).

Until the probe has proven GitHub's refusal, do not dispatch the controller without `pr`. A
dispatch without `pr` is a live sweep that merges every fully qualifying PR.

## Order of operations

1. **Carry-over is merged.** Reviews and formal approvals carry over to "Update branch" heads
   (decision 2 on #100). Without it, strict up-to-date checks would invalidate every review on each
   update.
2. **An administrator turns strict on** ([ruleset change](#1-ruleset-change-administrator)).
3. **The activation flips PR lands** ([flips](#2-activation-flips-one-tiny-pr)), with the schedule
   still commented out. Only a maintainer's manual dispatch can now merge.
4. **The live race probe passes** ([probe](#3-live-race-probe)).
5. **The schedule PR lands** ([schedule](#4-schedule-one-tiny-pr)). Unattended merging is on.

Merging also needs the policy prerequisites, which have landed: a nonempty `mathematical_paths`
(#149) and opted-in maintainers in `approving_reviewers` (#155, and this activation).

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

The probe shows, with the real executor and its job token, that GitHub refuses to land a stale
combination. The controller finishes its final check, main then moves, and its head-pinned PUT
must be refused. The full rationale is in [merge controller](merge-controller.md#tested-tree-through-the-merge).

**0. Readiness check (merges nothing).** Dispatch the controller for a human-route PR, which can
never be an automatic merge (for example a docs PR):

```bash
gh workflow run merge-controller.yml --ref main -f pr=<human-route PR>
gh run list --workflow merge-controller.yml --limit 1     # then: gh run view <id> --log
```

The JSON `setup` must show `ready: true`, `merging_requested: true` and `executor_verified: true`,
with `executor.token_view: "never"` and `executor.token.installation: true`. It must also show
`protection.tested_tree_enforced: true` and no `halt`. The PR's result is `blocked` (human route).
Anything else is fixed before going on.

**1. Pick PR B, the candidate.** B must fully qualify:
- it changes only library modules under `SphereCeti/`, any topic (not `SphereCeti.lean` or the
  protected `SphereCeti/Basic.lean`, `Pinned.lean` and `Suggested.lean`);
- it has a current, complete 10/10 official review by an authorized reviewer other than its author;
- it has the formal APPROVE of an opted-in maintainer (all authorized reviewers are opted in);
- its trusted run (`trusted-build`, `trusted-scope`, `trusted-merge`) attests current main;
- its head contains current main.

Find one, read-only:

```bash
sphereceti reviews                                  # open PRs with their review state
sphereceti auto-approve-check <N> --json            # must say "would_approve": true
sphereceti merge-control --pr <N> --json            # preview: results[0].state == "would_merge"
```

If B lacks the review or the approval, an opted-in maintainer who is not B's author runs
`sphereceti review <N>`. An all-green review posts the record and submits the APPROVE; do not pass
`--no-approve`, which opts out for that run. If B is behind main, use "Update branch": the review
and approval carry over (decision 2), and the new head gets a fresh trusted run. Re-run the two
checks until `would_merge`.

**2. Prepare PR A, the main mover.** Use any human-route PR, for example a one-line docs fix, that a
maintainer can squash-merge at once: approved, `build` passing, and up to date with main. A must not
touch any file B changes.

**3. Dispatch the probe for B:**

```bash
gh workflow run merge-controller.yml --ref main -f pr=<B> -f probe=race
gh run watch "$(gh run list --workflow merge-controller.yml --limit 1 --json databaseId --jq '.[0].databaseId')"
```

**4. While it holds, merge A.** When the log prints
`probe race: waiting up to 20 minutes for main to move`, a maintainer squash-merges A
(`gh pr merge <A> --squash`, or the button). The probe sees main move and sends B's head-pinned PUT.

**5. Read the proof.** The log ends:

```text
probe race: final check passed: merge #<B> head <H>; main <M0>; tested tree <tree>
probe race: waiting up to 20 minutes for main to move
probe race: main moved to <M1>; sending the head-pinned squash PUT
probe race: PROOF: GitHub refused the stale combination {"status": "405", "message": "..."}
```

The JSON shows `probe.proof: true` and `probe.outcome: "rejected_stale"`, the refusal's status and
message, and `results[0].main_after` equal to `M1`. Confirm read-only:

```bash
gh api repos/thefundamentaltheor3m/SphereCeti/pulls/<B> --jq '.state, .merged'   # open, false
gh api repos/thefundamentaltheor3m/SphereCeti/commits/main --jq .sha              # A's merge, M1
```

**Not a proof:**
- `probe_timeout`: main did not move within 20 minutes, and no PUT was sent. Repeat.
- B merged: enforcement is absent. Revert B, keep the schedule off, and investigate.
- `rejected_unexpected` (for example a 403, or a missing approval): the race was not tested. This
  also opens a halt issue; after fixing the cause, a maintainer comments
  `/sphereceti acknowledge-halt` on it, and the probe is repeated.
- A refusal at step 0 or before the hold (`refused`, `blocked`, `needs_update`): B did not qualify.

**6. Afterwards** B is behind main. "Update branch" carries its review and approval over, and once
its fresh trusted run passes, a manual `pr=<B>` dispatch (no probe) merges it. Then land the
schedule PR.

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
