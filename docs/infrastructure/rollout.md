# Contributor CLI and official-worker rehearsal

Contributors run reviews with their own provider credentials and can create PRs with any
authoring tool. Official workers decide which review records count and enforce the repository's
merge policy. Only the official merge workflow on `main` holds a merge-capable credential, its own job token.
Installing the CLI, producing a green review, or publishing a comment grants no merge authority.

Main provides local review, explicit review publication and guarded review workers. The independent
`infra/review-readiness` branch repairs review scheduling and policy fixtures;
`infra/authoring-handoff` adds a provider-free `author plan` command for external tools. Those
features must land before their respective rehearsal steps below. The smoke runner itself can
land independently on main. Production authoring and production review/build/merge adapters remain
separate work. All repository automation switches remain off.

## 1. Repeatable local smoke

From the checkout under review, on Linux with `/proc` and pidfd support:

```bash
python3 scripts/smoke_cli.py
```

This runs offline CLI diagnostics and fixture regressions covering review dispatch, publication,
identity, stale evidence, bounded loops and official merge refusal/revalidation. When the readiness
or authoring module is present, its focused regressions are included too; a missing corresponding
test file fails the inventory check. The selected test modules appear in the JSON command record.
Providers and GitHub are fakes. A new temporary directory retains `report.json` and each stage's
log; `--output /path/to/new-directory` selects a durable location. A failed stage fails the smoke.
The JSON records which optional stages were not run and explicitly disclaims live activation.

For distribution testing and the real read-only GitHub query:

```bash
python3 scripts/smoke_cli.py --package --online
```

`--package` requires `uv`, checks the lock, builds fresh wheel/source distributions, and installs
both into temporary environments outside the checkout. Build dependencies may be downloaded.
`--online` requires `gh` authentication and only reads the PR queue. Neither option runs a live
reviewer or publishes anything. Each stage has a 600-second deadline by default. A private Linux
supervisor stops and reaps its descendants on timeout, including detached reviewer processes;
unsupported cleanup facilities fail the check. This is a smoke test, not a substitute for the
complete CI suite.

On a host with the approved sandbox installation:

```bash
python3 scripts/smoke_cli.py --sandbox --toolchain "$(lean --print-prefix)"
```

A different bubblewrap binary or unavailable isolation fails this stage; do not weaken the pin.
Hosted CI also runs `scripts/test_trusted_build_smoke.py` in its disposable checkout. That script
**moves and consumes `.lake/packages`** and must not be run in a shared development checkout.

## 2. Land readiness changes before activation

The implementation and policy used for a live official review must be approved on canonical
`main`, and the installed CLI/resources must match that revision. A prospective branch, a local
policy override, and successful fixture tests do not establish this authority. Land the intended
dependency migration and readiness changes through the normal human review route first:

1. Land `deps/lean-4.36-rc2-tauceti-83769e4` as its own dependency PR, preserving main's scaffold
   profile and admission policy. Its ordinary CI supplies validation; changed Lake configuration
   deliberately requires human dependency review.
2. Rebase PR #1 onto the resulting main. Do not fold unrelated infrastructure into its review.
3. Land the independent infrastructure PRs and reverify their tests against the approved pins.
   After review activation lands, reinstall exactly that approved main version for the canary.

The readiness branch distinguishes all-check CI (`ci`) from advisory review readiness (`review_ci`).
A failed `trusted-scope` can describe a passing build that requires human merging. The worker
permits review only when this is the sole failure, all other observed checks pass, and the shared
provenance assessor verifies the exact approved producer, workflow, run attempt, head, base and
successful build/status jobs. It retains the failed scope status; automatic merge eligibility is
unchanged. Missing, unknown, pending, truncated or untrusted evidence does not earn the exception.
Legacy survey snapshots retain their conservative all-check behavior. Saved v2 snapshots are not
re-authenticated on replay: their `review_ci`, like v1's `ci`, is caller-supplied advisory scheduling
input. Execution takes a fresh live survey instead.

Keep the prototype reviewable in three changes: worker readiness and policy-fixture repairs;
the repeatable smoke runner and installation checks; then the local authoring handoff. None of
these changes is the tiny live canary, and none enables repository automation.

The producer identities in `policy/merge-checks.toml` therefore need real, reviewed values before
the worker can use the exception. The shipped zero/empty values intentionally cannot pass. These
are identities, not permissions to merge. Disabled-policy tests use explicit fixtures so that
future activation does not require deleting the tests that prove an off switch prevents work.

Review activation is a separate reviewed change:

- Direct contributor publication requires `posting = true` on approved `main`.
- Official review workers also require `review_generation = true` and their immutable GitHub user
  identity in `authorized_reviewers`. The current worker adapter supports user identities.
- Contributor comments outside that allowlist remain advisory. Do not authorize all contributors
  merely to let them use the CLI. The official reviewer can independently review the same PR.
- Keep `authoring`, `reporting`, and `merging` off for the first review canary. Do not install a
  scheduler or supply a merge credential to a contributor/review process.
- Rebuild/reinstall the approved version after the activation change lands. Use diagnostics to
  distinguish implemented capability and requested policy from verified live readiness.

Read-only observations on 2026-11-12 found the active candidate workflow ID `358051984` at
`.github/workflows/pr-build.yml` and trusted statuses published by Bot ID `41898282`. These are
candidate values for the reviewed producer configuration; reverify them at activation. Bot
`41898282` is the generic GitHub Actions bot, so its ID alone does not authenticate this project:
the exact repository, workflow, run attempt, head/base and publication binding are essential. On
PR #1 head `39d382bc40268ce7f620ea001c262c77b1d98abf`, both trusted statuses were failures in
[run 43255550365, attempt 1](https://github.com/thefundamentaltheor3m/SphereCeti/actions/runs/43255550365/attempts/1).
The candidate job stops with `Configuration differs from approved tooling; human dependency review
required`. This is the intended gate for the pin change, not a failing mathematical build. The
ordinary build, source-rebuild-check, python-package and docs-cache checks passed on that head,
as verified in the 2026-11-17 review. The readiness exception still requires a successful trusted
build, so land the dependency PR and rebase PR #1 before the live canary.

## 3. One tiny live review PR

Use a new PR from approved current `main`, with one documentation correction and no policy,
workflow, dependency or mathematical changes. A suitable candidate is the stale
`roadmap_approved = false` paragraph in `docs/infrastructure/worker.md` after the roadmap profile
has landed. Leave that correction separate from the readiness and activation changes.

Record the repository, PR number, head SHA, approved tooling SHA, dependency digest, provider/model,
review budget and operator identities before the run. Start with evidence preparation:

```bash
# PR is the chosen canary number. These commands use the installed approved CLI.
sphereceti review "$PR" --dry-run --json
```

Choose one supported provider and an explicit supported model. For Codex, a complete contributor
pass is:

```bash
sphereceti review "$PR" --mode manual --provider codex \
  --codex-model "$REVIEW_MODEL" --budget-usd "$REVIEW_BUDGET" \
  --max-call-cost "$REVIEW_RESERVATION" --post --json
sphereceti review "$PR" --read-records --json
```

Choose the variables deliberately; these are not default spend authorizations. All ten rubrics
remain selected. `manual` requests the full picture even if an early rubric blocks the change.
The daily budget is shared with earlier runs in the same storage, and reservations are estimates,
not a provider-enforced billing cap. Set a provider-side limit if a strict financial ceiling is
needed. A partial/error review is a useful failure signal, never a complete review certificate.

Then exercise the authorized worker, using its own credentials, one explicit target and the
recorded head SHA. `--expect-head` makes the run refuse, with no model call or GitHub write, if
the PR has advanced since the preview that was authorized
([details](worker-execution.md#binding-a-run-to-the-authorized-head)):

```bash
sphereceti worker run --pr "$PR" --expect-head "$PR_HEAD" --json
sphereceti worker run --pr "$PR" --expect-head "$PR_HEAD" --loop --max-rounds 1 --execute \
  --worker-id canary --provider codex --codex-model "$REVIEW_MODEL" \
  --budget-usd "$WORKER_BUDGET" --max-call-cost "$REVIEW_RESERVATION" --post-review --json
```

`--codex-model` pins the model for every rubric, as for `review` (#35); without it the worker
uses the engine's default model and fallback. Its normal review can stop early on a blocking rubric. Require a complete
ten-rubric result for the positive rehearsal; stop and examine an incomplete result. Run a second
explicit one-round invocation to confirm an accepted current review causes an idle result without
new provider work. Do not widen the PR target or start a persistent loop.

Acceptance evidence is the exact-head review record, all ten completed rubrics, confirmed API
publication/readback, the publisher's immutable identity, the official reader's interpretation,
worker lease release and budget accounting. A second contributor's advisory result must not erase
an official blocker or acquire authority. Head changes must stale the old evidence. Cover adverse
cases with fixtures first; a deliberately changed live head needs a new explicitly budgeted run.

Use `merge-observe`/controller preview to confirm that this docs PR still requires human merging.
Human-merge it through the ordinary route once review and CI are satisfactory. This proves the
review pipeline and the correct merge refusal; it does not prove a successful automatic merge.

## 4. Official automatic-merge canary

The existing controller is for canonical **SphereCeti**, not Sphere-Packing-Lean, and SphereCeti's
merge policy has no eligible mathematical change class. A production canary first needs the
production profile, approved source/build adapter, genuine allowed change class, configured check
producers and the [supported server protection/credential setup](merge-controller.md).

The 2026-11-12 read-only setup check found effective repository ruleset `21449770` protecting
SphereCeti `main` with deletion, non-fast-forward, PR and required-check rules. The classic
branch-protection lookup returned HTTP 404, which by itself cannot distinguish absent protection
from insufficient API access. `branches/main` reports that classic protection is disabled.
`merge-doctor` verifies this ruleset profile and lists the remaining gaps: up-to-date branches,
`checks_app_id`, `workflow_id`, opted-in `approving_reviewers`, and the unverified executor. The trusted
contexts stay unrequired for all PRs, so protected PRs keep their human route. See [the ruleset profile](merge-controller.md#ruleset-profile-sphereceti-today).
No protection setting was changed during the prototype or this diagnostic work.

The executor follows [option A](merge-controller.md#identity-model-option-a). There is no bot or
machine user. The workflow on `main` merges with its own job token, and that token must report
`current_user_can_bypass: "never"` on the ruleset. The formal GitHub approval comes from an
opted-in maintainer's own APPROVE review, submitted by their all-green `sphereceti review` (built
separately). The controller requires that approval in addition to the auto-approval decision.

The workflow is installed read-only. Its first step towards the canary is a manual
`workflow_dispatch` run on `main`. That run verifies the run and the job token and prints the
`workflow_id` to record. It also prints whether GitHub reports `current_user_can_bypass` for the
installation token; see [reading the output](merge-controller.md#reading-the-executor-output).
An omitted or unreadable view is a blocker: merging stays impossible and nothing is guessed.

There is no persistent PR/head canary allowlist today. `--pr` narrows one invocation. The installed
workflow's schedule is commented out, and activation would enable hourly sweeps. Before enabling merging, implement a
reviewed canary restriction binding repository, PR, head and expiry that is checked by every entry
point, or a separately reviewed manual-only activation profile. Keep sweeps disabled throughout
the canary. A changed head requires a renewed reviewed authorization, not an implicit retry.

The ordinary contributor installation never receives a merge credential. The official executor
rechecks trusted build/scope, authorized review records, the formal approval, current head/base,
protection and its own run and job-token view before one head-conditioned merge request. GitHub's
native approval requirement remains separate from automated review comments: an all-green record
without the maintainer's APPROVE review leaves the PR open. The approved workflow and its job token
supply the executor's authority.

The positive canary must show one permitted PR merged, another PR/head refused, duplicate execution
becoming a no-op, and the stop condition preventing new attempts. Fixtures already cover several of
these controller boundaries; a real successful merge is still required before claiming production
merge readiness. Turning the policy off cannot recall a request already in flight; disable or cancel
the workflow if that boundary must be interrupted. The job token expires with its job.

## 5. Optional authoring after the handoff

After the authoring branch lands, external authors can consume `author plan` without joining an official worker service.
An integrated `author run` remains a separate feature: an isolated writable production checkout,
explicit provider/model and finite budgets, exact task/source revisions, enforced patch scope,
validation, and a reviewable diff before explicit fork/PR publication. Repairs need their own bounded
round count. It must never alter repository policy or acquire merge authority. The production
adapter and its pin migration are prerequisites, not assumptions hidden in the CLI.

See [prototype validation](prototype-validation.md) for the historical combined-tree results and
the checks rerun after moving infrastructure off the roadmap branch.
