# Serialized merge controller and activation diagnostics

This layer adds action and activation diagnostics to the shared merge observation contract.
It adds no Python or Lean dependencies. The controller remains disabled and must not be used
to land this native GitHub stack; bootstrap landing uses GitHub’s stack-aware interface.

**Adapted from [TauCetiReview contributors](https://github.com/TauCetiProject/TauCetiReview),
Apache-2.0, at [afb424e](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b):**
[`.github/workflows/merge-only.yml`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/.github/workflows/merge-only.yml)
and [`.github/workflows/merge-sweep.yml`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/.github/workflows/merge-sweep.yml)
supply the separate credential phase, head-conditioned mutation, shared sweep decision and
lifecycle reconciliation design. SphereCeti retains #15's stricter authenticated evidence and
uses direct, serialized squash merges with server protection. Upstream queue bypass, pin repair,
branch updates, queue clearing, labels, and App grants are not ported. Original #9 sources remain
unchanged; exact paths and adaptations are in `tools/upstream-lock.toml`.

## Commands

```bash
sphereceti merge-doctor --json
sphereceti merge-doctor --executor --json     # only meaningful in the approved workflow run
sphereceti merge-control --pr 15 --json       # preview
sphereceti merge-control --sweep --json       # preview; same policy gate
```

Optional `--source-repo`, `--dependencies-dir` and `--cache-dir` reuse source objects as in
[#15's observation guide](merge-observation.md). Authority always comes from immutable remote
`main`, never the candidate or cwd. Diagnostics and previews may write a source cache and local
lock; they do not change PRs, branches, policies, or repository settings. `merge-doctor` reports
concrete blockers and whether the supported setup profile is ready. Its `reasons` list every
blocker. `protection` lists the server rules it verified, recommended `findings`, and the missing
items. `automatic_path` lists what the executor verifies itself for each PR and what is
unconfigured, and `executor` reports the run and job-token checks
([below](#reading-the-executor-output)). Successful diagnostics, including a disabled result,
exit 0; unavailable/invalid data and unconfirmed write outcomes exit 2.

`--apply` is explicit and requires both ready setup and the verified executor. The shipped `merging`
switch is false, the mathematical allowlist and `approving_reviewers` are empty, and controller IDs are zero.
The CLI cannot configure those settings. Library proof PRs currently require human merging. The
workflow is installed read-only ([first run](#the-read-only-first-run)); no live merge, secret,
bot account or branch-rule change is part of it.

## Activation profile

The setup reader selects these files from the exact current-main Git tree:

- `sphereceti.toml`: identity, proof destination, and approved roadmap state.
- `policy/automation.toml`: the **single global merging stop switch**, nonempty approved paths and
  authorized review identities. Single-PR, scheduled sweep, and manual sweep routes all use it. Its
  optional `approving_reviewers` (absent means empty) lists the opted-in maintainers whose formal
  approval qualifies. Each entry is a unique `"user:ID"` that must also be in `authorized_reviewers`.
  The same list governs whose all-green `sphereceti review` submits that approval.
- `policy/merge-checks.toml`: #15's trusted candidate workflow and status-producer IDs.
- `policy/merge-controller.toml`: the controller workflow ID, the required-check integration ID,
  and the squash method. Zero IDs mean unconfigured. No merge identity is recorded: the executor is
  the workflow's job token, verified at run time.

Installed controller code and resources must match approved main. The installed
`.github/workflows/merge-controller.yml` must match the [packaged copy](../../tools/ci/merge-controller.yml)
byte-for-byte. A changed policy or workflow is reviewed as code; an operator config or a
feature-branch copy cannot supply it.

`merge-doctor` reads the branch summary (`branches/main`), the effective rules for `main`, and the
repository's ruleset list on every run, including while the controller IDs are zero. Exactly one
of the two server profiles below must apply. Classic protection together with rulesets, or neither,
is reported as unsupported.

### Ruleset profile (SphereCeti today)

SphereCeti `main` is protected by repository ruleset `21449770`; classic protection is disabled.
The diagnostic fails closed on ambiguity. Malformed or truncated paginated inventories, or a ruleset
detail that disagrees with the effective rules, are errors (exit 2). The following are reported as
missing items:

- **Inventory:** exactly one ruleset may exist, and it must supply every effective rule for `main`.
  It must be an active (not `evaluate` or `disabled`) branch ruleset owned by this repository.
- **Rule types:** only `deletion`, `non_fast_forward`, `pull_request` and `required_status_checks`
  are supported. Others, such as `update` or `merge_queue`, need a separately reviewed profile.
  Unknown parameters of the supported rules also fail closed.
- **History:** deletion and non-fast-forward rules must both be present.
- **Review:** the pull-request rule must require at least one approving review and allow squash
  merges. `dismiss_stale_reviews_on_push` and `require_last_push_approval` are reported as
  recommended findings but are not yet required. Thread resolution is reported when required.
- **Checks:** at least one status check is required for every PR. Each required check must be bound
  to an integration ID equal to `checks_app_id` (the live `build` check is bound to the GitHub
  Actions App, 15368). Up-to-date branches (`strict_required_status_checks_policy`) are required,
  because GitHub must reject a merge after `main` moves past the base the executor verified.
  Maintainers can still update a branch and merge.
- **Human route:** the diagnostic evaluates the rules against human-reviewed policy and dependency
  PRs. These PRs have one human approval and a passing `build`, while `trusted-scope` reports
  `human_review` (and dependency changes also stop `trusted-build`). If the ruleset would block
  them, that is reported as missing. `trusted-build` and `trusted-scope` therefore must **not** be
  required for every PR. The executor verifies them for each PR instead.
- **Bypass:** when `bypass_actors` is visible, only repository admin (5) and maintain (2) roles and
  organization admins may bypass, for maintainers. Any other actor (write or custom roles, teams,
  Apps including GitHub Actions, deploy keys) is rejected. GitHub shows the list only to readers
  with administration access, and the job token never has that, so an invisible list is a finding.
  What decides for the executor is the job token's own `current_user_can_bypass`, a blocker of the
  automatic path (see [the executor](#identity-model-option-a)).

Every PR needs GitHub's formal approval, enforced by the ruleset. Under option A that approval is a
maintainer's own: an opted-in maintainer's all-green `sphereceti review` submits an APPROVE review
under their account (built separately). The controller merges only after it. Protected changes still
go to humans through the ordinary route.

### Merge decision

For each candidate the controller runs the [auto-approval decision](merge-observation.md#auto-approval-decision)
under the approved policy; a hypothetical allowlist never counts. It then reads the PR's reviews.
A PR is eligible only when every item holds:

- **Paths:** every changed path is an eligible proof path under `mathematical_paths`, or an allowed
  library-root import.
- **Trusted checks:** `trusted-build` succeeded and `trusted-scope` is `mathematical`, from the
  approved producer (`policy/merge-checks.toml`). Both come from one exact run attempt bound to the
  head. The run's attested tooling is current approved `main`.
- **Compiled audit:** that run's candidate job ran the approved audit on the exact head.
- **Official review:** an authorized reviewer's complete, non-advisory record for the exact head is
  accepted. At least one accepted publisher is not the PR author.
- **Up to date:** the PR is open, not draft, based on current `main` and not conflicting.
- **Formal approval:** an opted-in maintainer (`approving_reviewers`), not the PR author, has a latest review
  of APPROVE on the exact head (`commit_id`). The maintainer has a maintainer association. No
  reviewer has an outstanding change request. Comments do not change a reviewer's state.

An all-green record without the formal review, as `sphereceti review --no-approve` posts it, leaves
the PR open with `no qualifying approval`. A formal approval without the decision's evidence does
not merge either. An eligible PR gets exactly one squash-merge PUT whose `sha` is the reviewed head.

### Classic profile

The original classic profile is unchanged. It is read only once all controller IDs are
configured, because its endpoint needs administrative access. It requires both trusted contexts for
every PR, so it does not fit SphereCeti's human route for protected changes.

- Classic protection for canonical `main`, with strict up-to-date requirements and both
  `trusted-build` and `trusted-scope` required from the configured App ID. Names alone, missing App
  bindings, or an any-App binding do not pass.
- Protection applies to admins; force pushes and deletions are explicitly disabled. At least one
  server-enforced PR approval is required, stale approvals are dismissed, and no user/team/App
  PR-review bypass allowance is present. #11's comment records are additional evidence, not a
  substitute for this GitHub review requirement.

### Both profiles

- The executor is the approved workflow's job token ([identity model](#identity-model-option-a)).
  The job-token bypass check is implemented for the ruleset profile only.
- Squash merging is enabled for the repository. The controller neither bypasses rules nor drains a
  merge queue.

### Remaining activation prerequisites for SphereCeti

Besides the policy switches (`merging`, `mathematical_paths`), `merge-doctor` reports these items
as missing:

- `policy/merge-controller.toml` has `workflow_id` and `checks_app_id` at zero, and
  `policy/automation.toml` has no `approving_reviewers`.
- The executor has not been verified by a run of the installed workflow. The first
  `workflow_dispatch` run reports its `workflow_id` and whether the job token can bypass the ruleset.
- The ruleset must require up-to-date branches.
- `checks_app_id` must name the integration that `build` is bound to.

Approval-dismissal and last-push settings are recommendations. `merging` stays `false` until a
separate policy change.

The implementation uses GitHub's [branch-protection API](https://docs.github.com/en/rest/branches/branch-protection),
[workflow-run API](https://docs.github.com/en/rest/actions/workflow-runs#get-a-workflow-run),
[pull-request reviews](https://docs.github.com/en/rest/pulls/reviews#list-reviews-for-a-pull-request),
[branch-rules API](https://docs.github.com/en/rest/repos/rules#get-rules-for-a-branch),
[repository rulesets](https://docs.github.com/en/rest/repos/rules#get-a-repository-ruleset), and
[head-conditioned merge API](https://docs.github.com/en/rest/pulls/pulls#merge-a-pull-request).
Missing API permissions or unsupported metadata are errors, not assumed readiness.

## Serialized executor and credentials

### Identity model (option A)

There is no bot or machine-user account. The merge is performed by the workflow on `main`, using
the job's own `GITHUB_TOKEN`, an installation token of the GitHub Actions App acting as
`github-actions[bot]`. Its login proves nothing, because every workflow in the repository shares
it. `merge-doctor --executor` and every `--apply` therefore verify, in the actual run:

- the environment: `GITHUB_WORKFLOW_REF` names `.github/workflows/merge-controller.yml` on
  `refs/heads/main`. `GITHUB_WORKFLOW_SHA` and `GITHUB_SHA` equal approved `main` read from the API.
  The ref, repository and event (`workflow_dispatch` or `schedule`) also match.
- the live run (`GITHUB_RUN_ID`/`GITHUB_RUN_ATTEMPT`): it is in progress for that path, head and
  repository, and its `workflow_id` equals `policy/merge-controller.toml`.
- the credential: the token handed to the writer is an installation token (`ghs_`). Another
  credential is refused and never sent anywhere.
- the token's own view of the effective ruleset: `current_user_can_bypass` must be `"never"`.
  GitHub resolves that value for the token, so nothing is inferred from bypass lists. If GitHub
  omits the field or the token cannot read the ruleset, that is the blocker and merging stays
  impossible. Nothing is guessed.

The approved workflow's bytes must equal the packaged copy on `main`, and that file passes
`${{ github.token }}`. These are consistency checks, not cryptographic attestation. Every workflow
in the repository gets an installation token, and code running elsewhere could set these
environment variables. What confines the merge is that write permission is granted only by
reviewed workflow files on `main`, and the job token can never bypass the ruleset. Without bypass,
GitHub still enforces the formal approval, required checks and up-to-date rule on every merge.

The writer receives the token privately; it is removed from the environment before any Git or
reader child process runs, and its subprocess environment is minimal. It permits only a GET of its
own ruleset view and the squash-merge PUT with an exact head SHA. It never calls `user`, because an
installation token has no user. Reads use the same job token through the GET-only reader. No API
response or error message includes token values.

### The read-only first run

[`.github/workflows/merge-controller.yml`](../../.github/workflows/merge-controller.yml) is installed
on `main`. It has `workflow_dispatch` only, and its `schedule` is commented out. Its permissions are
`contents: read` and `actions: read`. The job runs only on `refs/heads/main` and checks out `main`'s
exact SHA with credentials disabled. It never checks out, builds or executes PR code, and it calls
no provider. While `merging = false`, the job only runs `merge-doctor --executor --json` and prints
the result. No merge command runs, and the token could not merge anyway. Its concurrency group is
`sphereceti-merge-main` without cancellation, and it runs at most 30 minutes.

Activation is a separate reviewed change. It records `workflow_id`, `checks_app_id` and `approving_reviewers`,
grants `contents: write` and `pull-requests: write`, and replaces the step with
`merge-control --apply` (a PR or a sweep). It also enables the schedule and sets `merging = true`.

### Reading the executor output

The first manual run's JSON should show:

- `executor.context: "github_actions"`, and `executor.run` with the run ID, attempt, path, head
  and **`workflow_id`**. Because policy still has `workflow_id = 0`, `executor.missing` contains
  `workflow_id is not configured; this run reports workflow_id N`; that `N` is the value to record.
- `executor.token_view`: `"never"` is what activation needs. `"omitted"` (GitHub gave no field for
  the installation token) and `"unreadable"` are blockers that keep merging impossible.
  `"always"`, `"pull_requests_only"` or `"exempt"` mean the executor could bypass the ruleset.
- Any environment or run mismatch, each named with the observed and expected value.
- `protection`: the same ruleset verification as a local run. `ready: false` with the policy items
  listed in `automatic_path.missing`.

A local `merge-doctor` (no `--executor`) reports `executor.context: "local"`. It lists every check
that needs the job token under `requires_job_token`. Under `stand_in` it shows the local token's
own `current_user_can_bypass`, for information only; it counts for nothing.

A local nonblocking file lock also prevents overlapping preparation in one cache; it is not a
distributed lock and cannot replace workflow serialization.

## Revalidation and lifecycle

Both single-PR and sweep execution call `merge_controller.reconcile` and the
[merge decision](#merge-decision), which reuses #15's shared observer.
Disabled setup is checked before enumerating the sweep. The controller lists complete paginated
open-main PRs, rejects duplicates or excessive inventories, and refreshes the listing. It reads
current PR state again for each candidate. Already merged/closed PRs are no-ops; drafts and existing
human auto-merge requests are left alone. The shared observer also rejects an auto-merge request
created while a candidate is being assessed.

For an eligible candidate in apply mode, the controller obtains setup and full observation twice.
Changed head, integration base, review/contest, formal approval, policy, protection, job-token
view, workflow, or check evidence requires a new run. It refreshes all consumed observer and activation API responses
immediately before the PUT. The request's `sha` binds it to the exact reviewed head; strict server
checks and the non-bypassing job token protect against a base advancement between the last read
and the request.
GitHub has no atomic transaction spanning all these reads and the merge. An emergency switch change
cannot recall an already in-flight merge; credential revocation/workflow shutdown is the operational
stop for that boundary. Administrators remain responsible for preserving server protection.

There is at most **one merge request per invocation**, even in a sweep. After any request, the
controller rereads the PR and verifies the observed head and merge commit. A matching success
response is `merged`; an ambiguous response followed by a matching merged PR is `merged_observed`
without claiming who performed it. Otherwise the outcome is `unconfirmed`. There is no blind PUT
retry and no next candidate using the old base. The next scheduled run starts with fresh main.

GitHub is the durable lifecycle authority. Restart or duplicate events inspect current PR state;
local plans/receipts are never replayed as permission. No state branch, archive, persistent queue,
auto-rebase, label, notification, or claim system is required for this controller.

## Review and validation

Review #15 and #51 first, then this layer: activation/profile checks, job-token executor
verification, the merge decision with its formal approval, the narrow writer, the read-only
workflow, the shared observer's human-auto-merge guard, and regression tests.

```bash
python3 -B -m unittest discover -s tests -p 'test_merge_controller.py' -v
uv lock --check
uv build
python3 scripts/test_package.py
```

Tests exercise stop switches before both entry points, writer-token isolation, required check
producers, the job token accepted only with `current_user_can_bypass: "never"` (a missing or
unreadable view is the blocker), wrong workflow refs/SHAs/runs, the formal-approval rules, an
all-green record without a formal approval left open, exactly one head-pinned PUT for an approved
eligible PR (with `merging = true` only in a fixture), the read-only installed workflow, bypass
rejection, the live ruleset shape (`tests/ruleset_fixture.py`) and its
human route, multiple, inactive or foreign rulesets, missing rules, unknown rule types, truncated
inventories, the classic path, concurrent head/base/policy changes, review revocation, final
refresh failure, restart, duplicate events, human-managed PRs, ambiguous responses, and lock
contention. Installed wheel/source tests run diagnostics and disabled apply/sweep paths from a
foreign cwd against fake GitHub. No test invokes a real merge or provider.

See [tracking issue #23](https://github.com/thefundamentaltheor3m/SphereCeti/issues/23) for review order, prerequisites and landing status. All infrastructure lands before roadmap #1.