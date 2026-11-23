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
sphereceti merge-control --pr 15 --json       # preview
sphereceti merge-control --sweep --json       # preview; same policy gate
```

Optional `--source-repo`, `--dependencies-dir` and `--cache-dir` reuse source objects as in
[#15's observation guide](merge-observation.md). Authority always comes from immutable remote
`main`, never the candidate or cwd. Diagnostics and previews may write a source cache and local
lock; they do not change PRs, branches, policies, or repository settings. `merge-doctor` reports
concrete blockers and whether the supported setup profile is ready. Its `reasons` list every
blocker. `protection` lists the server rules it verified, recommended `findings`, and the missing
items, and `automatic_path` lists what the executor verifies itself and what is unconfigured. Successful diagnostics,
including a disabled result, exit 0; unavailable/invalid data and unconfirmed write outcomes exit 2.

`--apply` is explicit and requires both ready setup and the approved serialized executor. The
shipped `merging` switch is false, mathematical allowlist empty, and controller/producer IDs zero.
The CLI cannot configure those settings. Library proof PRs currently require human merging.
No activation, live merge, new secret, branch rule, or active controller workflow is part of this PR.

## Activation profile

The setup reader selects these files from the exact current-main Git tree:

- `sphereceti.toml`: identity, proof destination, and approved roadmap state.
- `policy/automation.toml`: the **single global merging stop switch**, nonempty approved paths and
  authorized review identities. Single-PR, scheduled sweep, and manual sweep routes all use it.
- `policy/merge-checks.toml`: #15's trusted candidate workflow and status-producer IDs.
- `policy/merge-controller.toml`: controller workflow ID, dedicated machine-user ID, required-check
  App ID, and the supported squash method. Zero IDs mean unconfigured.

Installed controller code and resources must match approved main. The installed workflow must
match the packaged [inactive template](../../tools/ci/merge-controller.yml) byte-for-byte. A changed
policy/template is reviewed as code; an operator config or a feature-branch copy cannot supply it.

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
- **Bypass:** the ruleset's `bypass_actors` must be visible. GitHub shows them only to readers with
  administration access, so a write-role reader is reported as unable to confirm them. Repository
  admin (5) and maintain (2) roles and organization admins may bypass, for maintainers; the merge
  identity holds the standard write role, which they do not cover. Any other actor (write or custom
  roles, teams, Apps, deploy keys) is rejected. With a configured identity, the merge token also
  reads the ruleset and must see `current_user_can_bypass: "never"`. GitHub resolves that
  value for the token's own roles, teams and Apps.

Every PR needs GitHub's formal approval. Today a maintainer approves each one, which is enough for
the first merge canary. In the intended end state, eligible proof PRs land without a human click.
A dedicated bot gives the formal GitHub approval, and a separate non-bypass merge worker merges.
Protected changes still go to humans. Policy does not yet name an approval bot, so `automatic_path`
reports that as an end-state gap rather than a readiness blocker.

The executor itself verifies `trusted-build` and `trusted-scope` (`policy/merge-checks.toml`):
the statuses must come from the approved creator in one attempt of the trusted workflow and be
bound to the exact PR head. The run's PR base must be current approved `main`. `trusted-scope` must
succeed, which means scope `mathematical` within the approved paths. Authorized review records are
also needed for the exact head.

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

- A dedicated machine-user token authenticates as the exact configured immutable user ID. Its
  repository role is the standard `write` role: admin, maintain, custom roles, site admins, App
  installation tokens, and unknown identity/role data do not satisfy either profile.
- Squash merging is enabled for the repository. The controller neither bypasses rules nor drains a
  merge queue.

### Remaining activation prerequisites for SphereCeti

As of 2026-11-23, `merge-doctor` on `main` reports these items as missing, besides the policy
switches and the uninstalled workflow:

- `policy/merge-controller.toml` still has `workflow_id`, `bot_user_id` and `checks_app_id` at zero.
- An administration-read observer token must confirm the ruleset's bypass actors.
- The ruleset must require up-to-date branches.
- `checks_app_id` must name the integration that `build` is bound to.

Approval-dismissal and last-push settings are recommendations. `merging` stays `false` until a
separate policy change.

The implementation uses GitHub's [branch-protection API](https://docs.github.com/en/rest/branches/branch-protection),
[collaborator permissions](https://docs.github.com/en/rest/collaborators/collaborators#get-repository-permissions-for-a-user),
[branch-rules API](https://docs.github.com/en/rest/repos/rules#get-rules-for-a-branch),
[repository rulesets](https://docs.github.com/en/rest/repos/rules#get-a-repository-ruleset), and
[head-conditioned merge API](https://docs.github.com/en/rest/pulls/pulls#merge-a-pull-request).
Missing API permissions or unsupported metadata are errors, not assumed readiness.

## Serialized executor and credentials

The template lives under `tools/ci/`, so GitHub cannot execute it on landing. A future reviewed
activation change must install its exact bytes at `.github/workflows/merge-controller.yml`, record
its real workflow ID, establish the server profile above, and configure credentials. The one
workflow handles both manual PR selection and scheduled/manual sweeps. Its concurrency group is
fixed at `sphereceti-merge-main`, with cancellation disabled. It runs at most 30 minutes per attempt.
It checks out exact approved workflow source with checkout credentials disabled and never builds
or executes candidate code or invokes a provider.

`SPHERECETI_OBSERVER_TOKEN` supplies the reader's `GH_TOKEN`: grant only the read permissions needed
for source, PRs/comments, Actions, protection, role and rules metadata, including administration
read access so that ruleset bypass actors are visible. `SPHERECETI_MERGE_TOKEN`
is a separate dedicated machine-user credential confined to this serialized executor. It must
not be installed in worker, reviewer, author, or other merger jobs. Its scoped contents/PR write
permission must confer no branch-rule bypass. Credential creation and confinement require operator
setup; the diagnostic cannot prove that an administrator has never copied a token elsewhere.

On entry the controller removes the writer token from the environment before any Git/reader child
process runs. The writer receives it privately and constructs a minimal subprocess environment.
It permits only identity lookup, a GET of its own view of the ruleset's bypass status, and a
squash-merge PUT containing an exact head SHA. It does not
inherit reader credentials, provider keys, or arbitrary environment secrets. No API response or
error message includes token values.

For `--apply`, runtime metadata must agree with the current approved SHA, main ref, canonical
workflow path, exact run/attempt and configured workflow ID. GitHub must report that run in progress
for `workflow_dispatch` or `schedule`. These are consistency checks, not cryptographic proof of
where a caller holding the merge token is running. The reviewed workflow and exclusive credential
placement establish the executor boundary. A local nonblocking file lock also prevents overlapping
preparation in one cache; it is not a distributed lock and cannot replace workflow serialization.

## Revalidation and lifecycle

Both single-PR and sweep execution call `merge_controller.reconcile` and #15's shared observer.
Disabled setup is checked before enumerating the sweep. The controller lists complete paginated
open-main PRs, rejects duplicates or excessive inventories, and refreshes the listing. It reads
current PR state again for each candidate. Already merged/closed PRs are no-ops; drafts and existing
human auto-merge requests are left alone. The shared observer also rejects an auto-merge request
created while a candidate is being assessed.

For an eligible candidate in apply mode, the controller obtains setup and full observation twice.
Changed head, integration base, review/contest, policy, protection, token identity, workflow, or
check evidence requires a new run. It refreshes all consumed observer and activation API responses
immediately before the PUT. The request's `sha` binds it to the exact reviewed head; strict server
checks and the no-bypass identity protect a base advancement between the last read and the request.
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

Review #15 first, then this diff: activation/profile checks, shared reconciliation and narrow writer,
the inactive workflow template, the shared observer's human-auto-merge guard, and regression tests.

```bash
python3 -B -m unittest discover -s tests -p 'test_merge_controller.py' -v
uv lock --check
uv build
python3 scripts/test_package.py
```

Tests exercise stop switches before both entry points, writer-token isolation, required check
producers, bypass/role rejection, the live ruleset shape (`tests/ruleset_fixture.py`) and its
human route, multiple, inactive or foreign rulesets, missing rules, unknown rule types, truncated
inventories, the classic path, concurrent head/base/policy changes, review revocation, final
refresh failure, restart, duplicate events, human-managed PRs, ambiguous responses, and lock
contention. Installed wheel/source tests run diagnostics and disabled apply/sweep paths from a
foreign cwd against fake GitHub. No test invokes a real merge or provider.

See [tracking issue #23](https://github.com/thefundamentaltheor3m/SphereCeti/issues/23) for review order, prerequisites and landing status. All infrastructure lands before roadmap #1.