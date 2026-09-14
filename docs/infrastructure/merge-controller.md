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
concrete blockers and whether the supported setup profile is ready. Successful diagnostics,
including a disabled result, exit 0; unavailable/invalid data and unconfirmed write outcomes exit 2.

`--apply` is explicit and requires both ready setup and the approved serialized executor. The
shipped `merging` switch is false, mathematical allowlist empty, and controller/producer IDs zero.
The CLI cannot configure those settings. Under the present roadmap-only contract there is no
SphereCeti mathematical change class to enable; production proofs still belong in Sphere-Packing-Lean.
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

The initial supported server profile is deliberately narrow:

- Classic protection for canonical `main`, with strict up-to-date requirements and both
  `trusted-build` and `trusted-scope` required from the configured App ID. Names alone, missing App
  bindings, or an any-App binding do not pass.
- Protection applies to admins; force pushes and deletions are explicitly disabled. At least one
  server-enforced PR approval is required, stale approvals are dismissed, and no user/team/App
  PR-review bypass allowance is present. #11's comment records are additional evidence, not a
  substitute for this GitHub review requirement.
- A dedicated machine-user token authenticates as the exact configured immutable user ID. Its
  repository role is the standard `write` role: admin, maintain, custom roles, site admins, App
  installation tokens, and unknown identity/role data do not satisfy this initial profile.
- Squash merging is enabled. Effective rulesets are absent; repositories using rulesets or merge
  queues need a separately reviewed profile. The controller neither bypasses rules nor drains a queue.

The implementation uses GitHub's [branch-protection API](https://docs.github.com/en/rest/branches/branch-protection),
[collaborator permissions](https://docs.github.com/en/rest/collaborators/collaborators#get-repository-permissions-for-a-user),
[branch-rules API](https://docs.github.com/en/rest/repos/rules#get-rules-for-a-branch), and
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
for source, PRs/comments, Actions, protection, role and rules metadata. `SPHERECETI_MERGE_TOKEN`
is a separate dedicated machine-user credential confined to this serialized executor. It must
not be installed in worker, reviewer, author, or other merger jobs. Its scoped contents/PR write
permission must confer no branch-rule bypass. Credential creation and confinement require operator
setup; the diagnostic cannot prove that an administrator has never copied a token elsewhere.

On entry the controller removes the writer token from the environment before any Git/reader child
process runs. The writer receives it privately and constructs a minimal subprocess environment.
It permits only identity lookup and a squash-merge PUT containing an exact head SHA. It does not
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
producers, bypass/role rejection, concurrent head/base/policy changes, review revocation, final
refresh failure, restart, duplicate events, human-managed PRs, ambiguous responses, and lock
contention. Installed wheel/source tests run diagnostics and disabled apply/sweep paths from a
foreign cwd against fake GitHub. No test invokes a real merge or provider.

See [tracking issue #23](https://github.com/thefundamentaltheor3m/SphereCeti/issues/23) for review order, prerequisites and landing status. All infrastructure lands before roadmap #1.