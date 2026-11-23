# Shared merge observation

This adapter reuses authenticated records and the trusted scope/compiled-build contract.
Review evidence and eligibility here before the controller’s action path. No Python or Lean
dependency is added.

**Adapted from the [TauCetiReview contributors](https://github.com/TauCetiProject/TauCetiReview),
Apache-2.0, at [afb424e](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b):**
[`runner/merge_from_scoreboard.py`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/merge_from_scoreboard.py)
supplies the shared decision and separation of review safety from overall eligibility.
The source was checked at exact upstream Git blob
[c3bbd00](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/merge_from_scoreboard.py).
SphereCeti reuses its strict #11 record parser rather than upstream's permissive legacy tables.
The imported source, rubrics, and tests in #9 remain unchanged. Trusted build/scope production
continues the [TauCeti](https://github.com/TauCetiProject/TauCeti) workflow adaptation at
[b743b60](https://github.com/TauCetiProject/TauCeti/tree/b743b607ce3e9742b18026ad79082e5d15badff5),
particularly [`.github/workflows/pr-build.yml`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/.github/workflows/pr-build.yml).

## Command and result

```bash
sphereceti merge-observe 1 --json

# Reuse local Git objects and existing pinned dependency sources:
sphereceti merge-observe 1 --source-repo /path/to/SphereCeti \
  --dependencies-dir /path/to/dependencies --cache-dir /tmp/sphereceti-observation --json
```

The command obtains PR/main identities from GitHub. Local source paths only supply immutable
Git objects; they cannot select the approved revision or replace policy. Missing source objects
are errors when a local store was explicitly provided. Otherwise a source-only cache fetches
exact revisions. No candidate code is executed, and no Lean build or provider runs in this command.
The cache is the only local write surface; the source checkout and reports are not changed.
Mathematical-scope review evidence uses #11's existing bounded source materialization. Protected
PRs skip dependency materialization and review-engine preparation entirely.

A successful read exits 0 with `eligibility` equal to `human_review`, `blocked`, or `eligible`,
concrete denial reasons, exact head/base/tooling, and available scope/check/review evidence.
API failures, incomplete inventories, or an observed race exit 2 with an error, never an empty
successful result. `merge_eligible` and `merge_allowed` are always false, including the synthetic
eligible test. `eligible` means only that this observation's predicates passed; it is not an
authorization or a reusable signed receipt. The output digest identifies data, not its producer.

## One decision, distinct requirements

`merge_observation.decide` is the shared deterministic decision for future workers, dashboards,
CI consumers, and the controller. Its inputs must be gathered by approved code; accepting a
user-supplied JSON dictionary would not establish authority. The command has no fixture-input,
policy-override, merge, enqueue, dispatch, posting, or provider option.

The eligible path requires all of:

- The exact canonical repository and an open, non-draft, unmerged PR with known clean mergeability.
- The current approved main as integration base and unique diff base; stacked, behind, conflicting,
  or indeterminate PRs are blocked. Scope comes from #6's complete immutable Git-tree comparison,
  including both sides of renames. Only explicitly permitted library paths can qualify.
- Approved candidate configuration and matching scope/head/base/dependency/tooling bindings.
- #11's current complete authorized review assessment, with exact context digests, installed
  tooling comparison, API identity, supersession, revocation, and contest rules intact.
- Successful trusted build and scope statuses from the configured producer and exact successful
  run attempt of the approved `pull_request_target` workflow, including its candidate/status jobs.

SphereCeti's mathematical allowlist stays empty. Proof PRs require human merging.
Roadmap and infrastructure changes therefore take the human route. A missing policy on current
main is explicitly reported; feature-branch policy cannot activate itself. Tests exercise the
future mathematical path using disposable evidence, not production mathematical implementations.
The `merging` switch is reported separately and cannot turn this observer into a merger.

## Trusted check provenance

`policy/merge-checks.toml` initially has workflow ID zero and no approved status-creator IDs.
It must be selected from immutable remote-main tooling, alongside automation policy. The
packaged copy participates in installed-tooling comparison; a cwd file cannot override it.
Configuring real producers is a separate reviewed setup change after the trusted workflow lands.

The observer reads the complete paginated status history for the exact head and chooses the
newest entry for each required context, including failures and unapproved producers. It does not
fall back to an older green status. API-reported Bot IDs establish publisher identity; names and
body claims do not. Both statuses must name one canonical run URL with an explicit attempt:

```text
https://github.com/OWNER/REPO/actions/runs/RUN_ID/attempts/ATTEMPT
```

The only change to the trusted producer in this PR adds that attempt suffix to its status links.
Older links without attempts cannot satisfy this observer. Build/scope context names and the
separate status-writing job remain unchanged.

The reader checks the run's repository, configured workflow ID, exact workflow path, event,
tooling revision, completed success, head repository, and PR binding. It then verifies both
expected jobs, their attempt/run IDs, and status publication timestamps within the status job.

**PR binding.** GitHub reports a fork PR's `pull_request_target` run with an empty
`pull_requests` association (SphereCeti #54, run 45224210603), so the trusted workflow's status
job also attests the event's own binding in the `trusted-build` description, taken from the
`pull_request_target` payload in main's workflow, never from candidate code:

```text
Approved tooling build: success; tooling <workflow_sha>; pr <number>; base <event base sha>
```

The head is the status's own commit (the status URL must name the PR head), and the run's
`head_sha` must equal it. GitHub caps a status description at 140 characters, so the head is not
repeated. A run is bound when its event is `pull_request_target` with the approved workflow ID,
its `head_sha` is the PR head, its `head_repository` equals the PR's head repository (from the PR
API, or the survey's `headRepository`), and the attested PR number and base match. An
association, when GitHub reports one for this PR, must agree. The older description without
`pr`/`base` remains accepted only together with the exact association, so same-repository PRs
keep working until their trusted run is refreshed; fork PRs need a refreshed run. A status on the
same commit attesting another PR number is refused for this PR. Incomplete API fields fail
closed. A rerun cannot reuse statuses from an earlier attempt. The latest run
must use the exact current tooling revision; unrelated main advancement conservatively requires
fresh base/build validation even if #11 can reuse unchanged review context.

These fields come from GitHub's [commit-status API](https://docs.github.com/en/rest/commits/statuses),
[workflow-run API](https://docs.github.com/en/rest/actions/workflow-runs), and
[workflow-job API](https://docs.github.com/en/rest/actions/workflow-jobs).
The trusted workflow and configured producer credentials remain trusted; this is not independent
proof that an arbitrary status poster ran Lean. Branch-protection/ruleset verification and
no-bypass bot setup belong to the next controller/activation PR.

Every consumed GitHub response is read again before returning, including PR/main, comments,
ancestry comparisons, statuses, runs, and jobs. Changed evidence aborts observation. GitHub offers
no atomic multi-endpoint snapshot, so a change after those reads remains possible. A later
controller must rerun observation immediately before acting and use server-enforced checks and
an expected-head condition; an old observation file cannot authorize a merge.

## Auto-approval decision

`sphereceti auto-approve-check N` answers one question read-only: would SphereCeti automatically
approve this proof PR, and why or why not? It is the decision a future review bot would consult
before submitting a GitHub APPROVE review on the exact head; a separate non-bypass worker would
merge. It reviews, approves, posts and merges nothing, and calls no model provider.

```bash
sphereceti auto-approve-check 50 --assume-proof-paths 'SphereCeti/E8/**' --json
```

The approved `mathematical_paths` list is empty, so a decision today needs an explicit
**hypothetical** allowlist. `--assume-proof-paths` never changes policy. The output then sets
`hypothetical: true`, repeats the assumed globs, and starts its note with `HYPOTHETICAL`.
Globs must lie under `SphereCeti/`; `*` and `?` stay within a segment, and `**` is a whole
segment. Without the flag, the approved policy's prefixes apply.

The command reuses `collect` (this observer's GET-only evidence gathering and end-of-run refresh),
`gate.evaluate`, `merge_checks.assess_checks` and `review_records.assess_records`. It reports
`would_approve`, every requirement with its evidence, the exact head/base/tooling, the PR
author against the review publishers, and the reasons for any refusal. A computed decision exits
0 either way. Incomplete evidence exits 2.

| Requirement | Evidence and binding |
|---|---|
| `paths` | The PR's complete file list from the API; a count differing from `changed_files`, GitHub's 3000-file cap, or a list differing from the exact Git diff fails closed. Each path must be an added or modified regular `SphereCeti/**/*.lean` library file under the allowlist; protected library modules are excluded. Renames, deletions, mode changes, symlinks and submodules are ineligible. Roadmap/specification, dependency, CI, policy, review and machinery paths are listed with their human route. |
| library root | Proof PRs never edit `SphereCeti.lean`; the `SphereCeti.*` Lake glob builds every topic module, and the root keeps its existing re-exports. An edit to the root is ineligible and routed to human review, like any other protected path. |
| `trusted_checks` | `assess_checks`: `trusted-build` success and `trusted-scope` present from the approved producer and one exact `pull_request_target` run attempt. The run's `head_sha` is the PR head, its head repository is the PR's, and the attested PR binding (or, for older runs, the PR association) names this PR and base. The gate reports `human_review` while the allowlist is empty, and it protects the library root. That status is replaced by the stricter path rule only under the hypothesis. With an approved allowlist, a module-only PR receives `mathematical` from the gate itself. |
| `compiled_audit` | The `candidate` job of that same run attempt. It ran the approved tooling's `scripts/check_audits.py` through `scripts/sandbox-build.sh` on the exact head. The tooling is bound by #48's attestation: `trusted-build` publishes the run's `github.workflow_sha`, and `assess_checks` requires it to equal current main. The output reports the attested SHA. The ordinary `build` check runs candidate-controlled scripts, and its name alone is not used. |
| `official_review` | `assess_records` accepts a complete, non-advisory record covering all ten rubrics. Its exact head, base, diff base and context digests come from an authorized reviewer. Run it from installed tooling equal to main; otherwise the installed-tooling comparison fails. |
| `independent_reviewer` | At least one accepted publisher is not the PR author, by API user ID. The author can never supply the sole approval. |
| `pull_request` | Open, not draft, targets main, base equals current main and is the diff base, and not conflicting. No GitHub approving review is read or required. `mergeable_state` `blocked` or `unstable` is accepted, while `dirty`, `behind` and `unknown` are not. |
| `policy` | Reports the real `merging`, `mathematical_paths` and authorized reviewers, and the hypothesis if one was used. |

GitHub reports a workflow run's `pull_requests[].base.sha` from the PR's live state, not from
the time of the run. On 2026-11-23, PR #36's run 44856402521, created on 2026-11-21, reported
base `495ebff`, a main commit merged two days later. So only the attestation binds the tooling.
For diagnosis, the output also compares the run's creation time with the default branch's last
move, from the repository activity API. That timestamp comparison never decides.

## Review and validation

Review this diff against #11: read this guide, then the shared decision/reader, check authentication,
the one-line status-link change, and the adversarial and installed-CLI tests. No new active
workflow is needed for the read-only CLI. Existing CI runs the new tests and packaging checks.

```bash
python3 -B -m unittest discover -s tests -p 'test_merge_observation.py' -v
uv lock --check
uv build
python3 scripts/test_package.py
```

Tests cover the future eligible path, every scope binding, missing/untrusted statuses, exact
workflow/attempt/job provenance, revoked/stale/partial/shadow/contested reviews, draft/closed/behind
PRs, API races and pagination errors. Real disposable Git fixtures exercise protected and
mathematical scope from a foreign cwd with conflicting policy, no provider calls, and GET-only
fake GitHub. Wheel and source installs run the same observation flow.

See [tracking issue #23](https://github.com/thefundamentaltheor3m/SphereCeti/issues/23) for review order, prerequisites and landing status. All infrastructure lands before roadmap #1.