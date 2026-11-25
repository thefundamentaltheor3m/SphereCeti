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
sphereceti merge-control --pr 15 --apply --probe race --json  # live race probe; manual runs only
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
switch is false. The mathematical allowlist names `SphereCeti/Contour/` and `SphereCeti/E8/`,
`approving_reviewers` is empty, and controller IDs are zero.
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

- **Paths:** every changed path is an eligible proof path under `mathematical_paths`. Proof PRs
  never edit the library root `SphereCeti.lean`.
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

### Per-PR actions: stale build versus stale review

Each candidate gets one action, in `merge-control` results (`action`, `state`, `reasons`,
`review_inputs`) and in `merge-doctor --pr N` (`candidate`). Both commands also print text without
`--json`. The checks run in this order:

1. **`blocked`:** not an automatic-route PR (paths, policy, a hypothesis).
2. **`needs_review`:** route back for review; nothing is posted or merged. This applies when there
   is no accepted official review for the current head, or when the review is not provably still
   valid (rule below).
3. **`blocked`:** the head does not merge cleanly with current main.
4. **`needs_update`:** the head does not contain current main. GitHub's merge API pins only the
   head, so a behind head would land a tree that was never tested. The branch must be updated.
5. **`refresh_build`:** only the trusted build is stale. The review is valid, the formal approval
   qualifies and every other requirement passes. The build fails only with refreshable reasons:
   older attested tooling, a missing or older attestation, a tested merge that is missing or made
   with an older main, or (with those) a scope verdict made under that older tooling.
6. **`blocked`:** a misbound or failed build (another PR's binding, a tested tree other than the
   merge of current main and the head), an unmergeable PR, or no qualifying formal approval.
7. **`merge`:** everything is current and the formal approval qualifies.

**Option 2: when a review stays valid across main moves.** This is the maintainer's choice. A
review stays valid when the reviewed change is provably the same and the trusted build and audit
of the merged tree cover compatibility with current main. An unchanged head alone does not
establish it. For the same head, an accepted review is valid only when all of these hold:

- **The record is accepted against the current context**, as before. It binds the head, GitHub's
  `base.sha` snapshot and the diff base it implies, and digests computed at current main of: the
  specification documents and roadmap targets, the dependency manifest, policy, installed
  tooling, engine and rubrics. For a fixed head the snapshot does not move, so these bindings
  reproduce whenever main changed nothing the review read.
- **The change is the same.** The PR's own change from the reviewed diff base, and from
  `merge-base(current main, head)`, is identical: every differing path, with both modes and blob
  IDs. If main changed a file the PR also changes, the change differs.
- **No review input changed on main.** Every path changed between the record's `tooling_revision`
  (main when it ran) and current `commits/main` is classified as specification (`SphereCetiRoadmap/`,
  the spec documents), dependencies, policy, review tooling (`tools/`), library (`SphereCeti/`;
  imports are not traced, so any library change counts), library root (`SphereCeti.lean`), or
  other. Every category is an input except `tests/`, `docs/infrastructure/`, `scripts/` and
  `.github/`. The merged-tree build at current main covers build and CI tooling, and reviewers are
  not shown tests or infrastructure docs. Any input change means `needs_review`.

This starts conservatively. Proof PRs no longer edit `SphereCeti.lean`, which is frozen, so a main
move touching only that file should become rare; it still forces re-review. Every result reports
`review_inputs` (`changed_inputs` by category, `library_root_only`, `change_identical`,
`unrelated_changes`, `reviewed_at_main`). A `SphereCeti.lean`-only case adds the reason
`measurement: only SphereCeti.lean changed on main since the review`. This measures how often that
file alone forces re-review before any exception is designed; none is built.

**Carry-over to "Update branch" heads** (decision 2 on #100). GitHub's "Update branch" merges main
into the PR, so the head changes while the PR's own change does not. A review record or a formal
APPROVE on head H1 carries over to the current head H2 only if all of these hold
(`tools/project/sphereceti/carry_over.py`):

1. **Only update merges.** Every commit from H2 back to H1 has exactly two parents: the previous
   head first, and a commit on current main's first-parent history second. At most 20 such merges;
   no other commit may appear.
2. **Same change.** `merge-base(M, H1)..H1` equals `merge-base(main, H2)..H2` path by path in mode
   and blob ID, where M is the newest merged main commit. A conflict resolution, a main change to a
   file the PR changes, or any extra change in a merge commit makes them differ.
3. **No review input changed** on main between the review's `tooling_revision` and current main
   (which contains M), by the classification above, including the `SphereCeti.lean` measurement.
4. **Approvals.** The approver's latest review is APPROVE on H1, H1 to H2 meets 1 to 3 (with the
   accepted review's `tooling_revision`), and the approver is not the PR author.

In the decision, a carried record must also still be accepted: its context for H1 is replayed at
current main and checked by the unchanged record reader, so its bindings, verdicts and contests
apply as before. Any doubt means no carry-over, and the reason is reported: an extra commit, a
non-main parent, a changed input, an unreadable or truncated tree listing. The decision reports
`carried_from` and the merges in `official_review` and `review_inputs`; the controller's formal
approval reports `carried_from` and `carried_via`. Selection, the review queue and
`review --read-records` evaluate the same rule through GET-only API reads.

**GitHub's `base.sha` follows head updates, not main.** When a PR's head merges main, GitHub
re-snapshots `base.sha` to the merged main commit. Read-only on 2026-11-24, every PR whose head is
a merge of main (#44, #50, #55, #67, #69, #70, #79, #85, #86, #91, #97, #99, #102, #107) reports
`base.sha` equal to that merge's second parent. So after "Update branch" the PR's base is the merged
main, and its scope is exactly its own change.

**GitHub's `base.sha` is a snapshot, not live.** Observed read-only on 2026-11-23, after main
moved to `e64e506`, every open PR into main still reported an older main as `base.sha`. #85 had a
head pushed after the move and still reported `5db3655`. #41 reported `f435c43`, which is neither
main nor its merge-base `bab1893`. The decision therefore never compares `base.sha` with main. It
uses `commits/main` together with the change identity, the review inputs, the tested merge and
GitHub's mergeability.

### Tested tree through the merge

The trusted run builds and audits the head merged into its own main (`github.workflow_sha`). It
publishes `trusted-merge` (`Tested merge tree <tree> with main <main>`) on the head
([trusted build](trusted-build.md#tested-merge)). The decision recomputes that merge locally with
`git merge-tree` and requires the attested tree and main to match. If main advances, the tested
merge is stale, and the combination must be rebuilt before anything can land.

GitHub's merge API pins only the head (`sha`). A client-side final read of main cannot close the
race to the merge PUT, so the executor must be able to enforce that the tested tree is the tree
that lands. The options (evidence read-only, 2026-11-23):

- **(a) Strict ruleset with up-to-date heads (recommended).** With
  `strict_required_status_checks_policy` and at least one required check (`build` already is),
  GitHub refuses to merge a head that does not contain the current base tip. That check is
  server-side, at merge time. For a head that contains main, the squash merge's tree is the head's
  tree. That equals the tested merge of that head with that main, which the decision verifies, and
  the `sha` pin fixes the head. So the tested tree lands or nothing does.
  - The live ruleset has strict off (#49 already reports it), and `allow_update_branch` is on.
  - An update-branch merge commit is a new head. The review and the formal approval carry over
    to it under the rule above, so turning strict on does not force a re-review for each update.
    A behind PR is `needs_update`; once updated, its carried review and approval and a fresh
    trusted run of the new head let it land.
  - A required trusted check is not needed for enforcement: the executor verifies the trusted
    statuses itself, and requiring them for every PR would block the human route.
- **Others: not viable.** GitHub documents its merge queue only for organization-owned
  repositories, and SphereCeti is user-owned (`owner.type: User`), so that option is dropped. A fast-forward ref update of `main` to a locally built squash commit
  would be a server-side compare-and-swap, but the ruleset's pull-request rule forbids direct
  updates without bypass. Auto-merge does not pin the tree either.

**The decisive test: the race at the PUT.** An enforcement design is sound only if GitHub itself
refuses to land a stale combination when main advances after the controller's last check. The
fixture `test_decisive_main_advances_between_the_final_check_and_the_put_and_github_refuses` runs
the actual sequence:

1. **The PR otherwise fully qualifies.** It is in scope, with a current review, a qualifying formal
   approval and a passing merged-tree build; the preview says `would_merge`. So the refusal can only
   come from the race.
2. **The final check.** The controller finishes its final eligibility check (its last refresh) with
   main at `T`, and the head contains `T`.
3. **Main moves.** Only then does another PR land on main, and GitHub's `commits/main` moves.
4. **The PUT.** The executor sends its one head-pinned PUT with its writer.
5. **The refusal.** The fake GitHub applies the strict rule at merge time:
   `HTTP 405: Head branch is not up to date with the base branch`.

The executor records the refusal's status code and message, and rereads the PR (still open, not
merged) and `commits/main` (`main_after`, which does not contain the PR's change). There is exactly
one PUT, and nothing is retried. Without strict, the same PUT would have landed
`merge(new main, head)`, a tree nobody tested.

**Refusal classification.** A definite HTTP 4xx that leaves the PR open is classified:

- **`rejected_stale` (run state `rejected`):** an HTTP 405 whose message says the head is not up to
  date, the base branch was modified, or a required status check is missing. This is the expected
  stale-combination refusal. It is reported, and the next run re-evaluates against the new main.
- **`rejected_unexpected` (run state `stopped`, CLI exit 2):** anything else, such as a 403 for
  permissions or a 405 for a missing approval. The controller stops and reports, and retries
  nothing. It also opens a halt issue, and every later applying run halts until a maintainer
  acknowledges it ([halt](#halt-after-an-unexpected-refusal)).

Any other failure stays `unconfirmed`. The exact live messages are confirmed by the live procedure.

**The live procedure** must perform exactly that sequence with the real executor path and identity:
the controller's decision, then the workflow's job token. The probe mode is built (`merge-control
--pr N --apply --probe race`, the workflow's `probe: race` input); running it needs the activation
flips ([activation](activation.md)).

- **Preconditions.**
  - An administrator has enabled strict on ruleset 21449770; `build` stays required.
  - Policy has a nonempty `mathematical_paths` and an opted-in maintainer in `approving_reviewers`.
  - `merging = true`, with the workflow's schedule still commented out, so only a manual dispatch
    can merge. Unattended merging therefore stays off.
  - The controller workflow has its activation flips: `CONTROLLER: apply` and write permissions.
    Its `probe` input holds between the final check and the PUT.
- **PR B, the candidate.** It must fully qualify: a disposable proof PR inside the approved paths,
  with an accepted official review for its head, the opted-in maintainer's formal APPROVE on that
  head, and a passing trusted run whose `trusted-merge` attests main `M0`. B's head contains `M0`.
- **PR A, the main mover.** Any human-route PR, for example a `docs/` change, ready to be
  squash-merged by a maintainer.
- **Run.** Dispatch the controller on main with `pr=B` and `probe=race`. The probe refuses unless
  the API confirms a `workflow_dispatch` run, `merging = true` and one PR. In one run it:
  1. performs the full executor path up to its final check. It prints the decision (`merge`), main
     `M0`, and the verified tested tree;
  2. holds, bounded (for example 20 minutes), until `commits/main` differs from `M0`. During the
     hold a maintainer squash-merges PR A, so main becomes `M1`;
  3. sends the executor's head-pinned squash PUT for B with the job token;
  4. records GitHub's status code and message, then rereads B and `commits/main`.
- **Proof.** All of these hold:
  - the result is `rejected_stale`: HTTP 405 with the not-up-to-date (or required-check) message;
  - B is still open and unmerged;
  - main is `M1` and does not contain B's change.

  A 403, an approval message, or any other refusal (`rejected_unexpected`) leaves the race untested;
  fix the setup and repeat. If B lands, enforcement is absent: revert it and keep unattended
  merging off. Unattended merging is enabled only after this proof.

### Halt after an unexpected refusal

Decision 3 on #100 (`tools/project/sphereceti/controller_halt.py`). After `rejected_unexpected`,
the controller uses its job token to open a halt issue titled `Merge controller halted after an
unexpected refusal`. The body starts with a `<!--sphereceti-merge-halt:v1 {...}-->` marker naming
the run, PR, head and HTTP status, and the writer can create no other issue.

Every applying run, scheduled or dispatched, reads the issues authored by `github-actions[bot]`
(GET only). While any halt is unacknowledged, setup is not ready, with the reason `merge controller
halted by an unexpected refusal ...`.

**Acknowledging a halt** is a maintainer action: an unedited comment whose first line is
`/sphereceti acknowledge-halt`, posted after the halt, by a human in policy `authorized_reviewers`
with association OWNER, MEMBER or COLLABORATOR. Closing the issue alone does not acknowledge it, and
the bot cannot acknowledge its own halt. If the issue cannot be created, the run still ends `stopped`
(exit 2) and reports `halt_error`.

**Enforced by the executor.** Before any merge PUT it requires `protection.tested_tree_enforced`:
the single ruleset, or the classic profile, verified with strict up-to-date checks in effect. It
also requires the attested tested tree to equal the head's tree, so the head contains current
main. Otherwise it refuses with `refused`. With strict off, setup is also not ready, and merging
stays off.

### Trusted refresh dispatch

For `refresh_build`, an applying run (`--apply`, ready setup, verified executor, `merging` on)
confirms the same evidence once more and then dispatches one
[refresh](trusted-build.md#dispatched-refresh) of `pr-build.yml` on main. It uses the approved
trusted workflow ID from `policy/merge-checks.toml`, with inputs `pr` and the exact `head`. It
then moves on without waiting; the next scheduled run re-evaluates. Each PR gets at most one
dispatch per run, and an unconfirmed dispatch is never retried in that run. A preview, or any run
while switches are off, only reports `would dispatch refresh for #N`. Previews classify PRs
read-only even while setup is not ready. Applying with switches off lists no work at all.

The dispatch is gated by the existing `merging` switch, not a new `refreshing` switch. A refresh
exists only to let a merge follow, and the same stop switch then halts both. A new policy field
would also make every older CLI refuse the approved policy, because older CLIs parse an exact field
set. The job token needs `actions: write` to dispatch; only the activation change grants it,
together with `contents`/`pull-requests: write`.

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
- Squash merging is enabled. Under the ruleset profile, the authority is the single ruleset's
  `allowed_merge_methods`, which must be exactly `["squash"]`: GitHub enforces it at merge time, and
  the job token can read it. The repository flag `allow_squash_merge` must be true when visible. The
  read-only job token cannot see it (probe run 45274799597), so then it is an advisory finding.
  Without a squash-only ruleset, an invisible flag fails closed. The executor sends only squash
  PUTs, so a disabled setting could only make GitHub refuse the PUT (`rejected_unexpected`, a stop),
  never land anything else. The controller neither bypasses rules nor drains a
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
- the credential, identified by behaviour rather than format. GitHub does not fix the length or
  character set of installation tokens, and the first probe on `main` refused the real job token
  under a `ghs_[A-Za-z0-9_]+` pattern. The rule is:
  - Personal (classic and fine-grained), OAuth, user-to-server and refresh-token prefixes (`ghp_`,
    `github_pat_`, `gho_`, `ghu_`, `ghr_`) are refused without any request.
  - Empty, malformed (whitespace, control or non-ASCII characters) and oversized values are refused
    the same way.
  - Any other token makes one GET to api.github.com, `installation/repositories`. Only an
    installation token can call it, and it must list exactly this repository, as the job token
    does. A refusal, another repository or a wider installation fails.
  - The ruleset view is read only after this check passes. The token goes nowhere but
    api.github.com.
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
own ruleset view and installation probe, a squash-merge PUT with an exact head SHA, and a
`workflow_dispatch` POST of the approved trusted workflow on `main` for a PR number and exact
head SHA. Reads use the same job token through the GET-only reader. Diagnostics report the
token's shape (below) and omit its value.

### The read-only first run

[`.github/workflows/merge-controller.yml`](../../.github/workflows/merge-controller.yml) is installed
on `main`. It has `workflow_dispatch` only, and its `schedule` is commented out. Its permissions are
`contents: read` and `actions: read`. The job runs only on `refs/heads/main` and checks out `main`'s
exact SHA with credentials disabled. It never checks out, builds or executes PR code, and it calls
no provider. While `merging = false`, the job only runs `merge-doctor --executor --json` and prints
the result. No merge command runs, and the token could not merge anyway. Its concurrency group is
`sphereceti-merge-main` without cancellation, and it runs at most 30 minutes.

The workflow already contains the controller step, the `pr` and `probe` inputs, and every
permission it will need, all switched off: `CONTROLLER: doctor`, permissions at `read`, and the
schedule commented out. Activation is a separate tiny PR that flips the marked lines and the policy
values; the [activation checklist](activation.md) gives the exact diff and the order of operations.

### Reading the executor output

The first manual run's JSON should show:

- `executor.context: "github_actions"`, and `executor.run` with the run ID, attempt, path, head
  and **`workflow_id`**. Because policy still has `workflow_id = 0`, `executor.missing` contains
  `workflow_id is not configured; this run reports workflow_id N`; that `N` is the value to record.
- `executor.token`: `installation` and, on refusal, its `reason`. It also has a non-secret
  `shape`: the first 4 characters, the length, and the character classes present (lowercase,
  uppercase, digit, underscore, hyphen, period, other ASCII, whitespace, non-ASCII). The token itself
  never appears. A refusal names that shape in `executor.missing` too.
- `executor.token_view`: `"never"` is what activation needs. `"not read"` means the credential was
  refused first. `"omitted"` (GitHub gave no field for
  the installation token) and `"unreadable"` are blockers that keep merging impossible.
  `"always"`, `"pull_requests_only"` or `"exempt"` mean the executor could bypass the ruleset.
- Any environment or run mismatch, each named with the observed and expected value.
- `protection`: the same ruleset verification as a local run. `ready: false` with the policy items
  listed in `automatic_path.missing`.

**Observed, not configured:** the first probe, run
[45238596085](https://github.com/thefundamentaltheor3m/SphereCeti/actions/runs/45238596085)
(`workflow_dispatch` on `main` at `5db3655`, 2026-11-23), verified the run and reported
`workflow_id 428151597` for `.github/workflows/merge-controller.yml`. Policy keeps `workflow_id = 0`;
activation records it. That run refused the job token under the former format check, so
`token_view` was `"not read"`. The next probe reports the token's shape and, once it is accepted,
`current_user_can_bypass`.

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