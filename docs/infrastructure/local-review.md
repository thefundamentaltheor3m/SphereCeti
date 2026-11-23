# Local advisory reviews

**SphereCeti adapts the [TauCetiReview contributors' engine and CLI](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner)
at [afb424e](https://github.com/TauCetiProject/TauCetiReview/commit/afb424eda89e8ac96d9eb69f6a88972055a4cd1b),
under Apache-2.0.** The source import was introduced in [PR #9](https://github.com/thefundamentaltheor3m/SphereCeti/pull/9).
The adapter reuses its provider adapters, rubric ordering, verdicts, case files, contests,
shadow runs, and budget accounting. Source selection follows the immutable Git approach from
[PR #6](https://github.com/thefundamentaltheor3m/SphereCeti/pull/6). SphereCeti supplies the project
context, installed resources, and local execution boundary.

## Use

```bash
# Pick the open PR that most needs your review, say why in one line, and review it.
sphereceti review
# The same choice as a preview: no model call and no GitHub write.
sphereceti review --dry-run

# No provider calls: identify and verify the exact PR, approved context, and dependency sources.
uv run --locked sphereceti review 1 --dry-run \
  --source-repo . --dependencies-dir .lake/packages

# Explicit local advisory review using an operator's configured subscription.
uv run --locked sphereceti review 9 --provider codex --budget-usd 5 \
  --source-repo . --dependencies-dir .lake/packages
```

The same commands work with an installed `sphereceti` executable outside the checkout.
`--operator-config preferences.toml` accepts the existing provider, budget, and storage
preferences. For local subscription reviews you can set a budget once. Create
`~/.config/sphereceti/operator.toml` with your chosen values, for example:

```toml
provider = "codex"
budget_usd = 5
```

Then `sphereceti review` and `sphereceti review 9` use those preferences. The budget is a daily estimate threshold,
checked before each rubric with a default $1 reservation. Actual usage can exceed the threshold.
An explicit `--operator-config` replaces the default file and command-line flags take precedence.
With no configured budget the default is zero. Worker execution, API authentication and
shadow runs require their own explicit flags or operator config.

## Posting by default

A live GitHub review (bare `review` or `review N`) publishes its review record on the PR,
under your own `gh` identity, through the [record publisher](review-records.md): exactly what
`--post` did before. `--no-post` keeps the record local. `--post` remains accepted as the
explicit form; `--post --no-post` is a usage error (exit 2).

- Dry runs, `--read-records`, `--local-sources`, `--shadow`, reply mode and `--replies-json`
  never post, and need no `--no-post`.
- Posting still requires approved policy: `posting = true` in `policy/automation.toml` on
  remote main, read from the approved tooling commit T. When that policy is unavailable (for
  example an explicit prospective `--tooling`) or disables posting, the default keeps the
  record local and reports `Not posted: posting is disabled by approved repository policy.`
  (`not_posted` in `--json`). An explicit `--post` still fails before any provider call.
- Anyone may post. A record from a GitHub identity outside the approved
  `authorized_reviewers` is an advisory record: readers and merge gates ignore it. The result
  says so: `Posted: <comment URL> (advisory: user:N is not an authorized reviewer).`
- The text result always ends with `Posted: <URL> (...)` or `Not posted: <reason>.`

The worker (`worker run --execute`) is unchanged: it posts only with `--post-review`.

## Publishing a saved run

A review that finished but was not posted keeps its exact record in the run directory
(`record.md`, with `record.json` and `result.json` beside it). The record may be unposted because
the POST was interrupted, the network failed, policy was unavailable or disabled, or the review ran
with `--no-post`. Publish it later without spending provider usage again:

```bash
sphereceti review-publish 0123456789abcdef0123456789abcdef   # run id under the review storage
sphereceti review-publish /path/to/run-directory             # for example an --output directory
sphereceti review-publish --latest 53                        # the newest saved run for PR #53
```

`--latest` takes only the newest saved run for that PR. If that run is ineligible, the command
says why. It never falls back to an older run. `--source-repo` and `--dependencies-dir` work as
for `review`. `--json` prints `schema: sphereceti.review-publish/v1` with `state` (`published`,
`already_published`, `unconfirmed` or `refused`) and, when refused, the list of `reasons`.

The command never starts the engine or a provider. In order, it:

1. **Loads the saved run** and checks that `record.md`, `record.json` and `result.json` agree,
   as archive capture does. It publishes those exact bytes. A record saved by an earlier renderer
   stays valid, because readers hash the published text.
2. **Checks eligibility.** Only a run that `review --post` could have published is eligible:
   - a live GitHub review against approved main (not `--local-sources`, not a prospective `--tooling`);
   - commit or manual mode (shadow and reply runs never publish);
   - complete or partial completion (an errored run has nothing to publish);
   - no local reply inputs (`--replies-json` or `--reply-file`). Such inputs are untrusted text,
     and the record's contest watermarks must not claim to have answered a GitHub contest from
     them. A run saved before contest provenance was recorded is refused only when it carries
     nonzero watermarks.

   A partial run is published as the advisory record it already says it is. A run that was
   already confirmed on GitHub is never published again, even if that comment was deleted.
3. **Checks the identity.** It reads the `gh` identity. A posting run records the identity that
   was about to post, and a publication attempt records the identity it used. A different
   identity is refused. A `--no-post` run is published under the identity that runs this command.
4. **Reconciles with GitHub.** If a comment by this identity already carries this record (same
   body, hence the same record ID), it reports `Already published: <URL>` and writes nothing.
5. **Revalidates** as `review --post` does immediately before its POST. The PR must still be
   open with the same head and base. A moved head means the saved run reviews an older head and
   cannot be published as current: run a new review. The command also materializes approved main
   again and requires every bound digest to match: dependencies, engine, effective rubrics,
   installed tooling, policy, review context and PR description. Whether the installed tooling
   matches T must be unchanged. The run's T must be an ancestor of approved main, and approved
   main's policy must still set `posting = true`. Every failed check is listed.
6. **Publishes once** through the same publisher as `review --post`. That means confirmed
   readback and the API identity receipt. The local archive entry is captured idempotently. The
   receipt is saved in `result.json`. A POST whose outcome is unknown is reported as `unconfirmed`
   and never retried. Run the same command again: it finds the comment if GitHub created it, and
   posts only if GitHub did not.

The command exits 0 when the record is published or already on the PR, and 2 otherwise.

## Choosing what to review

`sphereceti review` without a number selects one PR, prints one line explaining the choice,
and then reviews it exactly as `sphereceti review N` would, bound to the head and base it
observed. If the PR moves before the provider starts, the run stops (exit 2) and asks you to
rerun. Selection reuses the worker's read-only `survey` and `plan`; it never writes to GitHub.

**Eligible PRs** are open PRs the planner offers for `review-assessment`: not a draft,
mergeable, and with passing review readiness (CI passed, or the authenticated human-review
scope exception with main-only skipped jobs). For review readiness only, that exception also
accepts a trusted run on the **same PR head** whose attested tooling, and the PR's recorded base,
are older approved main commits: equal to or ancestors of current main, checked with GitHub's
compare API (an unknown or diverged commit is not ready). Every producer, workflow, run,
attempt, job, head and association check still applies. A review runs with current tooling T and
binds T itself, so the trusted run's tooling does not change the review's authority. Approval
and merging keep exact current evidence: the shared assessor (`merge_checks`, used by
`auto-approve-check` and merging) still requires the attested tooling and the base to equal
current main. Such a PR carries the note `trusted build predates main; refresh to merge`, as
information only. Then it skips:

| Code | Reason |
|---|---|
| `yours` | You authored it (author login equals the authenticated `gh` user, case-insensitively). |
| `draft` | Draft PR. |
| `not_ready` | Conflicting, unknown mergeability, or CI failed. |
| `awaiting_ci` | CI is pending or unknown. |
| `awaiting_github` | GitHub has not yet computed mergeability (it recomputes after main moves). |
| `awaiting_refresh` | Only a fresh trusted run is missing (a build from before tooling attestation). |
| `reviewed` | It already has an accepted review of this head (below). |
| `reviewed_by_you` | You already published or produced a complete review of this head. |

"Already reviewed" is checked per exact head **and** base:

- **Accepted review:** a PR comment holds an unedited, complete, non-advisory commit/manual
  review record for this PR's current head and base, published by an identity in the installed
  policy's `authorized_reviewers` (the same records `review --read-records` reads). An
  authenticated contest newer than that record, not yet answered by its publisher, reopens the
  PR. Selection does not recompute tooling, context or engine digests (that would mean
  materializing every candidate's sources); the record reader still checks them all.
- **Reviewed by you:** a complete commit/manual record for this head and base that you posted
  (comment author login equals yours, advisory or not), or that you produced locally: a
  `record.json` under your storage's `runs/`, or a record in the local archive journal, which
  also covers runs with `--output`. Dry runs, partial and errored runs do not count. A local
  record that was never posted is published with
  [`review-publish`](#publishing-a-saved-run), not by reviewing again.

**Priority** comes from the planner. Every eligible PR is at the `review-assessment` stage, so
they tie, and the planner's tie-break decides: **longest waiting first**, by the PR's GitHub
`updatedAt` (oldest first), then the lowest PR number. The planner does not observe when the
current head became ready, so `updatedAt` stands in for it. Any comment, including a posted
record, refreshes it.

The rationale line has this form:

```text
Reviewing #50 (head 8cdec1b): ready, not yours, no current review; waiting 3h; will post if policy permits.
```

`Previewing` replaces `Reviewing` under `--dry-run`, which ends `; nothing will be posted.`
`--no-post` ends `; will not post (--no-post).` and an explicit `--post` ends `; will post.`
`ready (human-review scope)` marks the scope exception, and
`ready (human-review scope; trusted build predates main; refresh to merge)` an older trusted run.
A PR skipped for another reason keeps that note beside its reason, e.g. `is yours (trusted build
predates main; refresh to merge)`. Waiting is rounded down to `<1m`,
minutes, hours or days. The result then lists the ten rubric verdicts, the record path
(`record.md`, with `record.json` beside it), the local archive entry, and whether and where the
record was posted.

When nothing qualifies, the command prints why and **exits 0**:

```text
No PRs need your review: #53 is not ready (CI failed); #51 is yours; #50 is yours.
```

When some PRs only await current evidence, the answer summarizes them instead of listing each,
so stale evidence is not mistaken for an empty queue; real failures stay listed:

```text
No PR is ready with current evidence: 20 open PRs await a refreshed trusted build (main moved to 5db3655); 2 open PRs await CI; 3 are yours; #41 is not ready (CI failed).
```

An unknown queue (GitHub unavailable, more than 100 open PRs, unreadable review records) is
never reported as nothing to do: it exits 2. A review that ran but ended in error exits 1, as
for `review N`. PR-specific inputs (`--local-sources`, `--read-records`, `--shadow`, reply
inputs, `--head`/`--base`/`--description-file`) need an explicit number.

`--json` prints `schema: sphereceti.review-selection/v1` with `state` (`selected` or
`nothing_to_review`), `actor`, `observed_at`, `priority`, `waiting_since: updatedAt`,
`selected` (PR, title, author, head, base, `updated_at`, `waiting_seconds`, `ci`,
`review_ci`, `note`), the ordered eligible `candidates`, `skipped` entries (`pr`, `head`, `code`,
`reason`, `note`), `main` (current main, when some PR awaits a refresh), the `rationale` line, the `posting` note, and the full `review` report
(`null` when nothing was selected).

`--auth api` uses the selected provider's API credential instead.
Supported providers are the imported engine's Claude, Sonnet, Codex, Kiro, DeepSeek, MiniMax,
and Grok adapters. Tests invoke only a fake executable, never these services.

Without `--source-repo` or local dependency stores, the adapter fetches exact commits into
its private Git cache. It never checks out or executes candidate configuration. An explicit
source store must already contain all requested commits. Partial/promisor stores are rejected
because older Git can lazily fetch missing objects during an otherwise local read.

For a network-free source selection using locally available objects:

```bash
sphereceti review 9 --dry-run --local-sources --source-repo . \
  --dependencies-dir .lake/packages \
  --tooling FULL_CONTEXT_SHA --base FULL_PR_BASE_SHA --head FULL_PR_HEAD_SHA
```

`--local-sources` disables GitHub queries and fetching, not an explicitly requested provider
call. Combine it with `--dry-run` to make no inference calls. Local references and an explicit
prospective `--tooling` override cannot establish that context was approved on GitHub.

## Your review queue and bounded batches

Adapted in design from TauCetiWorker's [dashboard](https://github.com/TauCetiProject/TauCetiWorker#the-dashboard)
and review-only [rounds](https://github.com/TauCetiProject/TauCetiWorker#what-a-round-does): the
previous reviewer gets first chance at a revised PR. No TauCetiWorker code is used.

`sphereceti reviews` is read-only (no model call, no GitHub write). It surveys the open queue
once, with the same survey, planner and readiness rules as bare `review`, reads each candidate
PR's comments, and lists your queue in sections:

```text
Review queue for yvonne (thefundamentaltheor3m/SphereCeti, observed 2026-11-23T21:29:38Z)
Revised since your review (1):
  #66 bob "Prove the contour deformation" 6031efc: revised 1a2b3c4 → 6031efc, 2 commits; author replied 1×; waiting 3h
Author replied (1):
  #69 carol "Prove the box boundary layers" 99e8687: you requested changes (scope); author replied 1×: https://github.com/thefundamentaltheor3m/SphereCeti/pull/69#issuecomment-41; waiting 2m
New to you (1):
  #55 carol "Prove the lower bound" daff9e6: ready (human-review scope); no review by you; waiting 5h
Waiting on the author (1):
  #54 dave "Prove the wedge geometry" 8cb4c8c: you requested changes (api-design, documentation); no new head; waiting 2h
Not ready: No PR is ready with current evidence: 8 open PRs await CI; 7 are yours; #41 is not ready (CI failed).
```

- **Revised since your review:** your latest posted (unedited, commit/manual) record names an
  older head and the PR is ready. It shows the old and new short heads, the commits since (the
  compare API; a rewritten history is reported, never guessed), and author replies and contests
  posted after your record. These rank first.
- **Author replied:** your latest record names the current head and requested changes or
  blocked, and since then the PR author has replied (a comment by the author) or anyone has
  posted a contest. It links the newest reply. These rank right after revised PRs.
- **New to you:** exactly bare `review`'s eligible PRs.
- **Waiting on the author:** your latest record names the current head and requested changes or
  blocked, and there is neither a revision nor a response; it names those rubrics.
- **Your follow-ups, not ready yet:** a PR you reviewed that was revised or answered but awaits
  CI, GitHub or a refreshed build is named on its own line instead of disappearing into the
  summary (`follow_ups_not_ready` in JSON).
- **Not ready:** the aggregated summary of bare `review`, with your own PRs counted. PRs that
  already have the review they need are listed as already reviewed.

Each entry gives the PR, author, title, short head, the reason and how long it has waited (since
`updatedAt`). `--json` prints `sphereceti.review-queue/v1` with `sections` (`revised`, `author_replied`, `new`,
`waiting_on_author`, `not_ready`), `done`, `follow_ups_not_ready`, `not_ready_summary`, `main` and `order`. A failed
lookup (survey, comments, compare response) exits 2 and lists nothing.

`sphereceti review --new --limit N`, `--revised --limit N` (your follow-ups: revised, then author
replied) or `--all --limit N` (follow-ups, then new) reviews up to N **distinct** PRs (default 1,
at most 10) from that section, one at a time, each exactly as `review N` would. Follow-ups use the
normal follow-up mode (`commit`), not `--mode manual`. Before each item the queue is surveyed
again and eligibility rechecked, and the review is bound to the head it selected. A PR that moved
before its review, or left the section (became a draft, not ready, or reviewed), is skipped with
its reason. If the head moves during the review, the batch reports it and leaves the new revision
for a later invocation; no PR is reviewed twice in one batch. Each item prints
`[i/N] #PR author head: reason`, the plan line, the summary line and the next action; the batch
ends with one line and one line per PR (outcome and posted link):

```text
Batch (new): 3 reviewed, 3 posted, 1 skipped; stopped: limit of 3 reached.
  #55: approved · posted https://github.com/thefundamentaltheor3m/SphereCeti/pull/55#issuecomment-1 · official
  #66: blocked (reuse) · posted <URL> · advisory
  #67: changes (naming) · posted <URL> · advisory
  #70: skipped (moved before review)
```

A finding is not an execution failure: a block or requested changes ends only that PR's review,
and the batch continues. Unknown usage, an exhausted budget, a provider failure (an engine error
or an unavailable provider), an unconfirmed publication or a failed GitHub lookup **stop** the
batch with no further spend, and the summary names the PRs left `untouched`. Before each item it
also stops when today's recorded spend plus the per-call reservation would exceed the daily
budget. `--json` prints `sphereceti.review-batch/v1` (`items` with each outcome, plan and
summary, `skipped`, `untouched`, `reviewed`, `posted`, `stopped`, `line`, `lines`). Exit codes: 2 for a failed lookup,
1 if a review ended in error, else 0. Without these flags, bare `review` still reviews one PR.

## What the terminal says

Before any provider call (after the exact evidence is prepared), `review N` and bare `review`
print one plan line with the PR, short head and base, each selected provider with its effective
model after defaults (from the packaged engine's pricing table, or `--codex-model` /
`--claude-model` / `--kiro-model`), and whether the result will post:

```text
Review #54: head 8cdec1b, base 5db3655 · codex gpt-5.6-sol (falls back to gpt-5.6-terra) · will post
```

The posting part is `will post`, `will not post (--no-post)`, `will not post (approved policy
disables posting)`, or `dry run: no model call, nothing posted`.

At the end it prints one summary line and a concrete next action:

```text
10/10 approve · posted https://github.com/thefundamentaltheor3m/SphereCeti/pull/54#issuecomment-1 · official
4/10 reviewed · stopped: blocked on attribution · posted <URL> · advisory
Next: author: address attribution (see record); rerun after the head changes
```

- **Counts:** rubrics with a verdict on this head out of those requested; `approve` when all of
  them approve, else `reviewed`. A review that stops early names the first blocking rubric and
  the stop reason from the run's receipt: `usage unknown` (the engine's usage stop), `provider
  unavailable (not authenticated|quota exhausted|rate limited)` from the archived attempts'
  error kinds, `provider failed to start` (every rubric ended without a verdict and without the
  model touching a file), `blocked on <rubric>`, an engine error, or `budget or round limit
  reached`. A complete review with requested changes says `changes requested: <rubrics>`.
- **Posting:** `posted <URL> · official` (an authorized reviewer's record) or `· advisory`,
  `not posted: <reason>`, or `publication interrupted`.
- **Next action:** `author: address <rubric> (see record); rerun after the head changes`;
  ``run `sphereceti review-check-sandbox --compare-path --compare-tmpdir` `` after a provider
  startup failure; sign in again, wait for the usage window, or rerun later for a provider that
  is down; ``publication was interrupted; run `sphereceti review-publish RUN` `` (RUN is the run id
  under the operator store, or the run directory for an `--output` run, as `sphereceti review-publish`
  takes it); `rerun without --no-post to publish
  the record`; `run again without --dry-run to review`; or `none: every rubric approves`.

`--json` carries the same as `plan` (`line`, `pr`, `head`, `base`, `providers`, `models`,
`posting`) and `summary` (`line`, `reviewed`, `total`, `first_blocking`, `stop`, `posted`,
`official`, `next_action`); bare `review` adds both at the top level of its selection report.

## Evidence and authority

- **T** is the selected tooling/context commit. By default it is the repository's remote
  `main` commit, obtained separately from the PR. The report also compares the installed
  adapter, engine, overlays, profile, policy, and source lock against T. An installed tooling
  revision is asserted only when all those bytes match; otherwise its digest is recorded
  and the revision remains unknown.
- **H** is the exact PR head. The PR's base commit and unique merge base are recorded
  separately. The diff is generated from immutable objects with external diff and textconv
  disabled. A candidate profile, Lakefile, or manifest cannot select the review's dependencies.
- **D** contains every Git package resolved by T's manifest, including the actual TauCeti
  and Mathlib source trees. The profile's pins must agree with the manifest. Working-tree
  edits and Git replacement objects cannot change the snapshots. Only full commit IDs are
  fetched; symbolic `inputRev` values in Lake's manifest are not followed.

The provider workspace contains `approved/` at T, `code/` at H, and `dependencies/` at D.
The report individually identifies the README, conventions, migration, provenance, upstream
ledger, validation guide, infrastructure plan, target-signature file, profile, and policies.
Only documents listed with approved authority count as approved specification. A proposed
roadmap, especially PR #1's README and target signatures, remains candidate evidence.

Before the roadmap is integrated, missing context is expected and explicitly listed. All
results in this implementation have `merge_eligible: false`, even when every rubric approves.
The local result does not authenticate a reviewer or independently verify CI. The separate
[record reader and explicit poster](review-records.md) verify publication identity through GitHub. Partial, errored,
shadow, prospective-tooling, and missing-context results are visibly advisory.

The snapshots are raw Git source bytes, without `.git` metadata, checkout filters, generated
build trees, or inherited Git-directory overrides. Candidate/context symlinks and submodules
are rejected. Pinned dependency symlinks are preserved only when their complete chain resolves
to an ordinary file inside that exact dependency tree; escaping, dangling, directory, and
cyclic links are rejected. Their targets are listed in the evidence report. Source files are
read-only, and no Lean build or candidate program runs during review preparation.

Preparation caps materialized source bytes at 512 MiB and checks for a 2 GiB free disk reserve.
It copies no `.lake` build cache. Temporary source trees are removed afterward unless
`--keep-workspace` is requested.

## One engine, installed resources

`sphereceti.local_review.run_review` is the shared adapter entry for callers. The project CLI
calls it; future worker/CI adapters should call the same entry. A fresh interpreter imports
the packaged TauCetiReview engine and invokes its existing `main` with fixed `--no-post`
arguments. It does not call the upstream CLI or any upstream workflow. The eight legacy
launchers and archive sync imported in #9 remain disabled.

The wheel and source distribution bundle the engine, prices, ten rubrics, reference material,
project overlays, import manifest, and upstream license. Resource lookup is anchored to the
installed package, with a module-anchored development fallback; the caller's cwd cannot supply
rubrics or project identity. There is no mutable upstream `main` fallback.

Two explicit prompt overlays adapt the upstream shared protocol and scope rubric to
SphereCeti's roadmap-package role and approved-evidence boundary. The original rubric files,
reference credits, and all upstream tests remain unchanged. Exact TauCeti imports, namespaces,
and mathematical destinations keep their names. Effective prompt bytes and installed tooling
have separate full content digests in the evidence record.

The engine subprocess receives only selected provider credentials and basic process settings,
never GitHub credentials or unrelated environment secrets. Each provider uses upstream's
private credential home and read-only tools. The adapter refuses upstream's fallback to a
personal home/config when subscription credentials cannot be isolated. In that case use
supported isolated credentials or API authentication. The Python engine may launch only the
selected provider CLIs; GitHub, archive, and merge subprocesses are rejected. Raw provider
console streams are not retained in the adapter's artifacts.

Codex tool commands keep upstream's `shell_environment_policy.inherit=none`. Following
TauCetiReview [#196](https://github.com/TauCetiProject/TauCetiReview/pull/196)
([8cb4374](https://github.com/TauCetiProject/TauCetiReview/commit/8cb4374133d429627c31d9835bfe6fc9d71771e9)),
the engine then restores exactly two runtime variables for the Linux sandbox launcher: `PATH`,
so it can find the system `bwrap`, and a private per-attempt `TMPDIR` inside the throwaway
reviewer home, so its bookkeeping works when the host `/tmp` is read-only. Neither carries a
credential, and the model's tools stay read-only, including inside that directory.

## Codex sandbox diagnostic

When a Codex review fails before inspecting any source, run the diagnostic adapted from
TauCetiReview [#194](https://github.com/TauCetiProject/TauCetiReview/pull/194)
([51149da](https://github.com/TauCetiProject/TauCetiReview/commit/51149da792cd8b28aba617f118d1ae01aefbe501))
and #196 **in the same host, container, and account that runs reviews**:

```bash
uv run --locked sphereceti review-check-sandbox --compare-path --compare-tmpdir
```

It calls the native `codex sandbox` directly in the reviewer's clean environment: no API key,
no copied subscription login, no model inference, and no GitHub access. The probe checks that a
known file is readable and a workspace write is denied, then removes its scratch files. By
default it probes a fresh private directory under the operator's review storage; `--cwd DIR`
probes an existing workspace instead. The JSON report records the Codex version, relevant
Linux kernel settings, the system `bwrap`, and the actual launcher or sandbox error.
`--compare-path` adds an empty-`PATH` probe and `--compare-tmpdir` a system-`TMPDIR` probe;
`path_restoration_fixed_sandbox` or `private_tmpdir_fixed_sandbox` is true when only the fixed
environment works. The command exits 0 only for a healthy probe. A failed report never relaxes
the sandbox; namespace, AppArmor, and Seatbelt denials must be investigated on that host.

This is an operator-run advisory tool, not the build sandbox or a sandbox for hostile Python.
Provider processes retain their provider-specific authentication and isolation limits. The
adapter's restrictions do not authenticate review records or make them merge authority.

## State, modes, and output

The default output is a new run directory under the operator's storage; `--output` must name a
new directory. `evidence.json` records source selection. `result.json` adds completion, mode,
verdicts, and engine status. `record.json` and `record.md` carry a strict attestation proposal;
only API-authenticated publication can supply an authorized review record. `advisory.md` presents the review with an advisory heading and
without upstream scoreboard markers. Dry runs create the evidence and result records only.

The existing upstream case-file and budget ledger is private local state. A repository-wide
lock serializes reviews and remains held by the engine subprocess. Changes to effective
context, tooling, dependencies, or the diff base invalidate cached verdicts while preserving
spend and round history. Candidate head changes use upstream's normal staleness rules.

`--rubrics naming,correctness` selects a subset in canonical upstream order. `--mode manual`
forces the selected rubrics. `--mode reply --reply-rubric correctness --reply-file reply.txt`
passes an untrusted contest through the upstream reply path; `--replies-json` accepts its
existing author-reply format. Upstream may continue through previously unreviewed rubrics when
a reply clears the last blocker. A subset or explicit reply run stays partial/advisory.

`--shadow LABEL` starts a fresh manual comparison arm, retains its archive locally, and keeps
normal case files intact. Executed arms additionally require `--shadow-budget-usd`; see
[evaluation](evaluation.md) for comparisons, labels and the allowance within the shared daily cap. Its spend is checkpointed into the shared daily ledger after each
attempt, including unsuccessful runs. No archive is pushed. Daily and per-call reservations
use upstream cost estimates; they are not a provider-enforced billing limit. Provider failures
are errors, never approvals. Execution has a 30-minute limit and terminates its process group
on timeout or interruption. Each provider attempt also has its own `--attempt-timeout` (default
600 seconds); see [when the worker stops spending](worker-execution.md#when-the-worker-stops-spending).

## Codex model selection and accounting

`sphereceti review` uses `gpt-6.1-sol` when Codex is selected. Use `--codex-model MODEL` to
choose a different model. The contributor CLI pins that choice, including the default.
[`worker run --execute`](worker-execution.md) uses the engine's `gpt-5.6-sol` default with
automatic Terra fallback unless the worker operator pins a model. Every dispatchable model must have a row in
`runner/prices.json`; an unpriced model is rejected before any inference. The table carries
the gpt-6 family from TauCetiReview [#172](https://github.com/TauCetiProject/TauCetiReview/pull/172)
([baf2e68](https://github.com/TauCetiProject/TauCetiReview/commit/baf2e680b43369805621e6ff0b6c984cab5e4ccb)),
so `--codex-model gpt-6.1-sol` (Sol61: 2.00 input, 0.10 cached input, 10.00 output per million
tokens) is accepted. The corrected rates and cache-write rates of
[#175](https://github.com/TauCetiProject/TauCetiReview/pull/175)
([4684a52](https://github.com/TauCetiProject/TauCetiReview/commit/4684a52a03859a5e22ba2af736720426de373e1f))
also apply, including `gpt-5.6-sol`'s 2026-08-21 window.

Codex reports no dollar figure, under either authentication mode. A subscription-backed run
therefore records `cost_estimated: true` and charges the shared daily budget the dated
list-price estimate of its measured tokens. This is a budget guard, not a statement of
subscription billing. The budget is a stop threshold checked before each rubric; see
[when the worker stops spending](worker-execution.md#when-the-worker-stops-spending).
Following [#148](https://github.com/TauCetiProject/TauCetiReview/pull/148)
([7f1d288](https://github.com/TauCetiProject/TauCetiReview/commit/7f1d28863dcd914f3bcc2ae1d9e2b7ee42a96441)),
round token totals use one convention across providers: `input_tokens` is all input traffic,
with fresh, cache-read and cache-write components. Archived runs keep the provider's raw
usage and exact model.

## Validation and next boundary

Regression fixtures use exact disposable Git commits and a fake provider executable. They
exercise approved/proposed evidence, missing context, dirty trees, replacement refs, source
links, partial/budgeted reviews, contests, shadow accounting, and provider failures. Both fresh
wheel and source installations run a dry review and all ten rubrics outside the checkout with
conflicting cwd resources and credential canaries. A fake Codex executable checks the
subscription-login isolation and restored launcher runtime through the full adapter, and the
sandbox diagnostic's credential-free probes and cleanup. The 18 imported upstream test scripts
also continue to run without external calls.

The [record adapter](review-records.md) adds API-authenticated review records and explicit
policy-gated posting. Shared merge observation will combine those records with #8’s mechanical
evidence. All infrastructure lands before the mathematical roadmap in #1.
