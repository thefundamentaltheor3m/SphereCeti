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
preferences. For local subscription reviews they live in `~/.config/sphereceti/operator.toml`:

```toml
provider = "codex"
budget_usd = 5
```

`sphereceti review` and `sphereceti review 9` use those preferences.

## First run and `sphereceti setup`

A new contributor needs only the installed `sphereceti`, a signed-in `gh`, and a signed-in
provider CLI (for example Codex). When a review that will call a provider is about to start,
and there is no `--operator-config`, no `~/.config/sphereceti/operator.toml` and no
`--budget-usd`, the CLI asks once:

```text
SphereCeti needs two review preferences before your first review.
Review provider (claude, sonnet, codex, kiro, deepseek, minimax, grok) [codex]:
The budget is a daily threshold in estimated dollars, checked before each rubric; it is not a cap on subscription usage.
Daily budget threshold in estimated USD [5]:
Saved review preferences to /home/you/.config/sphereceti/operator.toml. Change them with `sphereceti setup`.
```

It then continues the same review. An invalid answer is asked again, up to three times; end of
input or a third invalid answer stops with exit 2 and saves nothing. The file is created with
mode 0600 (a new directory with mode 0700) and is never overwritten. Prompts and messages go to stderr, so
`--json` output stays clean. `--provider` becomes the offered default provider.

- **Only on a terminal:** both stdin and stdout must be TTYs. Otherwise nothing is asked and
  the command exits 2 with one line:
  ``sphereceti: no review preferences yet; create them with `sphereceti setup --provider codex --budget-usd 5` (or pass --provider and --budget-usd)``.
- **Never for** `--dry-run`, `--read-records`, `--auth api`, `--shadow`, an explicit
  `--operator-config` or `--budget-usd`, or when the saved file exists. Bare `review` asks only
  after it has chosen a PR, so "No PRs need your review" never needs preferences; a batch asks
  once, before its first review, and uses the answer for every item.
- **No model preference.** The preferences schema has only provider, budget and storage, so the
  model is not asked or saved; `--codex-model` pins one per run.

`sphereceti setup` changes the preferences later. It shows the current values and offers them
as defaults, asks for whatever `--provider` and `--budget-usd` leave open, keeps a saved
`storage`, and rewrites the file atomically with mode 0600. With both flags it needs no
terminal, which also suits scripts: `sphereceti setup --provider codex --budget-usd 5`.
`--operator-config PATH` selects another file. Bad values change nothing and exit 2. The budget is a daily estimate threshold,
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

A posting review reads the PR's comments before inference. It carries every unanswered
`/sphereceti contest <rubric>` reply into that rubric's prompt, as quoted data together with the
finding it disputes, even after the head has moved. The record's details then say whether each
reply was considered and whether the finding still stands. See
[contesting a finding](review-records.md#contesting-a-finding-in-an-ordinary-comment).

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

   A daily budget stop keeps the run local, even with `--post`. The CLI saves any completed
   findings and explains why it skipped publication. Run the review again when budget is available.
   Other eligible partial runs can publish an advisory record. A run that was
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

## Approvals by opted-in maintainers

A maintainer runs `sphereceti review N` (or bare `review`) once. If the PR qualifies and every
rubric approves, the CLI also submits a formal GitHub **APPROVE** under that maintainer's own
account. A separate CI merge step, not this CLI, lands the PR. There is no bot account, and the
CLI has no merge path.

**Policy.** Approved main's `policy/automation.toml` gates it with two fields, both optional when
parsing (absent means off and empty):

```toml
approving = true             # the switch
approving_reviewers = [...]  # "user:ID" maintainers, a subset of authorized_reviewers
```

Since 2026-11-25 approving is on, and every authorized reviewer is opted in (each confirmed by the
maintainer). A later reviewer is added by a one-line policy PR once they agree. `--no-approve` opts
out for one run.

**Guards before inference, in order** (inside the review claim, after evidence preparation):
`--no-approve` not given; the record is being posted (not `--no-post`, a dry run, or posting
degraded by policy); approved policy available at T; `approving = true`; your `gh` identity
(`user:ID`) is in `approving_reviewers`; you are not the PR author. When all hold, the CLI prints
`If all rubrics approve and this PR qualifies, I'll submit your GitHub approval.` before any
model call. Otherwise it prints nothing then, and the result names the first failing guard.

**After the review, in order**, stopping at the first failure:

1. The record was posted and confirmed under your identity.
2. The review is complete, with no stop, and all ten rubrics approve.
3. Confirmed readback through the official reader (`assess_records`, the `--read-records`
   semantics): `review_safe`, for this exact head and base, with your posted comment selected. An
   author contest on your earlier record that this record leaves unanswered therefore blocks the
   approval. The PR's head and base are re-read and must be unchanged.
4. The read-only decision (`sphereceti auto-approve-check`, `auto_approval.py`), never
   hypothetical, must say `would_approve: true` for the same head and base. It covers scope (only
   library modules under `SphereCeti/`, never the root or the protected files), the
   trusted build and its tooling attestation, the compiled audit, the independent reviewer and
   the PR state.
5. If your current review state already approves this head, nothing is written. As in the merge
   controller, your current state is your latest `APPROVED`, `CHANGES_REQUESTED` or `DISMISSED`
   review, so a later change request supersedes an earlier approval.
6. One `POST repos/<repo>/pulls/N/reviews` with `event = APPROVE`, `commit_id` = the exact head,
   and a short body linking the review record. A failed or ambiguous POST is reported and never
   retried; check the PR before rerunning.

**Reporting.** The text result reports both outcomes separately:
`Posted: <url>` / `Not posted: <reason>` and `Approval: submitted <url>` /
`Approval: not submitted: <reason>`. Reasons include `--no-approve`, `approving is off in the
approved policy`, `you (user:N) are not opted in`, `you are the PR author`, `not all rubrics
approve (naming)`, `readback did not accept your record ...`, and `the auto-approval decision
refused (<its reasons>)`. `--json` carries `approval` (`state`: `submitted`, `existing` or
`not_submitted`, with `reason`, `decision_reasons`, `review_id`, `url`); bare `review` also
repeats it at the top level. `--no-approve` posts the findings and leaves the merge decision to
the maintainer. Batch items (`review --new/--revised/--all`) and bare `review`, including its
stack-aware selection, go through the same approval inside the same claim, and each batch item's
line says when an approval was submitted.

The merge controller counts this approval only as it counts any other: a current `APPROVE` on the
exact head, by a maintainer in `approving_reviewers` who is not the author. The CLI approves only
the head it just reviewed; whether an approval still counts after the head moves is the merge
controller's rule, not the CLI's.

## Review-in-progress claims

A review that will post announces itself so contributors do not race each other. The claim is
**advisory coordination only**: it grants no review or merge authority and needs no
`authorized_reviewers` entry. Dry runs, `--no-post`, `--read-records`, local-source, shadow
and reply runs, and runs whose posting policy degraded to a local record, post no claim.

**Budget first.** Before posting a claim, the run applies the engine's own check before each
rubric: today's recorded spend plus one `--max-call-cost` reservation must fit the daily budget.
If not even the first rubric can start, nothing is posted: the PR stays silent and the run
reports the budget stop as usual (`Not posted: daily review budget reached (run saved locally)`).

**Marker.** After evidence preparation and before any provider call, the run posts one PR
comment under your `gh` identity:

```text
<!--sphereceti-review-claim:v1 {"actor":"user:7","base":"…","claim":"<32 hex>","detail":null,"expires_at":"2026-11-23T15:35:00Z","head":"…","login":"yvonne","pr":50,"repository":"thefundamentaltheor3m/SphereCeti","started_at":"2026-11-23T15:05:00Z","state":"in_progress"}-->
Reviewing 8cdec1b now · `yvonne` (started 15:05 UTC, expires 15:35 UTC)
```

Logins are rendered as code, never as `@` mentions: GitHub does not notify you of your own
mention, but an edited claim that mentioned another contributor (`yielded to ...`) would notify
them for nothing.

The notice shows the selected provider and model, including defaults. On completion it shows
the models recorded for the attempts and the estimated USD cost of this run, including retries.
Subscription estimates use list prices. Missing usage is displayed as unavailable.

The claim lasts `TTL = 1800` seconds, the review's whole-run deadline (`RUN_TIMEOUT`).

**Live claims.** A claim counts only if it parses strictly, its GitHub comment author is its
`actor` (`user:ID` from the API; a forged or relabelled claim is ignored), its state is
`in_progress`, it names the PR's current head, and it has not expired. Its expiry must also lie
within 30 minutes (plus 60 seconds of clock slack) of the comment's GitHub `updated_at`, so no
claim outlives one run. Claims on an older head, expired claims and claims edited to
`finished`, `abandoned`, `yielded` or `paused` are ignored.

**Race rule: post, then confirm.** Before posting, a live claim by another contributor stops
the run (below). After posting, the run reads the readback and then all PR comments again
(paginated; an incomplete or duplicated listing fails closed, before any spend, and the claim
is marked abandoned). The **earliest live claim wins: lowest comment ID**, then `created_at`.
If another contributor's live claim is earlier, the run edits its own claim to
`yielded to <other>` and stops with nothing spent: explicit `review N` exits 2; bare `review`
records the PR as skipped (`claimed`) and moves on to the next candidate (with `--output`,
later attempts use `<output>-pr<N>`). If yours is earliest, the review proceeds.

**Before selecting.** Bare `review` skips PRs with another contributor's live claim on the
current head: `#50 review in progress by @alice, 12 min left`. Explicit `review N` refuses
(exit 2) with `PR #50: review in progress by @alice, 12 min left; rerun with --force-claim to
review anyway`. `--force-claim` reviews anyway: it ignores other claims before selection and
in the race, and still posts its own.

**Batches** (`review --new/--revised/--all --limit N`) claim each item the same way; a PR refused
or yielded for another contributor's claim is skipped with that reason and the batch continues.

**Your own live claim** on the same head (a re-run after a crash, say) is never a blocker:
the run refreshes your earliest live claim in place, with a new claim ID and a fresh 30-minute
expiry, instead of posting another comment. It keeps that comment's position in the race.

**On finish** the run edits the same comment, never adds another: `finished: <link to the
posted review record>` for a complete, posted review; `Review paused · k of N rubrics completed
(daily budget reached)` when the daily budget runs out partway (the record stays local, as for
any budget stop; the paused claim is no longer live, so others are not blocked); and
`abandoned (<reason>)` for an error, timeout, unknown-usage stop, another partial review, a
failed publication, Ctrl-C or SIGTERM. If that edit fails, the result says so (`Claim comment N could not be marked finished
(...); it expires on its own at HH:MM UTC.`) and the claim simply expires. `--json` reports
the outcome under `claim` (`comment_id`, `url`, `state`, `detail`, `edit`, `expires_at`).

**Claims and official worker leases are independent.** The worker's leases
(`worker_leases.py`) use `<!--sphereceti-worker-lease:v1 `; claims use
`<!--sphereceti-review-claim:v1 `. Each parser ignores the other's marker, and review-record
readers ignore both. Claims follow the leases' design (strict marker JSON, API comment-author
identity, post-then-confirm with the earliest comment winning) but differ where advisory
coordination needs it: anyone may claim, and a claim is one comment edited in place rather
than an append-only chain. The official worker does not wait for contributor claims. That is
the conservative choice for authority: an unauthenticated contributor comment can never delay
or block authorized review, and the worker's behaviour is unchanged. Contributors likewise
ignore worker leases; at worst an advisory review duplicates an official one.

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
| `waiting_on_parent` | A stacked PR whose parent (or an earlier ancestor) is not review-satisfied (below). |
| `awaiting_refresh` | Only a fresh trusted run is missing (a build from before tooling attestation). |
| `reviewed` | It already has an accepted review of this head (below). |
| `reviewed_by_you` | You already published or produced a complete review of this head. |
| `claimed` | Another contributor's live [review claim](#review-in-progress-claims) is on this head. |

"Already reviewed" is checked per exact head **and** base:

- **Accepted review:** a PR comment holds an unedited, complete, non-advisory commit/manual
  review record for this PR's current head and base, published by an identity in the installed
  policy's `authorized_reviewers` (the same records `review --read-records` reads). An
  authenticated contest newer than that record, not yet answered by its publisher, reopens the
  PR. So does an unanswered [author contest](review-records.md#contesting-a-finding-in-an-ordinary-comment)
  written as `/sphereceti contest <rubric>` in an ordinary comment, whatever head it was
  written against. Selection does not recompute tooling, context or engine digests (that would mean
  materializing every candidate's sources); the record reader still checks them all.
- **Carried over from an older head:** when the only commits since a reviewed head are "Update
  branch" merges of main, the PR's own change is identical, and no review input changed on main,
  the older review is current ([rule](merge-controller.md#per-pr-actions-stale-build-versus-stale-review)).
  The reason ends with `current (carried over from <H1> via update-branch)`, and no fresh review is
  asked for. Selection reads this through GET-only API calls (commits, trees and compare); any
  doubt means no carry-over.
- **Reviewed by you:** a complete commit/manual record for this head and base that you posted
  (comment author login equals yours, advisory or not), or that you produced locally: a
  `record.json` under your storage's `runs/`, or a record in the local archive journal, which
  also covers runs with `--output`. Dry runs, partial and errored runs do not count. A local
  record that was never posted is published with
  [`review-publish`](#publishing-a-saved-run), not by reviewing again.

**Stacks.** A PR whose base branch is not `main` is stacked. Its parent is the open PR whose head
branch is that base (a same-repository head is preferred; a fork head with that branch name
counts when it is the only one), and its chain runs up to the root PR that targets `main`. The
survey (`worker-survey/v4`) carries each PR's base and head branch names, so this costs no extra
read; only a base branch that no open PR heads costs one read, to tell a merged parent apart. A
stacked PR is eligible only when every open ancestor is **review-satisfied**: an accepted,
complete, non-advisory record on the ancestor's current head with all ten rubrics approving, or
the ancestor is merged. Otherwise it is skipped as `waiting_on_parent` with the nearest
unsatisfied ancestor: `waiting on parent #63 (9/10 on its head)`, `(no review on its head)` or
`(not ready)`, and `waiting on ancestor #63 (...)` further up. Review effort thus goes to stack
roots, whose approval unblocks their children.

**Priority** comes from the planner. Every eligible PR is at the `review-assessment` stage, so
they tie. Among them, **stack roots that block the most descendants come first** (the rationale
says `unblocks 3 stacked PRs`); then the planner's tie-break decides: **longest waiting first**, by the PR's GitHub
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
once, with the same survey, planner and readiness rules as bare `review`, and reads each candidate
PR's comments. By default it fits on about one screen:

```text
Queue: 1 ready to merge · 19 revised · 26 new · 28 waiting on parents · 32 awaiting CI
Ready to merge:
  #57 erin  Prove the theta identity  (approve + merge)
Revised since your review:
  #64 CBirkbeck  Prove that the even presented lattice has no roo…  (author replied, unblocks 3)
  #66 bob  Prove the contour deformation
  … and 17 more (sphereceti reviews --all)
New to you:
  #121 CBirkbeck  Prove that the Fourier transform preserves radia…  (unblocks 2)
  #55 carol  Prove the lower bound  (CI held)
  … and 24 more (sphereceti reviews --all)
28 PRs wait on a parent (biggest stacks: #64 ×3, #121 ×2, #132 ×2)
32 PRs await CI (2 held for a maintainer's approval)
Not ready: 6 yours, 5 failing CI, 1 conflicting
Also: 14 of your follow-ups not ready yet; 3 already reviewed (sphereceti reviews --all)
Next: sphereceti merge-ready --apply
```

- **Counts:** the first line counts each part of the queue.
- **Top PRs:** the actionable sections (Ready to merge, Revised, Author replied, New) list their
  top 8 in priority order, one short line each.
- **Tags:** a tag appears only when it changes what to do: `unblocks N`, `CI held`,
  `author replied`, `contested`, `history rewritten`, or the merge step.
- **Collapsed counts:** waiting on authors, waiting on parents, awaiting CI and not ready are one
  count line each.
- **Next:** the line suggests one command:
  - `sphereceti merge-ready --apply` when something is ready to merge;
  - otherwise `sphereceti review --revised --limit N` for your follow-ups;
  - otherwise `sphereceti review --new --limit N`.
- **Progress:** stderr gets one line, `Reading 84 open PRs… done in 26s`, which updates in place on
  a terminal.

`--all` prints the full listing below, every PR with its reason. `-v`/`--verbose` prints the same
and also each phase's progress lines. `--json` is unchanged.

```text
Review queue for yvonne (thefundamentaltheor3m/SphereCeti, observed 2026-11-23T21:29:38Z)
Ready to merge (2):
  #57 erin "Prove the theta identity" 4c1d2e3: approve + merge; no approval on this head; record https://github.com/thefundamentaltheor3m/SphereCeti/pull/57#issuecomment-12
  #153 arajasek "Give the Euclidean Leech lattice an even unimodular integ..." 5c590b4: waiting on CI (held: needs maintainer approval) (CI, Documentation and cache, Progress sources); no approval on this head; record <URL>
Accepted 10/10 but not ready to merge: #72 CI not done: build was cancelled on this head; re-run it; #150 stacked on leech-shells; merge its parent first
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

- **Ready to merge** (listed first, for maintainers): open PRs where all of these hold:
  - the base is `main` (not stacked);
  - an accepted official record approves all ten rubrics on the **current** head. It must be
    authorized, intact, complete and not advisory, by someone other than the author, with every
    author contest on that publisher's records answered;
  - CI passes on the current head apart from the expected `trusted-scope` human-review result
    (bare `review`'s review CI), and every check main's ruleset requires (today `build`) has
    completed and succeeded there. A cancelled run is not done;
  - GitHub reports it mergeable: not conflicting, and not `blocked` by anything other than the
    missing approval or a required check (for example unresolved review threads).

  Each entry gives the next step:
  - `approve + merge`: no formal GitHub approval of the current head by a non-author. An approval
    of an older head is shown but does not count;
  - `merge`: there is one;
  - `waiting on CI (held: needs maintainer approval)`: the latest run of a workflow on this head
    is `action_required`, which is how GitHub holds a fork PR's runs until a maintainer approves
    them. The held workflows are named.

  It also gives the formal approval state and the record link. PRs with such a record that fail
  another condition are listed after it with the reason (`ready_to_merge.not_ready` in JSON). The
  listing only reads; it never approves or merges.
- **Revised since your review:** your latest posted (unedited, commit/manual) record names an
  older head and the PR is ready, unless that review carries over through update-branch merges.
  Then the PR is done (`current (carried over from <H1> via update-branch)`), or, if you requested
  changes, it waits on the author with `no new change`. It shows the old and new short heads, the commits since (the
  compare API; a rewritten history is reported, never guessed), and author replies and contests
  posted after your record. These rank first.
- **Author replied:** your latest record names the current head and requested changes or
  blocked, and since then the PR author has replied (a comment by the author) or anyone has
  posted a contest. It links the newest reply. These rank right after revised PRs.
- **New to you:** exactly bare `review`'s eligible PRs.
- **Waiting on the author:** your latest record names the current head and requested changes or
  blocked, and there is neither a revision nor a response; it names those rubrics.
- **Awaiting CI, held:** wherever readiness says a fork PR awaits CI and the latest run of a
  workflow on its head is `action_required`, the reason reads `awaits CI: awaiting maintainer
  approval of workflow runs (<workflows>)`, and the summary counts them. Bare `review` words it
  the same way. A fork PR can also look ready to review while its `pull_request` workflows were
  never run: the rollup then holds only the `pull_request_target` runs, as on #153. Its entry in
  the sections above then ends with `CI held, awaiting maintainer approval of workflow runs
  (<workflows>)` (`held_workflows` in JSON).
- **Your follow-ups, not ready yet:** a PR you reviewed that was revised or answered but awaits
  CI, GitHub or a refreshed build is named on its own line instead of disappearing into the
  summary (`follow_ups_not_ready` in JSON).
- **Blocked by a parent:** each stacked PR whose ancestors are not review-satisfied, with the
  reason, grouped by stack root with the number of PRs that root unblocks, most first (your own
  PRs included and marked). These are left out of the sections above, so batches review roots
  first:

  ```text
  Blocked by a parent (5):
    stack #63 (unblocks 3): #64 waiting on parent #63 (9/10 on its head); #71 waiting on ancestor #63 (9/10 on its head); #116 waiting on parent #63 (9/10 on its head)
    stack #75 (unblocks 1): #115 waiting on parent #75 (9/10 on its head)
  ```

  Within the other sections, entries that unblock stacked PRs say so and come first.
- **Not ready:** the aggregated summary of bare `review`, with your own PRs counted. PRs that
  already have the review they need are listed as already reviewed.

Each entry gives the PR, author, title, short head, the reason and how long it has waited (since
`updatedAt`). `--json` prints `sphereceti.review-queue/v1` with `ready_to_merge` (`items`, each with `next_step`,
`record`, `record_publisher`, `approval` (`on_head`, `older_heads`, `changes_requested`),
`held_workflows`, `required_checks` and `mergeable_state`; `not_ready` with `reason`; and the
`required_checks` names), `sections` (`revised`, `author_replied`, `new`,
`waiting_on_author`, `not_ready`), `done`, `follow_ups_not_ready`, `not_ready_summary`, `main` and `order`. A failed
lookup (survey, comments, compare response, and for Ready to merge the branch rules, check runs,
workflow runs, PR and its reviews) exits 2 and lists nothing.

### How the queue is read

`reviews`, bare `review` and batches read the open queue in **one GraphQL pass**
(`sphereceti/bulk.py`). Two read-only queries run side by side, 50 PRs per page:
- the survey's fields, in exactly `gh pr list --json`'s shape, so readiness is computed by the same
  code;
- each PR's comments with their author ids, in the shape the record readers check.

They no longer read comments with one REST call per PR. On the live queue (53 PRs, 142 comments)
both match `gh pr list` and the REST comments exactly.

Per-PR REST reads remain only for what that pass cannot answer:
- trusted-scope provenance for the human-review exception;
- `compare` and commit reads for revised PRs and carry-over. Main's history is read 100 commits per
  listing, not one commit per request;
- held-run checks for fork PRs;
- the merged state of a missing stack parent;
- main's required checks, once;
- the PR, its reviews and its runs for Ready to merge candidates.

These reads run on a pool of 8 threads (`SPHERECETI_READ_WORKERS`), and results keep queue order.
One survey reads current main once, and each exact-commit compare once.

Results stay fail-closed:
- A PR with more than 100 comments has the rest read through REST, for that PR only.
- These all exit 2, as before: a queue that changes between pages, a GraphQL error, or any failed
  read.
- A read refused by GitHub's **secondary** rate limit is retried after 5, 15 and 30 seconds. Only
  reads are retried, never a write.
- An exhausted **primary** limit fails at once and says when it resets.

**Queue cache.** Facts that cannot change under their key are kept in the operator store
(`<storage>/<repo>/queue-cache.json`):
- a scope verdict, keyed by PR, head, base, head repository, current main, every status and check
  in the PR's rollup, and the packaged merge-checks settings;
- a commit's parents and tree;
- a compare of two exact commits;
- a merged stack parent.

Current main, the PR list, comments, reviews and runs are read fresh on every run. A failed read is
never cached. `--no-cache` (on `reviews` and `review`) neither reads nor writes the cache.

The worker survey shares the bulk pass and the pool, but never the cache. The merge controller,
`auto-approve-check`, the maintainer approval and posting do not use the cache or the bulk pass.
They keep their own fresh per-PR reads.

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

## Merge-ready sweep (maintainers)

`sphereceti merge-ready` does, as the invoking maintainer's own `gh` identity, what a maintainer
does by hand for each PR in Ready to merge. It updates the branch if it is behind, approves, and
merges, one PR at a time. **Without `--apply` it is a dry run**: it reads everything and prints the
plan, and writes nothing.

```text
sphereceti merge-ready                    # the plan
sphereceti merge-ready --apply --limit 3  # act: at most three merges
```

**Candidates** are the Ready-to-merge PRs (found through the fast queue path). It also takes PRs
whose accepted 10/10 record is on an older head that carries over to the current one through
update-branch merges, for example a PR this sweep updated earlier. They are taken one at a time,
stack roots first. A PR whose runs are held for approval is reported, not touched.

For each candidate, everything is first read again **fresh**, never from the queue cache:
- the PR: open, not a draft, base `main`, the same head as listed, not conflicting;
- its record, on this head or carried over to it;
- current main;
- how far behind main it is;
- its CI;
- its reviews.

Then:
1. **Behind main:** it updates the branch.
   - The call is `PUT pulls/N/update-branch` with `expected_head_sha` set to the listed head.
   - It waits up to 3 minutes for the new head, and then requires that the record carries over to it
     (#156's rule: update merges only, the same change, no review inputs changed on main).
   - It then waits for the required checks and review CI on the new head. The wait is bounded by
     `--wait-ci MIN` (default 20) and reads once a minute. A failure, a held run, or a timeout skips
     the PR with the reason.
2. **Approval:** if you have no approval of this head, it submits one APPROVE.
   - The approval is pinned to the head (`commit_id`), and its body links the record.
   - It never approves your own PR: that PR is skipped unless another maintainer has approved this
     head. It never approves over your own CHANGES_REQUESTED: that PR is skipped too.
   - Anyone else's outstanding change request also skips the PR.
3. **Merge:** `PUT pulls/N/merge`, `merge_method=squash`, `sha` = the head.
   - The head is read again just before the call; if it moved, the PR is skipped.
   - On HTTP 405 or 409 it reads the PR again, reports it and moves on. It never retries.
4. **Next PR:** the queue is read again before the next PR, since main has moved. The rest may now
   be behind, and step 1 handles them.

**Safety.**
- Before every merge, it looks for a live "reviewing now" claim on any open PR. A review in progress
  pauses the sweep, reading once a minute up to `--wait-review MIN` (default 30). After that the sweep
  stops with `a review is in progress on #N; rerun later`. An update is not made under a review of
  that same head.
- Any unexpected error, and any write it cannot confirm, stops the whole sweep. Every write is
  confirmed by reading the PR or the response:
  - the new head after an update;
  - an APPROVED review of that commit;
  - `merged: true` on the PR.
- Stacked, draft and conflicting PRs are never touched.

**After each merge**, it lists the open PRs based on the merged branch: `#X is stacked on #N (now
merged): retarget to main`, or `GitHub already retargeted it to main` when GitHub did.
`--retarget-children` changes only their base to `main`, through the API. It never pushes to anyone's
branch.

**Output.** One line per PR, then the accepted-10/10 PRs that are not mergeable (with the reason),
and a summary. Per-PR outcomes are `updated`, `approved`, `merged`, or `skipped: <reason>`. Progress
goes to stderr; `--quiet` hides it.

`--json` prints `sphereceti.merge-ready/v1`:
- `items`, each with `actions`, `outcome`, `reason`, `record`, and `updated_head` / `approval` /
  `merge_commit` where they apply;
- `children`, `not_ready`, `counts` and `stopped`.

Exit status is 1 when the sweep stopped, 2 when the queue could not be read, and 0 otherwise.

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
10/10 reviewed · blocked: scope · changes requested: api-design, documentation · posted <URL> · official
Next: author: address scope, api-design, documentation (see record); rerun after the head changes
```

The result block above it opens with `Review #N: <completion>`. Whether the record counts as
official or advisory is said once, on the summary line.

- **Counts:** rubrics with a verdict on this head out of those requested; `approve` when all of
  them approve, else `reviewed`. A review that stops early names the first blocking rubric and
  the stop reason from the run's receipt: `usage unknown` (the engine's usage stop), `provider
  unavailable (not authenticated|quota exhausted|rate limited)` from the archived attempts'
  error kinds, `provider failed to start` (every rubric ended without a verdict and without the
  model touching a file), `blocked on <rubric>`, an engine error, or `budget or round limit
  reached`. A complete review with findings says `blocked: <rubrics>` and `changes requested:
  <rubrics>`.
- **Posting:** `posted <URL> · official`, or `· advisory (<why>)`, `not posted: <reason>`, or
  `publication interrupted`.
  - Official requires both: the posted record itself is not advisory (its `advisory` field), and
    the publisher is an authorized reviewer. Authorization alone never makes it official.
  - The reasons come from the record's evidence. Examples: `installed tooling is not approved main;
    reinstall`, `partial`, `reviewed tooling is not approved main`, `missing approved context`,
    `not an authorized reviewer`.
  - `--json` carries `official` and `advisory_reasons`.
- **Next action:** `author: address <rubrics> (see record); rerun after the head changes`, naming
  every blocked rubric and then every rubric that requested changes, as on the summary line;
  ``run `sphereceti review-check-sandbox --compare-path --compare-tmpdir` `` after a provider
  startup failure; sign in again, wait for the usage window, or rerun later for a provider that
  is down; ``publication was interrupted; run `sphereceti review-publish RUN` `` (RUN is the run id
  under the operator store, or the run directory for an `--output` run, as `sphereceti review-publish`
  takes it); `rerun without --no-post to publish
  the record`; `run again without --dry-run to review`; or `none: every rubric approves`.

`--json` carries the same as `plan` (`line`, `pr`, `head`, `base`, `providers`, `models`,
`posting`) and `summary` (`line`, `reviewed`, `total`, `first_blocking`, `findings`, `stop`, `posted`,
`official`, `next_action`); bare `review` adds both at the top level of its selection report.

### Progress lines

During the long steps, `review` (explicit, bare and batches) and `reviews --verbose` write short
progress lines to **stderr**, each stamped with the local time. Plain `reviews` writes one line
instead: `Reading N open PRs… done in 26s`. Stdout keeps the plan, summary and `--json`
document unchanged. `--quiet` turns them off. They print on a terminal and off one (logs, CI), but
counters behave differently. On a terminal they overwrite one line, at most every two seconds.
Elsewhere they print every tenth item and the last, so a log never gets carriage returns.

```text
[19:02:11] Surveying open PRs… (49 open)
[19:02:41]   scope 10/49
[19:03:43] Surveying open PRs… done in 1m32s
[19:03:44] Preparing evidence for #63 at 9c587b5 (fetching pinned sources…)
[19:04:26] Evidence for #63 ready in 42s
[19:04:27] Posting "reviewing now" claim on #63…
[19:04:28] claim posted: https://github.com/thefundamentaltheor3m/SphereCeti/pull/63#issuecomment-1
[19:04:28] Rubric 1/10 correctness: running (codex gpt-6.2-sol (medium))…
[19:06:38] Rubric 1/10 correctness: approve (2m10s, est. $0.07)
...
[19:31:02] Posting record…
[19:31:04] posted https://github.com/thefundamentaltheor3m/SphereCeti/pull/63#issuecomment-2
```

- **Survey:** the open-PR count, then `scope i/N` as each PR's CI and trusted-scope provenance is
  read, then the total time.
- **`reviews`:** the survey, then `reading comments i/N`.
- **Evidence:** start and finish of the pinned source preparation.
- **Claim:** posted, refreshed (your own live claim) or yielded.
- **Rubrics:** a start line when the engine begins a rubric, with provider and model. A finish
  line gives its verdict, duration and cost (`est.` when the engine estimated it). A rubric
  already current at this head and not re-run says `reused`. The CLI polls the engine's own
  ledger: its write-ahead `in_flight` marker and each finished case file. The engine needs no
  callback, and the result is never affected.
- **Stops and posting:** `stopped early: <reason>` (e.g. `usage unknown`, `daily budget`), then
  `Posting record…` and `posted <URL>` or `record not posted: <reason>`. With maintainer
  approvals enabled, one more line says `approval: submitted` or `not submitted (<reason>)`.

Bare `review` still prints its selection line (`Reviewing #63 (head 9c587b5): …`) and batches their
`[i/N] #PR …` lines on stdout, as before.

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

`sphereceti review` uses Sol 6.2 (`gpt-6.2-sol`) when Codex is selected. Use
`--codex-model MODEL` to choose a different model, for example `--codex-model gpt-6.1-sol` for
the previous default.

Every Codex call also gets an explicit reasoning effort, `--codex-effort`, which defaults to
`medium`. It is passed as `-c model_reasoning_effort=<effort>`, which takes precedence over
`~/.codex/config.toml`, so a contributor's personal Codex configuration no longer changes a
review. Before, each review silently inherited that setting, and the model's own default was
`low`. The choices are `low`, `medium`, `high` and `xhigh`. These are the efforts that
codex-cli 0.171.0's bundled catalog lists for the Sol models, without `max` and without `ultra`,
which delegates to sub-agents that reviews withhold; `minimal` is not offered for them. Higher
efforts take longer, and the attempt timeout still applies. The plan line and progress lines name
the effort (`codex gpt-6.2-sol (medium)`). `result.json` records it as `codex_effort`, and the
engine request's argument list carries it too. It is not part of the review record marker or any
digest. Batch (`--new`, `--revised`, `--all`) and bare `review` use the same flag. `worker run`
has its own `--codex-effort`, also defaulting to `medium` (it previously passed none), and records
it in its receipt; its model default stays the engine's. The contributor CLI pins that choice, including the default.
[`worker run --execute`](worker-execution.md) uses the engine's `gpt-5.6-sol` default with
automatic Terra fallback unless the worker operator pins a model. Every dispatchable model must have a row in
`runner/prices.json`; an unpriced model is rejected before any inference. The table carries
the gpt-6 family from TauCetiReview [#172](https://github.com/TauCetiProject/TauCetiReview/pull/172)
([baf2e68](https://github.com/TauCetiProject/TauCetiReview/commit/baf2e680b43369805621e6ff0b6c984cab5e4ccb)),
so `--codex-model gpt-6.1-sol` (Sol61: 2.00 input, 0.10 cached input, 10.00 output per million
tokens) is accepted. SphereCeti adds a local `gpt-6.2-sol` row, effective 2026-11-17, at the same
standard and long-context (over 272,000 input tokens) rates, as listed on OpenAI's pricing page;
no upstream TauCetiReview change prices it yet. The corrected rates and cache-write rates of
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
