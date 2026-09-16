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
# No provider calls: identify and verify the exact PR, approved context, and dependency sources.
uv run --locked sphereceti review 1 --dry-run \
  --source-repo . --dependencies-dir .lake/packages

# Explicit local advisory review using an operator's configured subscription.
uv run --locked sphereceti review 9 --provider codex --budget-usd 5 \
  --source-repo . --dependencies-dir .lake/packages
```

The same commands work with an installed `sphereceti` executable outside the checkout.
`--operator-config preferences.toml` accepts the existing provider, budget, and storage
preferences. A real review requires an explicit provider and positive budget; the default
preferences spend nothing. `--auth api` uses the selected provider's API credential instead.
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
on timeout or interruption.

## Validation and next boundary

Regression fixtures use exact disposable Git commits and a fake provider executable. They
exercise approved/proposed evidence, missing context, dirty trees, replacement refs, source
links, partial/budgeted reviews, contests, shadow accounting, and provider failures. Both fresh
wheel and source installations run a dry review and all ten rubrics outside the checkout with
conflicting cwd resources and credential canaries. The 16 original upstream test scripts also
continue to run without external calls.

The [record adapter](review-records.md) adds API-authenticated review records and explicit
policy-gated posting. Shared merge observation will combine those records with #8’s mechanical
evidence. All infrastructure lands before the mathematical roadmap in #1.
