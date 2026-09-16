# Review cost analysis and human evaluation

**Adapted from the [TauCetiReview contributors](https://github.com/TauCetiProject/TauCetiReview),
Apache-2.0, at [afb424e](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b):**
[`runner/costs.py`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/costs.py)
supplies separate recorded/derived cost views and dated, cache-aware calculations;
[`runner/pricing.py`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/pricing.py)
and [`runner/prices.json`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/prices.json)
supply the price-window design;
[`runner/cli.py`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/cli.py)
and [`runner/review.py`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/review.py)
supply fresh shadow arms and isolated case state. The imported engine, prices, license,
manifest and upstream tests stay unchanged. SphereCeti independently defines its adapters,
comparison/label schemas and local interface.

[TauCetiData](https://github.com/TauCetiProject/TauCetiData) at
[e8e9154](https://github.com/TauCetiProject/TauCetiData/tree/e8e915472b02875f9a3864492616662c0c902876)
remains a source candidate with unresolved reuse terms. None of its `schema/`, `scripts/`,
`docs/`, records or historical blobs is copied. This implementation uses the licensed Review
route. This PR follows guarded execution #22, which integrates archive #19 and planner #21.
This sequencing makes changes to the shared reviewer lifecycle visible in one stack. Reporting,
profiling, lifecycle and merge-controller work remain separate.

## Offline front door

```bash
sphereceti evaluation costs --json
sphereceti evaluation costs --prices /path/to/dated-prices.json --json
sphereceti evaluation costs --prices /path/to/dated-prices.json --as-of 2026-09-12 --json
sphereceti evaluation pair --left EXECUTION_UUID --right EXECUTION_UUID --json
sphereceti evaluation show --pair PAIR_ID
sphereceti evaluation label --pair PAIR_ID --reviewer alice --choice A --json
sphereceti evaluation labels --pair PAIR_ID --json
# A correction is a new immutable record linked to that reviewer's current label.
sphereceti evaluation label --pair PAIR_ID --reviewer alice --choice tie --supersedes LABEL_ID --json
```

These commands never invoke a provider, GitHub, a shell, or a live review/merge reader. They
consume the validated archive journal by default; `--source` selects another local archive
snapshot. `--operator-config` selects the existing storage preference. Pair/label files live
under `storage/OWNER__REPOSITORY/evaluation/`, outside the archive outbox and operational state.
There is no evaluation publishing command or workflow. JSON reports can be redirected to a
local file; no command updates an existing database or archive record.

## Cost facts and explicit price inputs

`costs` validates every archive entry, collapses optional-text variants of the same execution,
and returns stable, sorted rows plus totals and per-mode groups. Distinct executions remain
separate, including retries of an entire review. Run and attempt usage/cost facts are retained.
Recorded run spend is summed once; attempt spend is not added again. Run-reported usage may
cover only the final attempt of a retry; the report identifies such coverage rather than
claiming complete token accounting. Missing cost/token fields stay unknown and every aggregate
reports coverage. Empty executions are counted explicitly. No archive producer data means no
claim of zero real spend. Cost-estimation flags and original price identifiers stay visible.

Repricing is optional and never changes recorded values, even for provider-billed costs. A
price file has this independently authored schema (the following rates/model are illustrative,
not current provider prices):

```json
{"schema_version":1,"models":{"example-model":[
  {"effective":"2026-09-01","input":"2","output":"4","cache_read":"0.5",
   "input_convention":"total"},
  {"effective":"2026-09-11","input":"3","output":"6","cache_read":"1",
   "input_convention":"total",
   "long_context":{"threshold":100000,"input":"5","output":"10","cache_read":"2"}}
]}}
```

Rates are USD per million tokens, parsed with decimal arithmetic. Windows must be strictly
increasing valid dates with finite nonnegative rates; duplicate JSON fields and unknown keys
are errors. Select the latest window effective on the recorded **run start date**, or on the
explicit `--as-of` forecast date. Never use today's date implicitly, extend the earliest price
backward, fetch a price service, or substitute an unknown model. The report records the exact
price-file SHA-256 and a digest of all semantic execution facts.

`input_convention: "total"` means input includes cached reads: subtract the cached subset
before pricing ordinary input. `"uncached"` means input excludes cached reads/writes: price
those buckets separately. It requires explicit cache-read and cache-creation counts, including
zero counts; positive cache writes also require `cache_write` pricing. Duplicate cache-read
aliases must agree. Reasoning-output tokens are retained as facts, not added again to output.
Above a long-context threshold, the higher rates apply to the entire request. The caller must
supply the correct accounting convention for its provider snapshot; the adapter does not infer
one from a model name. Missing/incompatible counts and missing windows produce an unknown
estimate with a reason, not zero. Multi-attempt or ambiguous dispatches are not repriced from
final-attempt usage because retry models/dates may differ. This is an analysis estimate, not
an invoice or a billing guarantee.

## Archive version and comparison constraints

New executions produce `sphereceti.archive/v2`: #19's evidence plus the producer's UTC start
time and explicit requested rubrics, auth mode, shadow label, context classification, daily
budget and shadow allowance. Producer auth/arm/mode must agree with the request. Ordinary
reviews conservatively say `prior_case_possible`; only isolated shadow stores say
`fresh_shadow`. Archive v1 remains readable and re-enqueues unchanged. It lacks run-time and
request evidence, so historical repricing/pairing reports the missing facts instead of
inventing them. The state-branch anchor remains v1. Older readers reject v2; upgrade approved
installed tooling before consuming mixed archives. The archive's exact-main writer check
prevents an outdated publisher from continuing after the approved tooling changes.

`pair` selects two explicit execution UUIDs, never guesses a favorable pairing. Both must be
v2 fresh shadows with distinct named arms, matching repository/PR, head/base/diff base,
dependency, engine/rubric/tooling/policy/context/description digests, tooling revision, auth
mode and requested rubric scope. Every requested rubric must have exactly one fresh run,
one successful attempt with an unambiguous model, and a valid verdict. Partial coverage,
reactivations, retries, failed runs and ordinary reviews are ineligible. A budget-limited
shadow cannot be relabeled as a complete comparison. The requested allowances may differ;
they constrain dispatch, and both executions must still satisfy full coverage.

Pair identity binds the complete immutable execution facts. Reversing selection order or
adding a text variant preserves identity. Showing or labeling a pair revalidates its exact
source records. Provider/model choices remain available in the source facts for analysis;
this is an explicit comparison contract, not proof that every possible experimental variable
was controlled or that a preferred response is mathematically correct.

## Human labels and paid generation

`show` requires both reviews' explicitly archived, redacted prose. Enqueue each completed
output with `archive enqueue --output PATH --include-text` first. The display uses stable A/B
assignment and hides model metadata; prose can still reveal a model, so this is not a
blinding guarantee. Inspect prose before opting it into an archive; pattern redaction cannot
remove every private fact. Merely pairing metadata does not include or publish text.

Choices are `A`, `B`, `tie`, `neither`, and `unsure`. Reviewer names are self-reported local
identifiers, not authenticated GitHub identities. Identical current labels are idempotent.
Corrections must name the current label ID and append a new record; stale/cross-reviewer
corrections, branched history, tampered bytes, and unknown fields fail closed. Per-store
locking serializes concurrent label updates. Old labels remain on disk. Label records contain
no free-form private notes, and no label is an accepted review record or merge signal.

Generating new paid evidence remains a separate explicit `review` command:

```bash
sphereceti review 19 --shadow model-a --provider codex --codex-model MODEL_A \
  --budget-usd 10 --shadow-budget-usd 2 --max-call-cost 0.2 --output /path/to/new-arm-a
```

An executed shadow now requires a finite positive `--shadow-budget-usd` at least as large as
`--max-call-cost`, in addition to the existing shared daily cap. The bridge bounds the engine's
cap using the actual ledger day balance at dispatch initialization, including a day rollover.
Shadow attempts still debit the shared budget immediately and retain the normal case files.
These are estimated dispatch limits; actual provider charges can exceed an estimate. A small
allowance can stop before all rubrics run. Dry runs spend nothing and do not require the extra
allowance. Shadow execution cannot combine with `--post`, live record inspection, or `--replies-json`
prior-contest input. This PR
runs only fake providers in tests and does not enable or launch paid evaluation.

## Validation

Tests cover dated/forecast pricing, cache conventions and long-context boundaries, unknown
usage, retries, duplicate accounting, legacy/v2 compatibility, every pair evidence binding,
context/auth/scope rejection, label corrections and concurrent-history conflicts, and rejection
by live review/archive schemas. Fake-provider integration checks the extra shadow allowance,
shared accounting, fresh context, and real pair generation. Fresh wheel/source installs use
the same CLI outside the checkout. Existing archive/review regressions and unchanged upstream
test scripts remain part of CI; the full Lean/audit/sandbox pipeline is unchanged.
