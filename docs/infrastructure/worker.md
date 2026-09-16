# SphereCeti worker planning

This worker is independently authored under SphereCeti's [Apache-2.0 license](../../LICENSE).
The high-level maintenance-before-new-work idea and strict targeting behavior were informed by
[the TauCetiWorker contributors' README at `27c234a`](https://github.com/kim-em/TauCetiWorker/blob/27c234a5722cfe557279aa47fbfd8e51450481a6/README.md).
No TauCetiWorker implementation, prompts, tests, or assets are copied or relicensed. The source
ledger records this as `reference-only`, with upstream reuse terms still unresolved. The
planned Worker source import is superseded by this independent implementation.

SphereCeti has one cohesive roadmap. There are no area selectors, per-dimension worker fleets,
or random roadmap selection. Existing README prose and target signatures remain authoritative.
An optional work frontier is a disposable set of estimates derived from that single roadmap;
it is neither a second specification nor a required annotation format for mathematical PRs.

## Review and dependency boundary

Review `worker.py` (validation and ranking), then `worker_cli.py` (read-only survey),
and `tests/test_worker.py`. The preceding layers supply the installed profile and shared
reviewer. The execution layer adds guards and leases around that reviewer.

## Commands

```bash
# One observation; no persistent loop or execution.
sphereceti worker plan
sphereceti worker plan --pr 9,11 --json

# Export a complete or strictly targeted survey, then replay it offline within 15 minutes.
sphereceti worker survey --pr 9 --json > survey.json
sphereceti worker plan --snapshot survey.json --pr 9 --json
```

Live surveys authenticate the operator with `gh api user` and query only the configured
SphereCeti repository on `github.com`. Maintenance advice applies to that operator's own PRs.
A targeted survey fetches only its named PRs, including closed ones, rather than scanning the
queue. Each survey has a 60-second total request budget and 45-second per-request timeout;
there are at most 25 targeted PRs. An unrestricted survey requests 101 records and rejects
queues larger than 100 instead of silently treating a truncated queue as complete. Use a
smaller explicit target set in that case.

`--pr` accepts repeated positive numbers or comma lists, with optional `#` prefixes. Empty,
malformed or excessive targeting fails before querying. Targeting only removes work. A
snapshot of specific PRs cannot become an unrestricted plan or cover additional PRs. A
missing target in a complete open-queue snapshot yields a per-PR explanation, with no fallback;
a missing target during a live query aborts. Closed or merged PRs receive no recommendation.

API failures, malformed/duplicate JSON fields, destination mismatches, duplicate PRs and
stale observations exit 2 without a plan. A confirmed empty observation is distinct from
missing or unreadable data. Offline input never invokes GitHub or a provider. Survey and
frontier observations expire after 15 minutes; future timestamps are rejected. These times
are caller assertions in imported snapshots, not authenticated evidence. Worker JSON files
are limited to two million characters. Command errors do not print raw API responses or credentials.

## What is recommended

The implemented priority is:

1. Investigate conflicts on the operator's PRs.
2. Investigate failing CI on the operator's PRs.
3. Ask the shared reviewer to assess whether review work is needed on observed green,
   non-draft PRs with known mergeability.
4. Consider ready work from the single approved roadmap's optional frontier.

Within each PR category, older updates come first, then PR number. Draft PRs can receive
maintenance advice but not review-assessment advice. A green check summary is only a hint:
this planner does not know required checks, trust their publishers, inspect accepted review
records or prove that a review is needed. Neutral, skipped, absent and potentially capped
check summaries do not become all-green. The execution adapter must re-read the exact
head/base, invoke the existing review/gate logic, account for provider availability and
budgets, and exclude already satisfied work before dispatch. No paid provider is queried.

Dependency-graph repair, progress generation and review-response repair are explicitly
reported as deferred stages, pending their existing adapters and authenticated evidence.
They are not silently inferred from branch names, labels or untrusted review text. An unknown
mergeability/check summary yields no review recommendation for that PR; it does not claim
the entire queue is empty. Other observed work can still be recommended.

Every plan includes `advisory_only: true`, `executable: false`, exact PR head/base commits, a
source-input digest and diagnostics. A recommendation is **never an executable ticket or
permission to write**. All automation policy switches remain false. There is no authoring,
provider dispatch, review posting, state publication, lease acquisition, forking, merge,
background service or repository-setting change in this PR. The output does not authenticate
its operator, prove snapshot completeness or establish current server state.

## One optional roadmap frontier

The current scaffold has `roadmap_approved = false`, so it cannot recommend mathematical
work even if a frontier is supplied. The production adapter also remains absent. Once the
roadmap is approved through the normal project profile, a reporting tool or operator can
supply this **advisory** JSON through `worker plan --frontier frontier.json`:

```json
{
  "schema": "sphereceti.worker-frontier/v1",
  "repository": "thefundamentaltheor3m/SphereCeti",
  "implementation_repository": "thefundamentaltheor3m/Sphere-Packing-Lean",
  "roadmap_revision": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
  "implementation_revision": "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",
  "document": "README.md",
  "targets": "SphereCetiRoadmap/Suggested.lean",
  "observed_at": "2026-09-12T12:00:00Z",
  "items": [
    {
      "id": "packing-api-adapter",
      "summary": "A small packing API adapter",
      "reference": "README.md#layer-1--packing-api-preservation-and-import-hygiene",
      "status": "remaining",
      "effort": "small",
      "depends_on": [],
      "blocked_by": []
    }
  ]
}
```

This is a format example, not an actual task assessment; replace the example pins and time
with observations. No live frontier is committed. Each item cites a heading in the existing
README. Identifiers are local to the disposable frontier. Estimates cover the whole remaining
roadmap, with no area field/filter. The planner requires exact full roadmap and implementation
revisions but does not fetch/verify those revisions, headings, completion assertions or the
completeness of the index. Its output always records `source_verified: false`; production
execution must independently validate approved sources and current completion evidence.

An item is ready only when it is `remaining`, has no explicit blockers, and all listed
prerequisites are `complete`. `active` work and descendants of unfinished work are excluded.
Unknown prerequisites, duplicate IDs and cycles anywhere in the graph fail. At most 1,000
items are accepted. Among ready items, estimated `small`, `medium`, `large`, then `unknown`
effort ranks first; within the same estimate, prefer work with more immediate remaining
dependents, then stable ID. This favors useful low-hanging work without allowing a cheap but
blocked task to jump over its prerequisites. Effort is an estimate, not a theorem-complexity
measurement. Mathematical recommendations name Sphere-Packing-Lean as their destination.
Strict PR targeting always excludes all frontier work.

The frontier remains optional and provider-free. Automatic extraction, mathematical
completion verification and source-approved authoring belong to later production integration;
this PR does not rewrite the roadmap into a task database or add mathematical implementations.
