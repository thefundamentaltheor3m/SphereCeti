# Infrastructure PR sequence before the mathematical roadmap

Implementation plan, 2026-09-11. This translates the operator's `sphereceti-notes.md` into
independently reviewable SphereCeti infrastructure PRs. It does not change the mathematical
roadmap or authorize deployment of the automation.

**This infrastructure plan adapts the work of the TauCeti contributors.** Its build and audit
design comes from [TauCeti](https://github.com/TauCetiProject/TauCeti), its specification
discipline from [TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap), its review
engine and rubrics from [TauCetiReview](https://github.com/TauCetiProject/TauCetiReview), its
worker experience from [kim-em/TauCetiWorker](https://github.com/kim-em/TauCetiWorker), its
progress reporting from [TauCetiProgress](https://github.com/TauCetiProject/TauCetiProgress),
and its archive/evaluation design from [TauCetiData](https://github.com/TauCetiProject/TauCetiData).
SphereCeti's contribution is the project-specific integration and authority boundaries.
The source snapshot table below records exact commits and paths for the planned ports;
adapted code must retain its authorship, license, and source attribution.

The recommended first milestone is **I01–I07: separate build boundaries, trusted checks,
and an installable local review command**. Rebase and land the mathematical roadmap after
that milestone. The remaining infrastructure can also land before the roadmap, using test
fixtures and disabled operational entry points, but need not delay it.

## Starting point

Checked against GitHub and the local checkout:

| Surface | Inspected state |
|---|---|
| SphereCeti `main` | `32e7242c2de5a3547a2d5732af8d77d5877b97f7`; a dependency/build scaffold |
| Roadmap PR | [PR #1](https://github.com/thefundamentaltheor3m/SphereCeti/pull/1), open against `main` |
| Roadmap head | `1180f0f364cb7c0126a316ad990d4138fc0f8511`, branch `roadmap/initial` |
| Lean / TauCeti / Mathlib | `v4.34.0-rc1` / `8671bee98125933c56b9b00a08ded873b77dd23b` / `618f225e1ff4a6b2790a944e01b806b7c68bdc56` |
| Current roadmap build | `SphereCeti.lean` publicly imports both target files; one Lake library |
| Target namespaces | Already `SphereCeti.Suggested` and `SphereCeti.Pinned` |
| Existing admission check | Counts standalone `sorry` commands in immediate `SphereCeti/*.lean` files; the documented total is 282 |

The existing static checker is a useful signature/pin contract. Its textual count is not a
compiled axiom audit or a recursive module inventory. These are separate checks to add.

All implementation branches start from the then-current SphereCeti `main`, or name one
immediate infrastructure predecessor. They do not branch from PR #1. Use the IDs in this
document for infrastructure; retain the roadmap's A0–O4 production PR IDs.

## Preserve the roadmap's form and authority

Keep the authoritative root README, its Layers 0–11, the summit statements, conventions,
production migration sequence, and single `UPSTREAM.md`. Tools consume the existing prose
and target signatures. No per-theorem YAML, new task DSL, or mandatory machine annotations
are required. An optional derived work index belongs to tooling/state and records the
source revision; it cannot become a second specification.

The proposed Lean layout is:

```text
SphereCeti.lean                 # Existing admission-free scaffold/adapters
SphereCeti/
  Basic.lean

SphereCetiRoadmap.lean          # Separate target-signature aggregator
SphereCetiRoadmap/
  Suggested.lean                # Still namespace SphereCeti.Suggested
  Pinned.lean                   # Still namespace SphereCeti.Pinned
```

File/module names and declaration namespaces serve different purposes. Relocating the two
files does not require renaming the declarations or rewriting the mathematics. Keep
`Pinned.lean` frozen apart from necessary module references; delete it at the existing A2
handoff after production migration. Do not leave target-importing compatibility modules in
the audited `SphereCeti/` tree.

The notes' proved-development/staging proposal needs a separate scope decision. Under the
current repository instructions, substantive proofs still land in Sphere-Packing-Lean,
TauCeti, or Mathlib. These infrastructure PRs reserve a clean Lean boundary but do not open
SphereCeti to a second sphere-packing implementation. The worker must represent the
infrastructure repository and mathematical destination separately. Production authoring
and merging remain disabled until the destination has its own approved adapter and policy.

Other additions live beside the roadmap:

```text
sphereceti.toml                 # Identity, paths, capabilities, defaults
pyproject.toml                  # One installed sphereceti entry point
uv.lock
policy/                        # Trusted scope, review, and activation policy
tools/project/                 # Small shared configuration/adapter layer
tools/review/                   # Upstream engine and rubrics
tools/worker/                   # Upstream worker
tools/data/
tools/progress/
tools/upstream-lock.toml        # Source commits, paths, licenses, adaptations
scripts/                       # Build/audit/lint entry points
tests/                         # Infrastructure tests and isolated fixtures
docs/infrastructure/           # Installation, operation, and setup instructions
.github/workflows/             # Active workflow YAML only
```

Preserve upstream Python package names initially, and make the installed CLI dispatch to
them. Resolve package-name conflicts explicitly. Package prompts, rubrics, schemas, and
scripts as resources; test both wheel and source installations outside this checkout.

## Source snapshots for the import PRs

These are inspected candidate source revisions, not new Lean dependency pins. Each import
PR must record its actual selected revision and source-to-destination mapping, retain
applicable attribution, and run the corresponding upstream tests. A different revision
requires an explicit lock update.

| Component | Exact candidate source commit | Source paths to start from |
|---|---|---|
| TauCeti infrastructure | `b743b607ce3e9742b18026ad79082e5d15badff5` | `.github/workflows/pr-build.yml`, `scripts/sandbox-build.sh`, `scripts/attest-pr-config.sh`, `scripts/source-modules.sh`, `scripts/Axioms.lean`, `scripts/ModuleSystem.lean`, `scripts/HeaderStyle.lean`, lint scripts and their tests |
| TauCetiReview | `afb424eda89e8ac96d9eb69f6a88972055a4cd1b` | `runner/`, `rubrics/`, `tests/`, `pyproject.toml`, `LICENSE` |
| kim-em/TauCetiWorker | `27c234a5722cfe557279aa47fbfd8e51450481a6` | `tauceti_worker/`, `prompts/`, `scripts/`, `tests/`, `pyproject.toml` |
| TauCetiProgress | `880e8b9737973bfbd8f1f214f4ac2ded67f5b856` | `progress/`, `README.md`, `pyproject.toml`, `LICENSE` |
| TauCetiData | `e8e915472b02875f9a3864492616662c0c902876` | `schema/`, `scripts/`, `docs/`; exclude historical records and blobs |

Source inspection found two prerequisites that the notes' staging table should make explicit:

- The inspected TauCeti toolchain is rc2. Backport/test the audit tools on SphereCeti's rc1
  graph; do not combine infrastructure import with a Lean/TauCeti/Mathlib upgrade.
- The Worker and Data trees have no top-level license file, and GitHub reports null license
  metadata for both. Resolve the applicable reuse terms before copying either component;
  do not assume SphereCeti's Apache license covers them. This affects I08 and the Data-derived
  portions of I12/I16, not the independent core sequence.

The inspected TauCeti PR workflow uses pinned `bwrap`. TauCetiReview's `SECURITY.md` still
describes `landrun` in its build section. Use the executable workflow and its regression
tests as the porting source, and write SphereCeti's operating documentation to match the port.

## Focused PRs

### I01 — Separate Lean library and roadmap targets

**Base:** current `main`. **Scope:** Lake library declarations, aggregators, module-boundary
inventory/checker, isolated test fixtures, and a short boundary document.

Keep the existing `SphereCeti.Basic` dependency smoke check. Add a separate, initially empty
roadmap aggregator with a descriptive module docstring; do not invent mathematical targets.
Make both targets explicit in the default build. Reserve the two roadmap paths for PR #1.
Classify all repository Lean sources, including nested and otherwise unimported modules;
test fixtures are separately identified and never public imports.

**Acceptance:** both Lake targets build on `main`; a disposable test project demonstrates
that a direct or transitive import from the library into roadmap targets is rejected, and
that an unclassified nested Lean file cannot escape inventory. Actual compiled axiom
checking follows in I04. The mathematical target files do not enter this PR.

### I02 — Project profile, source ledger, and CLI packaging

**Depends on:** I01. **Scope:** `tools/project/`, project configuration, install metadata,
source-lock schema, and `sphereceti doctor` / `sphereceti status --json`.

Separate project identity, approved source locations, server policy, and operator preferences.
Include an explicit scaffold/roadmap capability state, mathematical destination, and separate
switches for paid review generation, posting, authoring, reporting, and merging. Default
external writes and paid inference off. Before PR #1 lands, report that the approved roadmap
is not installed; never silently fetch its open branch as an approved specification.

**Acceptance:** fresh wheel/source installs work outside a checkout; unavailable capabilities
produce a specific diagnostic; operator overrides cannot alter server acceptance policy;
source-lock entries require a full commit and source paths. `doctor` distinguishes an API
failure from an empty queue and reports missing external setup without modifying it.

### I03 — Trusted candidate build and scope classification

**Depends on:** I02. **Scope:** selected TauCeti sandbox/config-attestation code and tests,
trusted PR workflow, shared scope classifier, and human-review routing.

Distinguish approved tooling/policy `T`, immutable candidate head `H`, and validated dependency
graph `D`. Run candidate Lean under the pinned sandbox without posting or merge credentials.
Build results and automation eligibility are separate outputs. Protect roadmap documents,
target files, semantic contracts, tooling, rubrics, workflows, and dependency configuration.
Mixed changes take the more restrictive route. Resolve trusted code/config from the approved
snapshot, not the installed candidate's adjacent files.

**Acceptance:** changing an audit script or policy in the candidate cannot change the trusted
verdict; incomplete file listings, unknown paths, symlink escapes, and sandbox probe failures
prevent automatic acceptance. Infra PRs can exercise their proposed tooling in isolated tests
while remaining subject to human review. No merge workflow is activated.

### I04 — Complete module, axiom, and lint audits

**Depends on:** I03. **Scope:** compiled module/axiom checks, environment/source lint, explicit
baseline/exception handling, and the roadmap-validation interface.

Build every classified module, not only the public root's closure. Audit all declarations
owned by the library modules, including definitions and transitive axiom dependencies, with
the proposed allowed axioms `propext`, `Classical.choice`, and `Quot.sound`. Reject roadmap
imports independently of whether a particular declaration uses an admitted target. Roadmap
elaboration has its own admission ledger, established when PR #1 is integrated. A textual
`sorry` count remains informational and cannot certify proof completion.

**Acceptance:** isolated fixtures reject an unimported admitted module, a new axiom, a
definition depending on an admission, a forbidden imported target, and a disallowed
`native_decide` axiom. rc1 compatibility is demonstrated. Legitimate target admissions remain
confined to the roadmap check; axiom/lint exceptions require policy review.

### I05 — Import the review engine and rubrics, inactive

**Depends on:** I02. **Scope:** `tools/review/`, its upstream tests and source-lock entry.

Copy the approved source subset with attribution and the ten existing rubrics in order:
correctness, reuse, scope, attribution, api-design, generality, placement, naming,
documentation, proof-quality. Preserve upstream internal structure and verdict semantics.
Keep minimal path adjustments distinguishable from the source import. Imported workflow
examples must not become active merely by being copied into `.github/workflows/`.

**Acceptance:** upstream engine tests run without spending provider credits or publishing;
the import/adaptation mapping is reviewable; no operational identity points to TauCeti for
writes. Real TauCeti imports, credits, and mathematical destinations retain their names.

### I06 — Local review adapter and installed resources

**Depends on:** I03, I05. **Scope:** project-aware review workspace, CLI dispatch, evidence
selection, and package-resource tests.

Make `sphereceti review N` produce a local advisory result through the imported engine. Supply
approved roadmap/convention/migration/provenance evidence and actual pinned dependency source
trees. A review of PR #1 treats its proposed roadmap as a specification change, not as already
approved evidence. Preserve provider adapters, contests, shadow runs, and budget handling.

**Acceptance:** worker/CLI/CI call one engine; a dry run names `T/H/D` and all evidence;
missing approved context prevents a merge-eligible review; partial/shadow runs remain
advisory. Fake-provider integration tests run from a fresh installation. Tests do not invoke
paid inference or post comments.

### I07 — Authenticated review records and explicit posting

**Depends on:** I04, I06. **Scope:** review record schema, posting adapter, scoreboard parser,
reviewer authorization, and staleness tests.

Implement explicit `review N --post`, keeping publishing credentials outside the reviewer
process. Records identify repository, head, diff base, dependency digest, full tooling
revision, effective engine/rubric/policy digest, completion state, and execution mode. Only
approved GitHub identities or the designated App can supply a merge-eligible signal; inspect
API identity rather than a name embedded in comment text. Advisory boards cannot supersede
authorized decisions. Define contest and supersession behavior explicitly.

**Acceptance:** forged, partial, errored, shadow, wrong-repository, stale-head, and stale-policy
boards cannot qualify. An unrelated main-branch mathematics commit does not invalidate the
policy digest; changed integration bases are checked separately. Changed review evidence
does invalidate the affected review. This completes the recommended pre-roadmap core.

### I08 — Import the worker, inactive

**Depends on:** I02 and resolved Worker reuse terms. **Scope:** upstream worker packages,
prompts, tests, attribution, and source-lock entry.

Preserve the dashboard, providers, repair stages, strict PR targeting, and API-failure
handling. Do not enable authoring or copy the claims-access grant into SphereCeti. Imported
tests use fixtures; no live scheduling, forking, provider spend, or write credentials.

**Acceptance:** upstream worker tests pass with a documented adaptation delta, and the
installed package carries the resources its entry points resolve. No second review engine
is introduced. This PR can proceed independently of the review/CI branch once I02 lands.

### I09 — Worker scheduling, targeting, and cooperative leases

**Depends on:** I07, I08. **Scope:** worker project adapter and comment-lease adapter.

Wire the imported scheduler to the shared profile and review engine. Preserve priority:
rebase, dependency repair, progress, CI repair, review-response repair, review, new work.
Unsupported stages are explicitly disabled. Strict PR targeting never falls through into
unrelated authoring. Before an approved roadmap and production adapter exist, new mathematical
work reports unavailable. Pin repair proposes a coherent graph update for human review.

Use same-repository cooperative leases with expiry, renewal, identity, and revision; keep
persistent intentions separate. Do not grant contributor write access to the monorepo as a
substitute for claims-repository access.

**Acceptance:** fake-API tests cover provider outage, inaccessible queue, expired lease,
duplicate workers, exact PR targeting, destination mismatch, and disabled capabilities.
Document that leases reduce duplicate effort; strict exclusion needs a trusted broker.

### I10 — Shared merge decision in observation mode

**Depends on:** I04, I07. **Scope:** one eligibility function and a read-only CLI/workflow
report consuming trusted scope, audits, review records, and current GitHub state.

Require the correct repository/head, trusted check identity, complete authorized review,
current policy, compatible base, and permitted paths. The initial mathematical allowlist
is empty under SphereCeti's roadmap-only contract. Specification and infrastructure changes
take the human route. Worker, dashboard, CI, and eventual merger consume this same decision.

**Acceptance:** table-driven tests cover both eligibility and the reason it is denied; missing
or indeterminate API data never becomes permission. Observing PR #1 yields human review
required. A mathematically eligible fixture exercises the future path without adding a
production proof or permitting a real merge.

### I11 — Serialized merge controller and activation diagnostics

**Depends on:** I10. **Scope:** a disabled merge controller, lifecycle reconciliation, and
setup/stop-switch documentation.

Use serialized merges with an expected-head condition and server-enforced required checks
and up-to-date branches. Re-read eligibility immediately before merging. A head/base change
causes revalidation. Keep credentials outside author/reviewer jobs. All merge entry points,
including scheduled sweeps, obey the same global stop switch.

**Acceptance:** tests simulate concurrent base advancement, review revocation, restart,
duplicate events, and disabled automation. Activation requires verified branch protections,
trusted required-check producers, an approved nonempty change class, and an explicitly
configured bot with no status-check bypass. Code landing is not activation. With the current
proof-home policy there is no eligible SphereCeti mathematics class to enable.

### I12 — Durable archive and same-repository state branches

**Depends on:** I07 and resolved reuse terms for any Data-derived code. **Scope:** schemas,
local outbox, idempotent publication/sync, and derived database tooling.

Use `reviews` for operational review state and `review-data` for immutable records/blobs in
the same repository. Keep executable code and policy on `main`. Import schemas/tools, not
TauCeti's historical transcripts. Keep upstream field filtering and transcript handling
explicit. Fetch source shallowly and by branch to avoid downloading archive history.

**Acceptance:** an upload outage retains the outbox and does not undo a posted review;
duplicate uploads are idempotent; immutable records cannot be silently overwritten;
concurrent branch updates retry safely; SQLite remains derived and uncommitted. Branch
creation and publication are separate setup actions, not prerequisites for local tests.

### I13 — Progress reports grounded in published evidence

**Depends on:** I02, I04; live theorem reporting also needs an approved destination and
published declaration index. **Scope:** Progress import/adapter, report validators, fixtures.

Preserve tested code for window selection and fact extraction; let the model write only
prose. Keep `STATUS.md` replaceable and `PROGRESS.md` append-only, separate from the README.
Track the documented production repository/revision and the actually published documentation
cursor. Before those exist, report missing evidence instead of treating target elaboration
as mathematical achievement. Do not scrape Lean with an approximate declaration parser.

**Acceptance:** byte-exact append checks, cursor validation, valid declaration links, and
scope checks reject roadmap edits. Admission-dependent target glue never appears as a
proved milestone. Local fixtures suffice before PR #1 lands. No upstream Zulip notification
workflow is copied or enabled.

### I14 — Documentation and cache operations

**Depends on:** I04. **Scope:** documentation build/publication adapter, SphereCeti cache
namespace/publisher, scheduled source verification, and optional artifact comparison.

Preserve anonymous consumption of the pinned TauCeti cache and source-build fallback. Own
cache publication uses a separate credential-bearing job and includes only the intended
audited outputs. Label roadmap documentation as targets and keep it distinct from proof API
documentation. Source rebuilds and advisory cache-byte comparisons are separate results.

**Acceptance:** cache outages do not turn into theorem failures; publishers cannot execute
candidate code with credentials; the published docs advertise their actual source revision;
nightly tests demonstrate a cache-independent path. Pages/storage configuration remains an
explicit setup step. This enables local published-doc inputs to I13 where appropriate.

### I15 — Profiling and lifecycle maintenance

**Depends on:** I03, I10; live actions depend on setup. **Scope:** selected profiling,
main-health, conflict/label, housekeeping, and stuck-work tooling with upstream tests.

Keep performance reports advisory and measured against recorded revisions. Share status and
lifecycle interpretation with the worker/merger. Port maintenance actions individually within
the reviewed path/capability policy; do not inherit TauCeti's access grants or external
notification destinations. If profiling and lifecycle imports are independently substantial,
land them as I15a and I15b rather than mixing them.

**Acceptance:** duplicate events are idempotent, missing data remains an error, reports do not
override mathematical checks, and every mutating maintenance entry point obeys its switch.

### I16 — Cost analysis, shadow evaluation, and human meta-review

**Depends on:** I12 and resolved reuse terms. **Scope:** evaluation schemas/tools, cost
accounting, pairing, and local human-label interface.

Preserve immutable token usage, dated pricing inputs, and distinctions between fresh shadow
runs and reviews with prior-case context. Evaluation records do not become live merge
decisions. Keep paid evaluation opt-in and separately budgeted.

**Acceptance:** reproducible cost aggregation from fixtures, correct pairing constraints,
idempotent labels/records, and no shadow-result path into I10's acceptance signal.

## Landing order and the PR #1 integration patch

The core dependency chain is:

```text
I01 → I02 → I03 → I04 ────────────┐
        └→ I05 → I06 (also I03) → I07 → roadmap PR #1
```

Worker import can proceed after I02; its adapter waits for I07. Merge observation and archive
work begin after the review record contract. Reporting and publication are independent
operational branches. This is a dependency map, not a requirement for parallel agents.

Before merging PR #1, apply one mechanical integration patch to that branch:

1. Rebase onto the infrastructure-bearing `main`; preserve its clean library root.
2. Move `Suggested.lean` and `Pinned.lean` into `SphereCetiRoadmap/`; change module imports,
   retain declaration namespaces, and wire the roadmap aggregator.
3. Update literal file/module paths in README, AGENTS, CONTRIBUTING, CONVENTIONS, MIGRATION,
   PROVENANCE, and the static checker. Keep the README layer prose and production PR IDs.
4. Connect the existing shape/pin checker to the new inventory and roadmap validation job.
   Scope its Markdown-link scan to project-owned documentation, with an explicit separate
   rule for vendored upstream docs; imported cross-repository links must not cause a global
   bypass of link checks.
5. Establish the reviewed roadmap admission ledger at the rebased head; the inspected head
   has 282 standalone commands. Check the compiled declaration inventory as well as the
   textual count. Do not freeze 282 as an eternal requirement.
6. Build both targets, run all trusted checks, and compare target declaration types and
   bodies against the pre-integration snapshot after only the allowed module-path edits.
   Record any exception as a separate mathematical review item.

`lake build` continues to check both libraries. Explicit CI commands distinguish an
admission-free library check from target elaboration. The main roadmap's only architectural
addition is a short pointer to the infrastructure instructions and the separate build boundary.

The existing README/target differences in production planning are outside this integration
patch. For example, MIGRATION D2/D3 still mentions a `FundamentalPattern` while the current
README and targets use the orbit quotient directly. Resolve that through the roadmap's normal
review process, not as an incidental infrastructure rewrite.

## Operational gates and completion evidence

Every PR should state its source snapshot/paths, local adaptation, tests, capability enabled,
and external setup still required. Import PRs and adaptation PRs should have distinct commits
when separating them into individual PRs would leave an untestable intermediate state.

All sixteen PR scopes can be developed against the scaffold and fixtures. That does not mean
all sixteen capabilities should be enabled before the roadmap is approved. Local commands
come first; authoritative checks follow; posting is explicit; merge decisions are observed
before execution. Production authoring/merging requires an additional destination-policy
handoff, or a separately approved change to SphereCeti's repository role.

GitHub currently limits native merge queues to organization-owned repositories; SphereCeti
is public and personally owned. Serialized merges are therefore the planned adapter.
[GitHub merge-queue documentation](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/configuring-pull-request-merges/managing-a-merge-queue)

Required checks and branch protection are external configuration. `doctor` must verify their
effective settings and expected check producers before enabling a merge controller; committing
workflow YAML or CODEOWNERS alone is insufficient.
[GitHub branch-protection documentation](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches)

Trusted `pull_request_target` orchestration must keep candidate execution isolated from
credentials. A local reusable-workflow path does not by itself establish a trusted caller.
[GitHub workflow-event documentation](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#pull_request_target)

This plan was grounded by source/configuration reads and GitHub metadata checks. No upstream
tooling has been ported or compatibility-tested, no provider inference was run, and no PR,
repository setting, state branch, or automation switch was changed while preparing it.
