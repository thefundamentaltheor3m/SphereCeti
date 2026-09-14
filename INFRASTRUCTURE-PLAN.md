# SphereCeti infrastructure architecture

SphereCeti adapts the TauCeti contributors' infrastructure around one cohesive sphere-packing
roadmap. Keep mathematical statements, Layers 0–11, production PR IDs and the single
`UPSTREAM.md` ledger in their existing form. This package states targets; substantive proofs
belong in Sphere-Packing-Lean, TauCeti or Mathlib.

The [infrastructure tracking issue](https://github.com/thefundamentaltheor3m/SphereCeti/issues/23)
owns the live dependency graph, review order, landing status and remaining milestones. Each
feature PR states its immediate prerequisites, review focus, source credit, validation and
activation status. Use native SphereCeti PR numbers. Keep queue counts out of this document.

## Source credit and exact provenance

| Source | Pinned reference | Paths and role |
| --- | --- | --- |
| TauCeti infrastructure | [b743b60](https://github.com/TauCetiProject/TauCeti/tree/b743b607ce3e9742b18026ad79082e5d15badff5) | `scripts/`, `.github/workflows/`: trusted builds, compiled audits, docs/cache, profiling and maintenance; Apache-2.0 |
| TauCeti mathematical dependency | [8671bee](https://github.com/TauCetiProject/TauCeti/tree/8671bee98125933c56b9b00a08ded873b77dd23b) | Fixed Lake dependency; original module inventory adapted from `scripts/source-modules.sh` |
| TauCetiReview | [afb424e](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b) | `runner/`, `rubrics/`, `tests/`, references and license; Apache-2.0 |
| TauCetiProgress | [880e8b9](https://github.com/TauCetiProject/TauCetiProgress/tree/880e8b9737973bfbd8f1f214f4ac2ded67f5b856) | `progress/`, tests, prompts, references and license; Apache-2.0 |
| TauCetiWorker | [27c234a](https://github.com/kim-em/TauCetiWorker/blob/27c234a5722cfe557279aa47fbfd8e51450481a6/README.md) | Behavioral reference: README only. SphereCeti's Worker is independently authored under Apache-2.0; no source, prompts, tests or assets copied |
| TauCetiData | [e8e9154](https://github.com/TauCetiProject/TauCetiData/tree/e8e915472b02875f9a3864492616662c0c902876) | Reference candidate with unresolved reuse terms; no source or historical records imported |

The [source ledger](tools/upstream-lock.toml) records precise upstream paths, destinations,
licenses and adaptations. Import manifests retain original paths, bytes and file modes.
Archive/evaluation reuse the licensed Review engine and independently authored SphereCeti
schemas. Do not describe them as a TauCetiData import. Infrastructure pins are distinct from
the mathematical dependency graph; no floating upstream branch substitutes for either.

## Review boundaries

Keep these questions separately reviewable:

- Foundation: module boundaries, CLI/configuration, trusted candidate builds, compiled audits.
- Review: faithful inactive source import; exact-evidence local adaptation; authenticated
  records and explicit publication.
- Runtime: archive capture; guarded Worker execution; evaluation and shadow accounting.
  These modify the same reviewer lifecycle and need sequential integration and combined tests.
- Reporting: inactive source import; docs/cache evidence; same-tree installed adaptation.
- Operations: read-only merge observation; gated merge action; lifecycle diagnostics;
  advisory profiling. All infrastructure lands before the mathematical specification.

The infrastructure is published as one native GitHub stack, with the mathematical roadmap at
the top. Each PR contains the full preceding integration baseline plus its own focused change.
The tracking issue records the landing order. Preserve separate import and adaptation commits,
and keep integration fixes in the layer that introduces the combined behavior. After lower-layer
edits, use cascading stack rebases and validate the affected layers before publishing.

## Mathematical roadmap integration

Land the complete infrastructure before the mathematical roadmap. Keep one mathematical roadmap
covering dimensions 8 and 24, with its mechanical integration separately reviewable.

Prepare a separately identifiable mechanical integration commit on the final infrastructure tip:

1. Preserve the admission-free `SphereCeti` library and relocate targets into
   `SphereCetiRoadmap/`, with a separate aggregator. Preserve declaration namespaces,
   statements and the frozen public semantics of `Pinned.lean`.
2. Update module references, checker paths and literal documentation links. Keep roadmap
   layer prose and production IDs unchanged. Do not leave target-importing compatibility
   files in the audited library.
3. Inspect actual compiled axiom dependencies and review exact admission-ledger entries,
   including generated/transitive declarations. A textual `sorry` count is informational.
4. Update the profile's roadmap state and run the existing roadmap contract checker alongside
   complete module/axiom/lint audits. Compare declaration statements against the old snapshot;
   mathematical revisions remain separate review items.

The initial admission-policy change follows human review. Proposed policy cannot authorize
itself: trusted checks use approved tooling and policy. Keep the existing production migration
and deletion of `Pinned.lean` at the direct-import handoff.

## Installed resources and evidence

The root `sphereceti` distribution bundles its project policy and adapted resources from the
same checkout. Review and Progress imports remain separately reviewable. Preserve their
upstream pins and import manifests; do not install another SphereCeti revision through a
self-Git dependency. No global `progress` module is installed.

The wheel resource mapping in `pyproject.toml` and named source components in
`tools/upstream-lock.toml` are reviewed inventories. Fresh-install tests compare installed
resources with these checkout inputs, validate manifests and exercise every available command
family outside the checkout. Source distributions must build the same usable wheel. Resource
verification must catch omissions, stale payloads and unexpected entries rather than checking
only a total count or accepting a minimum count.

Project identity and automation policy come from approved installed resources. Caller-directory
files and operator preferences cannot replace them. Proposed sources are evidence, never
instructions or accepted policy. Documentation and progress reports must distinguish roadmap
targets from production proofs and bind the actual documented revision.

## Worker and shared reviewer

Use one roadmap, maintenance-first selection and ready low-effort work. Strict PR targeting can
only narrow the eligible queue. Missing or stale observations stop selection; they never imply
an empty queue or authorize unrelated authoring. A derived frontier cites the existing roadmap
and exact revisions; it is not a second specification or proof of completion.

The independent Worker reuses the existing review engine, authenticated-record protocol and
shared budget ledger. Its guards check exact sources, approved policy, identity and cooperative
lease ownership. Renewal must not rerun inference. On interruption, retain completed-attempt
accounting and mark incomplete results; cancellation before publication prevents further writes.
Already submitted writes require readback reconciliation. Cooperative leases reduce duplicate
work but do not promise strict exclusion.

Archive facts, human evaluation labels and operational receipts do not establish accepted
reviews or merge authority. Archive publication failure must preserve completed local work.
Fresh-shadow evaluation stays isolated from live publication while debiting its intended ledger.

A bounded repeat loop and a bare-command overview are useful follow-ups. Production authoring,
repair execution, fork publication and unattended services require separate focused contracts.
An authoring adapter must use the approved production destination, isolated credentials and
checkout, exact evidence, bounded work, validation and explicit publication. No area-specific
Worker modes or duplicate mathematical roadmap are needed.

## Validation and activation

Self-review each focused change. Test a combined checkout against the complete stack:
complete installed CLI/resources, real roadmap admissions, shared archive/Worker/shadow behavior,
and the compiled build/audit pipeline. Keep integration fixes visible in their owning PRs.

Landing implementation does not enable automation. Posting, merge action, labels, archive sync
and Worker execution remain explicitly gated. Main-based trusted workflows and required-status
producers must be exercised after landing before enabling writers. Configuration diagnostics
must check actual server protections; committed YAML alone is insufficient. No infrastructure
reorganization authorizes merging PRs, changing repository access or contacting contributors.
