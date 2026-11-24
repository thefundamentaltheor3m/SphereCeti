# Contributing to SphereCeti

SphereCeti hosts the sphere-packing roadmap and its admission-free proof library.

## Authority

- `README.md` is the definitive mathematical specification.
- `SphereCetiRoadmap/Suggested.lean` gives suggested forms for the declarations, together with
  `#check` lines confirming that the declarations they depend on exist; it is not exhaustive.
- `CONVENTIONS.md` fixes normalizations and attribute policy.
- `MIGRATION.md` records mathematical dependencies and the Sphere-Packing-Lean compatibility migration.
- `PROVENANCE.md` records sources and exact pins.
- `UPSTREAM.md` is the issue-ready list of Mathlib and TauCeti destinations for general results.
  Maintainers curate it; an ordinary proof PR leaves it alone.
- `VALIDATION.md` records the current static and Lean-elaboration status.

A change to `Suggested.lean` does not silently change the roadmap; update the relevant prose and
convention entry in the same PR.

## Roadmap changes

A roadmap PR must identify:

1. the mathematical ambiguity or gap being resolved;
2. the exact layer affected;
3. whether a convention changes;
4. whether a suggested Lean signature changes;
5. whether the production migration sequence changes;
6. any new source or upstream destination.

Do not add vague work items such as “finish analysis” or “generalize later.”  Name the object,
hypotheses, precise statement, and dependency layer.

## Lean target signatures

`sorry` is allowed in this repository because the declarations are targets.  It must be used
honestly.

- Do not disguise an unstated hypothesis as a field of type `Prop` with body `sorry`.
- Do not use `True` as a placeholder for a mathematical condition.
- Import existing pinned TauCeti declarations directly instead of restating them.
- The temporary declarations in `SphereCetiRoadmap/Pinned.lean` model only the public statements
  of the older production release; do not add new mathematics there.
- Prefer `example` for final statements whose namespace is not settled, and named declarations
  only for objects whose name and type are settled.

## Pin updates

A pin update must be one atomic PR updating:

- `lean-toolchain`;
- the TauCeti revision in `lakefile.toml`;
- `lake-manifest.json`;
- the pin table in `README.md`;
- the dependency record in `PROVENANCE.md`, and the matching entries in `CONVENTIONS.md` and
  `MIGRATION.md`;
- `sphereceti.toml` dependency pins and `scripts/check_roadmap.py` expected pins/CLI release line;
- publication toolchain references in `scripts/publication.py` and
  `.github/workflows/docs-cache.yml`, affected test fixtures, and `INFRASTRUCTURE-PLAN.md`;
- any `#check` lines or imports affected by API changes, and the explanatory toolchain text in
  `Pinned.lean` while preserving its frozen production semantics;
- `VALIDATION.md` and the reviewed admission ledger when compiled declarations or axiom
  dependencies change.

Build both `SphereCeti` and `SphereCetiRoadmap`, check module boundaries, and run
`lake env python3 -I scripts/check_audits.py` for the full classified-source build and compiled
audit.  Run the infrastructure/Python regression suite for affected configuration and publication
code.  A bare `#check` verifies name resolution; use typed checks for newly adopted interfaces.

The PR must state the old and new TauCeti and resolved Mathlib SHAs.  Never change the effective
Mathlib revision only by deleting or ignoring the manifest.

## Contributing proofs

Suggested prompt for a coding assistant:

> Read AGENTS.md and CONVENTIONS.md in https://github.com/thefundamentaltheor3m/SphereCeti. Pick
> one target from roadmap #1 or a prerequisite it needs. Prove it in a topic module under
> `SphereCeti/`, using `SphereCetiRoadmap/Suggested.lean` as the specification. Run
> `sphereceti verify` in the checkout and get an overall PASS. Open a focused PR that names the
> target, then address CI failures and review feedback.

Pick one target from the roadmap or a prerequisite you can prove against the current pins.
Add a module under `SphereCeti/<Topic>/`.
For an ordinary proof PR, edit the topic modules under SphereCeti/. Import topic modules directly.
Leave SphereCeti.lean and UPSTREAM.md alone. If a lemma belongs upstream, name the proposed
destination in the PR description.
The `SphereCeti.*` glob in `lakefile.toml` builds every library module and the compiled audit
checks every source file, so a new module needs no root import. `SphereCeti.lean` keeps its
existing re-exports, so `import SphereCeti` still works downstream, and is otherwise frozen.
Build on library definitions and imported results. The library audit
forbids direct and transitive `sorryAx` dependencies. If a target needs an admitted roadmap
definition, implement the definition or a smaller independent prerequisite in the library first.

In the PR description, link the roadmap target, name the library declaration and explain how
their hypotheses, normalization and conclusion correspond.  If a lemma belongs upstream, name the
proposed destination (the Mathlib or TauCeti file) in the PR description; leave `UPSTREAM.md` alone. Keep `Suggested.lean` as the
specification. Landing a separate proof leaves its roadmap admission ledger entry intact
while the target still depends on `sorryAx`. Change a target statement only in an explicit
specification change. Start proof PRs from SphereCeti `main` or name one stacking dependency.
Work using the current pins can start before Sphere-Packing-Lean's Phase A migration.

Before opening the PR, run `sphereceti verify` and get an overall PASS. A skipped step means
verification is incomplete, not passed; fixing the first failure often clears the skips after it.

Keeping a proof PR mergeable:

- For a stacked PR, when the PR below yours merges, merge `main` into your branch rather than
  rebasing or force-pushing. The PR then shows only your own change, and existing reviews keep
  pointing at commits that still exist.
- For a PR from a fork, GitHub holds the ordinary CI runs for a maintainer to approve until your
  first PR is merged. Waiting on that is expected, not a failure; the trusted build runs without
  approval.

## Automation attributes

A proposed or production `@[simp]`, `@[grind]`, or `@[fun_prop]` attribute is an API decision.
Include a small `example` showing the intended successful behavior and a note explaining why the
rule will not cause semantic expansion or search loops.

## Provenance

When adapting code, identify repository, commit, source path, destination path, and license/header
action.  When independently formalizing a theorem from the literature, cite the mathematical
source in the module docstring.

## Building

With the pinned Lean toolchain installed:

```bash
python3 scripts/check_roadmap.py
lake exe cache get
lake build
```

Run the static consistency check before asking Lean to elaborate the targets.  The committed
`lake-manifest.json` pins the full dependency graph; do not run `lake update` outside a pin-update
PR, and if it is ever run it must leave the committed manifest unchanged.  `sorry` warnings are
expected in the roadmap targets; syntax, imports, and types must elaborate.
