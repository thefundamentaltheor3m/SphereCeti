# Contributing to SphereCeti

SphereCeti is a human-steered roadmap and target-signature package for the production
`Sphere-Packing-Lean` development.  It is not a second implementation repository.

## Authority

- `README.md` is the definitive mathematical specification.
- `SphereCeti/Suggested.lean` gives suggested declaration shapes and compile-time dependency
  contracts; it is not exhaustive.
- `CONVENTIONS.md` fixes normalizations and attribute policy.
- `MIGRATION.md` fixes production PR sequencing.
- `PROVENANCE.md` records sources and exact pins.
- `UPSTREAM.md` is the issue-ready ledger of generic destinations.
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
hypotheses, theorem boundary, and dependency layer.

## Lean target signatures

`sorry` is allowed in this repository because the declarations are targets.  It must be used
honestly.

- Do not disguise an unstated hypothesis as a field of type `Prop` with body `sorry`.
- Do not use `True` as a placeholder for a mathematical condition.
- Import existing pinned TauCeti declarations directly instead of restating them.
- The temporary declarations in `SphereCeti/Pinned.lean` model only the older production boundary;
  do not add new mathematics there.
- Prefer `example` for endpoint shapes whose final namespace is not settled, and named definitions
  only for genuinely pinned object boundaries.

## Pin updates

A pin update must be one atomic PR updating:

- `lean-toolchain`;
- the TauCeti revision in `lakefile.toml`;
- `lake-manifest.json`;
- the pin table in `README.md`;
- the dependency ledger in `PROVENANCE.md`;
- any `#check` or import contracts affected by API changes.

The PR must state the old and new TauCeti and resolved Mathlib SHAs.  Never change the effective
Mathlib revision only by deleting or ignoring the manifest.

## Production work

Mathematical implementations normally belong in `Sphere-Packing-Lean`, TauCeti, or Mathlib.
SphereCeti PRs track their statements and dependencies; they do not duplicate completed production
proofs.

Production PRs follow the template in `MIGRATION.md` and begin from current production `main`, unless
one immediate stacking dependency is named explicitly.

## Automation attributes

A proposed or production `@[simp]`, `@[grind]`, or `@[fun_prop]` attribute is an API decision.
Include a small contract showing the intended successful behavior and a note explaining why the
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

Run the static contract check before asking Lean to elaborate the targets.  The committed
`lake-manifest.json` pins the full dependency graph; do not run `lake update` outside a pin-update
PR, and if it is ever run it must leave the committed manifest unchanged.  `sorry` warnings are
expected in the roadmap targets; syntax, imports, and types must elaborate.
