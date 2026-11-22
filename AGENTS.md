# Agent instructions for SphereCeti

Read, in order:

1. `README.md`;
2. `CONVENTIONS.md`;
3. `MIGRATION.md`;
4. `PROVENANCE.md`;
5. `UPSTREAM.md`;
6. `VALIDATION.md`;
7. `SphereCetiRoadmap/Suggested.lean`.

For work on the coefficient construction of the magic functions, also read
`SphereCetiRoadmap/CoefficientMagic/README.md`, `FINITE_SECTION_EXISTENCE.md`, and the three target
files in that directory.

The repository is a roadmap package, not the production proof.  Do not add completed mathematical
implementations here unless they are tiny auxiliary definitions or lemmas needed only to state the
targets.

`SphereCetiRoadmap/Pinned.lean` is temporary and frozen to the public semantics of
`Sphere-Packing-Lean@bad3de916074748eb88b7d1ee6dbf9494361ad17`.  Do not extend it with new project
concepts.  After production migrates to the pinned 4.36 dependency line, delete it and import
production directly.

Never:

- weaken a target merely to make it easy to state;
- use `True` or an unconstrained `Prop` field as a placeholder;
- track TauCeti `main` instead of an exact commit;
- redefine locally an object that the pinned TauCeti revision already provides;
- conflate sphere radius with center separation;
- state global uniqueness for arbitrary limsup-density packings;
- turn Poisson summation, a density expansion, or a theta transformation into a simp rule;
- treat `gauss2` or PR #420 as a branch base;
- give a prose-specified target of the coefficient roadmap (the contour measures, the endpoint
  continuation, the concrete regularizer, the orbifold bundle) a `sorry`-bodied stand-in;
- impose the dimension-8 constant moment rows in dimension 24, or drop them in dimension 8;
- treat the SymPy check of the finite modular witness as a proof.

When adapting proofs from a source, record the exact commit and path.  For general material,
consult `UPSTREAM.md`, but do not wait for upstream acceptance before making progress in
production.
