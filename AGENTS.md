# Agent instructions for SphereCeti

Read, in order:

1. `README.md`;
2. `CONVENTIONS.md`;
3. `MIGRATION.md`;
4. `PROVENANCE.md`;
5. `UPSTREAM.md`;
6. `VALIDATION.md`;
7. `SphereCeti/Suggested.lean`.

The repository is a roadmap package, not the production proof.  Do not add completed mathematical
implementations here unless they are tiny elaboration adapters needed to state targets.

`SphereCeti/Pinned.lean` is temporary and frozen to the public semantics of
`Sphere-Packing-Lean@bad3de916074748eb88b7d1ee6dbf9494361ad17`.  Do not extend it with new project
concepts.  After production migrates to the pinned 4.34 dependency line, delete it and import
production directly.

Never:

- weaken a target merely to make it easy to state;
- use `True` or an unconstrained `Prop` field as a placeholder;
- track TauCeti `main` instead of an exact commit;
- redefine a pinned TauCeti object behind a local stand-in;
- conflate sphere radius with center separation;
- state global uniqueness for arbitrary limsup-density packings;
- turn Poisson summation, a density expansion, or a theta transformation into a simp rule;
- treat `gauss2` or PR #420 as a branch base.

For source mining, record exact commit and path.  For generic material, consult `UPSTREAM.md`, but do
not wait for upstream acceptance before making progress in production.
