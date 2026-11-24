# Agent instructions for SphereCeti

Read, in order:

1. `README.md`;
2. `CONVENTIONS.md`;
3. `MIGRATION.md`;
4. `PROVENANCE.md`;
5. `UPSTREAM.md`;
6. `VALIDATION.md`;
7. `SphereCetiRoadmap/Suggested.lean`.

Roadmap proofs land in this repository. Add admission-free Lean modules under
`SphereCeti/<Topic>/` and import their public entry points from `SphereCeti.lean`.
Use `SphereCetiRoadmap/Suggested.lean` as the target specification. Keep proof bodies out of
that file. Library modules must build independently of `SphereCetiRoadmap`, including its
admitted targets and frozen compatibility model. Cite the target and any remaining prerequisites in the PR.

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
- treat `gauss2` or PR #420 as a branch base.

When adapting proofs from a source, record the exact commit and path.  For general material,
consult `UPSTREAM.md`, but do not wait for upstream acceptance before proving roadmap results in SphereCeti.
In an ordinary proof PR, leave `UPSTREAM.md` alone.  If a lemma belongs upstream, name the proposed
destination in the PR description.
