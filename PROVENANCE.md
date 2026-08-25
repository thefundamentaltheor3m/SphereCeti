# SphereCeti provenance and dependency ledger

This file records what the roadmap is pinned against and where implementation material may be
mined.  It is a provenance ledger, not an instruction to copy an entire branch or repository.

## 1. Exact dependency snapshot

### SphereCeti toolchain

```text
leanprover/lean4:v4.34.0-rc1
```

### TauCeti

```text
repository  https://github.com/TauCetiProject/TauCeti
commit      8671bee98125933c56b9b00a08ded873b77dd23b
```

The commit is the complete sibling-library snapshot imported by SphereCeti.  It is not described as
a contour-integration release or a sphere-packing release.

### Mathlib

The pinned TauCeti manifest resolves Mathlib to:

```text
repository  https://github.com/leanprover-community/mathlib4
commit      618f225e1ff4a6b2790a944e01b806b7c68bdc56
```

SphereCeti follows that resolved revision.  It does not independently request `master` or a release
tag.

### Sphere-Packing semantic baseline

```text
repository  https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean
commit      bad3de916074748eb88b7d1ee6dbf9494361ad17
```

This is the August 5, 2026 `main` commit adding the radial Schwartz submodule.  The baseline still
uses Lean and Mathlib `v4.32.0`, so the initial SphereCeti package models its public statement
boundary in `SphereCeti/Pinned.lean`.  The model is deleted after the synchronized production
upgrade and is never a source of independent mathematical truth.

## 2. Pinned TauCeti modules consumed directly

### Integral lattices

The roadmap is shaped against:

```text
TauCeti/LinearAlgebra/IntegralLattice/Basic.lean
TauCeti/LinearAlgebra/IntegralLattice/Norm.lean
TauCeti/LinearAlgebra/IntegralLattice/Gram.lean
TauCeti/LinearAlgebra/IntegralLattice/Even.lean
TauCeti/LinearAlgebra/IntegralLattice/Signature.lean
TauCeti/LinearAlgebra/IntegralLattice/Isometry.lean
TauCeti/LinearAlgebra/IntegralLattice/StandardCoordinates.lean
TauCeti/LinearAlgebra/IntegralLattice/Dual/Basic.lean
TauCeti/LinearAlgebra/IntegralLattice/Discriminant/*
TauCeti/LinearAlgebra/IntegralLattice/Unimodular.lean
TauCeti/LinearAlgebra/IntegralLattice/Overlattice/*
```

Relevant existing declarations include:

- `TauCeti.IntegralLattice`;
- `IntegralLattice.ofGramMatrix`;
- integral and rational norm/form comparisons;
- `IntegralLattice.IsEven`;
- `IntegralLattice.IsPosDef` and signature;
- `IntegralLattice.Isometry`;
- `IntegralLattice.dualCarrier` and discriminant group;
- `IntegralLattice.IsUnimodular` and determinant criteria.

SphereCeti adds the bridge from this rational algebraic presentation to Mathlib's real topological
`ZLattice` representation.  It does not copy the TauCeti lattice bundle.

### Contour and complex analysis

Directly consumed:

```text
TauCeti/Analysis/Contour/Cauchy/Goursat.lean
TauCeti/Analysis/Complex/UpperHalfPlane/ResToImagAxis.lean
TauCeti/Analysis/Fourier/Continuous.lean
```

The pole-free meromorphic circle theorem was introduced in the TauCeti contour-integration work at:

```text
66e7c687b9793320e895988f6762ba0da1c99b81
```

and later moved by a tree-wide file-placement refactor.  SphereCeti imports it through the pinned
snapshot `8671bee...` while retaining the origin commit for semantic provenance.

### Modular forms and q-expansions

Directly consumed or targeted:

```text
TauCeti/NumberTheory/ModularForms/ResToImagAxis.lean
TauCeti/NumberTheory/ModularForms/STransform.lean
TauCeti/NumberTheory/ModularForms/QExpansion/Basic.lean
TauCeti/NumberTheory/ModularForms/QExpansion/BigO.lean
TauCeti/NumberTheory/ModularForms/QExpansion/Order.lean
TauCeti/NumberTheory/ModularForms/SturmBound.lean
```

SphereCeti keeps dimension-specific E8 and Leech modular forms in the sphere-packing production
repository.  The TauCeti material supplies generic restriction, transformation, growth, and finite
coefficient-equality machinery.

## 3. Sphere-Packing-Lean material to preserve

At the semantic baseline, preserve the mathematics of:

```text
SpherePacking/Basic/SpherePacking.lean
SpherePacking/Basic/PeriodicPacking.lean
SpherePacking/Basic/E8.lean
SpherePacking/CohnElkies/LPBound.lean
SpherePacking/ForMathlib/RadialSchwartz/*
SpherePacking/MagicFunction/IntegralParametrisations.lean
SpherePacking/MagicFunction/PolyFourierCoeffBound.lean
SpherePacking/MagicFunction/a/*
SpherePacking/MagicFunction/b/*
SpherePacking/MagicFunction/g/*
SpherePacking/ModularForms/*
```

In particular:

- the packing structures and limsup density are the pinned starting definitions;
- the E8 coordinate/basis equivalence, minimum norm, packing, and density are retained;
- `Function.IsRadial` and `RadialSchwartzMap` are the common Fourier boundary;
- the existing modular-form and magic-function proof content is a production asset, even where its
  present file placement or API should be improved.

The root `SpherePacking.lean` currently also imports tactic test modules.  That fact is not a
semantic convention and should be repaired.

## 4. Historical `gauss2` branch

The `gauss2` branch is a proof quarry.  Mine only named coherent results, with source commit and
path recorded in the destination file or PR description.

High-value material includes:

- the completed E8 Cohn--Elkies upper bound;
- the final E8 main theorem assembly;
- completed Fourier permutations of the `a` integral pieces;
- the Möbius-inversion/convex-wedge contour development;
- strengthened Schwartz, sign, and special-value arguments;
- proof-local refactors that reduce duplicate analytic plumbing.

Do not:

- use `gauss2` as the base branch for new production work;
- assume every namespace or helper abstraction on the branch is the desired public API;
- combine branch archaeology, toolchain migration, directory movement, and a hard proof in one PR.

## 5. PR #420

PR #420 targets historical work and contains several separable contributions.  Treat it as source
material for:

1. Schwartz summability on lattices;
2. real dual-lattice adapters;
3. Poisson summation;
4. basis-independent covolume facts;
5. general periodic Cohn--Elkies counting;
6. cleanup of wrappers that obstruct Mathlib simplification.

Each item is ported in a focused PR onto upgraded current `main`.  A claim that PR #420 is “merged
by replacement” must list the replacement declarations; broad textual similarity is not enough.

## 6. Mathematical source papers and theorem scopes

### Optimality and periodic uniqueness

- Maryna S. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185
  (2017), 991--1015.
- Henry Cohn, Abhinav Kumar, Stephen D. Miller, Danylo Radchenko, and Maryna Viazovska,
  *The sphere packing problem in dimension 24*, Annals of Mathematics 185 (2017), 1017--1033.

The roadmap uses their exact sphere-packing optimality and **periodic uniqueness** scopes.  It does
not silently strengthen them to literal uniqueness among all limsup-density packings.

### Linear-programming bound and exact periodic rigidity

- Henry Cohn and Noam Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689--714.

The exact periodic-uniqueness route is specifically Section 8:

- Conjecture 8.1 asks for an optimal auxiliary function whose direct and Fourier transforms have no
  roots away from the candidate lattice lengths;
- the uniqueness proof uses the direct-side root condition to put every periodic center difference
  at an even squared norm;
- Lemma 8.2 proves that the translated centers generate an even integral lattice;
- the finite quotient count and integer Gram determinant force covolume one and occupancy of every
  generated-lattice coset;
- the paper explicitly observes that the uniqueness deduction does not need the Fourier-root
  restriction.

Viazovska's dimension-eight theorem supplies the exact no-extraneous-zero property needed by this
argument, and the 24-dimensional paper supplies its Leech analogue.

### Lattice uniqueness

- Henry Cohn and Abhinav Kumar, *Optimality and uniqueness of the Leech lattice among lattices*,
  Annals of Mathematics 170 (2009), 1003--1050.

The rank-eight theorem also uses the classical characterization of E8 as the unique
positive-definite even unimodular lattice of rank eight.  The intended formal statement is generic
integral-lattice mathematics and should ultimately live in TauCeti.

### Universal optimality and interpolation

- Henry Cohn, Abhinav Kumar, Stephen D. Miller, Danylo Radchenko, and Maryna Viazovska,
  *Universal optimality of the E8 and Leech lattices and interpolation formulas*, Annals of
  Mathematics 196 (2022), 983--1082.

These results motivate preservation of zero multiplicities and quantitative estimates but are not
quietly included in the sphere-packing summit.

### Stability

- Károly J. Böröczky, Danylo Radchenko, and João P. G. Ramos,
  *A quantitative stability result for the sphere packing problem in dimensions 8 and 24*, Journal
  für die reine und angewandte Mathematik 2024 (808), 241--270.

The exact uniqueness statements belong in SphereCeti.  Quantitative lattice and periodic local-frame
stability require a separate roadmap and additional metric/quantitative infrastructure.

### Lattice and code references

- J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed.
- E. Bannai and N. J. A. Sloane, *Uniqueness of certain spherical codes* and related rigidity
  literature as needed by the chosen equality-case proof.
- V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*.
- W. Ebeling, *Lattices and Codes*.

Exact chapter/theorem citations should be added to the implementation PR that chooses the
rank-eight or rootless rank-24 classification route.

## 7. TauCetiRoadmap sources

SphereCeti follows the roadmap discipline and borrows target shape from:

```text
TauCetiRoadmap/IntegralLattices/README.md
TauCetiRoadmap/ContourIntegration/README.md
TauCetiRoadmap/ContourIntegration/Suggested.lean
TauCetiRoadmap/ModularForms/README.md
```

Unlike TauCetiRoadmap, SphereCeti pins TauCeti to a fixed commit and maintains one issue-ready
`UPSTREAM.md` rather than a directory of sibling proposed roadmaps.

## 8. License and adaptation rules

The relevant code repositories are Apache-2.0 licensed.  Adapted source files retain:

- the original copyright line where required;
- all material authors;
- the Apache-2.0 header;
- a module docstring provenance paragraph naming repository, path, and source commit.

A theorem independently reproved after reading a paper still cites the mathematical source.  A
proof substantially ported from code also cites the code source.

Do not copy code from an unclear-license source merely because the mathematical theorem is standard.
Do not list an AI tool as the sole mathematical author where the file is adapted from named human
authors' work.

## 9. Provenance checklist for production PRs

For each mined theorem, record:

```text
Source repository:
Source ref/commit:
Source path:
Destination path:
Statement changed? (how):
Proof changed? (how):
New dependencies:
License/header action:
```

For large ports, add a temporary mapping table to the PR description.  The permanent code should
retain only useful mathematical provenance, not branch-war history.

## 10. Status of this scaffold

`scripts/check_roadmap.py` checks the scaffold for pin coherence, file/link consistency, and
target-shape contracts.  On the pinned toolchain, `lake exe cache get` followed by `lake build`
elaborates every target signature, locally and in CI, with the intentional `sorry` warnings in the
target files as the only warnings.
