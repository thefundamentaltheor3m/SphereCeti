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

This baseline contains the radial Schwartz submodule and uses Lean and Mathlib `v4.32.0`.
`SphereCeti/Pinned.lean` models its public statement boundary until PR A2 replaces the model with
direct imports from the synchronized production dependency.  The model is never a source of
independent mathematical truth.

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

Origin commit for the pole-free meromorphic circle theorem:

```text
66e7c687b9793320e895988f6762ba0da1c99b81
```

Pinned import path: `TauCeti/Analysis/Contour/Cauchy/Goursat.lean` at snapshot `8671bee...`.

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
- the existing modular-form and magic-function proof content is a production asset; named file and
  API changes belong in the migration sequence.

In the pinned production snapshot, the root `SpherePacking.lean` imports tactic test modules.
PR B1 removes those imports; they are not a semantic convention.

## 4. Source branch: `gauss2`

The `gauss2` branch is a proof quarry.  Mine only named coherent results, with source commit and
path recorded in the destination file or PR description.

High-value material includes:

- the completed E8 Cohn--Elkies upper bound;
- the final E8 main theorem assembly;
- completed Fourier permutations of the `a` integral pieces;
- the Möbius-inversion/convex-wedge contour development;
- strengthened Schwartz, sign, and special-value arguments.

Do not:

- use `gauss2` as the base branch for new production work;
- assume every namespace or helper abstraction on the branch is the desired public API;
- combine branch archaeology, toolchain migration, directory movement, and a hard proof in one PR.

## 5. PR #420

PR #420 is a source quarry containing several separable contributions:

1. Schwartz summability on lattices;
2. real dual-lattice adapters;
3. Poisson summation;
4. basis-independent covolume facts;
5. general periodic Cohn--Elkies counting.

Each item is ported in a focused PR onto production `main` after A1.  A claim that PR #420 is “merged
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
integral-lattice mathematics whose intended home is TauCeti.

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

- N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Springer (2002), Chapter VI,
  §4 and Plates I--IX.  These supply the ADE classification, ranks, root counts, and Bourbaki
  numbering used by the rank-eight route.
- H.-V. Niemeier, “Definite quadratische Formen der Dimension 24 und Diskriminante 1,” *Journal of
  Number Theory* **5** (1973), 142--178,
  [DOI](https://doi.org/10.1016/0022-314X(73)90068-1).  Its main classification theorem gives the
  24 positive-definite even unimodular rank-24 lattices.
- J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer
  (1999), [DOI](https://doi.org/10.1007/978-1-4757-6568-7).  Chapter 4, §8.1 fixes the E8 model;
  Chapter 16, §1 and Table 16.1 enumerate the Niemeier lattices and §3 verifies the list; Chapter
  18, §§2--5 gives the root-system proof and constructions, with §5 characterizing the rootless
  case as the Leech lattice.
- V. V. Nikulin, “Integral symmetric bilinear forms and some of their applications,” *Math.
  USSR-Izv.* **14** (1980).  Section 1.1 fixes discriminant-form conventions; §1.4,
  Proposition 1.4.1 supplies the even-overlattice/isotropic-subgroup correspondence.
- W. Ebeling, *Lattices and Codes*, 3rd ed., Springer (2013).  Chapter 1 supplies lattice, dual,
  discriminant, and glue calculations; Chapter 3 supplies the even unimodular examples.

The Leech construction targets pin the Conway--Sloane normalization: the extended Golay generator
polynomial, the modulo-eight/residue-code coordinate description scaled by `1 / sqrt 8`, and the
24-row integer basis matrix in that same scaling.

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

A theorem independently reproved after reading a paper cites the mathematical source.  A
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

For large ports, add a temporary mapping table to the PR description.  The permanent code must
retain only useful mathematical provenance, not branch-war history.

## 10. Roadmap-package validation

`scripts/check_roadmap.py` checks the package for pin coherence, file/link consistency, and
target-shape contracts.  On the pinned toolchain, `lake exe cache get` followed by `lake build`
elaborates every target signature, locally and in CI, with the intentional `sorry` warnings in the
target files as the only warnings.
