# SphereCeti provenance and dependency record

This file records what the roadmap is pinned against and from which sources proofs may be
adapted.  It is a record of provenance, not an instruction to copy an entire branch or repository.

## 1. Exact dependency snapshot

### SphereCeti toolchain

```text
leanprover/lean4:v4.36.0-rc2
```

### TauCeti

```text
repository  https://github.com/TauCetiProject/TauCeti
commit      83769e442d55cda9d85b3927a93b286831c595ff
```

The commit is the complete sibling-library snapshot imported by SphereCeti.  It is not described as
a contour-integration release or a sphere-packing release.

### Mathlib

The pinned TauCeti manifest resolves Mathlib to:

```text
repository  https://github.com/leanprover-community/mathlib4
commit      1b1ccf4b088b32fa3f23f2de1127433254a81e1e
```

SphereCeti follows that resolved revision.  It does not independently request `master` or a release
tag.

### Sphere-Packing semantic baseline

```text
repository  https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean
commit      bad3de916074748eb88b7d1ee6dbf9494361ad17
```

This baseline contains the radial Schwartz submodule and uses Lean and Mathlib `v4.32.0`.
`SphereCetiRoadmap/Pinned.lean` models its public statements until PR A2 replaces the model with
direct imports from the synchronized production dependency.  The model is never a source of
independent mathematical truth.

The current production head observed on 2026-11-10 is
[`803f1623539ece84a19b2b6805764b8dea9ea6e6`](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/commit/803f1623539ece84a19b2b6805764b8dea9ea6e6),
dated 2026-11-05, on Lean `v4.35.0`.  The 4.32 baseline above is frozen provenance, not the current
production toolchain.  Production still differs from this package's 4.36.0-rc2 line; A1/A2 remain
necessary before replacing `Pinned.lean` with imports.

## 2. Pinned TauCeti modules used directly

### Integral lattices

The roadmap statements are written against:

```text
TauCeti/LinearAlgebra/IntegralLattice/Basic.lean
TauCeti/LinearAlgebra/IntegralLattice/Norm.lean
TauCeti/LinearAlgebra/IntegralLattice/Gram.lean
TauCeti/LinearAlgebra/IntegralLattice/Even.lean
TauCeti/LinearAlgebra/IntegralLattice/Signature.lean
TauCeti/LinearAlgebra/IntegralLattice/Isometry/Basic.lean
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

SphereCeti adds the bridge from this rational algebraic presentation to the real topological
`ZLattice` representation.  It does not copy the TauCeti lattice definitions.

### Real lattices, Poisson summation, and theta series

Used directly:

```text
TauCeti/Algebra/Module/ZLattice/Dual.lean
TauCeti/Algebra/Module/ZLattice/Integral.lean
TauCeti/Algebra/Module/ZLattice/Determinant.lean
TauCeti/Algebra/Module/ZLattice/Covolume.lean
TauCeti/Algebra/Module/ZLattice/Shell.lean
TauCeti/Algebra/Module/ZLattice/RationalModel.lean
TauCeti/Algebra/Module/ZLattice/RealModel.lean
TauCeti/Algebra/Module/ZLattice/ModelShell.lean
TauCeti/Analysis/Distribution/SchwartzSpace/ZLattice.lean
TauCeti/Analysis/Fourier/PoissonSummation.lean
TauCeti/NumberTheory/ModularForms/ThetaSeries/Basic.lean
TauCeti/NumberTheory/ModularForms/ThetaSeries/QExpansion.lean
TauCeti/NumberTheory/ModularForms/ThetaSeries/Inversion.lean
TauCeti/NumberTheory/ModularForms/ThetaSeries/LevelOne.lean
TauCeti/NumberTheory/ModularForms/ThetaSeries/Eisenstein.lean
TauCeti/NumberTheory/ModularForms/ThetaSeries/RankTwentyFour.lean
```

These supply `ZLattice.dual`, the real predicates `ZLattice.IsIntegral`, `ZLattice.IsEven`, and
`ZLattice.IsUnimodular`, shells and representation numbers, the summability of Schwartz functions over a lattice and its
dual, Poisson summation
`SchwartzMap.tsum_eq_tsum_dual_fourier`, and the theta series `ZLattice.thetaSeries` with its
q-expansion, the `S`-transformation `ZLattice.thetaSeries_S_smul`, the level-one theta form
`ZLattice.thetaForm`, and the rank-8 and rank-24 identities.  The rational and real models
`ZLattice.ratModel` and `IntegralLattice.realModel`, with their invariant, dual, and shell
comparisons, are the target of SphereCeti's presentation bridge.  The
[resync watchlist](UPSTREAM.md#g-resync-watchlist) records the commits that introduced them.

### E8, the Golay code, and the Leech lattice

Used directly:

```text
TauCeti/LinearAlgebra/IntegralLattice/RootLattice/TypeE/Basic.lean
TauCeti/LinearAlgebra/IntegralLattice/RootLattice/TypeE/Roots.lean
TauCeti/LinearAlgebra/IntegralLattice/PosDef/Minimum.lean
TauCeti/LinearAlgebra/IntegralLattice/PosDef/RepresentationNumber.lean
TauCeti/LinearAlgebra/IntegralLattice/PosDef/SmallRankUnimodular.lean
TauCeti/InformationTheory/Coding/Binary/Golay/Basic.lean
TauCeti/InformationTheory/Coding/Equivalence.lean
TauCeti/LinearAlgebra/IntegralLattice/ConstructionB/Golay.lean
TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/Basic.lean
TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/Minimum.lean
TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/MinimalVectors.lean
```

`SmallRankUnimodular.lean` supplies the theta-independent classification of even unimodular
lattices of rank eight, and `MinimalVectors.lean` the Leech kissing number `196560` by direct
enumeration.  The canonical algebraic E8 and Leech lattices are `IntegralLattice.typeE₈RootLattice` and
`leechLattice`; the canonical Golay code is `BinaryGolay.code`, in the coordinates of its systematic
generator.  SphereCeti compares its Euclidean lattices and its other code and basis descriptions
with these objects and does not construct them again.

### Contour and complex analysis

Used directly:

```text
TauCeti/Analysis/Complex/UpperHalfPlane/ResToImagAxis.lean
TauCeti/Analysis/Fourier/Continuous.lean
```

### Modular forms and q-expansions

Used directly or targeted:

```text
TauCeti/NumberTheory/ModularForms/ResToImagAxis.lean
TauCeti/NumberTheory/ModularForms/STransform.lean
TauCeti/NumberTheory/ModularForms/QExpansion/Basic.lean
TauCeti/NumberTheory/ModularForms/QExpansion/BigO.lean
TauCeti/NumberTheory/ModularForms/QExpansion/Order.lean
TauCeti/NumberTheory/ModularForms/SturmBound.lean
TauCeti/NumberTheory/ModularForms/LevelOne/GradedRing.lean
```

`LevelOne/GradedRing.lean` supplies `TauCeti.ModularForm.mvPolynomialEquivModularForms`, the
isomorphism between `ℂ[E₄, E₆]` and the level-one modular forms, for the theta identities of ranks 8
and 24 once the theta series is a modular form.

SphereCeti keeps dimension-specific E8 and Leech modular forms in the sphere-packing production
repository.  The TauCeti material supplies the general results on restriction, transformation,
growth, and finite coefficient equality.

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
- `Function.IsRadial` and `RadialSchwartzMap` are the common setting for Fourier analysis;
- the existing modular-form and magic-function proof content is a production asset; named file and
  API changes belong in the migration sequence.

In the pinned production snapshot, the root `SpherePacking.lean` imports tactic test modules.
PR B1 removes those imports; they are not a semantic convention.

## 4. Source branch: `gauss2`

The `gauss2` branch is a source of proofs to adapt.  Adapt only named, coherent results, with the
source commit and path recorded in the destination file or PR description.

High-value material includes:

- the completed E8 Cohn–Elkies upper bound;
- the final E8 main theorem assembly;
- completed Fourier permutations of the `a` integral pieces;
- the contour development in the convex wedge under the inversion `z ↦ -1/z`;
- strengthened Schwartz, sign, and special-value arguments.

The Layer 8 contour targets are based on the following branch material at commit
`01f23eccf963c50250c9e48dd103e8cc88c36f85`, with two deliberate changes: the contour-deformation
theorems are stated for a single pair of kernels rather than for families indexed by the radius,
and the change-of-variables and half-infinite-rectangle statements carry explicit derivative and
integrability hypotheses instead of relying on the conventional values Lean assigns to derivatives
and integrals that do not exist.

```text
SpherePacking/Contour/MobiusInv/WedgeSetContour.lean   -- one-forms, wedge, signed permutations
SpherePacking/ForMathlib/CauchyGoursat/OpenRectangular.lean  -- half-infinite rectangles
SpherePacking/Integration/Measure.lean                 -- interval measures for the profiles
SpherePacking/MagicFunction/a/Eigenfunction.lean       -- six-piece assembly, +1 component
SpherePacking/MagicFunction/b/Eigenfunction.lean       -- six-piece assembly, -1 component
```

The corresponding design documents are the blueprint sections
`blueprint/src/subsections/contour-integration.tex` and
`blueprint/src/subsections/integration-infrastructure.tex` of Sphere-Packing-Lean PR #435 at
commit `5df95c5124ba691f0d377dbe8a54d6972276b0ef`, and Chapters 4–5 of Sidharth Hariharan's M4R
thesis (`thefundamentaltheor3m/M4R_Thesis`, commit
`5c478f0193104a70f070bfcfece283767ba17304`), which record the dependency structure of the
eigenfunction and double-zero arguments.

Do not:

- use `gauss2` as the base branch for new production work;
- assume every namespace or helper abstraction on the branch is the desired public API;
- combine digging through the branch's history, toolchain migration, directory movement, and a
  hard proof in one PR.

## 5. PR #420

PR #420 is a source of proofs to adapt, containing several separable contributions:

1. Schwartz summability on lattices;
2. comparison of the real inner-product dual lattice with the bilinear-form dual;
3. Poisson summation;
4. basis-independent covolume facts;
5. general periodic Cohn–Elkies counting.

Items 1–4 are already supplied by the pinned TauCeti snapshot: Schwartz lattice summability,
`ZLattice.dual_def`, `SchwartzMap.tsum_eq_tsum_dual_fourier`, and the basis-independent covolume
API listed in §2.  Import these declarations rather than porting those proofs.  Only the general
periodic Cohn–Elkies counting is adapted onto production `main` after A1, with the exact source
commit and path recorded.  A claim that PR #420 is “merged by replacement” must list the replacement
declarations; broad textual similarity is not enough.

## 6. Mathematical source papers and theorem scopes

### Optimality and periodic uniqueness

- Maryna S. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185
  (2017), 991–1015.
- Henry Cohn, Abhinav Kumar, Stephen D. Miller, Danylo Radchenko, and Maryna Viazovska,
  *The sphere packing problem in dimension 24*, Annals of Mathematics 185 (2017), 1017–1033.

The roadmap uses their exact sphere-packing optimality and **periodic uniqueness** scopes.  It does
not silently strengthen them to literal uniqueness among all limsup-density packings.

### Linear-programming bound and exact periodic rigidity

- Henry Cohn and Noam Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714.

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
  Annals of Mathematics 170 (2009), 1003–1050.

The rank-eight theorem also uses the classical characterization of E8 as the unique
positive-definite even unimodular lattice of rank eight.  The intended formal statement is generic
integral-lattice mathematics whose intended home is TauCeti.

### Stability

- Károly J. Böröczky, Danylo Radchenko, and João P. G. Ramos,
  *A quantitative stability result for the sphere packing problem in dimensions 8 and 24*, Journal
  für die reine und angewandte Mathematik 2024 (808), 241–270.

The exact uniqueness statements belong in SphereCeti.  Quantitative lattice and periodic local-frame
stability require a separate roadmap and additional metric/quantitative infrastructure.

### Lattice and code references

- N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Springer (2002), Chapter VI,
  §4 and Plates I–IX.  These supply the ADE classification, ranks, root counts, and Bourbaki
  numbering used by the rank-eight route.
- H.-V. Niemeier, “Definite quadratische Formen der Dimension 24 und Diskriminante 1,” *Journal of
  Number Theory* **5** (1973), 142–178,
  [DOI](https://doi.org/10.1016/0022-314X(73)90068-1).  Its main classification theorem gives the
  24 positive-definite even unimodular rank-24 lattices.
- J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer
  (1999), [DOI](https://doi.org/10.1007/978-1-4757-6568-7).  Chapter 4, §8.1 fixes the E8 model;
  Chapter 16, §1 and Table 16.1 enumerate the Niemeier lattices and §3 verifies the list; Chapter
  18, §§2–5 gives the root-system proof and constructions, with §5 characterizing the rootless
  case as the Leech lattice.
- V. V. Nikulin, “Integral symmetric bilinear forms and some of their applications,” *Math.
  USSR-Izv.* **14** (1980).  Section 1.1 fixes discriminant-form conventions; §1.4,
  Proposition 1.4.1 supplies the even-overlattice/isotropic-subgroup correspondence.
- W. Ebeling, *Lattices and Codes*, 3rd ed., Springer (2013).  Chapter 1 supplies lattice, dual,
  discriminant, and glue calculations; Chapter 3 supplies the even unimodular examples.

The Leech construction targets pin the Conway–Sloane normalization: the extended Golay generator
polynomial, the modulo-eight/residue-code coordinate description scaled by `1 / sqrt 8`, and the
24-row integer basis matrix in that same scaling.

### Coefficient construction of the magic functions

- *A construction of the sphere-packing magic functions in dimensions 8 and 24*, Hexagon
  2610.00330v1, <https://hexagonmath.org/2610.00330v1>; TeX source
  <https://hexagonmath.org/api/v1/works/2610.00330v1/source?path=magic-8-24.tex>, retrieved
  2026-11-22.  The source ends with the statement “This document was generated by ChatGPT-6 Astra
  with prompting from Thomas Hales.”  The sibling roadmap in `SphereCetiRoadmap/CoefficientMagic/` takes its definitions
  and the statements of its numbered results as targets; none is used as a hypothesis.
- Its stated scope is kept: uniqueness is within the coefficient families of its Theorems 2.1 and
  11.1.  Uniqueness among all radial Schwartz functions with the same interpolation data uses the
  interpolation theorem of Cohn, Kumar, Miller, Radchenko, and Viazovska (2022), and is not a
  target.  The sign inequalities are those of Viazovska (2017) and of Cohn, Kumar, Miller,
  Radchenko, and Viazovska (2017), transferred by comparison.
- Luca Candelori and Cameron Franc, *Vector valued modular forms and the modular orbifold of
  elliptic curves*, International Journal of Number Theory 13 (2017), 39–63, arXiv:1506.09192: the
  Riemann–Roch argument for existence that the paper uses; here it is needed only for the
  geometric correspondence.
- The existence proof from explicit modular forms in
  `SphereCetiRoadmap/CoefficientMagic/MODULAR_EXISTENCE.md` was proposed for
  this roadmap on 2026-11-22.  It replaces the paper's Riemann–Roch step for existence by explicit
  solutions in a finite-dimensional family built from `E₄`, `E₆`, `Δ`, and the theta quartics.  It claims no
  mathematical novelty.  Its finite algebra is checked exactly by
  `scripts/check_modular_identities.py` (run with SymPy 1.14.0); in Lean only the two identities
  `cuspMatrix *ᵥ witness = 0` are proved.  The transformation laws, the expansions at the
  cusp, and the theorem that such a solution gives a coefficient solution are targets.
- Reuse sources for the theta identities, on the older production toolchain and available only
  after the Layer 0 migration:
  `SpherePacking/ModularForms/JacobiTheta/{Defs,Basic,MDifferentiable,JacobiIdentity,Derivative}.lean`
  and `SpherePacking/ModularForms/Derivative.lean` at
  `Sphere-Packing-Lean@bad3de916074748eb88b7d1ee6dbf9494361ad17`.  The targets `Witness.H₂`,
  `Witness.H₄` are stated through Mathlib's `jacobiTheta₂` and are to be identified with the
  production `H₂`, `H₄` then.  A transitive axiom audit of those files is still required.

## 7. TauCetiRoadmap sources

SphereCeti follows the roadmap discipline and borrows the form of its target statements from:

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

For each theorem adapted from an existing source, record:

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
retain only useful mathematical provenance, not a history of competing branches.

## 10. Roadmap-package validation

`scripts/check_roadmap.py` checks the package for pin coherence, file/link consistency, and
required features of the target statements, for the primary roadmap and for each sibling roadmap
registered in `sphereceti.toml`.  On the pinned toolchain, `lake exe cache get`
followed by `lake build` elaborates every target signature, locally and in CI, with the
intentional `sorry` warnings in the target files as the only warnings.
