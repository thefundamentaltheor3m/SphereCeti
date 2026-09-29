# Potential Mathlib and TauCeti destinations

This file lists results and topics intended for Mathlib or TauCeti, each described so that it
can be filed as an issue.  It deliberately does **not** create a parallel directory tree of
upstream roadmaps.  Each item records the intended home, a precise statement or scope, and the
fallback used if the item has not landed upstream when it is needed (a local version, or an
existing TauCeti import); the items are not ordered.  Filing an item as an issue does not commit
Mathlib or TauCeti to accepting it.

The list follows two rules:

1. SphereCeti never waits for upstream work.  When the production development needs a general
   theorem, it proves it locally, stated in the form intended for its upstream home, and keeps the
   proof usable.
2. Contributing a result upstream lets the local proof be replaced by an import; it is not part of
   the proof of the sphere-packing main theorems.

## Issue title suggestion

```text
[SphereCeti upstream candidates] General lattice, Fourier, contour, and rigidity results
```

## A. Focused Mathlib candidates

### A1. Continuity of the Fourier transform of an integrable function on a finite-dimensional real
inner-product space

- [ ] **Destination:** Mathlib Fourier analysis.
- [ ] **Current source:** `TauCeti.Analysis.Fourier.Continuous`.
- [ ] **Candidate declarations:**

  ```lean
  continuous_fourier_of_integrable
  continuous_fourierInv_of_integrable
  ```

- [ ] **Why general:** these are specializations of Mathlib's vector Fourier theorem.
- [ ] **SphereCeti use:** pointwise Fourier sign conditions and limits in Cohn--Elkies.
- [ ] **Fallback:** import TauCeti.

### A2. Generic restriction to the positive imaginary axis

- [ ] **Destination:** Mathlib upper-half-plane analysis.
- [ ] **Current source:**
  `TauCeti.Analysis.Complex.UpperHalfPlane.ResToImagAxis`.
- [ ] **Candidate declarations:**

  ```lean
  UpperHalfPlane.resToImagAxis
  UpperHalfPlane.RealOnImagAxis
  UpperHalfPlane.PosOnImagAxis
  UpperHalfPlane.EventuallyPosOnImagAxis
  ```

  together with evaluation, algebraic closure, differentiability, and appropriate `@[simp]` and
  `@[fun_prop]` lemmas.

- [ ] **Why general:** none of the definitions is intrinsically modular-form-specific.
- [ ] **SphereCeti use:** sign proofs for E8 and Leech modular kernels.
- [ ] **Fallback:** import TauCeti and migrate Sphere-Packing's older duplicate API by aliases.

### A3. Slash-by-`S` restriction identity

- [ ] **Destination:** Mathlib modular forms, if the maintainers prefer it there; otherwise TauCeti.
- [ ] **Current source:** `TauCeti.NumberTheory.ModularForms.ResToImagAxis`.
- [ ] **Candidate declaration:**

  ```lean
  UpperHalfPlane.resToImagAxis_slash_S
  ```

- [ ] **Why general:** it is a direct identity for Mathlib's slash action and the general
  imaginary-axis restriction.
- [ ] **SphereCeti use:** the `t ↦ 1/t` symmetry underlying Fourier eigenfunction constructions.
- [ ] **Fallback:** exact TauCeti import.

### A4. Generic `S`-transformation of a slash-invariant form and its logarithmic derivative

- [ ] **Destination:** Mathlib modular forms or complex analysis.
- [ ] **Current source:** `TauCeti.NumberTheory.ModularForms.STransform`.
- [ ] **Candidate declarations:**

  ```lean
  ModularForm.comp_ofComplex_S_transform
  ModularForm.differentiableAt_comp_ofComplex_S_transform
  ModularForm.logDeriv_comp_ofComplex_S_transform
  ```

- [ ] **SphereCeti use:** contour pairing and zero-counting arguments.
- [ ] **Fallback:** exact TauCeti import.

### A5. q-coefficient vanishing versus cusp-function Big-O

- [ ] **Destination:** Mathlib q-expansion theory, or TauCeti if Mathlib considers it too
  specialized.
- [ ] **Current source:** `TauCeti.NumberTheory.ModularForms.QExpansion.BigO`.
- [ ] **Candidate declarations:**

  ```lean
  cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero
  qExpansion_coeff_eq_zero_of_cuspFunction_isBigO_pow
  tendsto_valueAtInfty
  ```

- [ ] **Why general:** the main layer is about periodic functions with analytic cusp functions,
  with modular-form corollaries.
- [ ] **SphereCeti use:** uniform cusp decay and Schwartz estimates from finite q-data.
- [ ] **Fallback:** import TauCeti.

### A6. `SchwartzMap.mkOfCocompact`

- [ ] **Destination:** Mathlib Schwartz space.
- [ ] **Current source:**
  `SpherePacking.ForMathlib.RadialSchwartz.SchwartzMap`.
- [ ] **Candidate declaration:** construct a Schwartz map when all polynomial derivative bounds hold
  eventually in the cocompact filter, using compact boundedness for the remaining region.
- [ ] **Why general:** no sphere-packing content.
- [ ] **SphereCeti use:** magic-function Schwartz proofs.
- [ ] **Fallback:** retain a focused `ForMathlib` file with provenance and regression tests.

### A7. Radial Schwartz submodule and Fourier involution

- [ ] **Destination:** Mathlib Schwartz/Fourier analysis.
- [ ] **Current source:** `SpherePacking.ForMathlib.RadialSchwartz.Basic` and related files.
- [ ] **Candidate declarations:**

  ```lean
  Function.IsRadial
  RadialSchwartzMap
  RadialSchwartzMap.fourierTransformCLM
  RadialSchwartzMap.fourier_apply_apply
  ```

  plus self/skew-adjoint eigenspace decompositions.

- [ ] **Why general:** it is a reusable Fourier-analytic subspace on arbitrary finite-dimensional
  inner-product spaces.
- [ ] **SphereCeti use:** common 8+24 magic-function layer.
- [ ] **Fallback:** preserve the current production implementation and make it the standard
  version there.
- [ ] **Design note:** intrinsic radiality factors through `‖x‖`; `ofNormSq` is a separate
  constructor, not the definition of radiality.

### A8. Euclidean `ZLattice` norm-shell finiteness

- [ ] **Destination:** Mathlib `Algebra/Module/ZLattice`.
- [ ] **Candidate declarations:** finiteness of

  ```lean
  {x : Λ | ‖(x : V)‖ ≤ R}
  {x : Λ | ‖(x : V)‖ ^ 2 = a}
  ```

  and transport under linear isometries.
- [ ] **SphereCeti use:** theta coefficients, minimum norms, equality spectra.
- [ ] **Fallback:** local `SpherePacking/Lattice/Euclidean/Shell.lean`.

### A9. Real inner-product dual lattice versus the bilinear-form dual

- [ ] **Destination:** Mathlib bilinear-form dual lattice / `ZLattice` comparison.
- [ ] **Candidate statement:** identify the inner-product dual of a full Euclidean `ℤ`-lattice with
  `LinearMap.BilinForm.dualSubmodule`, and establish discreteness/full rank.
- [ ] **SphereCeti use:** Poisson summation and self-duality.
- [ ] **Fallback:** local bridge, explicitly connected to TauCeti's rational dual carrier.

### A10. Covolume squared versus Gram determinant

- [ ] **Destination:** Mathlib `ZLattice`/Haar measure.
- [ ] **Candidate statement:** for a real lattice basis, square of the covolume equals the
  determinant of its Gram matrix; include basis independence and positive-definite square-root
  corollaries.
- [ ] **SphereCeti use:** compare real covolume with TauCeti discriminant/unimodularity.
- [ ] **Fallback:** SphereCeti real/rational bridge.

### A11. Lattice Poisson summation and theta series

- [ ] **Destination:** the TauCeti ThetaSeries roadmap, where general real-lattice duality,
  Poisson summation, theta series, transformation laws, the modular theta form, and the
  rank-8/rank-24 classifications are to be developed.
- [ ] **SphereCeti use:** the provisional local statements in the `ThetaSeries` namespace of
  `Suggested.lean` are stated to match that roadmap's targets; the presentation bridges and
  E8/Leech corollaries use them.
- [ ] **Fallback:** those provisional local statements, to be deleted and replaced by imports; they
  must not grow into a second general implementation.
- [ ] **Upstream test:** the provisional `ThetaSeries` namespace is deleted and replaced by direct
  TauCeti imports.

### A12. Contour deformation for half-infinite rectangles

- [ ] **Destination:** Mathlib complex analysis, beside the bounded rectangular Cauchy--Goursat
  theorem.
- [ ] **Current source:** `Sphere-Packing-Lean` `ForMathlib/CauchyGoursat/OpenRectangular.lean`
  (see `PROVENANCE.md`).
- [ ] **Candidate declaration:** deformation of a horizontal edge into the two vertical
  half-lines above its endpoints, with explicit `IntegrableOn` hypotheses on the half-lines and
  the top edge controlled by convergence of the top-edge integrals to zero.
- [ ] **Why general:** it depends only on the bounded rectangle theorem and dominated limits; the
  statement mentions no packing or modular object.
- [ ] **SphereCeti use:** vertical-line rewrites, Laplace representations, and double-zero
  arguments for the magic functions.
- [ ] **Fallback:** the Layer 8 target in `Suggested.lean`.
- [ ] **Upstream test:** no project import remains in a minimal reproduction.

### A13. Segment change of variables for curve integrals

- [ ] **Destination:** Mathlib `MeasureTheory.Integral.CurveIntegral`.
- [ ] **Current source:** `Sphere-Packing-Lean` `Contour/MobiusInv/WedgeSetContour.lean`
  (see `PROVENANCE.md`), restated for a single pair of kernels with genuine derivative
  hypotheses.
- [ ] **Candidate declaration:** change of variables along `Path.segment a b` under
  `ContinuousOn` plus interior `HasDerivAt` hypotheses, with the image path given by
  `Path.map'`.  Mathlib already provides `Path.map'` and `curveIntegral_segment`; the
  change-of-variables lemma is the genuinely new piece.
- [ ] **Why general:** it is a basic curve-integral lemma about Mathlib's own `curveIntegral`
  and `Path.segment`, independent of any application geometry.
- [ ] **SphereCeti use:** the change of variables `z ↦ -1/z` in the magic-function contour
  integrals.
- [ ] **Fallback:** the Layer 8 target in `Suggested.lean`.
- [ ] **Upstream test:** no project import remains in a minimal reproduction.

The structure `ClosedOneFormOn` (which packages the closed-one-form hypotheses together), the
wedge set, and the two signed contour permutations are application geometry and remain in
SphereCeti/Sphere-Packing (section E); Mathlib's Poincaré lemma takes the differentiability and
closure-continuity hypotheses separately.

## B. TauCeti IntegralLattices roadmap extensions

These are general algebraic lattice results.  Their sphere-packing consequences remain in
SphereCeti.

### B0. Cohn--Elkies generated-lattice lemma

- [ ] **Destination:** TauCeti IntegralLattices, with a possible later Mathlib extraction of the
  Euclidean subgroup lemma.
- [ ] **Source:** Cohn--Elkies, *New upper bounds on sphere packings I*, Lemma 8.2.
- [ ] **Target statement:** if `S ⊆ V` contains `0`, spans a finite-dimensional real
  inner-product space, and every pairwise squared distance is an even integer, then the additive
  subgroup generated by `S` is a full even integral lattice.
- [ ] **Reusable proof ingredients:** polarization, finite generation from a real basis chosen in
  `S`, discreteness of an integral Gram lattice, and an `IntegralLattice` presentation of the
  generated group.
- [ ] **Why TauCeti:** this is pure integral-lattice formation and is independent of packing
  density or Cohn--Elkies certificates once its hypotheses are stated.
- [ ] **SphereCeti fallback:** `Rigidity.generatedIntegralLattice_evenIntegral_full`.

### B1. E8 as the unique positive-definite even unimodular rank-eight lattice

- [ ] **Destination:** extension of `TauCetiRoadmap/IntegralLattices`.
- [ ] **Target statement:** every positive-definite even unimodular integral lattice of rank `8` is
  integrally isometric to a canonical E8 integral lattice.
- [ ] **Required supporting results:**
  - canonical E8 Gram/integral lattice built from TauCeti root data;
  - roots/vectors of norm `2`;
  - finite crystallographic root system, spanning, and ADE decomposition;
  - rank `8` plus `240` roots identifies type E8;
  - the E8 root sublattice has index one;
  - isometry from equality of Gram data;
  - invariance of evenness, unimodularity, and rank.
- [ ] **Why TauCeti:** the statement mentions no real packing, density, or Fourier analysis.
- [ ] **Fallback:** if TauCeti has not provided it when the production uniqueness proof needs
  it, production proves it locally, with its conclusion stated as an `IntegralLattice.Isometry`
  exactly as intended upstream, and replaces the local proof by an import once TauCeti provides
  it.
- [ ] **Not the preferred proof:** a mass-formula proof would require much more infrastructure and
  yields less explicit data for transporting packings.

### B2. Rootless rank-24 even-unimodular uniqueness

- [ ] **Destination:** a dedicated Niemeier-completeness extension of the Integral Lattices
  roadmap.  That roadmap defines the twenty-four reference lattices but does not prove
  completeness, so this endpoint remains a mandatory SphereCeti dependency.
- [ ] **Target statement:** every positive-definite even unimodular integral lattice of rank `24`
  with no norm-`2` vectors is isometric to the Leech lattice.
- [ ] **Implementation route:** Niemeier classification with the exact 24-case root-system list,
  canonical lattices constructed from their glue codes, and an integral-lattice classification
  isometry; the enumeration of the cases and the selection of the matching case are to be
  developed upstream, not in SphereCeti.
- [ ] **Required isolation theorem:** the norm-`2` root set is empty if and only if the classified
  Niemeier type is Leech.
- [ ] **Fallback:** if TauCeti has not provided it when the production uniqueness proof needs
  it, production proves it locally, stated and namespaced in the form intended upstream, never as
  an axiom, and replaces the local proof by an import once TauCeti provides it.

### B3. Canonical E8 integral lattice from root-system data

- [ ] **Destination:** TauCeti integral-lattice/root-system bridge.
- [ ] **Target:** convert TauCeti's E8 Cartan/root data into `IntegralLattice`, prove positive
  definiteness, evenness, unimodularity, determinant one, and identify its 240 roots.
- [ ] **SphereCeti use:** compare the existing Euclidean E8 definition with the canonical algebraic
  E8 object.

### B4. Explicit Leech integral lattice

- [ ] **Destination:** TauCeti rank-24/code-lattice roadmap.
- [ ] **Target:** a canonical rational integral-lattice object with coordinate/glue and Gram
  presentations, equality between them, evenness, unimodularity, rootlessness, and minimum norm.
- [ ] **SphereCeti use:** the algebraic object behind the real packing.

### B5. Integral-presentation bridge to the ThetaSeries roadmap

- [ ] **Destination:** the analytic theta series, its modularity, and the low-rank
  classifications belong to the TauCeti ThetaSeries roadmap; evenness and unimodularity of
  presentations belong to the IntegralLattices side.
- [ ] **Target:** the bridge from an integral presentation to the roadmap's real-lattice
  evenness, unimodularity, and shell coefficients.
- [ ] **SphereCeti use:** the Layer 5 presentation bridges; avoid a sphere-packing-specific theta
  namespace.

## C. TauCeti coding-theory and code-lattice roadmap

### C1. Linear codes over finite fields

- [ ] **Destination:** new TauCeti coding-theory roadmap.
- [ ] **Scope:** linear codes, duality, Hamming weight/distance, weight enumerators, self-dual and
  doubly-even binary codes, equivalence under coordinate permutations.
- [ ] **Scope limit:** reusable algebraic coding theory, not a one-off Golay matrix verification.

### C2. Extended binary Golay code

- [ ] **Destination:** coding-theory roadmap.
- [ ] **Targets:** explicit construction; dimension `12`; self-duality; doubly-evenness; minimum
  distance `8`; relevant weight enumerator and automorphism facts.
- [ ] **SphereCeti use:** Leech coordinate/glue construction and rootlessness.

### C3. Code-lattice constructions

- [ ] **Destination:** code-lattice roadmap connected to IntegralLattices.
- [ ] **Targets:** Construction A and its dual/even/unimodular criteria, shifted/glue variants, and
  explicit E8/Leech comparisons.
- [ ] **Critical naming rule:** naive Construction A from the extended Golay code is not itself the
  Leech lattice.

## D. Larger TauCeti roadmaps suggested by the uniqueness literature

These are not required to finish SphereCeti's main theorems on density and exact periodic
uniqueness.

### D1. Radial Fourier interpolation in dimensions 8 and 24

- [ ] **Scope:** interpolation bases, uniqueness of radial Schwartz functions from values and radial
  derivatives at E8/Leech radii, construction of the magic functions as basis elements.
- [ ] **Source:** the E8/Leech universal-optimality and interpolation theory.
- [ ] **SphereCeti preparation:** retain exact zero multiplicities and radial derivative data.

### D2. Universal optimality of E8 and Leech

- [ ] **Scope:** point configurations, admissible pair potentials, completely monotone functions of
  squared distance, energy per point, periodic and lattice formulations, interpolation-derived
  lower bounds, equality and uniqueness.
- [ ] **Why separate:** this is a theory of energies, not merely sphere radius and packing density.
- [ ] **Dependencies:** D1 plus point-configuration/energy infrastructure.

### D3. Quantitative stability for sharp lattice inequalities

- [ ] **Scope:** norms/metrics on Gram matrices and lattices modulo isometry, quantitative
  determinant and minimum-norm rigidity, E8/Leech stability estimates.
- [ ] **SphereCeti preparation:** retain numerical constants and multiplicity estimates instead of
  collapsing every argument to qualitative zero/nonzero facts.

### D4. Periodic local-frame stability

- [ ] **Scope:** almost-optimal periodic packings, large finite frames locally modeled on E8 or
  Leech, quantitative dependence on density defect.
- [ ] **Why separate:** the conclusion is local-frame resemblance, not global congruence.
- [ ] **Dependencies:** D3 plus finite-pattern geometry and quantitative Cohn--Elkies estimates.

### D5. Equality and rigidity for sharp linear-programming bounds

- [ ] **Scope:** an abstract framework that turns strict direct/Fourier signs and exact zero sets
  into structural constraints on optimal periodic configurations.
- [ ] **Potential destination:** TauCeti discrete geometry or harmonic analysis.
- [ ] **SphereCeti role:** first substantial worked example in dimensions 8 and 24.
- [ ] **Upstream threshold:** wait until E8 and Leech reveal a genuinely common statement; do not
  abstract a single proof prematurely.

### D6. Euclidean point configurations and energy density

- [ ] **Scope:** locally finite configurations, periodic configurations, finite-pattern quotient,
  energy per point, translation/isometry/scale actions, and limits independent of fundamental
  domains.
- [ ] **Use:** universal optimality and other sharp energy problems.

### D7. Niemeier lattices

- [ ] **Scope:** rank-24 positive-definite even unimodular lattices, root systems, glue codes,
  construction and classification of the 24 isometry classes.
- [ ] **Relationship to SphereCeti:** supplies B2 as the rootless case, but is much broader than the
  minimum needed for Leech packing uniqueness.

## E. Candidates that should remain in SphereCeti/Sphere-Packing

The following are application-specific and should not be pushed upstream merely because they are
important:

- [ ] the `SpherePacking` and `PeriodicSpherePacking` semantics;
- [ ] the `CohnElkies.Certificate` structure specialized to packing density;
- [ ] E8 and Leech magic modular forms;
- [ ] the exact E8 and Leech auxiliary functions;
- [ ] dimension-specific contour decompositions and sign inequalities;
- [ ] the closed-one-form structure `ClosedOneFormOn`, the wedge set, and the signed contour
  permutations under `z ↦ -1/z`;
- [ ] E8/Leech packing density formulas;
- [ ] the equality-case path from a periodic packing to a generated lattice;
- [ ] the main theorems on optimality and periodic uniqueness.

General sublemmas inside those developments may still be upstream candidates, but the application
assembly belongs with the application.

## F. Conversion to GitHub issues

When an item is ready, its issue should contain:

```text
Destination repository/roadmap:
Motivating SphereCeti use:
Proposed declarations:
Current local or sibling implementation:
Exact source commit/path:
Mathlib/TauCeti overlap search:
Normalization decisions:
Minimal first PR:
Deletion/import payoff after landing:
```

Mark an item complete here only after SphereCeti has switched to the upstream declaration or has
explicitly decided that the local version is permanent.
