# Potential Mathlib and TauCeti destinations

This file lists results and topics intended for Mathlib or TauCeti, each described so that it
can be filed as an issue.  It deliberately does **not** create a parallel directory tree of
upstream roadmaps.  Each item records the intended home, a precise statement or scope, and the
fallback used if the item has not landed upstream when it is needed (a local version, or an
existing TauCeti import); the items are not ordered.  Filing an item as an issue does not commit
Mathlib or TauCeti to accepting it.

Availability in sections A–C refers to the committed dependency pin, TauCeti
`83769e442d55cda9d85b3927a93b286831c595ff`, adopted on 2026-11-10.  The
[resync watchlist](#g-resync-watchlist) records what that update brought in, with exact sources.
A result that lands upstream after the pin still needs a dependency update and interface
validation before this package can import it.

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
  MeasureTheory.Integrable.continuous_fourier
  MeasureTheory.Integrable.continuous_fourierInv
  ```

- [ ] **Why general:** these are specializations of Mathlib's vector Fourier theorem.
- [ ] **SphereCeti use:** pointwise Fourier sign conditions and limits in Cohn–Elkies.
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
  TauCeti.ModularForm.comp_ofComplex_S_transform
  TauCeti.ModularForm.differentiableAt_comp_ofComplex_S_transform_iff
  TauCeti.ModularForm.logDeriv_comp_ofComplex_S_transform
  ```

  These are stated for subgroups `Γ` of `GL (Fin 2) ℝ` containing `S`.

- [ ] **SphereCeti use:** contour pairing and zero-counting arguments.
- [ ] **Fallback:** exact TauCeti import.

### A5. q-coefficient vanishing versus cusp-function Big-O

- [ ] **Destination:** Mathlib q-expansion theory, or TauCeti if Mathlib considers it too
  specialized.
- [ ] **Current source:** `TauCeti.NumberTheory.ModularForms.QExpansion.BigO`.
- [ ] **Candidate declarations:**

  ```lean
  TauCeti.UpperHalfPlane.cuspFunction_isBigO_pow_iff_qExpansion_coeff_eq_zero
  TauCeti.UpperHalfPlane.tendsto_valueAtInfty
  ```

  The equivalence assumes analyticity of the cusp function of a raw function `f : ℍ → ℂ`; the
  former one-directional lemmas are its two directions.  Mathlib's
  `UpperHalfPlane.orderAtInfty` and `orderAtInfty_eq_qExpansion_order` cover part of this
  dictionary but do not replace it.

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
- [x] **Already in Mathlib:** `Function.IsRadial`, defined as factoring through `‖·‖`, with
  `Function.isRadial_def` giving the pointwise form used by production
  (`Mathlib/Analysis/Normed/Group/RadialFunction.lean`, mathlib4#44305).  The frozen
  `SphereCeti.Pinned.Function.IsRadial` mirrors production and is not changed; production should
  adopt Mathlib's definition.

### A8. Euclidean `ZLattice` norm-shell finiteness

- [ ] **Destination:** Mathlib `Algebra/Module/ZLattice`.
- [ ] **Candidate declarations:** finiteness of

  ```lean
  {x : Λ | ‖(x : V)‖ ≤ R}
  {x : Λ | ‖(x : V)‖ ^ 2 = a}
  ```

  and transport under linear isometries.
- [ ] **SphereCeti use:** theta coefficients, minimum norms, equality spectra.
- [x] **Available in TauCeti at the pin:** `ZLattice.shell`, `ZLattice.finite_shell`,
  `ZLattice.representationNumber`, and `ZLattice.representationNumber_comap`
  (`TauCeti/Algebra/Module/ZLattice/Shell.lean`).  SphereCeti uses these; a later move to Mathlib
  would change only the import.

### A9. Real inner-product dual lattice versus the bilinear-form dual

- [ ] **Destination:** Mathlib bilinear-form dual lattice / `ZLattice` comparison.
- [ ] **Candidate statement:** identify the inner-product dual of a full Euclidean `ℤ`-lattice with
  `LinearMap.BilinForm.dualSubmodule`, and establish discreteness/full rank.
- [ ] **SphereCeti use:** Poisson summation and self-duality.
- [x] **Available in TauCeti at the pin:** `ZLattice.dual` with `ZLattice.dual_def`, its
  `DiscreteTopology` and `IsZLattice` instances, and `ZLattice.dual_dual`
  (`TauCeti/Algebra/Module/ZLattice/Dual.lean`).  SphereCeti uses these.  The comparison with
  TauCeti's rational dual carrier remains SphereCeti's (Layer 2).

### A10. Covolume squared versus Gram determinant

- [ ] **Destination:** Mathlib `ZLattice`/Haar measure.
- [ ] **Candidate statement:** for a real lattice basis, square of the covolume equals the
  determinant of its Gram matrix; include basis independence and positive-definite square-root
  corollaries.
- [ ] **SphereCeti use:** compare real covolume with TauCeti discriminant/unimodularity.
- [x] **Available in TauCeti at the pin:** `ZLattice.covolume_sq_eq_det_gram`,
  `ZLattice.covolume_dual`, `ZLattice.det_eq_det_gram`, and
  `ZLattice.IsIntegral.isUnimodular_iff_covolume_eq_one`
  (`TauCeti/Algebra/Module/ZLattice/{Covolume,Determinant}.lean`).  SphereCeti uses these.

### A11. Lattice Poisson summation and theta series

- [ ] **Destination:** the TauCeti ThetaSeries roadmap, where general real-lattice duality,
  Poisson summation, theta series, transformation laws, the modular theta form, and the
  rank-8/rank-24 classifications are to be developed.
- [x] **Available in TauCeti at the pin:** Poisson summation over a full lattice,
  `SchwartzMap.tsum_eq_tsum_dual_fourier`, with `SchwartzMap.tsum_eq_tsum_dual_fourier_neg` and
  `SchwartzMap.tsum_eq_tsum_dual_fourier_of_even`
  (`TauCeti/Analysis/Fourier/PoissonSummation.lean`); the summability of both sides,
  `ZLattice.summable_poisson_left` and `ZLattice.summable_poisson_right`
  (`TauCeti/Analysis/Distribution/SchwartzSpace/ZLattice.lean`); the theta series `ZLattice.thetaSeries` and
  `ZLattice.thetaCoset`, their convergence, holomorphy, q-expansions, and `T`-translation law
  (`TauCeti/NumberTheory/ModularForms/ThetaSeries/`).  SphereCeti uses these and keeps no copy.
- [x] **Available in TauCeti at the pin: the theta `S`-transformation.**  For a full lattice of even
  rank `2k`,

  ```text
  Θ_L(-1/τ) = covol(L)⁻¹ (-i)^k τ^k Θ_{L^∨}(τ),
  ```

  obtained by applying `SchwartzMap.tsum_eq_tsum_dual_fourier` to the Gaussian
  `x ↦ exp(π i ‖x‖² τ)`.  Acceptance conditions: the Fourier transform of the complex Gaussian is
  proved for every `τ` in the upper half-plane in Mathlib's `exp(-2πi⟪x,ξ⟫)` normalization; the
  factor `(-iτ)^(d/2)` is stated through natural powers `(-i)^k τ^k` in even rank, so that no
  complex square-root branch occurs; and the statement uses TauCeti's `ZLattice.dual` and
  `ZLattice.covolume` with no extra hypotheses.  TauCeti's `ZLattice.thetaSeries_S_smul`
  (`ThetaSeries/Inversion.lean`) meets these conditions.  The theta series of an even unimodular
  lattice as a level-one modular form, `ZLattice.thetaForm`, and the rank-8 and rank-24 identities
  are also at the pin; watchlist G lists them.
- [x] **Upstream test:** the provisional `ThetaSeries` namespace is deleted; `Suggested.lean`
  imports these declarations and keeps only typed checks of their normalizations.

### A12. Contour deformation for half-infinite rectangles

- [ ] **Destination:** Mathlib complex analysis, beside the bounded rectangular Cauchy–Goursat
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

**Partial upstream coverage at the pin:** Mathlib's unbounded-rectangle theorem is in the pinned
dependency graph; see watchlist G.  It assumes uniform decay of the function
throughout the strip.  The local `horizontal_add_vertical_eq_vertical_of_tendsto_top` assumes
only that the top-edge integrals tend to zero.  Keep that more general target and use the landed
theorem for the uniform-decay specialization; do not strengthen the local hypothesis to remove it.

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

### A14. Exact zero orders of functions of a real variable

- [ ] **Destination:** TauCeti analysis, as the real-variable companion of
  `TauCeti.IsZeroMultiplicity` in `TauCeti.Analysis.Complex.ZeroMultiplicity`, which records the
  same continuous-cofactor factorization for functions on `ℂ`.
- [ ] **Current source:** `SphereCeti/Analysis/ExactZeroOrder.lean`.
- [ ] **Candidate declarations:**

  ```lean
  SphereCeti.HasExactZeroOrder
  SphereCeti.hasExactZeroOrder_iff
  SphereCeti.HasExactZeroOrder.quantitativeLowerBound
  ```

  The predicate says that `f : ℝ → ℂ` factors near `a` as `(x - a) ^ m * g x` with `g`
  continuous at `a` and `g a ≠ 0`; the lower bound gives `c > 0` with `c * |x - a| ^ m ≤ ‖f x‖`
  near `a`.
- [ ] **Why general:** the statements involve only continuity and norms of a function of a real
  variable; nothing refers to radial profiles or packings.
- [ ] **SphereCeti use:** the Layer 7 predicate `MagicFunction.HasExactZeroOrder` and its
  quantitative lower bound, for the exact zeros of the E8 and Leech radial profiles at the shells
  (Layer 9) and the quantitative stability estimates of D3.
- [ ] **Fallback:** the local SphereCeti declarations.
- [ ] **Upstream test:** no project import remains in a minimal reproduction.

### A19. Integrability of parameterized Gaussian kernels

- [ ] **Destination:** Mathlib `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean`,
  beside `GaussianFourier.integral_rexp_neg_mul_sq_norm`.
- [ ] **Current source:** `SphereCeti/Analysis/GaussianKernel.lean`.
- [ ] **Candidate declarations:** for `y > 0`, the integral of `exp(-π ‖x‖² y)` over a real inner
  product space of dimension `n` is `y^(-n/2)`; for `y` measurable and positive on a measurable
  set `s` and `φ` measurable, `(x, t) ↦ φ(t) exp(-π ‖x‖² y(t))` is integrable on `E × s` exactly
  when `t ↦ φ(t) y(t)^(-n/2)` is integrable on `s`
  (`SphereCeti.integrable_mul_rexp_neg_pi_mul_sq_norm_prod_iff`).
- [ ] **Why general:** it uses only Tonelli's theorem and the Gaussian integral; nothing refers
  to contours or magic functions.
- [ ] **SphereCeti use:** the product integrability hypotheses `ComponentIntegrable` and
  `CentralIntegrable` of the Layer 8 component identities, reduced to one-variable conditions on
  the kernels (MIGRATION J3).
- [ ] **Fallback:** the local SphereCeti declarations.
- [ ] **Upstream test:** no project import remains in a minimal reproduction.

## B. TauCeti IntegralLattices roadmap extensions

These are general algebraic lattice results.  Their sphere-packing consequences remain in
SphereCeti.

### B0. Cohn–Elkies generated-lattice lemma

- [ ] **Destination:** TauCeti IntegralLattices, with a possible later Mathlib extraction of the
  Euclidean subgroup lemma.
- [ ] **Source:** Cohn–Elkies, *New upper bounds on sphere packings I*, Lemma 8.2.
- [ ] **Target statement:** if `S ⊆ V` contains `0`, spans a finite-dimensional real
  inner-product space, and every pairwise squared distance is an even integer, then the additive
  subgroup generated by `S` is a full even integral lattice.
- [ ] **Reusable proof ingredients:** polarization, finite generation from a real basis chosen in
  `S`, discreteness of an integral Gram lattice, and an `IntegralLattice` presentation of the
  generated group.
- [ ] **Why TauCeti:** this is pure integral-lattice formation and is independent of packing
  density or Cohn–Elkies certificates once its hypotheses are stated.
- [ ] **SphereCeti fallback:** `Rigidity.generatedIntegralLattice_evenIntegral_full`.

### B1. E8 as the unique positive-definite even unimodular rank-eight lattice

- [x] **Destination:** `TauCetiRoadmap/IntegralLattices`, milestone 6C, implemented at the pin by
  a theta-independent classification (watchlist G).
- [ ] **Target statement:** every positive-definite even unimodular integral lattice of rank `8` is
  integrally isometric to a canonical E8 integral lattice.
- [ ] **Supporting results for the former local fallback route:**
  - canonical E8 Gram/integral lattice built from TauCeti root data;
  - roots/vectors of norm `2`;
  - finite crystallographic root system, spanning, and ADE decomposition;
  - rank `8` plus `240` roots identifies type E8;
  - the E8 root sublattice has index one;
  - isometry from equality of Gram data;
  - invariance of evenness, unimodularity, and rank.
- [ ] **Why TauCeti:** the statement mentions no real packing, density, or Fourier analysis.
- [x] **Adopted:** `E8.even_unimodular_rank_eight_unique` is TauCeti's
  `IntegralLattice.IsPosDef.nonempty_isometry_typeE₈RootLattice_of_isEven` with the rank converted
  by `IntegralLattice.finrank_carrier` and the isometry reversed.  It already uses the canonical
  `typeE₈RootLattice`; no new classification proof or theta identity is needed.  The explicit
  production E8 presentation and extension to real isometries remain separate bridges.
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
- [x] **Available in TauCeti at the pin:** `IntegralLattice.typeE₈RootLattice` with
  `isEven_typeE₈RootLattice`, `isPosDef_typeE₈RootLattice`, and `determinant_typeE₈RootLattice`
  (`RootLattice/TypeE/Basic.lean`), and its roots `typeE₈RootEquiv : Fin 240 ≃ _`,
  `representationNumber_typeE₈RootLattice_two`, and `kissingNumber_typeE₈RootLattice`
  (`RootLattice/TypeE/Roots.lean`).  SphereCeti adopts `typeE₈RootLattice` as its canonical E8
  object; the Gram-preserving isometry from the production presentation remains SphereCeti's.

### B4. Explicit Leech integral lattice

- [ ] **Destination:** TauCeti rank-24/code-lattice roadmap.
- [ ] **Target:** a canonical rational integral-lattice object with coordinate/glue and Gram
  presentations, equality between them, evenness, unimodularity, rootlessness, and minimum norm.
- [ ] **SphereCeti use:** the algebraic object behind the real packing.
- [x] **Available in TauCeti at the pin:** `leechLattice`, built from Construction B of
  `BinaryGolay.code` and the odd shift, with `isEven_leechLattice`, `isUnimodular_leechLattice`,
  `isPosDef_leechLattice`, `finrank_leechLattice` (`Rank24/Leech/Basic.lean`), the congruence model
  `mem_leechLattice_carrier_iff_exists`, `minimum_leechLattice`, and
  `vectorsOfNorm_two_leechLattice` (`Rank24/Leech/Minimum.lean`).  SphereCeti adopts `leechLattice`
  as its canonical Leech object and transports it into the packing space; no Gram presentation is
  needed upstream for that.
- [x] **Available in TauCeti at the pin: the kissing number.**  `TauCeti.kissingNumber_leechLattice`
  proves `leechLattice.kissingNumber = 196560` by direct enumeration in
  `Rank24/Leech/MinimalVectors.lean`.  SphereCeti imports it in place of its former local target;
  `Leech.shellCard_four` follows from `TauCeti.ncard_vectorsOfNorm_four_leechLattice` and
  `Leech.representationNumber_lattice`.  The later `ZLattice.IsEven.representationNumber_four_of_rootless` gives another
  route to the real count once the real lattice hypotheses are established (watchlist G).

### B5. Integral-presentation bridge to the ThetaSeries roadmap

- [ ] **Destination:** the analytic theta series, its modularity, and the low-rank
  classifications belong to the TauCeti ThetaSeries roadmap; evenness and unimodularity of
  presentations belong to the IntegralLattices side.
- [ ] **Target:** the bridge from an integral presentation to the roadmap's real-lattice
  evenness, unimodularity, and shell coefficients.
- [ ] **SphereCeti use:** the Layer 5 presentation bridges; avoid a sphere-packing-specific theta
  namespace.
- [ ] **Status:** the real predicates `ZLattice.IsIntegral`, `ZLattice.IsEven`, and
  `ZLattice.IsUnimodular` are in TauCeti at the pin, as are `ZLattice.ratModel`,
  `IntegralLattice.realModel`, inverse isometries, dual transport, and shell comparisons.
  PR #20950 closed unmerged; #21332 supplied the rational model.  SphereCeti reuses these APIs
  through `IntegralPresentation.ratModelIsometry`, the basis-induced isometry from the Gram
  presentation to `ratModel`, and keeps the explicit presentation and application-specific
  transport results (watchlist G).

## C. TauCeti coding-theory and code-lattice roadmap

### C1. Linear codes over finite fields

- [ ] **Destination:** new TauCeti coding-theory roadmap.
- [ ] **Scope:** linear codes, duality, Hamming weight/distance, weight enumerators, self-dual and
  doubly-even binary codes, equivalence under coordinate permutations.
- [ ] **Scope limit:** reusable algebraic coding theory, not a one-off Golay matrix verification.
- [x] **Available in TauCeti at the pin:** `LinearCode`, Euclidean duality, Hamming weights,
  weight enumerators, and doubly-even and Type II binary codes
  (`TauCeti/InformationTheory/Coding/`).

### C2. Extended binary Golay code

- [ ] **Destination:** coding-theory roadmap.
- [ ] **Targets:** explicit construction; dimension `12`; self-duality; doubly-evenness; minimum
  distance `8`; relevant weight enumerator and automorphism facts.
- [ ] **SphereCeti use:** Leech coordinate/glue construction and rootlessness.
- [x] **Available in TauCeti at the pin:** `BinaryGolay.code`, generated by the systematic matrix
  `[I₁₂ | B]`, with `finrank_code`, `natCard_code`, `isSelfDual_code`, `isDoublyEven_code`,
  `eight_le_hammingNorm`, and `weightEnumerator_code`
  (`Binary/Golay/Basic.lean`).  It was already present at the previous pin `1308f31`.
  SphereCeti adopts it as the canonical code and states that its cyclic-generator description is
  permutation equivalent to it, with TauCeti's `IsPermutationEquivalent`
  (`Coding/Equivalence.lean`).

### C3. Code-lattice constructions

- [ ] **Destination:** code-lattice roadmap connected to IntegralLattices.
- [ ] **Targets:** Construction A and its dual/even/unimodular criteria, shifted/glue variants, and
  explicit E8/Leech comparisons.
- [x] **Available in TauCeti at the pin:** Construction A and Construction B, and the Leech lattice
  as the odd-shift glue of Construction B of the Golay code (B4).
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
- [ ] **Dependencies:** D3 plus finite-pattern geometry and quantitative Cohn–Elkies estimates.

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

## G. Resync watchlist

Checked on **2026-11-10** against exact public Git snapshots, including source statements and
mainline history, and adopted the same day: the package pin moved from TauCeti
`271e1af4dd54c50b9192cf3e213b7686843a0b3a` (Lean `v4.36.0-rc1`, Mathlib
`2cabef97b63d3275776b8b060d802de6a6fa1055`) to the snapshot below, and both Lean libraries and the
compiled admission audit pass on it (see `VALIDATION.md`).  This supersedes the 2026-10-25
watchlist, against TauCeti `8384538` and TauCetiRoadmap `6493273`: the former open items have
landed.  TauCetiRoadmap was rechecked at upstream `20833089`.

| Audited component | Exact revision / toolchain |
|---|---|
| TauCeti | [`83769e442d55cda9d85b3927a93b286831c595ff`][tc-snapshot] |
| Its Lean toolchain | `leanprover/lean4:v4.36.0-rc2` |
| Its resolved Mathlib | [`1b1ccf4b088b32fa3f23f2de1127433254a81e1e`][tc-manifest] |
| Mathlib master, checked separately | [`21fc68be3752a8b64e4829512cdb95a8917e4d7f`][mathlib-snapshot] |
| Sphere-Packing-Lean main | [`803f1623539ece84a19b2b6805764b8dea9ea6e6`][production-toolchain], Lean `v4.35.0` |

Mathlib master is not an independent upgrade candidate: SphereCeti follows the exact graph in
TauCeti's manifest.  Production has advanced beyond the frozen 4.32 semantic baseline, but still
needs the synchronized migration before `Pinned.lean` can be removed.

### Landed targets adopted in the dependency update

| Former local target / use | Landed declaration and exact source |
|---|---|
| `ThetaSeries.thetaSeries_neg_inv` | `ZLattice.thetaSeries_S_smul`, [Inversion.lean][theta-inversion] |
| `ThetaSeries.thetaForm`, `coe_thetaForm`, `qExpansion_thetaForm_coeff` | `ZLattice.thetaForm`, `ZLattice.coe_thetaForm`, `ZLattice.qExpansion_thetaForm_coeff`, [LevelOne.lean][theta-levelone] |
| `ThetaSeries.thetaForm_eq_E₄`, `representationNumber_two_rank_eight` | `ZLattice.IsEven.thetaForm_eq_E₄`, `ZLattice.IsEven.representationNumber_two_of_finrank_eq_eight`, [Eisenstein.lean][theta-eisenstein] |
| `ThetaSeries.thetaForm_rank_24`, `coe_thetaForm_rank_24_rootless` | `ZLattice.IsEven.thetaForm_eq_E₄_cube_add_smul_discriminant` and pointwise `thetaSeries_eq_E₄_cube_add_mul_discriminant`, [RankTwentyFour.lean][theta-rank24]; specialize the root count to zero for the rootless identity |
| `E8.even_unimodular_rank_eight_unique` | `TauCeti.IntegralLattice.IsPosDef.nonempty_isometry_typeE₈RootLattice_of_isEven`, [SmallRankUnimodular.lean][e8-classification] |
| `Leech.kissingNumber_integralLattice` | `TauCeti.kissingNumber_leechLattice`, [MinimalVectors.lean][leech-minimal] |
| Alternative route to `Leech.shellCard_four` | `ZLattice.IsEven.representationNumber_four_of_rootless`, [RankTwentyFour.lean][theta-rank24] |

The theta inversion theorem uses the same `ModularGroup.S • τ`, positive Poisson phase, inverse
covolume, and natural powers as the local target; only multiplication is grouped differently.
The modular-form constructor takes evenness, unimodularity, then rank, instead of the local
argument order.  `Suggested.lean` imports these APIs in place of the former `ThetaSeries`
stand-ins, records the normalizations as typed `example`s, and keeps the application-facing
`Theta` corollaries with their presentation hypotheses as short specializations.

The rank-eight classification is **theta-independent** and uses the same canonical
`typeE₈RootLattice`.  Its conclusion is `Nonempty (Isometry typeE₈RootLattice L)`, so the local
orientation uses `Isometry.symm`.  Its rank hypothesis is `Module.finrank ℤ L = 8`; convert the
local ambient rational rank with `IntegralLattice.finrank_carrier`.  This removes the theta
identity from the E8 periodic-uniqueness dependency chain.  The production E8
presentation and extension to real isometries still require their own comparisons.

The Leech kissing number is proved by direct enumeration, independently of theta series.  It
directly supplies the algebraic target; `Leech.shellCard_four` follows from its norm-four count
`TauCeti.ncard_vectorsOfNorm_four_leechLattice` through `Leech.representationNumber_lattice`,
which reaches the chosen Euclidean embedding.  Alternatively the general rootless rank-24 theorem applies directly to that
Euclidean lattice once its evenness, unimodularity, rank, and absence of norm-two vectors have
been established.  A count in TauCeti's `realModel` is not automatically a count in SphereCeti's
coordinate image.

### Real/rational models: reuse the generic transport

- [RationalModel.lean][rational-model] supplies `ZLattice.ratModel`, `ratModelCarrierEquiv`,
  `isPosDef_ratModel`, `finrank_ratModel`, `isEven_ratModel_iff`, `isUnimodular_ratModel_iff`,
  `determinant_ratModel`, `discriminant_ratModel`, `ratModelDualEquiv`, and
  `ratModelDiscriminantGroupEquiv`.  The namespace is `ZLattice`, not the old proposal's
  `TauCeti.ThetaSeries`.
- [RealModel.lean][real-model] supplies `TauCeti.IntegralLattice.realModel`,
  `ratModelRealModelIsometry`, `realModelDualEquiv`, `realModelDiscriminantGroupEquiv`,
  `Isometry.ofRealModel`, and `ZLattice.realModelRatModelIsometry`.  The former watchlist's
  assertion that the converse, inverses, and dual transport are missing is obsolete.
- [ModelShell.lean][model-shell] supplies `ZLattice.shell_eq_image_vectorsOfNorm_ratModel`,
  `ZLattice.ncard_vectorsOfNorm_ratModel`, and
  `TauCeti.IntegralLattice.representationNumber_realModel`.

The remaining comparison is concrete: `P.toIntegralLattice` has ambient space `Fin d → ℚ`,
whereas `ZLattice.ratModel` has ambient space `ℚ ⊗[ℤ] Λ`.  The roadmap target
`IntegralPresentation.ratModelIsometry` is their `IntegralLattice.Isometry`, induced by `P.basis`
(`ratModelIsometry_single`) and depending on the Gram equation, with `isIntegral_real` supplying
the integrality hypothesis of `ratModel`.  `isEven_real` and `isUnimodular_real` are now proved by
transporting `isEven_ratModel_iff` and `isUnimodular_ratModel_iff` along it; the dual, shell, and
discriminant adapters are to be obtained the same way.  Do not delete `IntegralPresentation`, introduce another
abstract conversion, or infer that a returned carrier equivalence alone establishes the required
Gram compatibility.  Audit `carrierEquiv`, `dualCarrierEquiv`, `shellEquiv`, and
`realIsometryOfIsometry` as application adapters instead of reproving their generic ingredients.

### API changes absorbed in the update

Renames without deprecated aliases between `271e1af` and the pin:

- `TauCeti.continuous_fourier_of_integrable` is replaced by
  `MeasureTheory.Integrable.continuous_fourier`, with inverse counterpart `continuous_fourierInv`
  in [Continuous.lean][fourier-continuous] (#23743).  The `#check` in `Suggested.lean` was updated.
- `TauCeti.UpperHalfPlane.cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero` is replaced by
  `cuspFunction_isBigO_pow_iff_qExpansion_coeff_eq_zero` in [BigO.lean][q-bigo] (#31801).  It
  assumes analyticity of the raw function's cusp function and gives an equivalence; the old
  implication uses its `.mpr` direction.  The `#check` was updated.
- `TauCeti.ModularForm.sturm_bound_finiteIndex` is now `ModularForm.sturm_bound_finiteIndex`, still
  defined in TauCeti's `SturmBound.lean` but in Mathlib's root `ModularForm` namespace (#24387).
  The `#check` was updated.
- `TauCeti.fourier_gaussian_of_im_pos` and `..._of_finrank_eq_two_mul` from the 1F Gaussian PR
  #19284 were removed as duplicates (#32129); the surviving forms are
  `TauCeti.fourier_cexp_pi_mul_I_mul_norm_sq_mul` and its `_of_finrank_eq` variant.  SphereCeti
  imports neither; `SchwartzMap.gaussian` and `gaussian_apply` remain.
- The differentiability S-transform theorem is now
  `TauCeti.ModularForm.differentiableAt_comp_ofComplex_S_transform_iff`, for subgroups of
  `GL (Fin 2) ℝ`, in [STransform.lean][s-transform].  The transformation and logarithmic-derivative
  names remain; compare hypotheses when porting production uses.

No Mathlib change between `2cabef9` and `1b1ccf4` renames or deprecates a declaration used by
`Suggested.lean`, `Pinned.lean`, or `scripts/Audit.lean`, and the audit's linter set is unchanged.

The [atomic update checklist](CONTRIBUTING.md#pin-updates) covers both Lean libraries, the
compiled admission ledger, the exact manifest, configuration/publication pins, and affected tests.
Delete only targets whose full statements are supplied or whose application adapters have been
checked.  No imported Poisson, density, or theta transformation becomes a simp rule.

### Mathlib changes in and beyond the pinned graph

- **Unbounded rectangles (A12), in the pinned graph.**  Mathlib
  [`1a22a591d08f49075418a57625c7c52e2956a169`][mathlib-rectangles] adds
  `Complex.integral_boundary_unbounded_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on`
  and limit variants in `Mathlib/Analysis/Complex/CauchyIntegral.lean`.  The theorem assumes
  `Tendsto f (comap Complex.im atTop ⊓ 𝓟 strip) (𝓝 0)`, uniform decay of `f` through the strip.
  Our target assumes only that the top-edge integrals tend to zero, so retain it.  Use the new
  theorem for uniform-decay applications and preserve the derivative/integrability hypotheses.
- **Order at infinity, in the pinned graph.**  Mathlib
  [`e1b16f5f6a696c975ec188a85ed08ba1cc98f3bc`][mathlib-order] adds
  `Mathlib/NumberTheory/ModularForms/OrderAtInfty.lean`, including
  `UpperHalfPlane.orderAtInfty`, `orderAtInfty_eq_qExpansion_order`, `isTheta_orderAtInfty`, and
  `orderAtInfty_mul_of_holo`.  Search these before adding generic order/cusp estimates; they do
  not replace all of TauCeti's A5 coefficient/Big-O dictionary or Sturm theory.
- **No new replacement found for A13, A6, or the rest of A7.**  The curve-integral changes
  preserve the existing API while changing definition transparency; there is still no matching
  segment substitution theorem.  The inspected Schwartz/Fourier changes do not supply the cocompact
  constructor or radial Schwartz submodule; `Function.IsRadial` itself predates the range (A7).  No substantive new covolume/index result changes
  the current rigidity plan.
- **Mathlib master only, outside the pinned graph.**  The
  [cusp API change][mathlib-cusps] moves an arithmetic-group cusp instance to `Cusps.lean` and
  adds cusp/width transport.  The [discriminant derivative change][mathlib-discriminant] supplies
  `ModularForm.normalizedDerivOfComplex_discriminant` and
  `ModularForm.serreDerivative_discriminant`.  Record these for the next TauCeti graph update;
  do not independently advance Mathlib to import them.

### Remaining classification and disposition of the former watch items

`Leech.rootless_even_unimodular_rank_twentyFour_unique` remains a required development.  The
new [rank-24 reference-lattice file][rank24-reference] constructs and distinguishes the 24
examples but explicitly does not prove Niemeier completeness.  Neither the theta identities nor
the kissing number removes this dependency.

The former watched PRs are no longer open work: #19284 (Gaussian), #21080 (E₄/Δ polynomial
basis), #21251 (uniform root counts), #19380 (orthogonal sums), #20834 (rank-one theta), and
#20976 (Gauss sums) all landed.  #20950 was superseded by landed #21332 (rational model),
#20860 by #21484 (scaling), and #20694 by #21601 (level).  This disposition was checked against
mainline source/history: a Bors-integrated original PR can be closed with its REST `merged` flag
false even though the code landed.  Additive results are not by themselves reasons to create new
SphereCeti targets.

[tc-snapshot]: https://github.com/TauCetiProject/TauCeti/commit/83769e442d55cda9d85b3927a93b286831c595ff
[tc-manifest]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/lake-manifest.json
[mathlib-snapshot]: https://github.com/leanprover-community/mathlib4/commit/21fc68be3752a8b64e4829512cdb95a8917e4d7f
[production-toolchain]: https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/803f1623539ece84a19b2b6805764b8dea9ea6e6/lean-toolchain
[theta-inversion]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/NumberTheory/ModularForms/ThetaSeries/Inversion.lean
[theta-levelone]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/NumberTheory/ModularForms/ThetaSeries/LevelOne.lean
[theta-eisenstein]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/NumberTheory/ModularForms/ThetaSeries/Eisenstein.lean
[theta-rank24]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/NumberTheory/ModularForms/ThetaSeries/RankTwentyFour.lean
[e8-classification]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/LinearAlgebra/IntegralLattice/PosDef/SmallRankUnimodular.lean
[leech-minimal]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/MinimalVectors.lean
[rational-model]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/Algebra/Module/ZLattice/RationalModel.lean
[real-model]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/Algebra/Module/ZLattice/RealModel.lean
[model-shell]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/Algebra/Module/ZLattice/ModelShell.lean
[fourier-continuous]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/Analysis/Fourier/Continuous.lean
[q-bigo]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/NumberTheory/ModularForms/QExpansion/BigO.lean
[s-transform]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/NumberTheory/ModularForms/STransform.lean
[mathlib-rectangles]: https://github.com/leanprover-community/mathlib4/commit/1a22a591d08f49075418a57625c7c52e2956a169
[mathlib-order]: https://github.com/leanprover-community/mathlib4/commit/e1b16f5f6a696c975ec188a85ed08ba1cc98f3bc
[mathlib-cusps]: https://github.com/leanprover-community/mathlib4/commit/0e248bc7cb5345837452035093e94bb36398fc0a
[mathlib-discriminant]: https://github.com/leanprover-community/mathlib4/commit/34603ccd1f9d2780659eb9749003e4027e76e250
[rank24-reference]: https://github.com/TauCetiProject/TauCeti/blob/83769e442d55cda9d85b3927a93b286831c595ff/TauCeti/LinearAlgebra/IntegralLattice/Rank24/ReferenceLattices.lean
