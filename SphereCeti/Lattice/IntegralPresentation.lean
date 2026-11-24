/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Algebra.Module.ZLattice.RationalModel
public import TauCeti.Algebra.Module.ZLattice.Shell
public import SphereCeti.LinearAlgebra.IntegralLattice.Rootless

/-!
# Integral presentations of Euclidean lattices

An *integral presentation* of a lattice `Λ` in the Euclidean space `ℝ^d` is a `ℤ`-basis
`b₀, …, b_{d-1}` of `Λ` together with the integer matrix `G` of the inner products `⟪bᵢ, bⱼ⟫`.
The matrix `G` defines TauCeti's integral lattice `TauCeti.IntegralLattice.ofGramMatrix` in `ℚ^d`:
the lattice `ℤ^d` with the rational bilinear form whose matrix in the standard basis is `G`.  This
is the lattice of the presentation *in Gram coordinates*.

A presented lattice is integral, so for a full lattice `Λ` (with the instances
`DiscreteTopology Λ` and `IsZLattice ℝ Λ`) TauCeti's rational model `ZLattice.ratModel` of `Λ` is
defined.  The rational model lives in `ℚ ⊗[ℤ] Λ` rather than in `ℚ^d`.  The presentation basis
identifies the two: the `i`-th standard basis vector goes to `1 ⊗ bᵢ`, and the Gram equation makes
this an isometry of integral lattices.  TauCeti's comparisons between `Λ` and its rational model
therefore apply to the lattice in Gram coordinates: it is positive definite, and it is even
(unimodular) exactly when `Λ` is even (unimodular) in TauCeti's real sense.

## Main definitions

* `SphereCeti.EuclideanLattice.IntegralPresentation Λ`: a `ℤ`-basis of `Λ` indexed by `Fin d`
  together with its integer Gram matrix.
* `SphereCeti.EuclideanLattice.IntegralPresentation.ofBasis`: the presentation given by a basis and
  an integer matrix of the inner products of its vectors, whose symmetry is derived.
* `SphereCeti.EuclideanLattice.IntegralPresentation.toIntegralLattice`: the lattice of a
  presentation in Gram coordinates.
* `SphereCeti.EuclideanLattice.IntegralPresentation.ratModelIsometry`: the isometry from the
  lattice in Gram coordinates to TauCeti's rational model of `Λ` induced by the basis.
* `SphereCeti.EuclideanLattice.IntegralPresentation.carrierEquiv`,
  `SphereCeti.EuclideanLattice.IntegralPresentation.dualCarrierEquiv`,
  `SphereCeti.EuclideanLattice.IntegralPresentation.shellEquiv`: the identifications of `Λ`, of its
  real dual lattice, and of its shells with the carrier, the dual carrier, and the norm shells of
  the lattice in Gram coordinates.
* `SphereCeti.EuclideanLattice.IntegralPresentation.realIsometryOfIsometry`,
  `SphereCeti.EuclideanLattice.IntegralPresentation.affineIsometryOfIsometry`: the extension of an
  isometry between the lattices of two presentations in Gram coordinates to a real linear isometry
  of `ℝ^d`, and its affine version carrying one lattice coset to another.

## Main statements

* `SphereCeti.EuclideanLattice.IntegralPresentation.isIntegral_real`: a presented lattice is
  integral.
* `SphereCeti.EuclideanLattice.IntegralPresentation.ratModelIsometry_single`: the isometry sends
  the `i`-th standard basis vector to `1 ⊗ bᵢ`.
* `SphereCeti.EuclideanLattice.IntegralPresentation.isPosDef`: a presentation of a full lattice is
  positive definite.
* `SphereCeti.EuclideanLattice.IntegralPresentation.isEven_real_iff`,
  `SphereCeti.EuclideanLattice.IntegralPresentation.isUnimodular_real_iff`: `Λ` is even
  (unimodular) exactly when the presentation is; `isEven_real` and `isUnimodular_real` are the
  reverse directions, transporting evenness and unimodularity from the presentation to `Λ`.
* `SphereCeti.EuclideanLattice.IntegralPresentation.covolume_sq_eq_discriminant`: the squared
  covolume of `Λ` is the discriminant of the presentation.
* `SphereCeti.EuclideanLattice.IntegralPresentation.isUnimodular_iff_covolume_eq_one`,
  `SphereCeti.EuclideanLattice.IntegralPresentation.dual_eq_self_of_isUnimodular`: a presentation
  is unimodular exactly when `Λ` has covolume one, and then `Λ` is its own real dual.
* `SphereCeti.EuclideanLattice.IntegralPresentation.ratModelMap_ratModelIsometry`: read in `ℝ^d`,
  the isometry sends `q ∈ ℚ^d` to `∑ i, qᵢ bᵢ`.
* `SphereCeti.EuclideanLattice.IntegralPresentation.mem_dual_iff_exists_dualCarrier_coordinates`:
  the real dual lattice consists of the combinations of the basis with coordinates in the dual
  carrier.
* `SphereCeti.EuclideanLattice.IntegralPresentation.isRootless_iff_shell_two_eq_empty`: the lattice
  in Gram coordinates is rootless (`TauCeti.IntegralLattice.IsRootless`) exactly when `Λ` has no
  vector of squared length two.
* `SphereCeti.EuclideanLattice.IntegralPresentation.discreteTopology`,
  `SphereCeti.EuclideanLattice.IntegralPresentation.isZLattice`: a presented lattice is a discrete
  full lattice.
* `SphereCeti.EuclideanLattice.IntegralPresentation.realIsometry_maps_carrier`,
  `SphereCeti.EuclideanLattice.IntegralPresentation.realIsometryOfIsometry_basis`,
  `SphereCeti.EuclideanLattice.IntegralPresentation.affineIsometry_maps_coset`: the real extension
  carries `Λ` onto `Μ`, agrees with the given isometry on the basis in coordinates, and its affine
  version carries `v + Λ` onto `w + Μ`.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer (2013), Chapter 1.
-/

public section

open Module TensorProduct
open scoped InnerProductSpace Pointwise

namespace SphereCeti.EuclideanLattice

/-- An integral presentation of a lattice `Λ` in `ℝ^d`: a `ℤ`-basis of `Λ` indexed by `Fin d`,
together with the integer matrix of the real inner products of its vectors. -/
structure IntegralPresentation {d : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) where
  /-- A `ℤ`-basis of the lattice. -/
  basis : Basis (Fin d) ℤ Λ
  /-- The Gram matrix of the basis. -/
  gram : Matrix (Fin d) (Fin d) ℤ
  /-- The Gram matrix is symmetric. -/
  gram_isSymm : gram.IsSymm
  /-- The entries of the Gram matrix are the real inner products of the basis vectors. -/
  gram_spec : ∀ i j, (gram i j : ℝ) = ⟪(basis i : EuclideanSpace ℝ (Fin d)), basis j⟫_ℝ

namespace IntegralPresentation

variable {d : ℕ} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}

/-- The integral presentation given by a basis and an integer matrix recording the inner products
of its vectors.  The symmetry of the matrix follows from that of the inner product. -/
def ofBasis (basis : Basis (Fin d) ℤ Λ) (gram : Matrix (Fin d) (Fin d) ℤ)
    (gram_spec : ∀ i j, (gram i j : ℝ) = ⟪(basis i : EuclideanSpace ℝ (Fin d)), basis j⟫_ℝ) :
    IntegralPresentation Λ where
  basis := basis
  gram := gram
  gram_isSymm := Matrix.IsSymm.ext fun i j ↦ Int.cast_injective (α := ℝ) <| by
    rw [gram_spec, gram_spec, real_inner_comm]
  gram_spec := gram_spec

@[simp]
theorem ofBasis_basis (basis : Basis (Fin d) ℤ Λ) (gram : Matrix (Fin d) (Fin d) ℤ)
    (gram_spec : ∀ i j, (gram i j : ℝ) = ⟪(basis i : EuclideanSpace ℝ (Fin d)), basis j⟫_ℝ) :
    (ofBasis basis gram gram_spec).basis = basis :=
  (rfl)

@[simp]
theorem ofBasis_gram (basis : Basis (Fin d) ℤ Λ) (gram : Matrix (Fin d) (Fin d) ℤ)
    (gram_spec : ∀ i j, (gram i j : ℝ) = ⟪(basis i : EuclideanSpace ℝ (Fin d)), basis j⟫_ℝ) :
    (ofBasis basis gram gram_spec).gram = gram :=
  (rfl)

/-- Check that `simp` evaluates the projections of `ofBasis`. -/
example (basis : Basis (Fin d) ℤ Λ) (gram : Matrix (Fin d) (Fin d) ℤ)
    (gram_spec : ∀ i j, (gram i j : ℝ) = ⟪(basis i : EuclideanSpace ℝ (Fin d)), basis j⟫_ℝ) :
    (ofBasis basis gram gram_spec).basis = basis ∧ (ofBasis basis gram gram_spec).gram = gram := by
  simp

/-- The lattice of a presentation in Gram coordinates: the lattice `ℤ^d` in `ℚ^d`, with the
rational bilinear form whose matrix in the standard basis is the Gram matrix. -/
noncomputable def toIntegralLattice (P : IntegralPresentation Λ) :
    TauCeti.IntegralLattice (Fin d → ℚ) :=
  TauCeti.IntegralLattice.ofGramMatrix (Pi.basisFun ℚ (Fin d)) P.gram P.gram_isSymm

/-- The lattice of a presentation in Gram coordinates is TauCeti's lattice of the standard basis
of `ℚ^d` and the Gram matrix. -/
theorem toIntegralLattice_def (P : IntegralPresentation Λ) :
    P.toIntegralLattice =
      TauCeti.IntegralLattice.ofGramMatrix (Pi.basisFun ℚ (Fin d)) P.gram P.gram_isSymm :=
  (rfl)

/-- A presentation is even when its lattice in Gram coordinates is even. -/
abbrev IsEven (P : IntegralPresentation Λ) : Prop := P.toIntegralLattice.IsEven

/-- A presentation is unimodular when its lattice in Gram coordinates is unimodular. -/
abbrev IsUnimodular (P : IntegralPresentation Λ) : Prop := P.toIntegralLattice.IsUnimodular

/-- A presentation is positive definite when its lattice in Gram coordinates is positive
definite. -/
abbrev IsPosDef (P : IntegralPresentation Λ) : Prop := P.toIntegralLattice.IsPosDef

/-- A presented lattice is integral: the inner product of any two of its vectors is an integer. -/
theorem isIntegral_real (P : IntegralPresentation Λ) : ZLattice.IsIntegral Λ := by
  have hsum (z : Λ) : (z : EuclideanSpace ℝ (Fin d)) =
      ∑ i, (P.basis.repr z i : ℝ) • (P.basis i : EuclideanSpace ℝ (Fin d)) := by
    conv_lhs => rw [← P.basis.sum_repr z]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Int.cast_smul_eq_zsmul]
  rw [ZLattice.isIntegral_iff]
  intro x hx y hy
  lift x to Λ using hx
  lift y to Λ using hy
  -- Expand both vectors in the basis; the inner product is the Gram form of the coordinates.
  refine ⟨∑ i, ∑ j, P.basis.repr x i * P.basis.repr y j * P.gram i j, ?_⟩
  rw [hsum x, hsum y, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right, ← P.gram_spec]
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The identification of `Λ` with the carrier of its lattice in Gram coordinates that sends each
vector to its coordinate vector in the presentation basis (`coe_carrierEquiv_apply`). -/
noncomputable def carrierEquiv (P : IntegralPresentation Λ) :
    Λ ≃ₗ[ℤ] P.toIntegralLattice.carrier :=
  P.basis.equiv
    (TauCeti.IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin d)) P.gram P.gram_isSymm)
    (Equiv.refl _)

/-- The vector `P.carrierEquiv x` lists the coordinates of `x` in the presentation basis. -/
@[simp]
theorem coe_carrierEquiv_apply (P : IntegralPresentation Λ) (x : Λ) (i : Fin d) :
    (P.carrierEquiv x : Fin d → ℚ) i = P.basis.repr x i := by
  -- The presentation basis goes to TauCeti's basis of the lattice in Gram coordinates.
  have hb (j : Fin d) : (P.carrierEquiv (P.basis j) : Fin d → ℚ) = Pi.single j 1 :=
    (congrArg Subtype.val (P.basis.equiv_apply j _ (Equiv.refl _))).trans <|
      (TauCeti.IntegralLattice.ofGramMatrix.coe_basis _ _ _ j).trans (Pi.basisFun_apply ℚ _ j)
  conv_lhs => rw [← P.basis.sum_repr x]
  simp only [map_sum, map_zsmul, Submodule.coe_sum, Submodule.coe_smul_of_tower, hb,
    Finset.sum_apply, Pi.smul_apply]
  simp [Pi.single_apply]

/-- Check that `simp` computes the coordinates of a basis vector. -/
example (P : IntegralPresentation Λ) (i : Fin d) :
    (P.carrierEquiv (P.basis i) : Fin d → ℚ) i = 1 := by
  simp

variable [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- Every integral full lattice in `ℝ^d` has an integral presentation: a `ℤ`-basis indexed by
`Fin d`, together with the integer matrix of the inner products of its vectors. -/
theorem nonempty_of_isIntegral (h : ZLattice.IsIntegral Λ) : Nonempty (IntegralPresentation Λ) := by
  have := ZLattice.module_free ℝ Λ
  have := ZLattice.module_finite ℝ Λ
  let b : Basis (Fin d) ℤ Λ :=
    Module.finBasisOfFinrankEq ℤ Λ ((ZLattice.rank ℝ Λ).trans finrank_euclideanSpace_fin)
  exact ⟨ofBasis b (fun i j ↦ h.integralForm (b i) (b j)) fun i j ↦ h.integralForm_cast _ _⟩

/-- The presentation basis, carried into the rational model, has Gram matrix `P.gram`. -/
private theorem gramMatrix_ratModel (P : IntegralPresentation Λ) :
    (ZLattice.ratModel P.isIntegral_real).gramMatrix
      (P.basis.map (ZLattice.ratModelCarrierEquiv P.isIntegral_real)) = P.gram := by
  ext i j
  apply Int.cast_injective (α := ℝ)
  simp [P.gram_spec]

/-- The isometry from the lattice of a presentation in Gram coordinates to TauCeti's rational model
of `Λ` that sends the `i`-th standard basis vector to `1 ⊗ bᵢ` (`ratModelIsometry_single`). -/
noncomputable def ratModelIsometry (P : IntegralPresentation Λ) :
    TauCeti.IntegralLattice.Isometry P.toIntegralLattice (ZLattice.ratModel P.isIntegral_real) :=
  TauCeti.IntegralLattice.Isometry.ofGramMatrixEq
    (TauCeti.IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin d)) P.gram P.gram_isSymm)
    (P.basis.map (ZLattice.ratModelCarrierEquiv P.isIntegral_real))
    ((TauCeti.IntegralLattice.gramMatrix_ofGramMatrix _ _ _).trans P.gramMatrix_ratModel.symm)

/-- The isometry `ratModelIsometry` sends the `i`-th standard basis vector to `1 ⊗ bᵢ`. -/
@[simp]
theorem ratModelIsometry_single (P : IntegralPresentation Λ) (i : Fin d) :
    P.ratModelIsometry (Pi.single i 1) = (1 : ℚ) ⊗ₜ[ℤ] P.basis i := by
  have h := TauCeti.IntegralLattice.Isometry.ofGramMatrixEq_apply_basis
    (TauCeti.IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin d)) P.gram P.gram_isSymm)
    (P.basis.map (ZLattice.ratModelCarrierEquiv P.isIntegral_real))
    ((TauCeti.IntegralLattice.gramMatrix_ofGramMatrix _ _ _).trans P.gramMatrix_ratModel.symm) i
  simp only [TauCeti.IntegralLattice.ofGramMatrix.coe_basis, Pi.basisFun_apply, Basis.map_apply,
    ZLattice.coe_ratModelCarrierEquiv] at h
  -- `h` is the claim with `ratModelIsometry` and `toIntegralLattice` unfolded.
  exact h

/-- Check that `simp` evaluates the isometry on coordinate vectors, including inside a sum. -/
example (P : IntegralPresentation Λ) (i j : Fin d) :
    P.ratModelIsometry (Pi.single i 1) + P.ratModelIsometry (Pi.single j 1) =
      (1 : ℚ) ⊗ₜ[ℤ] P.basis i + (1 : ℚ) ⊗ₜ[ℤ] P.basis j := by
  simp

/-- Check that two presentations of the same lattice give isometric lattices in Gram
coordinates. -/
example (P Q : IntegralPresentation Λ) :
    Nonempty (TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice) :=
  ⟨P.ratModelIsometry.trans Q.ratModelIsometry.symm⟩

/-- A presentation is positive definite: the Gram matrix of a basis of a full Euclidean lattice is
positive definite. -/
theorem isPosDef (P : IntegralPresentation Λ) : P.IsPosDef :=
  P.ratModelIsometry.isPosDef_iff.mpr (ZLattice.isPosDef_ratModel P.isIntegral_real)

/-- The lattice is even in TauCeti's real sense, every vector of `Λ` having even integral squared
norm, exactly when the presentation is even. -/
theorem isEven_real_iff (P : IntegralPresentation Λ) : ZLattice.IsEven Λ ↔ P.IsEven :=
  (ZLattice.isEven_ratModel_iff P.isIntegral_real).symm.trans P.ratModelIsometry.isEven_iff.symm

/-- An even presentation makes the lattice even in TauCeti's real sense: every vector of `Λ` has
even integral squared norm. -/
theorem isEven_real (P : IntegralPresentation Λ) (heven : P.IsEven) : ZLattice.IsEven Λ :=
  P.isEven_real_iff.mpr heven

/-- The lattice is unimodular in TauCeti's real sense, `Λ` being its own dual lattice, exactly when
the presentation is unimodular. -/
theorem isUnimodular_real_iff (P : IntegralPresentation Λ) :
    ZLattice.IsUnimodular Λ ↔ P.IsUnimodular :=
  (ZLattice.isUnimodular_ratModel_iff P.isIntegral_real).symm.trans
    P.ratModelIsometry.isUnimodular_iff.symm

/-- A unimodular presentation makes the lattice unimodular in TauCeti's real sense: `Λ` is its
own dual lattice. -/
theorem isUnimodular_real (P : IntegralPresentation Λ) (hunimodular : P.IsUnimodular) :
    ZLattice.IsUnimodular Λ :=
  P.isUnimodular_real_iff.mpr hunimodular

/-- The squared covolume of `Λ` is the discriminant of its presentation, the absolute value of the
determinant of the Gram matrix. -/
theorem covolume_sq_eq_discriminant (P : IntegralPresentation Λ) :
    ZLattice.covolume Λ ^ 2 = P.toIntegralLattice.discriminant := by
  rw [← ZLattice.det_def, ← ZLattice.discriminant_ratModel P.isIntegral_real,
    P.ratModelIsometry.discriminant_eq]

/-- A presentation is unimodular exactly when `Λ` has covolume one. -/
theorem isUnimodular_iff_covolume_eq_one (P : IntegralPresentation Λ) :
    P.IsUnimodular ↔ ZLattice.covolume Λ = 1 :=
  P.isUnimodular_real_iff.symm.trans P.isIntegral_real.isUnimodular_iff_covolume_eq_one

/-- The real dual lattice of a lattice with a unimodular presentation is the lattice itself. -/
theorem dual_eq_self_of_isUnimodular (P : IntegralPresentation Λ) (h : P.IsUnimodular) :
    ZLattice.dual Λ = Λ :=
  (P.isUnimodular_real h).dual_eq

/-- Read in `ℝ^d` through TauCeti's map `ZLattice.ratModelMap`, the isometry `ratModelIsometry`
sends a vector `q` of `ℚ^d` to `∑ i, qᵢ bᵢ`. -/
theorem ratModelMap_ratModelIsometry (P : IntegralPresentation Λ) (q : Fin d → ℚ) :
    ZLattice.ratModelMap Λ (P.ratModelIsometry q) =
      ∑ i, (q i : ℝ) • (P.basis i : EuclideanSpace ℝ (Fin d)) := by
  conv_lhs => rw [← (Pi.basisFun ℚ (Fin d)).sum_repr q]
  simp [TensorProduct.smul_tmul']

/-- The coordinate vector of a vector of `Λ`, carried into the rational model and read in `ℝ^d`,
is the vector itself. -/
theorem ratModelMap_ratModelIsometry_carrierEquiv (P : IntegralPresentation Λ) (x : Λ) :
    ZLattice.ratModelMap Λ (P.ratModelIsometry (P.carrierEquiv x)) = x := by
  rw [ratModelMap_ratModelIsometry]
  conv_rhs => rw [← P.basis.sum_repr x]
  simp only [coe_carrierEquiv_apply, Rat.cast_intCast, Int.cast_smul_eq_zsmul, Submodule.coe_sum,
    Submodule.coe_smul_of_tower]

/-- The norm of the coordinate vector of a vector of `Λ` is its squared length. -/
theorem norm_carrierEquiv (P : IntegralPresentation Λ) (x : Λ) :
    (P.toIntegralLattice.norm (P.carrierEquiv x) : ℝ) = ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  rw [← P.ratModelIsometry.norm_apply, ← ZLattice.norm_sq_ratModelMap P.isIntegral_real,
    ratModelMap_ratModelIsometry_carrierEquiv]

/-- The identification of the real dual lattice of `Λ` with the dual carrier of the lattice in
Gram coordinates, through TauCeti's rational model. -/
noncomputable def dualCarrierEquiv (P : IntegralPresentation Λ) :
    ZLattice.dual Λ ≃ₗ[ℤ] P.toIntegralLattice.dualCarrier :=
  (ZLattice.ratModelDualEquiv P.isIntegral_real).trans P.ratModelIsometry.symm.dualCarrierEquiv

/-- A vector `y` of the real dual lattice is the combination of the presentation basis with
coefficients the coordinates of `P.dualCarrierEquiv y`. -/
theorem sum_dualCarrierEquiv_smul_basis (P : IntegralPresentation Λ) (y : ZLattice.dual Λ) :
    ∑ i, ((P.dualCarrierEquiv y : Fin d → ℚ) i : ℝ) • (P.basis i : EuclideanSpace ℝ (Fin d)) =
      y := by
  rw [← ratModelMap_ratModelIsometry]
  simp only [dualCarrierEquiv, LinearEquiv.trans_apply,
    TauCeti.IntegralLattice.Isometry.coe_dualCarrierEquiv_apply,
    TauCeti.IntegralLattice.Isometry.apply_symm_apply, ZLattice.ratModelMap_ratModelDualEquiv]

/-- A vector lies in the real dual lattice of `Λ` exactly when its coordinates in the presentation
basis form a vector of the dual carrier of the lattice in Gram coordinates. -/
theorem mem_dual_iff_exists_dualCarrier_coordinates (P : IntegralPresentation Λ)
    (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ ZLattice.dual Λ ↔
      ∃ q : P.toIntegralLattice.dualCarrier,
        x = ∑ i, ((q : Fin d → ℚ) i : ℝ) • (P.basis i : EuclideanSpace ℝ (Fin d)) := by
  refine ⟨fun hx ↦ ⟨P.dualCarrierEquiv ⟨x, hx⟩, (P.sum_dualCarrierEquiv_smul_basis ⟨x, hx⟩).symm⟩,
    ?_⟩
  rintro ⟨q, rfl⟩
  rw [← ratModelMap_ratModelIsometry, ← ZLattice.mem_ratModel_dualCarrier_iff P.isIntegral_real,
    P.ratModelIsometry.apply_mem_dualCarrier_iff]
  exact q.2

/-- The coordinate identification restricted to shells: the vectors of `Λ` of squared length `n`
correspond to the vectors of norm `n` of the lattice in Gram coordinates. -/
noncomputable def shellEquiv (P : IntegralPresentation Λ) (n : ℕ) :
    ↑(ZLattice.shell Λ n) ≃ ↑(P.toIntegralLattice.vectorsOfNorm n) where
  toFun v := ⟨P.carrierEquiv ⟨v, (ZLattice.mem_shell.mp v.2).1⟩, by
    rw [TauCeti.IntegralLattice.mem_vectorsOfNorm, ← (Rat.cast_injective (α := ℝ)).eq_iff,
      P.norm_carrierEquiv]
    exact_mod_cast (ZLattice.mem_shell.mp v.2).2⟩
  invFun w := ⟨P.carrierEquiv.symm w, by
    refine ZLattice.mem_shell.mpr ⟨(P.carrierEquiv.symm w).2, ?_⟩
    have h := P.norm_carrierEquiv (P.carrierEquiv.symm w)
    rw [LinearEquiv.apply_symm_apply, TauCeti.IntegralLattice.mem_vectorsOfNorm.mp w.2] at h
    exact_mod_cast h.symm⟩
  left_inv v := by simp
  right_inv w := by simp

/-- The shell identification is the coordinate identification `carrierEquiv`. -/
@[simp]
theorem coe_shellEquiv_apply (P : IntegralPresentation Λ) (n : ℕ) (v : ZLattice.shell Λ n) :
    (P.shellEquiv n v : P.toIntegralLattice) =
      P.carrierEquiv ⟨v, (ZLattice.mem_shell.mp v.2).1⟩ :=
  (rfl)

/-- Check that `simp` computes the coordinates of the image of a shell vector. -/
example (P : IntegralPresentation Λ) (n : ℕ) (v : ZLattice.shell Λ n) (i : Fin d) :
    ((P.shellEquiv n v : P.toIntegralLattice) : Fin d → ℚ) i =
      P.basis.repr ⟨v, (ZLattice.mem_shell.mp v.2).1⟩ i := by
  simp

/-- The inverse shell identification is the inverse coordinate identification. -/
@[simp]
theorem coe_shellEquiv_symm_apply (P : IntegralPresentation Λ) (n : ℕ)
    (w : P.toIntegralLattice.vectorsOfNorm n) :
    (((P.shellEquiv n).symm w : ZLattice.shell Λ n) : EuclideanSpace ℝ (Fin d)) =
      ((P.carrierEquiv.symm w : Λ) : EuclideanSpace ℝ (Fin d)) :=
  (rfl)

/-- Check that `simp` returns a vector of the lattice in Gram coordinates through the shell
identification. -/
example (P : IntegralPresentation Λ) (n : ℕ) (w : P.toIntegralLattice.vectorsOfNorm n) :
    P.carrierEquiv ⟨((P.shellEquiv n).symm w : EuclideanSpace ℝ (Fin d)),
      (ZLattice.mem_shell.mp ((P.shellEquiv n).symm w).2).1⟩ = w := by
  simp

/-- A presentation is rootless exactly when `Λ` has no vector of squared length two. -/
theorem isRootless_iff_shell_two_eq_empty (P : IntegralPresentation Λ) :
    P.toIntegralLattice.IsRootless ↔ ZLattice.shell Λ 2 = ∅ := by
  rw [TauCeti.IntegralLattice.isRootless_iff, ← Set.isEmpty_coe_sort, ← Set.isEmpty_coe_sort]
  exact_mod_cast (P.shellEquiv 2).isEmpty_congr.symm

end IntegralPresentation

/-! ### Full rank, and the real extension of an isometry -/

namespace IntegralPresentation

variable {d : ℕ} {Λ Μ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}

/-- A presented lattice is discrete. -/
theorem discreteTopology (P : IntegralPresentation Λ) : DiscreteTopology Λ :=
  P.isIntegral_real.discreteTopology

/-- A presented lattice spans `ℝ^d`: its `ℤ`-rank `d` is the dimension of its real span. -/
theorem isZLattice (P : IntegralPresentation Λ) [DiscreteTopology Λ] : IsZLattice ℝ Λ := by
  have : DiscreteTopology (Submodule.span ℤ (Λ : Set (EuclideanSpace ℝ (Fin d)))) := by
    rwa [Submodule.span_eq]
  have h := Real.finrank_eq_int_finrank_of_discrete this
  rw [Set.finrank, Set.finrank, Submodule.span_eq, Module.finrank_eq_card_basis P.basis,
    Fintype.card_fin] at h
  exact ⟨Submodule.eq_top_of_finrank_eq (h.trans finrank_euclideanSpace_fin.symm)⟩

/-- The vector of `ℝ^d` with coordinates `q` in the presentation basis. -/
private noncomputable def toReal (P : IntegralPresentation Λ) (q : Fin d → ℚ) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ i, (q i : ℝ) • (P.basis i : EuclideanSpace ℝ (Fin d))

private theorem toReal_single (P : IntegralPresentation Λ) (i : Fin d) :
    P.toReal (Pi.single i 1) = P.basis i := by
  rw [toReal, Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

private theorem toReal_sum_smul (P : IntegralPresentation Λ) (c : Fin d → ℚ)
    (q : Fin d → Fin d → ℚ) : P.toReal (∑ i, c i • q i) = ∑ i, (c i : ℝ) • P.toReal (q i) := by
  simp only [toReal, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Rat.cast_sum, Rat.cast_mul, Finset.sum_smul]
  exact Finset.sum_comm

private theorem toReal_carrierEquiv (P : IntegralPresentation Λ) (x : Λ) :
    P.toReal (P.carrierEquiv x) = x := by
  simp only [toReal, coe_carrierEquiv_apply, Rat.cast_intCast, Int.cast_smul_eq_zsmul]
  conv_rhs => rw [← P.basis.sum_repr x]
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]

private theorem toReal_mem (P : IntegralPresentation Λ) (c : P.toIntegralLattice) :
    P.toReal c ∈ Λ := by
  have h := P.toReal_carrierEquiv (P.carrierEquiv.symm c)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h ▸ (P.carrierEquiv.symm c).2

private theorem inner_toReal (P : IntegralPresentation Λ) (x y : Fin d → ℚ) :
    ⟪P.toReal x, P.toReal y⟫_ℝ = (P.toIntegralLattice.form x y : ℝ) := by
  simp only [toReal, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    ← P.gram_spec, toIntegralLattice_def, TauCeti.IntegralLattice.ofGramMatrix_form,
    Matrix.toBilin_apply, Pi.basisFun_repr, Matrix.map_apply, eq_intCast, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_intCast]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The extension to `ℝ^d` of an isometry `e` between the lattices of two presentations in Gram
coordinates: the real linear isometry sending the `i`-th basis vector of `P` to the vector with
coordinates `e eᵢ` in the basis of `Q` (`realIsometryOfIsometry_basis`). -/
noncomputable def realIsometryOfIsometry (P : IntegralPresentation Λ)
    (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  haveI := P.discreteTopology
  haveI := P.isZLattice
  let B := P.basis.ofZLatticeBasis ℝ Λ
  let f := B.constr ℝ fun i ↦ Q.toReal (e (Pi.single i 1))
  have hf : ∀ x y, ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ := by
    have h : (innerₗ (EuclideanSpace ℝ (Fin d))).compl₁₂ f f =
        innerₗ (EuclideanSpace ℝ (Fin d)) := by
      refine B.ext fun i ↦ B.ext fun j ↦ ?_
      simp only [LinearMap.compl₁₂_apply, innerₗ_apply_apply, f, Basis.constr_basis]
      simp only [B, Basis.ofZLatticeBasis_apply, ← P.toReal_single, inner_toReal,
        TauCeti.IntegralLattice.Isometry.map_app]
    exact fun x y ↦ LinearMap.congr_fun₂ h x y
  (f.isometryOfInner hf).toLinearIsometryEquiv rfl

/-- The real extension sends the `i`-th basis vector of `P` to the vector with coordinates
`e eᵢ` in the basis of `Q`. -/
theorem realIsometryOfIsometry_basis (P : IntegralPresentation Λ) (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice) (i : Fin d) :
    realIsometryOfIsometry P Q e (P.basis i : EuclideanSpace ℝ (Fin d)) =
      ∑ j, ((e (Pi.single i 1) j : ℚ) : ℝ) • (Q.basis j : EuclideanSpace ℝ (Fin d)) := by
  have := P.discreteTopology
  have := P.isZLattice
  rw [← Basis.ofZLatticeBasis_apply ℝ Λ P.basis i]
  simp only [realIsometryOfIsometry, LinearIsometry.coe_toLinearIsometryEquiv,
    LinearMap.coe_isometryOfInner, Basis.constr_basis, toReal]

/-- The real extension carries the vector with coordinates `q` in the basis of `P` to the vector
with coordinates `e q` in the basis of `Q`. -/
private theorem realIsometryOfIsometry_toReal (P : IntegralPresentation Λ)
    (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice)
    (q : Fin d → ℚ) : realIsometryOfIsometry P Q e (P.toReal q) = Q.toReal (e q) := by
  conv_rhs => rw [← (Pi.basisFun ℚ (Fin d)).sum_repr q]
  simp only [Pi.basisFun_repr, Pi.basisFun_apply, map_sum, map_smul, toReal_sum_smul]
  simp only [toReal, map_sum, map_smul, realIsometryOfIsometry_basis]

/-- The real extension of an isometry carries the lattice `Λ` onto the lattice `Μ`. -/
@[simp]
theorem realIsometry_maps_carrier (P : IntegralPresentation Λ) (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice) :
    realIsometryOfIsometry P Q e '' (Λ : Set (EuclideanSpace ℝ (Fin d))) = Μ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h : realIsometryOfIsometry P Q e x = Q.toReal (e (P.carrierEquiv ⟨x, hx⟩)) := by
      rw [← realIsometryOfIsometry_toReal, P.toReal_carrierEquiv]
    rw [h]
    exact Q.toReal_mem ⟨_, (e.apply_mem_carrier_iff _).mpr (P.carrierEquiv ⟨x, hx⟩).2⟩
  · intro hy
    refine ⟨P.toReal (e.symm (Q.carrierEquiv ⟨y, hy⟩)),
      P.toReal_mem ⟨_, (e.symm.apply_mem_carrier_iff _).mpr (Q.carrierEquiv ⟨y, hy⟩).2⟩, ?_⟩
    rw [realIsometryOfIsometry_toReal, TauCeti.IntegralLattice.Isometry.apply_symm_apply,
      Q.toReal_carrierEquiv]

/-- Check that `simp` computes the image of the lattice. -/
example (P : IntegralPresentation Λ) (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice) :
    realIsometryOfIsometry P Q e '' (Λ : Set (EuclideanSpace ℝ (Fin d))) = Μ := by
  simp

/-- The affine isometry `x ↦ realIsometryOfIsometry P Q e (x - v) + w`, which carries the coset
`v + Λ` onto the coset `w + Μ` (`affineIsometry_maps_coset`). -/
noncomputable def affineIsometryOfIsometry (P : IntegralPresentation Λ)
    (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice)
    (v w : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d) :=
  ((AffineIsometryEquiv.vaddConst ℝ v).symm.trans
    (realIsometryOfIsometry P Q e).toAffineIsometryEquiv).trans
      (AffineIsometryEquiv.vaddConst ℝ w)

/-- The affine extension is `x ↦ realIsometryOfIsometry P Q e (x - v) + w`. -/
theorem affineIsometryOfIsometry_apply (P : IntegralPresentation Λ) (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice)
    (v w x : EuclideanSpace ℝ (Fin d)) :
    affineIsometryOfIsometry P Q e v w x = realIsometryOfIsometry P Q e (x - v) + w :=
  (rfl)

/-- The affine extension carries the coset `v + Λ` onto the coset `w + Μ`. -/
@[simp]
theorem affineIsometry_maps_coset (P : IntegralPresentation Λ) (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice)
    (v w : EuclideanSpace ℝ (Fin d)) :
    affineIsometryOfIsometry P Q e v w '' (v +ᵥ (Λ : Set (EuclideanSpace ℝ (Fin d)))) =
      w +ᵥ (Μ : Set (EuclideanSpace ℝ (Fin d))) := by
  rw [← realIsometry_maps_carrier P Q e, ← Set.image_vadd, ← Set.image_vadd, Set.image_image,
    Set.image_image]
  refine Set.image_congr fun x _ ↦ ?_
  rw [affineIsometryOfIsometry_apply, vadd_eq_add, vadd_eq_add, add_sub_cancel_left, add_comm]

/-- Check that `simp` computes the image of a coset. -/
example (P : IntegralPresentation Λ) (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice)
    (v w : EuclideanSpace ℝ (Fin d)) :
    affineIsometryOfIsometry P Q e v w '' (v +ᵥ (Λ : Set (EuclideanSpace ℝ (Fin d)))) =
      w +ᵥ (Μ : Set (EuclideanSpace ℝ (Fin d))) := by
  simp

end IntegralPresentation

end SphereCeti.EuclideanLattice
