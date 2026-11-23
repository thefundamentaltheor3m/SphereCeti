/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Algebra.Module.ZLattice.RationalModel

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
  forward directions.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer (2013), Chapter 1.
-/

public section

open Module TensorProduct
open scoped InnerProductSpace

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

variable [DiscreteTopology Λ] [IsZLattice ℝ Λ]

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

end IntegralPresentation

end SphereCeti.EuclideanLattice
