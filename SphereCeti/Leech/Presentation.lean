/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Lattice.IntegralPresentation
public import SphereCeti.Leech.Lattice

/-!
# An integral presentation of the Euclidean Leech lattice

TauCeti's Leech lattice `TauCeti.leechLattice` has a carrier of rank `24` in `ℚ^24`.  Fix a
`ℤ`-basis `c₀, …, c₂₃` of it.  The isometric embedding `SphereCeti.Leech.embedding` (`x ↦ x / √2`)
carries this basis to a `ℤ`-basis of the Euclidean Leech lattice `SphereCeti.Leech.lattice`, and the
inner products of the embedded vectors are the values `⟪cᵢ, cⱼ⟫` of the Leech form, which are
integers.  This gives an integral presentation of the Euclidean Leech lattice whose Gram matrix is
TauCeti's Gram matrix of the basis `c`.

The lattice of this presentation in Gram coordinates is isometric to `TauCeti.leechLattice`: both
have a basis with the same Gram matrix.  Since the Leech lattice is even and unimodular, so is the
presentation, and the Euclidean Leech lattice has covolume one.

## Main definitions and results

* `SphereCeti.Leech.carrierBasis`: a `ℤ`-basis of TauCeti's Leech carrier indexed by `Fin 24`.
* `SphereCeti.Leech.carrierEquivLattice`: the `ℤ`-linear equivalence from the Leech carrier onto
  the Euclidean Leech lattice induced by `embedding`.
* `SphereCeti.Leech.integralPresentation`: the integral presentation of `SphereCeti.Leech.lattice`
  with basis vectors `embedding cᵢ` (`integralPresentation_basis_apply`) and Gram matrix
  `TauCeti.leechLattice.gramMatrix carrierBasis` (`integralPresentation_gram`).
* `SphereCeti.Leech.integralLatticeIsometry`: the isometry from the presentation in Gram
  coordinates to `TauCeti.leechLattice` sending the `i`-th standard basis vector to `cᵢ`
  (`integralLatticeIsometry_single`).
* `SphereCeti.Leech.integralPresentation_even`,
  `SphereCeti.Leech.integralPresentation_unimodular`: the presentation is even and unimodular.
* `SphereCeti.Leech.covolume_lattice`: the Euclidean Leech lattice has covolume one.

## Source

The Leech lattice, its rank `TauCeti.finrank_leechLattice`, its evenness
`TauCeti.isEven_leechLattice` and its unimodularity `TauCeti.isUnimodular_leechLattice` are
TauCeti's (repository `TauCetiProject/TauCeti`, commit
`83769e442d55cda9d85b3927a93b286831c595ff`, file
`TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/Basic.lean`); Gram matrices and the isometry
`TauCeti.IntegralLattice.Isometry.ofGramMatrixEq` between lattices with bases of equal Gram
matrices are from `TauCeti/LinearAlgebra/IntegralLattice/Gram.lean` at the same commit.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer
  (1999), Chapter 4, Section 11.
-/

public section

open scoped InnerProductSpace

namespace SphereCeti.Leech

/-- A `ℤ`-basis of TauCeti's Leech carrier, indexed by `Fin 24`, chosen from its rank `24`
(`TauCeti.finrank_leechLattice`). -/
noncomputable def carrierBasis : Module.Basis (Fin 24) ℤ TauCeti.leechLattice.carrier :=
  Module.finBasisOfFinrankEq ℤ _ TauCeti.finrank_leechLattice

/-- The `ℤ`-linear equivalence from TauCeti's Leech carrier onto the Euclidean Leech lattice
induced by the injective map `embedding`. -/
noncomputable def carrierEquivLattice : TauCeti.leechLattice.carrier ≃ₗ[ℤ] lattice :=
  (Submodule.equivMapOfInjective embedding.toIntLinearMap
    (fun _ _ h ↦ embedding_injective h) _).trans
    (LinearEquiv.ofEq _ _ lattice_def.symm)

/-- The equivalence `carrierEquivLattice` is `embedding` on underlying vectors. -/
@[simp]
theorem coe_carrierEquivLattice_apply (y : TauCeti.leechLattice.carrier) :
    (carrierEquivLattice y : EuclideanSpace ℝ (Fin 24)) = embedding y := by
  rw [carrierEquivLattice, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact Submodule.coe_equivMapOfInjective_apply _ _ _ _

example (y : TauCeti.leechLattice.carrier) :
    (carrierEquivLattice (y + y) : EuclideanSpace ℝ (Fin 24)) = embedding y + embedding y := by
  simp

/-- The integral presentation of the Euclidean Leech lattice transported from `carrierBasis`: its
basis vectors are the embedded vectors `embedding cᵢ` and its Gram matrix is TauCeti's Gram matrix
of `carrierBasis`. -/
noncomputable def integralPresentation : EuclideanLattice.IntegralPresentation lattice :=
  EuclideanLattice.IntegralPresentation.ofBasis (carrierBasis.map carrierEquivLattice)
    (TauCeti.leechLattice.gramMatrix carrierBasis) fun i j ↦ by
      simp only [Module.Basis.map_apply, coe_carrierEquivLattice_apply, inner_embedding,
        ← TauCeti.IntegralLattice.intCast_gramMatrix_apply]
      exact_mod_cast rfl

/-- The `i`-th basis vector of `integralPresentation` is the embedded `i`-th vector of
`carrierBasis`. -/
@[simp]
theorem integralPresentation_basis_apply (i : Fin 24) :
    (integralPresentation.basis i : EuclideanSpace ℝ (Fin 24)) = embedding (carrierBasis i) := by
  simp [integralPresentation]

example (i : Fin 24) :
    (integralPresentation.basis i : EuclideanSpace ℝ (Fin 24)) ∈ lattice := by
  simp only [integralPresentation_basis_apply, mem_lattice_iff]
  exact ⟨_, (carrierBasis i).2, rfl⟩

/-- The Gram matrix of `integralPresentation` is TauCeti's Gram matrix of `carrierBasis`. -/
@[simp]
theorem integralPresentation_gram :
    integralPresentation.gram = TauCeti.leechLattice.gramMatrix carrierBasis := by
  simp [integralPresentation]

example (i j : Fin 24) :
    (integralPresentation.gram i j : ℚ) =
      TauCeti.leechLattice.form (carrierBasis i : Fin 24 → ℚ) (carrierBasis j) := by
  simp

/-- The isometry from the lattice of `integralPresentation` in Gram coordinates to TauCeti's Leech
lattice sending the `i`-th standard basis vector to the `i`-th vector of `carrierBasis`
(`integralLatticeIsometry_single`): both lattices have a basis with the same Gram matrix. -/
noncomputable def integralLatticeIsometry :
    TauCeti.IntegralLattice.Isometry integralPresentation.toIntegralLattice
      TauCeti.leechLattice :=
  (TauCeti.IntegralLattice.Isometry.ofEq integralPresentation.toIntegralLattice_def).trans
    (TauCeti.IntegralLattice.Isometry.ofGramMatrixEq
      (TauCeti.IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin 24))
        integralPresentation.gram integralPresentation.gram_isSymm)
      carrierBasis
      ((TauCeti.IntegralLattice.gramMatrix_ofGramMatrix _ _ _).trans integralPresentation_gram))

/-- The isometry `integralLatticeIsometry` sends the `i`-th standard basis vector to the `i`-th
vector of `carrierBasis`. -/
@[simp]
theorem integralLatticeIsometry_single (i : Fin 24) :
    integralLatticeIsometry (Pi.single i 1) = carrierBasis i := by
  have h := TauCeti.IntegralLattice.Isometry.ofGramMatrixEq_apply_basis
    (TauCeti.IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin 24))
      integralPresentation.gram integralPresentation.gram_isSymm)
    carrierBasis
    ((TauCeti.IntegralLattice.gramMatrix_ofGramMatrix _ _ _).trans integralPresentation_gram) i
  simp only [TauCeti.IntegralLattice.ofGramMatrix.coe_basis, Pi.basisFun_apply] at h
  rw [integralLatticeIsometry, TauCeti.IntegralLattice.Isometry.trans_apply,
    TauCeti.IntegralLattice.Isometry.ofEq_apply]
  exact h

/-- Embedding the image of the `i`-th standard basis vector under `integralLatticeIsometry` gives
the `i`-th basis vector of `integralPresentation`. -/
theorem embedding_integralLatticeIsometry_single (i : Fin 24) :
    embedding (integralLatticeIsometry (Pi.single i 1)) =
      (integralPresentation.basis i : EuclideanSpace ℝ (Fin 24)) := by
  simp

/-- The integral presentation of the Euclidean Leech lattice is even. -/
@[simp]
theorem integralPresentation_even : integralPresentation.IsEven :=
  integralLatticeIsometry.isEven_iff.mpr TauCeti.isEven_leechLattice

/-- The integral presentation of the Euclidean Leech lattice is unimodular.  It is not a `simp`
lemma, since `simp` unfolds unimodularity by `TauCeti.IntegralLattice.isUnimodular_def`; the
unfolded form is the `simp` lemma `integralPresentation_carrier_eq_dualCarrier`. -/
theorem integralPresentation_unimodular : integralPresentation.IsUnimodular :=
  integralLatticeIsometry.isUnimodular_iff.mpr TauCeti.isUnimodular_leechLattice

/-- The lattice of the Leech presentation in Gram coordinates equals its dual lattice: the
unimodularity of the presentation in `simp` normal form. -/
@[simp]
theorem integralPresentation_carrier_eq_dualCarrier :
    integralPresentation.toIntegralLattice.carrier =
      integralPresentation.toIntegralLattice.dualCarrier :=
  integralPresentation.toIntegralLattice.isUnimodular_def.mp integralPresentation_unimodular

example : integralPresentation.IsEven ∧ integralPresentation.IsUnimodular := by simp

/-- The Euclidean Leech lattice has covolume one. -/
theorem covolume_lattice : ZLattice.covolume lattice = 1 :=
  integralPresentation.isUnimodular_iff_covolume_eq_one.mp integralPresentation_unimodular

end SphereCeti.Leech
