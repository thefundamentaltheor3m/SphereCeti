/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import SphereCeti.Leech.Embedding
public import TauCeti.Algebra.Module.ZLattice.Shell
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.RepresentationNumber

/-!
# The Euclidean Leech lattice

The Euclidean Leech lattice is the image of TauCeti's Leech lattice
`TauCeti.leechLattice ⊆ ℚ^24` under the isometric embedding `SphereCeti.Leech.embedding`
(`x ↦ x / √2`) into the packing space `EuclideanSpace ℝ (Fin 24)`.  It is a full `ℤ`-lattice in
`ℝ^24` whose nonzero vectors have squared norm at least `2`, and its representation numbers agree
with those of TauCeti's Leech lattice.  It is the lattice whose centers give the Leech sphere
packing.

## Main definitions and results

* `SphereCeti.Leech.lattice`: the Euclidean Leech lattice, a `ℤ`-submodule of
  `EuclideanSpace ℝ (Fin 24)`.
* `SphereCeti.Leech.mem_lattice_iff`: a vector lies in the lattice exactly when it is the image of
  a vector of TauCeti's Leech carrier.
* `SphereCeti.Leech.two_le_norm_sq_of_mem_lattice`: nonzero lattice vectors have squared norm at
  least `2`.
* `SphereCeti.Leech.lattice_discrete` and `SphereCeti.Leech.lattice_isZLattice`: the lattice is
  discrete and spans `ℝ^24`, so it is a full `ℤ`-lattice.
* `SphereCeti.Leech.representationNumber_lattice`: for every natural number `n`, the number of
  lattice vectors of squared norm `n` equals TauCeti's representation number of `n` for the Leech
  lattice.

## Source

The Leech lattice, its evenness, and its representation numbers are TauCeti's
(repository `TauCetiProject/TauCeti`, commit `83769e442d55cda9d85b3927a93b286831c595ff`, files
`TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/Basic.lean` and
`TauCeti/LinearAlgebra/IntegralLattice/PosDef/RepresentationNumber.lean`); the real shells are
TauCeti's `TauCeti/Algebra/Module/ZLattice/Shell.lean` at the same commit.
-/

public section

open scoped InnerProductSpace

namespace SphereCeti.Leech

/-- The Euclidean Leech lattice: the image of TauCeti's Leech lattice under `embedding`.  It is not
the naive unshifted Construction-A lattice of the Golay code. -/
noncomputable def lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 24)) :=
  TauCeti.leechLattice.carrier.map embedding.toIntLinearMap

/-- The Euclidean Leech lattice is the image of TauCeti's Leech carrier under `embedding`. -/
theorem lattice_def : lattice = TauCeti.leechLattice.carrier.map embedding.toIntLinearMap :=
  (rfl)

/-- A vector of `ℝ^24` lies in the Euclidean Leech lattice exactly when it is the embedded image of
a vector of TauCeti's Leech carrier. -/
@[simp]
theorem mem_lattice_iff (x : EuclideanSpace ℝ (Fin 24)) :
    x ∈ lattice ↔ ∃ y ∈ TauCeti.leechLattice.carrier, embedding y = x :=
  Iff.rfl

example {y : Fin 24 → ℚ} (hy : y ∈ TauCeti.leechLattice.carrier) : embedding y ∈ lattice := by
  simp only [mem_lattice_iff]
  exact ⟨y, hy, rfl⟩

/-- A nonzero vector of the Euclidean Leech lattice has squared norm at least `2`. -/
theorem two_le_norm_sq_of_mem_lattice {v : EuclideanSpace ℝ (Fin 24)} (hv : v ∈ lattice)
    (hv0 : v ≠ 0) : 2 ≤ ‖v‖ ^ 2 := by
  -- The squared norm is the Leech norm `2 * z` of the preimage, positive and hence `≥ 2`.
  obtain ⟨y, hy, rfl⟩ := (mem_lattice_iff v).mp hv
  obtain ⟨z, hz⟩ := TauCeti.isEven_leechLattice.exists_norm_eq_two_mul ⟨y, hy⟩
  rw [TauCeti.IntegralLattice.norm_apply] at hz
  have hpos : 0 < ‖embedding y‖ ^ 2 := by positivity
  rw [norm_embedding_sq, hz] at hpos ⊢
  push_cast at hpos ⊢
  have hz0 : (0 : ℝ) < z := by linarith
  have hz0' : (0 : ℤ) < z := by exact_mod_cast hz0
  have hz1' : (1 : ℤ) ≤ z := by omega
  have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast hz1'
  linarith

/-- The Euclidean Leech lattice is discrete. -/
instance lattice_discrete : DiscreteTopology lattice := by
  -- No nonzero lattice vector lies in the unit ball, since its squared norm is at least `2`.
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  refine ⟨1, one_pos, fun v hv => ?_⟩
  by_contra hne
  have hv0 : (v : EuclideanSpace ℝ (Fin 24)) ≠ 0 := fun h => hne (Subtype.ext h)
  have h2 := two_le_norm_sq_of_mem_lattice v.2 hv0
  rw [dist_zero_right] at hv
  have hv' : ‖(v : EuclideanSpace ℝ (Fin 24))‖ < 1 := hv
  nlinarith [norm_nonneg (v : EuclideanSpace ℝ (Fin 24))]

/-- The Euclidean Leech lattice is a full `ℤ`-lattice in `ℝ^24`. -/
instance lattice_isZLattice : IsZLattice ℝ lattice where
  span_top := by
    -- The Leech carrier spans `ℚ^24` and `embedding` is `ℚ`-linear, so the real span of the
    -- lattice contains every `embedding (Pi.single i 1) = e_i / √2`.
    set S := Submodule.span ℝ (lattice : Set (EuclideanSpace ℝ (Fin 24)))
    have hmem : ∀ x ∈ Submodule.span ℚ (TauCeti.leechLattice.carrier : Set (Fin 24 → ℚ)),
        embedding x ∈ S := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | zero => rw [map_zero]; exact S.zero_mem
      | add u w _ _ hu hw => rw [map_add]; exact S.add_mem hu hw
      | smul q u _ hu =>
        rw [map_rat_smul, ← Rat.cast_smul_eq_qsmul ℝ]
        exact S.smul_mem _ hu
    rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin 24) ℝ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi := hmem (Pi.single i 1) (by
      rw [TauCeti.leechLattice.isLattice.span_eq_top]; exact Submodule.mem_top)
    have heq : (EuclideanSpace.basisFun (Fin 24) ℝ).toBasis i =
        Real.sqrt 2 • embedding (Pi.single i 1) := by
      ext j
      simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.smul_apply,
        embedding_apply, smul_eq_mul]
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [heq]
    exact S.smul_mem (Real.sqrt 2) hi

/-- For every natural number `n`, the number of vectors of squared norm `n` in the Euclidean Leech
lattice equals the representation number of `n` by TauCeti's Leech lattice. -/
theorem representationNumber_lattice (n : ℕ) :
    ZLattice.representationNumber lattice n = TauCeti.leechLattice.representationNumber n := by
  rw [ZLattice.representationNumber_def, TauCeti.IntegralLattice.representationNumber_def]
  -- The real shell of squared norm `n` is the injective image of the Leech vectors of norm `n`.
  have hshell : ZLattice.shell lattice n =
      (fun y : TauCeti.leechLattice.carrier => embedding y) ''
        TauCeti.leechLattice.vectorsOfNorm n := by
    ext v
    simp only [ZLattice.mem_shell, Set.mem_image, TauCeti.IntegralLattice.mem_vectorsOfNorm,
      TauCeti.IntegralLattice.norm_apply, Subtype.exists, exists_and_right]
    constructor
    · rintro ⟨hv, hn⟩
      obtain ⟨y, hy, rfl⟩ := (mem_lattice_iff v).mp hv
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      rw [norm_embedding_sq] at hn
      exact_mod_cast hn
    · rintro ⟨y, ⟨hy, hn⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      rw [norm_embedding_sq, hn]
      push_cast
      rfl
  rw [hshell]
  exact Set.ncard_image_of_injective _ (embedding_injective.comp Subtype.val_injective)

end SphereCeti.Leech
