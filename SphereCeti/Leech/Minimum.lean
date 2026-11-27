/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Leech.Lattice
public import SphereCeti.Lattice.MinNorm
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Minimum

/-!
# The minimum squared norm of the Euclidean Leech lattice

The embedding of TauCeti's rational Leech lattice preserves its quadratic form as squared
Euclidean norm. Thus its lower bound of four transports to the Euclidean lattice, and the
embedded odd shift attains that bound. The resulting minimum gives the separation two used by
the canonical unit-ball packing, independently of a choice of integral presentation.

This implements the Layer 6 `Leech.hasMinNormSq` target (MIGRATION I1). The rational lower bound
and the odd-shift witness are from `TauCetiProject/TauCeti` at
`83769e442d55cda9d85b3927a93b286831c595ff`,
`TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/Minimum.lean` and `Basic.lean`.
-/

public section

namespace SphereCeti.Leech

/-- Every nonzero vector of the Euclidean Leech lattice has squared norm at least four. -/
theorem four_le_norm_sq_of_mem_lattice {v : EuclideanSpace ℝ (Fin 24)} (hv : v ∈ lattice)
    (hv0 : v ≠ 0) : 4 ≤ ‖v‖ ^ 2 := by
  obtain ⟨y, hy, rfl⟩ := (mem_lattice_iff v).mp hv
  have hy0 : y ≠ 0 := by
    intro h
    exact hv0 (by simp [h])
  have h4 := TauCeti.four_le_norm_leechLattice hy hy0
  rw [TauCeti.IntegralLattice.norm_apply] at h4
  rw [norm_embedding_sq]
  exact_mod_cast h4

/-- The Euclidean Leech lattice has attained minimum squared norm four. -/
theorem hasMinNormSq : EuclideanLattice.HasMinNormSq lattice 4 := by
  apply EuclideanLattice.hasMinNormSq_iff.mpr
  refine ⟨EuclideanLattice.minNormSqAtLeast_iff.mpr
    (fun x hx ↦ four_le_norm_sq_of_mem_lattice x.property (by simpa using hx)), ?_⟩
  refine ⟨⟨embedding TauCeti.leechShift,
    (mem_lattice_iff _).mpr ⟨_, TauCeti.leechShift_mem_leechLattice_carrier, rfl⟩⟩, ?_, ?_⟩
  · intro h
    apply TauCeti.leechShift_ne_zero
    apply embedding_injective
    simpa using congrArg Subtype.val h
  · rw [norm_embedding_sq, TauCeti.leechLattice_form_leechShift_leechShift]
    norm_num

/-- Separation two is valid for the centers of the canonical Leech packing. -/
theorem two_le_norm_of_mem_lattice {v : EuclideanSpace ℝ (Fin 24)} (hv : v ∈ lattice)
    (hv0 : v ≠ 0) : 2 ≤ ‖v‖ := by
  have h := four_le_norm_sq_of_mem_lattice hv hv0
  nlinarith [norm_nonneg v]

example (x : lattice) (hx : x ≠ 0) : 2 ≤ ‖(x : EuclideanSpace ℝ (Fin 24))‖ :=
  two_le_norm_of_mem_lattice x.property (by simpa using hx)

end SphereCeti.Leech
