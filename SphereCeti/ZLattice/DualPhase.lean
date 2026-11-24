/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Algebra.Module.ZLattice.Dual

/-!
# Phases at dual frequencies

For a subgroup `L` of a real inner product space and a frequency `y` in its dual lattice, the
phase `exp (2πi ⟪y, s⟫)` depends only on the class of `s` modulo `L`: two points that differ by a
vector of `L` have the same phase.

## Main statements

* `ZLattice.phase_eq_of_sub_mem_lattice`: at a dual frequency, two points that differ by a lattice
  vector have the same phase.
-/

public section

open Complex
open scoped Real RealInnerProductSpace

namespace ZLattice

/-- At a frequency `y` in the dual of `L`, two points that differ by a vector of `L` have the same
phase `exp (2πi ⟪y, ·⟫)`. -/
theorem phase_eq_of_sub_mem_lattice {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {L : Submodule ℤ E} {y : E} (hy : y ∈ ZLattice.dual L) {s t : E} (hst : s - t ∈ L) :
    cexp (2 * π * I * ⟪y, s⟫) = cexp (2 * π * I * ⟪y, t⟫) := by
  obtain ⟨m, hm⟩ := ZLattice.mem_dual.mp hy (s - t) hst
  -- The two inner products differ by the integer `m`, so the exponents differ by `2πi m`.
  have hexp : 2 * π * I * ⟪y, s⟫ = m * (2 * π * I) + 2 * π * I * ⟪y, t⟫ := by
    rw [inner_sub_right] at hm
    rw [show ⟪y, s⟫ = m + ⟪y, t⟫ by linarith]
    push_cast
    ring
  rw [hexp, exp_add, exp_int_mul_two_pi_mul_I, one_mul]

end ZLattice
