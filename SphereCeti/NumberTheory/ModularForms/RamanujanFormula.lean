/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Decay of `E₂ E₄ - E₆` at `i∞`

By Ramanujan's formula, `E₂ E₄ - E₆` is `3 D E₄`.  It tends to `0` at `i∞`, and there it is
`O(exp(-2π Im τ))`.

## Main statements

* `EisensteinSeries.isZeroAtImInfty_E2_mul_E4_sub_E6`: `E₂ E₄ - E₆` tends to `0` at `i∞`.
* `EisensteinSeries.isBigO_E2_mul_E4_sub_E6`: `E₂ E₄ - E₆ = O(exp(-2π Im τ))` at `i∞`.
-/

public section

open ModularForm UpperHalfPlane Filter Asymptotics
open scoped Manifold MatrixGroups Real

namespace EisensteinSeries

/-- `E₂ E₄ - E₆` tends to `0` at `i∞`. -/
theorem isZeroAtImInfty_E2_mul_E4_sub_E6 :
    IsZeroAtImInfty fun τ : ℍ ↦ E2 τ * E₄ τ - E₆ τ := by
  have h := (tendsto_E2_atImInfty.mul (tendsto_E_atImInfty (k := 4))).sub
    (tendsto_E_atImInfty (k := 6))
  simp only [mul_one, sub_self] at h
  exact h

/-- `E₂ E₄ - E₆` is `O(exp(-2π Im τ))` at `i∞`. -/
theorem isBigO_E2_mul_E4_sub_E6 :
    (fun τ : ℍ ↦ E2 τ * E₄ τ - E₆ τ) =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im) := by
  have hper : Function.Periodic ((fun τ : ℍ ↦ E2 τ * E₄ τ - E₆ τ) ∘ ofComplex) 1 :=
    (E2_periodic.mul (SlashInvariantFormClass.periodic_comp_ofComplex (f := E₄)
      one_mem_strictPeriods_SL)).sub
      (SlashInvariantFormClass.periodic_comp_ofComplex (f := E₆) one_mem_strictPeriods_SL)
  have hhol : MDiff fun τ : ℍ ↦ E2 τ * E₄ τ - E₆ τ :=
    (E2_mdifferentiable.mul (ModularFormClass.holo E₄)).sub (ModularFormClass.holo E₆)
  have hbdd : IsBoundedAtImInfty fun τ : ℍ ↦ E2 τ * E₄ τ - E₆ τ :=
    (isBoundedAtImInfty_E2.mul (ModularFormClass.bdd_at_infty E₄)).sub
      (ModularFormClass.bdd_at_infty E₆)
  simpa using isZeroAtImInfty_E2_mul_E4_sub_E6.exp_decay_atImInfty one_pos hper hhol hbdd

end EisensteinSeries
