/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Integer translates in `τ` of the two-variable Jacobi theta function

Mathlib's two-variable Jacobi theta function
`jacobiTheta₂ z τ = ∑_{n ∈ ℤ} exp (2 π i n z + π i n² τ)` has period `2` in `τ`
(`jacobiTheta₂_add_right`) and period `1` in `z` (`jacobiTheta₂_add_left`). Translating `τ` by an
integer `m` is translating `z` by `m / 2`: `jacobiTheta₂ z (τ + m) = jacobiTheta₂ (z + m / 2) τ`
for all `z τ : ℂ` and `m : ℤ`.

## Main statements

* `TauCeti.jacobiTheta₂_add_intCast_right`: `jacobiTheta₂ z (τ + m) = jacobiTheta₂ (z + m / 2) τ`.
* `TauCeti.jacobiTheta₂_add_one_right`: `jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ`.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-- Translating `τ` by an integer `m` in the two-variable Jacobi theta function is translating `z`
by `m / 2`: `jacobiTheta₂ z (τ + m) = jacobiTheta₂ (z + m / 2) τ`. -/
theorem jacobiTheta₂_add_intCast_right (z τ : ℂ) (m : ℤ) :
    jacobiTheta₂ z (τ + m) = jacobiTheta₂ (z + m / 2) τ := by
  simp only [jacobiTheta₂, jacobiTheta₂_term]
  refine tsum_congr fun n ↦ Complex.exp_eq_exp_iff_exists_int.mpr ?_
  -- The exponents differ by `π i m n (n - 1)`, and `n (n - 1)` is even.
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self n
  refine ⟨m * k, ?_⟩
  have hk' : (n : ℂ) * (n - 1) = k + k := by exact_mod_cast hk
  push_cast
  linear_combination (π * I * m) * hk'

/-- Translating `τ` by `1` in the two-variable Jacobi theta function is translating `z` by
`1 / 2`: `jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ`. -/
theorem jacobiTheta₂_add_one_right (z τ : ℂ) :
    jacobiTheta₂ z (τ + 1) = jacobiTheta₂ (z + 1 / 2) τ := by
  simpa using jacobiTheta₂_add_intCast_right z τ 1

end TauCeti
