/-
Copyright (c) 2026 Sphere-Packing-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere-Packing-Lean contributors, Bakhyt Momunov
-/

module

public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

import SphereCeti.Data.Int.Order
import SphereCeti.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Leading term of the second theta constant

At the infinite cusp, `H₂(τ) / exp(π i τ) → 16`. The diagonal Jacobi series
`jacobiTheta₂ (τ/2) τ` tends to two, from the terms indexed by `-1` and `0`.

The dominated-convergence argument for the diagonal theta series is adapted from
`thefundamentaltheor3m/Sphere-Packing-Lean@bad3de916074748eb88b7d1ee6dbf9494361ad17`,
`SpherePacking/ModularForms/JacobiTheta/Basic.lean` and `JacobiIdentity.lean` (Apache-2.0).
The result complements the unnormalized theta limits in `JacobiTheta.Basic`.
-/

@[expose] public noncomputable section

open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped UpperHalfPlane

namespace TauCeti.ModularForm

/-- `jacobiTheta₂ (τ / 2) τ` tends to `2` as `im τ` tends to infinity. -/
theorem tendsto_theta_half :
    Tendsto (fun τ : ℍ => jacobiTheta₂ (τ / 2) τ) atImInfty (𝓝 2) := by
  -- Only the summands indexed by `-1` and `0` survive at the infinite cusp.
  have hs : Summable (fun n : ℤ => ‖jacobiTheta₂_term n (I / 2) I‖) :=
    ((summable_jacobiTheta₂_term_iff (I / 2) I).2 (by simp)).norm
  have hlim (n : ℤ) : Tendsto (fun τ : ℍ => jacobiTheta₂_term n (τ / 2) τ)
      atImInfty (𝓝 (if n = -1 ∨ n = 0 then (1 : ℂ) else 0)) := by
    by_cases hn : n = -1 ∨ n = 0
    · rcases hn with rfl | rfl <;> simp [jacobiTheta₂_term_half]
    · simp only [hn, ↓reduceIte]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp_rw [norm_jacobiTheta₂_term_half]
      have hpos : 0 < (n : ℝ) ^ 2 + n := by
        have hi : 0 < n * (n + 1) := by
          rcases lt_or_ge 0 n with h | h
          · exact mul_pos h (by omega)
          · exact mul_pos_of_neg_of_neg (by omega) (by omega)
        have hquad : 0 < n ^ 2 + n := by nlinarith
        exact_mod_cast hquad
      exact Real.tendsto_exp_atBot.comp
        (tendsto_comap.const_mul_atTop_of_neg (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hpos))
  have hbound : ∀ᶠ τ : ℍ in atImInfty, ∀ n : ℤ,
      ‖jacobiTheta₂_term n (τ / 2) τ‖ ≤ ‖jacobiTheta₂_term n (I / 2) I‖ := by
    have hlarge : ∀ᶠ τ : ℍ in atImInfty, 1 ≤ τ.im :=
      preimage_mem_comap (Ici_mem_atTop 1)
    filter_upwards [hlarge] with τ hτ n
    rw [norm_jacobiTheta₂_term_half, norm_jacobiTheta₂_term_half]
    simp only [Complex.I_im]
    apply Real.exp_le_exp.mpr
    have hquad : 0 ≤ (n : ℝ) ^ 2 + n := by exact_mod_cast Int.sq_add_self_nonneg n
    simpa using mul_le_mul_of_nonpos_left hτ
      (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le hquad))
  have h := tendsto_tsum_of_dominated_convergence hs hlim hbound
  have he : (∑' n : ℤ, if n = -1 ∨ n = 0 then (1 : ℂ) else 0) = 2 := by
    rw [tsum_eq_sum (s := {-1, 0}) (fun n hn => by simpa using hn)]
    norm_num [Finset.sum_insert, Finset.sum_singleton, Finset.filter_insert,
      Finset.filter_singleton]
  rw [he] at h
  exact h

/-- The leading coefficient of `H₂` with respect to `exp(π i τ)` is `16`. -/
theorem tendsto_H₂_div_exp_atImInfty :
    Tendsto (fun τ : ℍ => H₂ τ / cexp (Real.pi * I * τ)) atImInfty (𝓝 16) := by
  have he (τ : ℍ) : H₂ τ / cexp (Real.pi * I * τ) =
      jacobiTheta₂ (τ / 2) τ ^ 4 := by
    rw [H₂_def, Θ₂_def, mul_pow, ← Complex.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    have hexponent : (4 : ℂ) * (Real.pi * I * τ / 4) = Real.pi * I * τ := by ring
    rw [hexponent]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  simp_rw [he]
  convert tendsto_theta_half.pow 4 using 1
  norm_num

end TauCeti.ModularForm
