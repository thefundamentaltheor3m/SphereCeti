/-
Copyright (c) 2026 Sphere-Packing-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere-Packing-Lean contributors, Bakhyt Momunov
-/

module

public import SphereCeti.ModularForms.ThetaConstants.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Cusp limits of the classical theta constants

At the infinite cusp, `H2` tends to zero and `H3`, `H4` tend to one. The sharper
normalization `H2(τ) / exp(π i τ) → 16` records the leading coefficient of `H2`.

The dominated-convergence argument for the diagonal theta series is adapted from
`thefundamentaltheor3m/Sphere-Packing-Lean@bad3de916074748eb88b7d1ee6dbf9494361ad17`,
`SpherePacking/ModularForms/JacobiTheta/Basic.lean` (Apache-2.0).
The other limits reuse the pinned TauCeti theta limit and the translation identity.
-/

@[expose] public noncomputable section

open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped UpperHalfPlane

namespace SphereCeti.ThetaConstants

private theorem norm_theta_half_term (n : ℤ) (τ : ℂ) :
    ‖jacobiTheta₂_term n (τ / 2) τ‖ =
      Real.exp (-Real.pi * ((n : ℝ) ^ 2 + n) * τ.im) := by
  rw [norm_jacobiTheta₂_term]
  congr 1
  norm_num [div_im]
  ring

private theorem int_sq_add_nonneg (n : ℤ) : 0 ≤ (n : ℝ) ^ 2 + n := by
  have h : 0 ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with hn | hn
    · exact mul_nonneg hn (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos hn.le (by omega)
  exact_mod_cast (show 0 ≤ n ^ 2 + n by nlinarith)

private theorem theta_half_term (n : ℤ) (τ : ℂ) :
    jacobiTheta₂_term n (τ / 2) τ = cexp (Real.pi * I * ((n : ℂ) ^ 2 + n) * τ) := by
  rw [jacobiTheta₂_term]
  congr 1
  ring

/-- The two surviving terms at the infinite cusp are indexed by `-1` and `0`. -/
theorem tendsto_theta_half :
    Tendsto (fun τ : ℍ => jacobiTheta₂ (τ / 2) τ) atImInfty (𝓝 2) := by
  have hs : Summable (fun n : ℤ => ‖jacobiTheta₂_term n (I / 2) I‖) :=
    ((summable_jacobiTheta₂_term_iff (I / 2) I).2 (by simp)).norm
  have hlim (n : ℤ) : Tendsto (fun τ : ℍ => jacobiTheta₂_term n (τ / 2) τ)
      atImInfty (𝓝 (if n = -1 ∨ n = 0 then (1 : ℂ) else 0)) := by
    by_cases hn : n = -1 ∨ n = 0
    · rcases hn with rfl | rfl <;> simp [theta_half_term]
    · simp only [hn, ↓reduceIte]
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp_rw [norm_theta_half_term]
      have hpos : 0 < (n : ℝ) ^ 2 + n := by
        have hi : 0 < n * (n + 1) := by
          rcases lt_or_ge 0 n with h | h
          · exact mul_pos h (by omega)
          · exact mul_pos_of_neg_of_neg (by omega) (by omega)
        exact_mod_cast (show 0 < n ^ 2 + n by nlinarith)
      exact Real.tendsto_exp_atBot.comp
        (tendsto_comap.const_mul_atTop_of_neg (mul_neg_of_neg_of_pos (neg_lt_zero.mpr Real.pi_pos) hpos))
  have hbound : ∀ᶠ τ : ℍ in atImInfty, ∀ n : ℤ,
      ‖jacobiTheta₂_term n (τ / 2) τ‖ ≤ ‖jacobiTheta₂_term n (I / 2) I‖ := by
    filter_upwards [show ∀ᶠ τ : ℍ in atImInfty, 1 ≤ τ.im from
      preimage_mem_comap (Ici_mem_atTop 1)] with τ hτ n
    rw [norm_theta_half_term, norm_theta_half_term]
    simp only [Complex.I_im]
    apply Real.exp_le_exp.mpr
    simpa using mul_le_mul_of_nonpos_left hτ
      (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (int_sq_add_nonneg n)))
  have h := tendsto_tsum_of_dominated_convergence hs hlim hbound
  have he : (∑' n : ℤ, if n = -1 ∨ n = 0 then (1 : ℂ) else 0) = 2 := by
    rw [tsum_eq_sum (s := {-1, 0}) (fun n hn => by simpa using hn)]
    norm_num [Finset.sum_insert, Finset.sum_singleton, Finset.filter_insert,
      Finset.filter_singleton]
  rw [he] at h
  exact h

/-- The leading coefficient of `H2` with respect to `exp(π i τ)` is `16`. -/
theorem tendsto_H2_div_exp :
    Tendsto (fun τ : ℍ => H2 τ / cexp (Real.pi * I * τ)) atImInfty (𝓝 16) := by
  have he (τ : ℍ) : H2 τ / cexp (Real.pi * I * τ) =
      jacobiTheta₂ (τ / 2) τ ^ 4 := by
    rw [H2, mul_pow, ← Complex.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (4 : ℂ) * (Real.pi * I * τ / 4) = Real.pi * I * τ by ring]
    exact mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)
  simp_rw [he]
  convert tendsto_theta_half.pow 4 using 1
  norm_num

/-- `H2` vanishes at the infinite cusp. -/
theorem tendsto_H2 : Tendsto H2 atImInfty (𝓝 0) := by
  have he : Tendsto (fun τ : ℍ => cexp (Real.pi * I * τ / 4)) atImInfty (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn (τ : ℍ) : ‖cexp (Real.pi * I * τ / 4)‖ =
        Real.exp ((-Real.pi / 4) * τ.im) := by
      rw [Complex.norm_exp]
      congr 1
      simp
      ring
    simp_rw [hn]
    exact Real.tendsto_exp_atBot.comp
      (tendsto_comap.const_mul_atTop_of_neg (by linarith [Real.pi_pos]))
  change Tendsto (fun τ : ℍ => (cexp (Real.pi * I * τ / 4) * jacobiTheta₂ (τ / 2) τ) ^ 4) _ _
  simpa using (he.mul tendsto_theta_half).pow 4

/-- `H3` has constant term one. -/
theorem tendsto_H3 : Tendsto H3 atImInfty (𝓝 1) := by
  change Tendsto (fun τ : ℍ => jacobiTheta τ ^ 4) _ _
  simpa using
    (TauCeti.tendsto_jacobiTheta_comap_im_atTop.comp tendsto_coe_atImInfty).pow 4

/-- `H4` has constant term one. -/
theorem tendsto_H4 : Tendsto H4 atImInfty (𝓝 1) := by
  have ht : Tendsto (fun τ : ℍ => (1 : ℝ) +ᵥ τ) atImInfty atImInfty := by
    simpa [atImInfty, tendsto_comap_iff, Function.comp_def] using
      (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop)
  simpa only [Function.comp_def, H3_T] using tendsto_H3.comp ht

end SphereCeti.ThetaConstants
