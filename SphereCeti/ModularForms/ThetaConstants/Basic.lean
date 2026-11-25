/-
Copyright (c) 2026 Sphere-Packing-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere-Packing-Lean contributors, Bakhyt Momunov
-/

module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Fourth powers of the classical theta constants

The functions `H2`, `H3`, and `H4` are the fourth powers of the classical theta constants
`θ₂`, `θ₃`, and `θ₄` on the upper half-plane. They are expressed using Mathlib's Jacobi theta
functions. Translation by one permutes `H3` and `H4` and negates `H2`; inversion exchanges
`H2` and `H4` and preserves `H3`, with the common weight-two factor `-τ²`.

## Source

Adapted from `thefundamentaltheor3m/Sphere-Packing-Lean` at commit
`bad3de916074748eb88b7d1ee6dbf9494361ad17`, files
`SpherePacking/ModularForms/JacobiTheta/Defs.lean` and
`SpherePacking/ModularForms/JacobiTheta/Basic.lean` (Apache-2.0).
The source definitions of the separate theta summands are replaced by direct use of Mathlib's
`jacobiTheta` and `jacobiTheta₂`; the transformation formulas use the same normalizations.
-/

@[expose] public noncomputable section

open Complex
open UpperHalfPlane hiding I
open scoped Real UpperHalfPlane

namespace SphereCeti.ThetaConstants

/-- The fourth power of the classical theta constant `θ₂`. -/
def H2 (τ : ℍ) : ℂ := (cexp (Real.pi * I * τ / 4) * jacobiTheta₂ (τ / 2) τ) ^ 4

/-- The fourth power of the classical theta constant `θ₃`. -/
def H3 (τ : ℍ) : ℂ := jacobiTheta τ ^ 4

/-- The fourth power of the classical theta constant `θ₄`. -/
def H4 (τ : ℍ) : ℂ := jacobiTheta₂ (1 / 2 : ℂ) τ ^ 4

/-- The shifted Gaussian-series expression for the fourth power of `θ₂`. -/
theorem H2_eq_tsum (τ : ℍ) :
    H2 τ = (∑' n : ℤ, cexp (Real.pi * I * (n + 1 / 2 : ℂ) ^ 2 * τ)) ^ 4 := by
  unfold H2
  congr 1
  rw [jacobiTheta₂, ← tsum_mul_left]
  apply tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  ring

/-- Translation by one negates `H2`. -/
theorem H2_T (τ : ℍ) : H2 ((1 : ℝ) +ᵥ τ) = -H2 τ := by
  suffices htheta :
      (∑' n : ℤ, cexp (Real.pi * I * (n + 1 / 2 : ℂ) ^ 2 * ((1 : ℝ) +ᵥ τ))) =
        cexp (Real.pi * I / 4) *
          ∑' n : ℤ, cexp (Real.pi * I * (n + 1 / 2 : ℂ) ^ 2 * τ) by
    rw [H2_eq_tsum, htheta, mul_pow, ← Complex.exp_nat_mul]
    norm_num
    rw [show (4 : ℂ) * (Real.pi * I / 4) = Real.pi * I by ring,
      Complex.exp_pi_mul_I, neg_one_mul, H2_eq_tsum]
  calc
    _ = ∑' n : ℤ, cexp (Real.pi * I / 4) *
        cexp (Real.pi * I * (n ^ 2 + n) +
          Real.pi * I * (n + 1 / 2 : ℂ) ^ 2 * τ) := by
      apply tsum_congr fun n => ?_
      rw [coe_vadd, Complex.ofReal_one, ← Complex.exp_add]
      congr 1
      ring
    _ = cexp (Real.pi * I / 4) * ∑' n : ℤ,
        cexp (Real.pi * I * (n ^ 2 + n) +
          Real.pi * I * (n + 1 / 2 : ℂ) ^ 2 * τ) := tsum_mul_left
    _ = _ := by
      congr 1
      apply tsum_congr fun n => ?_
      have hn : Even (n ^ 2 + n) := by
        convert Int.even_mul_succ_self n using 1
        ring
      rw [Complex.exp_add]
      have hphase : cexp (Real.pi * I * (n ^ 2 + n : ℂ)) = 1 := by
        rw [mul_comm (Real.pi * I), ← Int.cast_pow, ← Int.cast_add,
          Complex.exp_int_mul, Complex.exp_pi_mul_I, hn.neg_one_zpow]
      rw [hphase, one_mul]

/-- Translation by one sends `H3` to `H4`. -/
theorem H3_T (τ : ℍ) : H3 ((1 : ℝ) +ᵥ τ) = H4 τ := by
  unfold H3 H4
  rw [jacobiTheta_eq_jacobiTheta₂]
  congr 1
  rw [jacobiTheta₂, jacobiTheta₂]
  apply tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, jacobiTheta₂_term, coe_vadd, Complex.ofReal_one]
  rw [show (2 : ℂ) * Real.pi * I * n * (1 / 2) = Real.pi * I * n by ring]
  simp only [mul_zero, zero_add, mul_add, mul_one]
  rw [Complex.exp_add, Complex.exp_add]
  congr 1
  rw [← Int.cast_pow, mul_comm (Real.pi * I), Complex.exp_int_mul,
    Complex.exp_pi_mul_I, mul_comm (Real.pi * I), Complex.exp_int_mul,
    Complex.exp_pi_mul_I]
  rcases Int.even_or_odd n with hn | hn
  · rw [hn.neg_one_zpow, Even.neg_one_zpow]
    simp [sq, hn]
  · rw [hn.neg_one_zpow, Odd.neg_one_zpow]
    simp [sq, hn]

/-- Translation by one sends `H4` to `H3`. -/
theorem H4_T (τ : ℍ) : H4 ((1 : ℝ) +ᵥ τ) = H3 τ := by
  rw [← H3_T, H3, H3]
  congr 1
  simp only [coe_vadd, Complex.ofReal_one]
  rw [show (1 : ℂ) + (1 + τ) = 2 + τ by ring, jacobiTheta_two_add]

private theorem coe_S (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
  rw [modular_S_smul]
  change (-(τ : ℂ))⁻¹ = -1 / (τ : ℂ)
  rw [inv_neg, neg_div, one_div]

/-- Inversion sends `H2` to `H4` with weight-two factor `-τ²`. -/
theorem H2_S (τ : ℍ) : H2 (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * H4 τ := by
  have hτ : (τ : ℂ) ≠ 0 := ne_zero τ
  have htheta : jacobiTheta₂ (-1 / (2 * (τ : ℂ))) (-1 / τ) =
      1 / (I / τ) ^ (1 / 2 : ℂ) * cexp (Real.pi * I / (4 * τ)) *
        jacobiTheta₂ (1 / 2) τ := by
    rw [jacobiTheta₂_functional_equation]
    have hb : -I * (-1 / (τ : ℂ)) = I / τ := by ring
    have he : -Real.pi * I * (-1 / (2 * (τ : ℂ))) ^ 2 / (-1 / τ) =
        Real.pi * I / (4 * τ) := by field_simp [hτ]; ring
    have hz : (-1 / (2 * (τ : ℂ))) / (-1 / τ) = (1 / 2 : ℂ) := by
      field_simp [hτ]
    have ht : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
    rw [hb, he, hz, ht]
  have hroot : (1 / (I / (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 = -(τ : ℂ) ^ 2 := by
    rw [div_pow, one_pow, ← cpow_mul_nat]
    norm_num
    simp [div_pow]
    ring
  calc
    H2 (ModularGroup.S • τ) = cexp (-Real.pi * I / τ) *
        jacobiTheta₂ (-1 / (2 * (τ : ℂ))) (-1 / τ) ^ 4 := by
      rw [H2, coe_S, mul_pow, ← Complex.exp_nat_mul]
      congr 2 <;> field_simp
      ring
    _ = cexp (-Real.pi * I / τ) *
        ((1 / (I / (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 4 *
          cexp (Real.pi * I / (4 * τ)) ^ 4 * jacobiTheta₂ (1 / 2) τ ^ 4) := by
      rw [htheta]
      simp only [mul_pow]
    _ = cexp (-Real.pi * I / τ) *
        (-(τ : ℂ) ^ 2 * cexp (Real.pi * I / τ) * H4 τ) := by
      rw [hroot, ← Complex.exp_nat_mul, H4]
      congr 4
      ring
    _ = -(τ : ℂ) ^ 2 * H4 τ := by
      rw [show cexp (-Real.pi * I / τ) *
          (-(τ : ℂ) ^ 2 * cexp (Real.pi * I / τ) * H4 τ) =
          -(τ : ℂ) ^ 2 * (cexp (-Real.pi * I / τ) * cexp (Real.pi * I / τ)) * H4 τ by ring,
        ← Complex.exp_add]
      rw [show -Real.pi * I / (τ : ℂ) + Real.pi * I / τ = 0 by ring,
        Complex.exp_zero]
      ring

/-- Inversion preserves `H3` with weight-two factor `-τ²`. -/
theorem H3_S (τ : ℍ) : H3 (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * H3 τ := by
  rw [H3, jacobiTheta_S_smul, mul_pow, ← cpow_mul_nat]
  norm_num
  simp only [H3, mul_pow, I_sq]
  ring

/-- Inversion sends `H4` to `H2` with weight-two factor `-τ²`. -/
theorem H4_S (τ : ℍ) : H4 (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * H2 τ := by
  have h := H2_S (ModularGroup.S • τ)
  have hSS : ModularGroup.S • (ModularGroup.S • τ) = τ := by
    apply UpperHalfPlane.ext
    simp only [coe_S]
    field_simp
  rw [hSS, coe_S] at h
  field_simp [ne_zero τ] at h
  linear_combination h

end SphereCeti.ThetaConstants
