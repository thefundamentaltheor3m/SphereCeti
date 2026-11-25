/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.E8.MinusKernelHolomorphic
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.ImaginaryAxis
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.JacobiIdentity
public import Mathlib.Analysis.Complex.Order

import Mathlib.Analysis.Complex.Basic

/-!
# Strict imaginary-axis signs of the E8 minus modular functions

On the positive imaginary axis `ψ_I` and `ψ_T` are positive real numbers, whereas `ψ_S`
is negative. Jacobi's identity factors the non-manifest numerators as positive polynomials
in `H₂` and `H₄`. These statements retain strict signs, so the corresponding factors do not vanish.

The proofs are independent algebraic factorizations of the existing explicit formulas.
-/

public section

open Complex TauCeti.ModularForm
open scoped UpperHalfPlane ComplexOrder

namespace SphereCeti.E8

private theorem positive_div {a b : ℂ} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]
  exact mul_pos ha (RCLike.inv_pos_of_pos hb)

private theorem psiI_factor (τ : ℍ) :
    psiI τ = 128 * H₄ τ * (5 * H₂ τ ^ 2 + 5 * H₂ τ * H₄ τ + 2 * H₄ τ ^ 2) /
      (H₂ τ ^ 2 * H₃ τ ^ 2) := by
  rw [psiI_eq]
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, smul_eq_mul]
  have h2 := (theta_constants_ne_zero τ).1
  have h3 := (theta_constants_ne_zero τ).2.1
  field_simp
  have hj := congrFun jacobi_identity τ
  simp only [Pi.add_apply] at hj
  rw [← hj]
  ring

private theorem psiS_factor (τ : ℍ) :
    psiS τ = -(128 * H₂ τ * (2 * H₂ τ ^ 2 + 5 * H₂ τ * H₄ τ + 5 * H₄ τ ^ 2) /
      (H₃ τ ^ 2 * H₄ τ ^ 2)) := by
  rw [psiS_eq]
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, smul_eq_mul]
  have h3 := (theta_constants_ne_zero τ).2.1
  have h4 := (theta_constants_ne_zero τ).2.2
  field_simp
  have hj := congrFun jacobi_identity τ
  simp only [Pi.add_apply] at hj
  rw [← hj]
  ring

/-- `ψ_I` is strictly positive and real on the positive imaginary axis. -/
theorem psiI_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < psiI τ := by
  have ha := H₂_pos_of_re_eq_zero τ hτ
  have hb := H₄_pos_of_re_eq_zero τ hτ
  have hc := H₃_pos_of_re_eq_zero τ hτ
  rw [psiI_factor]
  apply positive_div
  · positivity
  · exact mul_pos (pow_pos ha 2) (pow_pos hc 2)

/-- `ψ_S` is strictly negative and real on the positive imaginary axis. -/
theorem psiS_neg_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : psiS τ < 0 := by
  have ha := H₂_pos_of_re_eq_zero τ hτ
  have hb := H₄_pos_of_re_eq_zero τ hτ
  have hc := H₃_pos_of_re_eq_zero τ hτ
  rw [psiS_factor]
  apply neg_lt_zero.mpr
  apply positive_div
  · positivity
  · exact mul_pos (pow_pos hc 2) (pow_pos hb 2)

/-- `ψ_T` is strictly positive and real on the positive imaginary axis. -/
theorem psiT_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < psiT τ := by
  have ha := H₂_pos_of_re_eq_zero τ hτ
  have hb := H₄_pos_of_re_eq_zero τ hτ
  have hc := H₃_pos_of_re_eq_zero τ hτ
  rw [psiT_eq]
  simp only [Pi.smul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, smul_eq_mul]
  apply mul_pos (by norm_num [Complex.lt_def] : (0 : ℂ) < 128)
  exact add_pos (positive_div (add_pos hc hb) (pow_pos ha 2))
    (positive_div (add_pos ha hc) (pow_pos hb 2))

-- The corrected factor `−2 ψ_S` gives a strictly positive ray kernel on the imaginary axis.
example (τ : ℍ) (hτ : τ.re = 0) : 0 < minusKernelRay τ := by
  rw [minusKernelRay_def, psiSExt_of_im_pos τ.2]
  have h := psiS_neg_of_re_eq_zero τ hτ
  have he : (-2 : ℂ) * psiS τ = 2 * (-psiS τ) := by ring
  rw [he]
  exact mul_pos (by norm_num [Complex.lt_def]) (neg_pos.mpr h)

end SphereCeti.E8
