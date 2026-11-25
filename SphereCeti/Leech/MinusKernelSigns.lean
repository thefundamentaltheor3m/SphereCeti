/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Leech.MinusKernels
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.Discriminant
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.ImaginaryAxis
public import Mathlib.Analysis.Complex.Order

import Mathlib.Analysis.Complex.Basic

/-!
# Strict imaginary-axis signs of the Leech minus modular functions

On the positive imaginary axis `ψ_I` and `ψ_T` are strictly positive real numbers,
whereas `ψ_S` is strictly negative. The discriminant is positive by its theta-product formula.
For `ψ_T`, the quadratic numerator becomes `7 (H₂ - H₃/2)² + H₃²/4`.

The proofs are independent algebraic factorizations of the existing explicit formulas.
-/

public section

open Complex TauCeti.ModularForm
open scoped UpperHalfPlane ComplexOrder

namespace SphereCeti.Leech

private theorem positive_div {a b : ℂ} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]
  exact mul_pos ha (RCLike.inv_pos_of_pos hb)

private theorem discriminant_pos (τ : ℍ) (hτ : τ.re = 0) :
    0 < _root_.ModularForm.discriminant τ := by
  rw [discriminant_eq_theta_product]
  apply positive_div
  · exact pow_pos (mul_pos (mul_pos (H₂_pos_of_re_eq_zero τ hτ)
      (H₃_pos_of_re_eq_zero τ hτ)) (H₄_pos_of_re_eq_zero τ hτ)) 2
  · norm_num [Complex.lt_def]

/-- The Leech function `ψ_I` is strictly positive and real on the positive imaginary axis. -/
theorem psiI_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < psiI τ := by
  have ha := H₂_pos_of_re_eq_zero τ hτ
  have hb := H₄_pos_of_re_eq_zero τ hτ
  have hd := discriminant_pos τ hτ
  rw [psiI_def]
  simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply,
    smul_eq_mul, CuspForm.coe_discriminant]
  apply positive_div
  · positivity
  · exact pow_pos hd 2

/-- The Leech function `ψ_S` is strictly negative and real on the positive imaginary axis. -/
theorem psiS_neg_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : psiS τ < 0 := by
  have ha := H₂_pos_of_re_eq_zero τ hτ
  have hb := H₄_pos_of_re_eq_zero τ hτ
  have hd := discriminant_pos τ hτ
  rw [psiS_eq]
  simp only [Pi.neg_apply, Pi.div_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply,
    Pi.pow_apply, smul_eq_mul, CuspForm.coe_discriminant]
  apply neg_lt_zero.mpr
  apply positive_div
  · positivity
  · exact pow_pos hd 2

private theorem psiT_factor (τ : ℍ) :
    psiT τ = H₃ τ ^ 5 * (7 * (H₂ τ - H₃ τ / 2) ^ 2 + H₃ τ ^ 2 / 4) /
      _root_.ModularForm.discriminant τ ^ 2 := by
  rw [psiT_eq]
  simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
    Pi.pow_apply, smul_eq_mul, CuspForm.coe_discriminant]
  ring

/-- Completing the square proves `ψ_T` is strictly positive and real on the imaginary axis. -/
theorem psiT_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < psiT τ := by
  have ha := H₂_pos_of_re_eq_zero τ hτ
  have hc := H₃_pos_of_re_eq_zero τ hτ
  have hd := discriminant_pos τ hτ
  have hia : (H₂ τ).im = 0 := (Complex.pos_iff.mp ha).2.symm
  have hic : (H₃ τ).im = 0 := (Complex.pos_iff.mp hc).2.symm
  have hs : (0 : ℂ) ≤ (H₂ τ - H₃ τ / 2) ^ 2 :=
    Complex.sq_nonneg_iff.mpr (by simp [hia, hic])
  rw [psiT_factor]
  apply positive_div
  · apply mul_pos (pow_pos hc 5)
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (by norm_num [Complex.le_def]) hs)
      (positive_div (pow_pos hc 2) (by norm_num [Complex.lt_def]))
  · exact pow_pos hd 2

-- The corrected factor `−2 ψ_S` makes the ray kernel strictly positive on the imaginary axis.
example (τ : ℍ) (hτ : τ.re = 0) : 0 < minusKernelRay τ := by
  rw [minusKernelRay_def, psiSExt_of_im_pos τ.2]
  have h := psiS_neg_of_re_eq_zero τ hτ
  have he : (-2 : ℂ) * psiS τ = 2 * (-psiS τ) := by ring
  rw [he]
  exact mul_pos (by norm_num [Complex.lt_def]) (neg_pos.mpr h)

end SphereCeti.Leech
