/-
Copyright (c) 2026 Sphere-Packing-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere-Packing-Lean contributors, Bakhyt Momunov
-/

module

public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.Basic
public import Mathlib.Analysis.Complex.Order

import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.Analysis.SpecialFunctions.Gaussian.LatticeSum

/-!
# Positivity of the theta constants on the imaginary axis

All three classical thetanullwerte and their fourth powers are positive real numbers on
the positive imaginary axis. In particular, their values there are nonzero.

The termwise positivity arguments are adapted from
`thefundamentaltheor3m/Sphere-Packing-Lean@bad3de916074748eb88b7d1ee6dbf9494361ad17`,
`SpherePacking/ModularForms/JacobiTheta/Basic.lean` (Apache-2.0).
For the alternating theta constant, the pinned TauCeti positivity theorem for
`jacobiTheta (1 + I*t)` is reused.
-/

public section

open Complex
open scoped UpperHalfPlane ComplexOrder

namespace TauCeti.ModularForm

private theorem shifted_gaussian_pos (s t : ℝ) (ht : 0 < t) :
    0 < ∑' n : ℤ, cexp (Real.pi * I * (n + (s : ℂ)) ^ 2 * (I * t)) := by
  have hs : Summable (fun n : ℤ => Real.exp (-Real.pi * ((n : ℝ) + s) ^ 2 * t)) := by
    convert Real.summable_abs_pow_mul_exp_neg_sub_sq_div 0 (-s)
      (one_div_pos.mpr (mul_pos Real.pi_pos ht)) using 1
    ext n
    simp only [pow_zero, one_mul, sub_neg_eq_add]
    congr 1
    field_simp
  have he (n : ℤ) : cexp (Real.pi * I * (n + (s : ℂ)) ^ 2 * (I * t)) =
      (Real.exp (-Real.pi * ((n : ℝ) + s) ^ 2 * t) : ℝ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  simp_rw [he]
  rw [← ofReal_tsum, zero_lt_real]
  exact hs.tsum_pos (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _)

private theorem coe_eq_I_mul_im (τ : ℍ) (hτ : τ.re = 0) : (τ : ℂ) = I * τ.im := by
  apply Complex.ext <;> simp [hτ]

/-- `Θ₂` is a positive real number on the positive imaginary axis. -/
theorem Θ₂_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < Θ₂ τ := by
  rw [Θ₂_eq_tsum]
  simp_rw [coe_eq_I_mul_im τ hτ]
  simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using
    shifted_gaussian_pos (1 / 2) τ.im τ.2

/-- `Θ₃` is a positive real number on the positive imaginary axis. -/
theorem Θ₃_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < Θ₃ τ := by
  rw [Θ₃_eq_tsum]
  simp_rw [coe_eq_I_mul_im τ hτ]
  simpa using shifted_gaussian_pos 0 τ.im τ.2

/-- `Θ₄` is positive on the positive imaginary axis, despite its alternating series. -/
theorem Θ₄_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < Θ₄ τ := by
  rw [← Θ₃_one_vadd, Θ₃_def, UpperHalfPlane.coe_vadd, ofReal_one,
    coe_eq_I_mul_im τ hτ]
  exact TauCeti.jacobiTheta_one_add_I_mul_pos τ.2

/-- `H₂` is a positive real number on the positive imaginary axis. -/
theorem H₂_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < H₂ τ := by
  rw [H₂_def]
  exact pow_pos (Θ₂_pos_of_re_eq_zero τ hτ) 4

/-- `H₃` is a positive real number on the positive imaginary axis. -/
theorem H₃_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < H₃ τ := by
  rw [H₃_def]
  exact pow_pos (Θ₃_pos_of_re_eq_zero τ hτ) 4

/-- `H₄` is a positive real number on the positive imaginary axis. -/
theorem H₄_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < H₄ τ := by
  rw [H₄_def]
  exact pow_pos (Θ₄_pos_of_re_eq_zero τ hτ) 4

-- The rational theta expressions used in the minus kernels have nonzero denominators here.
example (τ : ℍ) (hτ : τ.re = 0) : H₂ τ ^ 2 * H₃ τ ^ 2 * H₄ τ ^ 2 ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (H₂_pos_of_re_eq_zero τ hτ).ne')
    (pow_ne_zero 2 (H₃_pos_of_re_eq_zero τ hτ).ne'))
    (pow_ne_zero 2 (H₄_pos_of_re_eq_zero τ hτ).ne')

end TauCeti.ModularForm
