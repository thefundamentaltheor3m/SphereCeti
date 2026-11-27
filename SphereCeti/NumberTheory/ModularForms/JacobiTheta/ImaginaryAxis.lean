/-
Copyright (c) 2026 Sphere-Packing-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere-Packing-Lean contributors, Bakhyt Momunov
-/

module

public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.Basic
public import Mathlib.Analysis.Complex.Order

import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable
import SphereCeti.Analysis.SpecialFunctions.Gaussian.LatticeSum

/-!
# Positivity of the theta constants on the imaginary axis

All three classical thetanullwerte and their fourth powers are positive real numbers on
the positive imaginary axis. In particular, their values there are nonzero.

The imaginary-axis theta series identities are adapted from
`thefundamentaltheor3m/Sphere-Packing-Lean@bad3de916074748eb88b7d1ee6dbf9494361ad17`,
`SpherePacking/ModularForms/JacobiTheta/Basic.lean` (Apache-2.0).
For the alternating theta constant, the pinned TauCeti positivity theorem for
`jacobiTheta (1 + I*t)` is reused.
-/

public section

open Complex
open scoped UpperHalfPlane ComplexOrder

namespace TauCeti.ModularForm

/-- `Θ₂` is a positive real number on the positive imaginary axis. -/
theorem Θ₂_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < Θ₂ τ := by
  rw [Θ₂_eq_tsum]
  rw [← UpperHalfPlane.re_add_im τ]
  simp only [hτ, ofReal_zero, zero_add]
  rw [mul_comm (τ.im : ℂ) I]
  simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using
    Complex.tsum_exp_shifted_gaussian_pos (1 / 2) τ.im τ.2

/-- `Θ₃` is a positive real number on the positive imaginary axis. -/
theorem Θ₃_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < Θ₃ τ := by
  rw [Θ₃_eq_tsum]
  rw [← UpperHalfPlane.re_add_im τ]
  simp only [hτ, ofReal_zero, zero_add]
  rw [mul_comm (τ.im : ℂ) I]
  simpa using Complex.tsum_exp_shifted_gaussian_pos 0 τ.im τ.2

/-- `Θ₄` is positive on the positive imaginary axis, despite its alternating series. -/
theorem Θ₄_pos_of_re_eq_zero (τ : ℍ) (hτ : τ.re = 0) : 0 < Θ₄ τ := by
  rw [← Θ₃_one_vadd, Θ₃_def, UpperHalfPlane.coe_vadd, ofReal_one,
    ← UpperHalfPlane.re_add_im τ]
  simpa only [hτ, ofReal_zero, zero_add, mul_comm (τ.im : ℂ) I, UpperHalfPlane.coe_im] using
    TauCeti.jacobiTheta_one_add_I_mul_pos τ.2

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
