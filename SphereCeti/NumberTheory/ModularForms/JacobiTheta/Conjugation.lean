/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Complex conjugation of the Jacobi theta functions

Conjugation reflects the upper half-plane by `τ ↦ -conj τ`. The two-variable theta
function also reflects its first argument. These identities express the real Fourier
coefficients and support reality arguments for theta-based contour kernels.

The proofs use Mathlib's theta series and conjugation of infinite sums directly.
-/

public section

open Complex
open scoped ComplexConjugate

namespace TauCeti

/-- Conjugation of the two-variable Jacobi theta function. The identity also holds for
the totalized sums outside the upper half-plane. -/
theorem jacobiTheta₂_neg_conj (z τ : ℂ) :
    jacobiTheta₂ (-conj z) (-conj τ) = conj (jacobiTheta₂ z τ) := by
  rw [jacobiTheta₂, jacobiTheta₂, Complex.conj_tsum]
  apply tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_conj]
  congr 1
  simp only [map_add, map_mul, map_pow, map_intCast, map_ofNat, conj_I, conj_ofReal]
  ring

/-- Reflection of the second argument conjugates theta when the first argument is real. -/
theorem jacobiTheta₂_neg_conj_ofReal (z : ℝ) (τ : ℂ) :
    jacobiTheta₂ z (-conj τ) = conj (jacobiTheta₂ z τ) := by
  simpa only [conj_ofReal, jacobiTheta₂_neg_left] using jacobiTheta₂_neg_conj (z : ℂ) τ

/-- The one-variable Jacobi theta function has real Fourier coefficients. -/
theorem jacobiTheta_neg_conj (τ : ℂ) :
    jacobiTheta (-conj τ) = conj (jacobiTheta τ) := by
  rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta_eq_jacobiTheta₂]
  simpa only [map_zero, neg_zero] using jacobiTheta₂_neg_conj 0 τ

/-- In particular, a real first argument and a purely imaginary modulus give a real value. -/
theorem jacobiTheta₂_im_eq_zero (z t : ℝ) : (jacobiTheta₂ z (I * t)).im = 0 := by
  have h := jacobiTheta₂_neg_conj_ofReal z (I * t)
  simp only [map_mul, conj_I, conj_ofReal, neg_mul, neg_neg] at h
  exact Complex.conj_eq_iff_im.mp h.symm

-- The alternating theta series on the imaginary axis is covered at z = 1/2.
example (t : ℝ) : (jacobiTheta₂ (1 / 2) (I * t)).im = 0 := by
  simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using jacobiTheta₂_im_eq_zero (1 / 2) t

end TauCeti
