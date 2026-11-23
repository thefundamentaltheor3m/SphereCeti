/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Integrability of parameterized Gaussian kernels

Let `E` be a real inner product space of dimension `n`.  For a measurable family of Gaussians
`x ↦ exp(-π ‖x‖² y(t))` with `y(t) > 0`, weighted by `φ(t)`, the function
`(x, t) ↦ φ(t) exp(-π ‖x‖² y(t))` is integrable on `E × s` exactly when
`t ↦ φ(t) y(t)^(-n/2)` is integrable on `s`: the integral of `exp(-π ‖x‖² y)` over `E` is
`y^(-n/2)`.

The Fourier transforms of the magic-function contour components exchange a Fourier integral over
`E` with an integral along a contour, and their integrability hypotheses are of this product
form, with `φ(t) = ‖g(z(t))‖` and `y(t) = Im z(t)` for a kernel `g` and a parametrized contour
`z`.  This reduces them to a one-variable integrability condition on the kernel.  The result is
general analysis, stated in the form intended for Mathlib's Gaussian integrals (`UPSTREAM.md`,
item A19).

## Main statements

* `SphereCeti.integral_rexp_neg_pi_mul_sq_norm_mul`: `∫ x, exp(-π ‖x‖² y) = y^(-n/2)` for
  `y > 0`.
* `SphereCeti.integrable_mul_rexp_neg_pi_mul_sq_norm_prod_iff`: the integrability criterion.
-/

public section

open MeasureTheory Set
open scoped Real

namespace SphereCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- For `y > 0`, the Gaussian `x ↦ exp(-π ‖x‖² y)` is integrable on `E`. -/
theorem integrable_rexp_neg_pi_mul_sq_norm_mul {y : ℝ} (hy : 0 < y) :
    Integrable fun x : E ↦ Real.exp (-π * ‖x‖ ^ 2 * y) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E)
    (b := (π * y : ℂ)) (by simpa using mul_pos Real.pi_pos hy) 0 0).norm
  refine h.congr (ae_of_all _ fun x ↦ ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp only [neg_mul, Complex.neg_re, ← Complex.ofReal_mul, ← Complex.ofReal_pow,
    Complex.ofReal_re]
  ring

/-- For `y > 0`, the Gaussian `x ↦ exp(-π ‖x‖² y)` on a real inner product space of dimension
`n` has integral `y^(-n/2)`. -/
theorem integral_rexp_neg_pi_mul_sq_norm_mul {y : ℝ} (hy : 0 < y) :
    ∫ x : E, Real.exp (-π * ‖x‖ ^ 2 * y) = y ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (mul_pos Real.pi_pos hy)
  rw [div_mul_cancel_left₀ Real.pi_pos.ne', ← Real.rpow_neg_one, ← Real.rpow_mul hy.le,
    show (-1 : ℝ) * ((Module.finrank ℝ E : ℝ) / 2) = -(Module.finrank ℝ E : ℝ) / 2 by ring] at h
  rw [← h]
  congr 1 with x
  ring_nf

/-- **Integrability of a parameterized Gaussian kernel.**  Let `E` be a real inner product space
of dimension `n`, let `s` be a measurable set of parameters, and let `y` be measurable and
positive on `s`.  For `φ` almost everywhere strongly measurable on `s`, the function
`(x, t) ↦ φ(t) exp(-π ‖x‖² y(t))` is integrable on `E × s` exactly when
`t ↦ φ(t) y(t)^(-n/2)` is integrable on `s`. -/
theorem integrable_mul_rexp_neg_pi_mul_sq_norm_prod_iff {s : Set ℝ} (hs : MeasurableSet s)
    {φ y : ℝ → ℝ} (hφ : AEStronglyMeasurable φ (volume.restrict s)) (hy : Measurable y)
    (hy0 : ∀ t ∈ s, 0 < y t) :
    Integrable (fun q : E × ℝ ↦ φ q.2 * Real.exp (-π * ‖q.1‖ ^ 2 * y q.2))
        (volume.prod (volume.restrict s)) ↔
      IntegrableOn (fun t ↦ φ t * y t ^ (-(Module.finrank ℝ E : ℝ) / 2)) s := by
  have hmeas : AEStronglyMeasurable (fun q : E × ℝ ↦ φ q.2 * Real.exp (-π * ‖q.1‖ ^ 2 * y q.2))
      (volume.prod (volume.restrict s)) :=
    hφ.comp_snd.mul (by fun_prop : Measurable fun q : E × ℝ ↦
      Real.exp (-π * ‖q.1‖ ^ 2 * y q.2)).aestronglyMeasurable
  have hae : ∀ᵐ t ∂(volume.restrict s), t ∈ s := ae_restrict_mem hs
  rw [integrable_prod_iff' hmeas]
  -- The slices are integrable Gaussians, of total mass `|φ t| * y t ^ (-n / 2)`.
  have hslice : ∀ᵐ t ∂(volume.restrict s),
      Integrable (fun x : E ↦ φ t * Real.exp (-π * ‖x‖ ^ 2 * y t)) :=
    hae.mono fun t ht ↦ (integrable_rexp_neg_pi_mul_sq_norm_mul (hy0 t ht)).const_mul _
  have hnorm : (fun t ↦ ∫ x : E, ‖φ t * Real.exp (-π * ‖x‖ ^ 2 * y t)‖) =ᵐ[volume.restrict s]
      fun t ↦ ‖φ t * y t ^ (-(Module.finrank ℝ E : ℝ) / 2)‖ := by
    filter_upwards [hae] with t ht
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.rpow_pos_of_pos (hy0 t ht) _)]
    rw [integral_const_mul, integral_rexp_neg_pi_mul_sq_norm_mul (hy0 t ht)]
  have hφy : AEStronglyMeasurable (fun t ↦ φ t * y t ^ (-(Module.finrank ℝ E : ℝ) / 2))
      (volume.restrict s) :=
    hφ.mul (by fun_prop : Measurable fun t ↦
      y t ^ (-(Module.finrank ℝ E : ℝ) / 2)).aestronglyMeasurable
  rw [integrable_congr hnorm, integrable_norm_iff hφy, IntegrableOn]
  exact and_iff_right hslice

end SphereCeti
