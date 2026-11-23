/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Integrability of parameterized Gaussian kernels

Let `E` be a real inner product space of dimension `n`, and let `ν` be an s-finite measure on a
parameter space.  For a measurable family of Gaussians `x ↦ exp(-π ‖x‖² y(t))` with `y(t) > 0`
for almost every `t`, weighted by a measurable `φ(t)`, the function
`(x, t) ↦ φ(t) exp(-π ‖x‖² y(t))` is integrable for `volume.prod ν` exactly when
`t ↦ φ(t) y(t)^(-n/2)` is integrable for `ν`; the integral of `exp(-π ‖x‖² y)` over `E` is
`y^(-n/2)`.

The Fourier transforms of the magic-function contour components exchange a Fourier integral over
`E` with an integral along a contour, and their integrability hypotheses are of this product
form, with `φ(t) = ‖g(z(t))‖` and `y(t) = Im z(t)` for a kernel `g` and a parametrized contour
`z`.  This reduces them to a one-variable integrability condition on the kernel.

## Main statements

* `SphereCeti.integral_rexp_neg_pi_mul_sq_norm_mul`: `∫ x, exp(-π ‖x‖² y) = y^(-n/2)` for
  `y > 0`.
* `SphereCeti.integrable_mul_rexp_neg_pi_mul_sq_norm_prod_iff`: the integrability criterion, for
  an arbitrary s-finite parameter measure and almost everywhere hypotheses.
* `SphereCeti.integrable_mul_rexp_neg_pi_mul_sq_norm_prod_restrict_iff`: its form for a measurable
  set of real parameters.
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
  -- Mathlib's Gaussian integral at `b = π y` is `(π / (π y)) ^ (n / 2) = y ^ (-n / 2)`.
  have hpow : (π / (π * y)) ^ ((Module.finrank ℝ E : ℝ) / 2) =
      y ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
    rw [div_mul_cancel_left₀ Real.pi_pos.ne', Real.inv_rpow hy.le, ← Real.rpow_neg hy.le,
      neg_div]
  calc ∫ x : E, Real.exp (-π * ‖x‖ ^ 2 * y) = ∫ x : E, Real.exp (-(π * y) * ‖x‖ ^ 2) := by
        congr 1 with x
        ring_nf
    _ = y ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
        rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (mul_pos Real.pi_pos hy), hpow]

/-- **Integrability of a parameterized Gaussian kernel.**  Let `E` be a real inner product space
of dimension `n`, and let `ν` be an s-finite measure on a parameter space `α`.  For `φ` almost
everywhere strongly measurable and `y` almost everywhere measurable and almost everywhere
positive, the function `(x, t) ↦ φ(t) exp(-π ‖x‖² y(t))` is integrable on `E × α` exactly when
`t ↦ φ(t) y(t)^(-n/2)` is integrable. -/
theorem integrable_mul_rexp_neg_pi_mul_sq_norm_prod_iff {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [SFinite ν] {φ y : α → ℝ} (hφ : AEStronglyMeasurable φ ν)
    (hy : AEMeasurable y ν) (hy0 : ∀ᵐ t ∂ν, 0 < y t) :
    Integrable (fun q : E × α ↦ φ q.2 * Real.exp (-π * ‖q.1‖ ^ 2 * y q.2)) (volume.prod ν) ↔
      Integrable (fun t ↦ φ t * y t ^ (-(Module.finrank ℝ E : ℝ) / 2)) ν := by
  have hmeas : AEStronglyMeasurable (fun q : E × α ↦ φ q.2 * Real.exp (-π * ‖q.1‖ ^ 2 * y q.2))
      (volume.prod ν) := by
    have hy' : AEStronglyMeasurable (fun q : E × α ↦ y q.2) (volume.prod ν) :=
      hy.aestronglyMeasurable.comp_snd
    have hx : AEStronglyMeasurable (fun q : E × α ↦ -π * ‖q.1‖ ^ 2) (volume.prod ν) :=
      (by fun_prop : Continuous fun x : E ↦ -π * ‖x‖ ^ 2).aestronglyMeasurable.comp_fst
    exact hφ.comp_snd.mul (Real.continuous_exp.comp_aestronglyMeasurable (hx.mul hy'))
  rw [integrable_prod_iff' hmeas]
  -- The slices are integrable Gaussians, of total mass `|φ t| * y t ^ (-n / 2)`.
  have hslice : ∀ᵐ t ∂ν, Integrable (fun x : E ↦ φ t * Real.exp (-π * ‖x‖ ^ 2 * y t)) :=
    hy0.mono fun t ht ↦ (integrable_rexp_neg_pi_mul_sq_norm_mul ht).const_mul _
  have hnorm : (fun t ↦ ∫ x : E, ‖φ t * Real.exp (-π * ‖x‖ ^ 2 * y t)‖) =ᵐ[ν]
      fun t ↦ ‖φ t * y t ^ (-(Module.finrank ℝ E : ℝ) / 2)‖ := by
    filter_upwards [hy0] with t ht
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.rpow_pos_of_pos ht _)]
    rw [integral_const_mul, integral_rexp_neg_pi_mul_sq_norm_mul ht]
  have hφy : AEStronglyMeasurable (fun t ↦ φ t * y t ^ (-(Module.finrank ℝ E : ℝ) / 2)) ν :=
    hφ.mul (hy.pow_const _).aestronglyMeasurable
  rw [integrable_congr hnorm, integrable_norm_iff hφy]
  exact and_iff_right hslice

/-- The integrability criterion for a parameterized Gaussian kernel on a measurable set `s` of
real parameters, with `y` measurable and positive on `s`: `(x, t) ↦ φ(t) exp(-π ‖x‖² y(t))` is
integrable on `E × s` exactly when `t ↦ φ(t) y(t)^(-n/2)` is integrable on `s`. -/
theorem integrable_mul_rexp_neg_pi_mul_sq_norm_prod_restrict_iff {s : Set ℝ}
    (hs : MeasurableSet s) {φ y : ℝ → ℝ} (hφ : AEStronglyMeasurable φ (volume.restrict s))
    (hy : Measurable y) (hy0 : ∀ t ∈ s, 0 < y t) :
    Integrable (fun q : E × ℝ ↦ φ q.2 * Real.exp (-π * ‖q.1‖ ^ 2 * y q.2))
        (volume.prod (volume.restrict s)) ↔
      IntegrableOn (fun t ↦ φ t * y t ^ (-(Module.finrank ℝ E : ℝ) / 2)) s :=
  integrable_mul_rexp_neg_pi_mul_sq_norm_prod_iff hφ hy.aemeasurable
    ((ae_restrict_mem hs).mono hy0)

end SphereCeti
