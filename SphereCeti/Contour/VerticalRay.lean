/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability of Gaussian ray integrals

For a kernel `g : ℂ → ℂ`, the Gaussian ray integral is the function
`x ↦ ∫_{(1, ∞)} g(it) exp(πi ‖x‖² (it)) dt` on a finite-dimensional real inner product space `E`,
the integral of `g(z) exp(πi ‖x‖² z)` along the vertical ray from `i` to `i∞` up to the factor `i`.
On the ray `exp(πi ‖x‖² (it)) = exp(-π t ‖x‖²)`, a Gaussian in `x` of total mass `t^{-n/2} ≤ 1`
in dimension `n`.  So if `‖g(it)‖` is integrable on `(1, ∞)`, the Gaussian ray integral is
integrable on `E`.

## Main statements

* `SphereCeti.Contour.integrable_ray_gaussian_integral`: the Gaussian ray integral is integrable
  when `‖g(it)‖` is integrable on `(1, ∞)`.
-/

public section

open Complex MeasureTheory Set
open scoped Real RealInnerProductSpace

namespace SphereCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If `‖g(it)‖` is integrable on `(1, ∞)`, then the Gaussian ray integral
`x ↦ ∫_{(1, ∞)} g(it) exp(πi ‖x‖² (it)) dt` is integrable on `E`. -/
theorem integrable_ray_gaussian_integral {g : ℂ → ℂ}
    (hg : IntegrableOn (fun t : ℝ ↦ ‖g (t * I)‖) (Ioi 1)) :
    Integrable (fun x : E ↦
      ∫ t in Ioi (1 : ℝ), g (t * I) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (t * I))) := by
  by_cases hmeas : AEStronglyMeasurable (fun t : ℝ ↦ g (t * I)) (volume.restrict (Ioi 1))
  · -- On the ray the exponential factor is the real Gaussian `exp(-π t ‖x‖²)`.
    have hgauss (x : E) (t : ℝ) : cexp (π * I * (‖x‖ ^ 2 : ℝ) * (t * I)) =
        cexp (-(π * t : ℂ) * ‖x‖ ^ 2 + 0 * ⟪(0 : E), x⟫) := by
      congr 1
      push_cast
      ring_nf
      rw [I_sq]
      ring
    set f : E × ℝ → ℂ := fun q ↦ g (q.2 * I) * cexp (π * I * (‖q.1‖ ^ 2 : ℝ) * (q.2 * I))
    have hfmeas : AEStronglyMeasurable f (volume.prod (volume.restrict (Ioi (1 : ℝ)))) :=
      hmeas.comp_snd.mul (Continuous.aestronglyMeasurable (by fun_prop))
    refine Integrable.integral_prod_left (f := f) ?_
    rw [integrable_prod_iff' hfmeas]
    -- The Gaussian in `x` has total mass `(π / (π t))^{n/2} = t^{-n/2}`.
    have hslice (t : ℝ) (ht : 1 < t) : Integrable (fun x : E ↦ f (x, t)) := by
      have hb : 0 < ((π * t : ℂ)).re := by
        simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        positivity
      simp only [f, hgauss]
      exact (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : E)).const_mul _
    have hnorm (t : ℝ) (ht : 1 < t) : ∫ x : E, ‖f (x, t)‖ =
        ‖g (t * I)‖ * (π / (π * t)) ^ (Module.finrank ℝ E / 2 : ℝ) := by
      have hpt : 0 < π * t := by positivity
      rw [← GaussianFourier.integral_rexp_neg_mul_sq_norm hpt, ← integral_const_mul]
      congr 1 with x
      simp only [f, hgauss, norm_mul, zero_mul, add_zero]
      rw [← ofReal_mul, ← ofReal_pow, ← ofReal_neg, ← ofReal_mul, Complex.norm_exp_ofReal]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hslice t ht
    · refine hg.mono' hfmeas.norm.prod_swap.integral_prod_right' ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      have hpt : 0 < π * t := mul_pos Real.pi_pos ht0
      rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _), hnorm t ht]
      refine mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one
        (div_nonneg Real.pi_pos.le hpt.le) ?_ (by positivity))
      rw [div_le_one hpt]
      nlinarith [Real.pi_pos, mem_Ioi.mp ht]
  · -- Without measurability of the kernel along the ray, the function vanishes.
    convert (integrable_zero E ℂ volume) using 1
    funext x
    refine integral_non_aestronglyMeasurable fun h ↦ hmeas ?_
    refine (aestronglyMeasurable_fun_smul_iff₀ (c := fun t : ℝ ↦
      cexp (π * I * (‖x‖ ^ 2 : ℝ) * (t * I)))
      (Measurable.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun t ↦ exp_ne_zero _)).mp ?_
    exact h.congr (ae_of_all _ fun t ↦ by simp only [smul_eq_mul]; ring)

end SphereCeti.Contour
