/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Continuity of Gaussian segment integrals

For a segment `z(t) = a + t (b - a)`, `0 < t ≤ 1`, and a kernel `g : ℂ → ℂ`, the Gaussian segment
integral is the function `x ↦ ∫₀¹ g(z(t)) exp(πi ‖x‖² z(t)) (b - a) dt` on a real inner product
space `E`.  If the segment lies in the closed upper half-plane and `‖g(z(t))‖` is integrable on
`(0, 1]`, then this function is continuous: `|exp(πi ‖x‖² z)| ≤ 1` for `Im z ≥ 0`.

On a finite-dimensional space of dimension `n`, integrability of the real kernel
`‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` already forces `‖g(z(t))‖` to be integrable on
`(0, 1]`, since `Im z(t)` is bounded on the segment.  Conversely, if `z(t)` lies in the open upper
half-plane for `0 < t ≤ 1`, then integrability of `‖g(z(t))‖ (Im z(t))^{-n/2}` on `(0, 1]` gives
integrability of `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` on `E × (0, 1]`, since the Gaussian
`exp(-π s ‖x‖²)` has total mass `s^{-n/2}`.  This is the integrability hypothesis of the Fourier
identities of the left and central legs of the magic contour, so the Gaussian segment integrals of
those legs are continuous.

## Main statements

* `SphereCeti.Contour.continuous_segment_gaussian_integral`: continuity of a Gaussian segment
  integral along a segment in the closed upper half-plane.
* `SphereCeti.Contour.integrableOn_norm_of_integrable_prod`: integrability of
  `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` gives integrability of `‖g(z(t))‖` on `(0, 1]`.
* `SphereCeti.Contour.integrable_prod_of_integrableOn_rpow`: integrability of
  `‖g(z(t))‖ (Im z(t))^{-n/2}` on `(0, 1]` gives integrability of `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))`
  on `E × (0, 1]`.
-/

public section

open Complex MeasureTheory Set
open scoped Real

namespace SphereCeti.Contour

/-- Along a segment `z(t) = a + t (b - a)` in the closed upper half-plane, if `‖g(z(t))‖` is
integrable on `(0, 1]`, then the Gaussian segment integral
`x ↦ ∫₀¹ g(z(t)) exp(πi ‖x‖² z(t)) (b - a) dt` is continuous. -/
theorem continuous_segment_gaussian_integral {E : Type*} [SeminormedAddCommGroup E]
    {a b : ℂ} (hab : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ (a + t * (b - a)).im) {g : ℂ → ℂ}
    (hg : IntegrableOn (fun t : ℝ ↦ ‖g (a + t * (b - a))‖) (Ioc 0 1)) :
    Continuous (fun x : E ↦ ∫ t in (0 : ℝ)..1,
      g (a + t * (b - a)) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a)) := by
  by_cases hmeas : AEStronglyMeasurable (fun t : ℝ ↦ g (a + t * (b - a)))
    (volume.restrict (Ioc (0 : ℝ) 1))
  · refine intervalIntegral.continuous_of_dominated_interval
      (bound := fun t ↦ ‖g (a + t * (b - a))‖ * ‖b - a‖) (fun x ↦ ?_) (fun x ↦ ?_) ?_ ?_
    · rw [uIoc_of_le zero_le_one]
      exact (hmeas.mul (Continuous.aestronglyMeasurable (by fun_prop))).mul_const _
    · refine ae_of_all _ fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      rw [norm_mul, norm_mul, Complex.norm_exp]
      gcongr
      refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
      have him := hab t ht
      have hr : 0 ≤ ‖x‖ ^ 2 := by positivity
      generalize ‖x‖ ^ 2 = r at hr ⊢
      have hre : (π * I * (r : ℂ) * (a + t * (b - a))).re = -(π * r * (a + t * (b - a)).im) := by
        simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im, sub_re,
          sub_im]
        ring
      rw [hre, neg_nonpos]
      positivity
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact hg.mul_const _
    · exact ae_of_all _ fun t _ ↦ by fun_prop
  · -- Without measurability of the kernel along the segment, the function is zero.
    rcases eq_or_ne b a with rfl | hba
    · simpa using continuous_const
    convert continuous_const (y := (0 : ℂ)) using 1
    funext x
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine integral_non_aestronglyMeasurable fun h ↦ hmeas ?_
    refine (aestronglyMeasurable_fun_smul_iff₀ (c := fun t : ℝ ↦
      cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a))
      (Measurable.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun t ↦ mul_ne_zero (exp_ne_zero _) (sub_ne_zero.mpr hba))).mp ?_
    exact h.congr (ae_of_all _ fun t ↦ by simp only [smul_eq_mul]; ring)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If `g(z(t)) exp(-π ‖x‖² Im z(t))` is absolutely integrable on `E × (0, 1]` along the segment
`z(t) = a + t (b - a)`, then `‖g(z(t))‖` is integrable on `(0, 1]`. -/
theorem integrableOn_norm_of_integrable_prod {a b : ℂ} {g : ℂ → ℂ}
    (hint : Integrable (fun q : E × ℝ ↦
      ‖g (a + q.2 * (b - a))‖ * Real.exp (-π * ‖q.1‖ ^ 2 * (a + q.2 * (b - a)).im))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) :
    IntegrableOn (fun t : ℝ ↦ ‖g (a + t * (b - a))‖) (Ioc 0 1) := by
  -- Some slice `x₀` of the product is integrable on `(0, 1]`.
  obtain ⟨x₀, hx₀⟩ := hint.prod_right_ae.exists
  -- On the segment `Im z(t) ≤ M`, so `exp(-π ‖x₀‖² Im z(t))` has a positive lower bound.
  set M := |a.im| + |(b - a).im|
  have him (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : (a + t * (b - a)).im ≤ M := by
    have h1 : (a + t * (b - a)).im = a.im + t * (b - a).im := by simp
    have h2 : t * (b - a).im ≤ |(b - a).im| := by
      calc t * (b - a).im ≤ |t * (b - a).im| := le_abs_self _
        _ = t * |(b - a).im| := by rw [abs_mul, abs_of_pos ht.1]
        _ ≤ 1 * |(b - a).im| := by gcongr; exact ht.2
        _ = |(b - a).im| := one_mul _
    rw [h1]
    linarith [le_abs_self a.im]
  have hexp (t : ℝ) : ‖g (a + t * (b - a))‖ = (‖g (a + t * (b - a))‖ *
      Real.exp (-π * ‖x₀‖ ^ 2 * (a + t * (b - a)).im)) *
        Real.exp (π * ‖x₀‖ ^ 2 * (a + t * (b - a)).im) := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  refine (hx₀.mul_const (Real.exp (π * ‖x₀‖ ^ 2 * M))).mono' ?_ ?_
  · refine (hx₀.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))).congr
      (ae_of_all _ fun t ↦ (hexp t).symm)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc ‖g (a + t * (b - a))‖ = _ := hexp t
      _ ≤ _ := by
        gcongr
        exact him t ht

/-- Conversely, if `‖g(z(t))‖ (Im z(t))^{-n/2}` is integrable on `(0, 1]`, where `n` is the
dimension of `E` and the segment `z(t) = a + t (b - a)` lies in the upper half-plane for
`0 < t ≤ 1`, then the real kernel `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` is integrable on
`E × (0, 1]`: the Gaussian `exp(-π s ‖x‖²)` has total mass `s^{-n/2}`. -/
theorem integrable_prod_of_integrableOn_rpow {a b : ℂ}
    (hab : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < (a + t * (b - a)).im) {g : ℂ → ℂ}
    (hg : IntegrableOn (fun t : ℝ ↦ ‖g (a + t * (b - a))‖ *
      (a + t * (b - a)).im ^ (-(Module.finrank ℝ E / 2 : ℝ))) (Ioc 0 1)) :
    Integrable (fun q : E × ℝ ↦
      ‖g (a + q.2 * (b - a))‖ * Real.exp (-π * ‖q.1‖ ^ 2 * (a + q.2 * (b - a)).im))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  set n := Module.finrank ℝ E
  -- The kernel norm is measurable along the segment: multiply back the measurable weight.
  have hw : Measurable fun t : ℝ ↦ (a + t * (b - a)).im ^ (n / 2 : ℝ) :=
    (Measurable.pow_const (by fun_prop) _)
  have hgmeas : AEStronglyMeasurable (fun t : ℝ ↦ ‖g (a + t * (b - a))‖)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine (hg.aestronglyMeasurable.mul hw.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hs := hab t ht
    rw [Pi.mul_apply, mul_assoc, ← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero, mul_one]
  have hFmeas : AEStronglyMeasurable (fun q : E × ℝ ↦
      ‖g (a + q.2 * (b - a))‖ * Real.exp (-π * ‖q.1‖ ^ 2 * (a + q.2 * (b - a)).im))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    hgmeas.comp_snd.mul (Continuous.aestronglyMeasurable (by fun_prop))
  -- The Gaussian `exp(-π s ‖x‖²)` is integrable with total mass `(π / (π s))^{n/2} = s^{-n/2}`.
  have hgauss (s : ℝ) (hs : 0 < s) : Integrable fun x : E ↦ Real.exp (-π * ‖x‖ ^ 2 * s) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E)
      (b := ((π * s : ℝ) : ℂ)) (by simpa using mul_pos Real.pi_pos hs) 0 0).norm
    refine h.congr (ae_of_all _ fun x ↦ ?_)
    simp only [zero_mul, add_zero, Complex.norm_exp]
    congr 1
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    norm_cast
    ring
  have hmass (s : ℝ) (hs : 0 < s) :
      ∫ x : E, Real.exp (-π * ‖x‖ ^ 2 * s) = s ^ (-(n / 2 : ℝ)) := by
    have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (mul_pos Real.pi_pos hs)
    rw [div_mul_cancel_left₀ Real.pi_ne_zero, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le] at h
    rw [← h]
    congr 1 with x
    ring_nf
  refine (integrable_prod_iff' hFmeas).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hgauss _ (hab t ht)).const_mul _
  · refine hg.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [norm_mul, norm_norm, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [integral_const_mul, hmass _ (hab t ht)]

end SphereCeti.Contour
