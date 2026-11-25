/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.Complex.ExponentialIntegral
public import SphereCeti.Analysis.Complex.LaplaceDecay
public import SphereCeti.Analysis.Complex.LaplaceTail
public import SphereCeti.Analysis.Distribution.SchwartzSpace.HalfLine

import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Schwartz profiles from finite and infinite Laplace integrals

Finite cusp-decaying Laplace kernels, bounded exponential coefficients with strictly negative
real part, and exponentially decaying kernels on `(1,∞)` all give Schwartz profiles on the
nonnegative half-line. The constructors use smooth cutoffs only at negative arguments.
-/

public section

open Filter MeasureTheory Set Asymptotics
open scoped Topology Complex ContDiff SchwartzMap

namespace SchwartzMap

/-- A finite Laplace profile with cusp decay, extended to a Schwartz function without changing
any nonnegative value. -/
noncomputable def ofFiniteLaplace {f : ℝ → ℂ} {a T M : ℝ}
    (ha : 0 < a) (hT : 0 < T) (hM : 0 ≤ M) (hf : IntegrableOn f (Ioc 0 T))
    (hbound : ∀ t ∈ Ioc 0 T, ‖f t‖ ≤ M * Real.exp (-a / t)) (c : ℂ) (hc : 0 < c.re) :
    𝓢(ℝ, ℂ) :=
  mkOfHalfLineSqrtDecay 1 one_pos
    (fun r : ℝ ↦ ∫ (t : ℝ) in Ioc 0 T, f t * cexp (-(c * (r : ℂ)) * t))
    (by
      have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hf
      simpa only [intervalIntegral.integral_of_le hT.le] using
        (TauCeti.contDiff_intervalIntegral_mul_cexp_neg_mul_real hi c).contDiffOn)
    (fun n ↦ ⟨2 * Real.sqrt a * Real.sqrt c.re, by positivity,
      TauCeti.isBigO_iteratedDeriv_integral_Ioc_mul_cexp_neg_mul_sqrt ha hT hM hf hbound c hc n⟩)

/-- The finite Laplace Schwartz profile agrees with its defining integral for `r ≥ 0`. -/
theorem ofFiniteLaplace_apply_of_nonneg {f : ℝ → ℂ} {a T M : ℝ}
    (ha : 0 < a) (hT : 0 < T) (hM : 0 ≤ M) (hf : IntegrableOn f (Ioc 0 T))
    (hbound : ∀ t ∈ Ioc 0 T, ‖f t‖ ≤ M * Real.exp (-a / t)) (c : ℂ) (hc : 0 < c.re)
    {r : ℝ} (hr : 0 ≤ r) :
    ofFiniteLaplace ha hT hM hf hbound c hc r =
      ∫ (t : ℝ) in Ioc 0 T, f t * cexp (-(c * (r : ℂ)) * t) := by
  unfold ofFiniteLaplace
  exact mkOfHalfLineSqrtDecay_apply_of_nonneg _ _ _ _ _ hr

private lemma norm_exponential_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℂ} {K b : ℝ} (hf : Integrable f μ) (hK : 0 ≤ K)
    (hbound : ∀ᵐ t ∂μ, ‖g t‖ ≤ K) (hre : ∀ᵐ t ∂μ, (g t).re ≤ -b)
    (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ‖∫ t, (g t) ^ n * f t * cexp ((r : ℂ) * g t) ∂μ‖ ≤
      (K ^ n * ∫ t, ‖f t‖ ∂μ) * Real.exp (-b * r) := by
  calc
    _ ≤ ∫ t, (K ^ n * Real.exp (-b * r)) * ‖f t‖ ∂μ := by
      refine norm_integral_le_of_norm_le (hf.norm.const_mul _) ?_
      filter_upwards [hbound, hre] with t ht ht'
      simp only [norm_mul, norm_pow, Complex.norm_exp, Complex.re_ofReal_mul]
      have he : Real.exp (r * (g t).re) ≤ Real.exp (-b * r) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        ‖g t‖ ^ n * ‖f t‖ * Real.exp (r * (g t).re) ≤
            K ^ n * ‖f t‖ * Real.exp (-b * r) := by gcongr
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul]; ring

/-- An integrable kernel with bounded exponential coefficient of strictly negative real part
has a Schwartz extension on the nonnegative half-line. -/
noncomputable def ofExponentialIntegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℂ} {K b : ℝ} (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ)
    (hK : 0 ≤ K) (hbound : ∀ᵐ t ∂μ, ‖g t‖ ≤ K) (hb : 0 < b)
    (hre : ∀ᵐ t ∂μ, (g t).re ≤ -b) : 𝓢(ℝ, ℂ) :=
  mkOfHalfLineSqrtDecay 1 one_pos
    (fun r : ℝ ↦ ∫ t, f t * cexp ((r : ℂ) * g t) ∂μ)
    (TauCeti.contDiff_integral_mul_cexp_mul_real hf hg hK hbound).contDiffOn fun n ↦ by
      refine ⟨b, hb, Asymptotics.IsBigO.of_bound (K ^ n * ∫ t, ‖f t‖ ∂μ) ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      rw [TauCeti.iteratedDeriv_integral_mul_cexp_mul_real hf hg hK hbound n r,
        Real.norm_of_nonneg (Real.exp_nonneg _)]
      refine (norm_exponential_moment_le hf hK hbound hre n (zero_le_one.trans hr)).trans ?_
      have hs : Real.sqrt r ≤ r := Real.sqrt_le_self_iff.mpr (Or.inr hr)
      apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg (pow_nonneg hK n)
        (integral_nonneg fun _ ↦ norm_nonneg _))
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Evaluation of the Schwartz extension of a bounded-coefficient exponential integral. -/
theorem ofExponentialIntegral_apply_of_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℂ} {K b : ℝ} (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ)
    (hK : 0 ≤ K) (hbound : ∀ᵐ t ∂μ, ‖g t‖ ≤ K) (hb : 0 < b)
    (hre : ∀ᵐ t ∂μ, (g t).re ≤ -b) {r : ℝ} (hr : 0 ≤ r) :
    ofExponentialIntegral hf hg hK hbound hb hre r = ∫ t, f t * cexp ((r : ℂ) * g t) ∂μ := by
  unfold ofExponentialIntegral
  exact mkOfHalfLineSqrtDecay_apply_of_nonneg _ _ _ _ _ hr

private lemma integrable_laplace_tail_weight {f : ℝ → ℂ} {b M : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 1))) (hb : 0 < b)
    (hbound : ∀ t ∈ Ioi (1 : ℝ), ‖f t‖ ≤ M * Real.exp (-b * t)) :
    IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-(-b / 2) * t)) (Ioi 1) := by
  refine ((exp_neg_integrableOn_Ioi 1 (half_pos hb)).const_mul M).mono'
    (hf.norm.mul (by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-(-b / 2) * t)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    ‖f t‖ * Real.exp (-(-b / 2) * t) ≤
        (M * Real.exp (-b * t)) * Real.exp (-(-b / 2) * t) := by gcongr; exact hbound t ht
    _ = M * Real.exp (-(b / 2) * t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

private lemma laplace_tail_moment_bound {f : ℝ → ℂ} {b c M : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Ioi (1 : ℝ), ‖f t‖ ≤ M * Real.exp (-b * t))
    (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ‖∫ (t : ℝ) in Ioi 1, (-(c : ℂ) * (t : ℂ)) ^ n * f t *
        cexp (-((c : ℂ) * (r : ℂ)) * t)‖ ≤
      ((c ^ n * M) * ∫ t in Ioi (1 : ℝ), t ^ n * Real.exp (-b * t)) * Real.exp (-c * r) := by
  have hint : IntegrableOn (fun t : ℝ ↦ t ^ n * Real.exp (-b * t)) (Ioi 1) :=
    by simpa only [neg_mul] using
      (TauCeti.integrableOn_pow_mul_exp_neg_mul_Ioi n hb).mono_set (Ioi_subset_Ioi zero_le_one)
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), ((c ^ n * M) * (t ^ n * Real.exp (-b * t))) *
        Real.exp (-c * r) := by
      refine norm_integral_le_of_norm_le ((hint.const_mul _).mul_const _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 ≤ t := zero_le_one.trans ht.le
      have he : Real.exp (-(c * r) * t) ≤ Real.exp (-c * r) := by
        apply Real.exp_le_exp.mpr
        have ht1 : 1 ≤ t := ht.le
        have := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hc.le hr)
        nlinarith
      simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hc, abs_of_nonneg ht0, Complex.norm_exp, Complex.re_mul_ofReal,
        Complex.neg_re, Complex.ofReal_re]
      calc
        (c * t) ^ n * ‖f t‖ * Real.exp (-(c * r) * t) ≤
            (c * t) ^ n * (M * Real.exp (-b * t)) * Real.exp (-c * r) := by
          gcongr
          exact hbound t ht
        _ = _ := by rw [mul_pow]; ring
    _ = _ := by rw [integral_mul_const, integral_const_mul]

/-- The Laplace tail of an exponentially decaying complex kernel has a Schwartz extension
agreeing with the integral at every nonnegative parameter. -/
noncomputable def ofLaplaceTail {f : ℝ → ℂ} {b c M : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 1)))
    (hb : 0 < b) (hc : 0 < c) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Ioi (1 : ℝ), ‖f t‖ ≤ M * Real.exp (-b * t)) : 𝓢(ℝ, ℂ) :=
  mkOfHalfLineSqrtDecay (b / (2 * c)) (by positivity)
    (fun r : ℝ ↦ ∫ (t : ℝ) in Ioi 1, f t * cexp (-((c : ℂ) * (r : ℂ)) * t))
    (by
      apply (TauCeti.contDiffOn_integral_Ioi_mul_cexp_neg_mul_real zero_le_one hf
        (integrable_laplace_tail_weight hf hb hbound) (c : ℂ)).mono
      intro r hr
      change -(b / (2 * c)) < r at hr
      simp only [mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      have he : c * (-(b / (2 * c))) = -b / 2 := by field_simp
      have := mul_lt_mul_of_pos_left hr hc
      linarith)
    (fun n ↦ by
      let C := (c ^ n * M) * ∫ t in Ioi (1 : ℝ), t ^ n * Real.exp (-b * t)
      have hC : 0 ≤ C := by
        apply mul_nonneg (mul_nonneg (pow_nonneg hc.le n) hM)
        exact integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioi
          fun t ht ↦ by positivity [zero_le_one.trans ht.le])
      refine ⟨c, hc, Asymptotics.IsBigO.of_bound C ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
      rw [TauCeti.iteratedDeriv_integral_Ioi_mul_cexp_neg_mul_real zero_le_one hf
        (integrable_laplace_tail_weight hf hb hbound) (c : ℂ) (by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
          nlinarith [mul_nonneg hc.le (zero_le_one.trans hr)]) n,
        Real.norm_of_nonneg (Real.exp_nonneg _)]
      refine (laplace_tail_moment_bound hb hc hM hbound n (zero_le_one.trans hr)).trans ?_
      have hs : Real.sqrt r ≤ r := Real.sqrt_le_self_iff.mpr (Or.inr hr)
      apply mul_le_mul_of_nonneg_left ?_ hC
      apply Real.exp_le_exp.mpr
      nlinarith)

/-- Evaluation of the Schwartz extension of an exponentially decaying Laplace tail. -/
theorem ofLaplaceTail_apply_of_nonneg {f : ℝ → ℂ} {b c M : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 1)))
    (hb : 0 < b) (hc : 0 < c) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Ioi (1 : ℝ), ‖f t‖ ≤ M * Real.exp (-b * t)) {r : ℝ} (hr : 0 ≤ r) :
    ofLaplaceTail hf hb hc hM hbound r =
      ∫ (t : ℝ) in Ioi 1, f t * cexp (-((c : ℂ) * (r : ℂ)) * t) := by
  unfold ofLaplaceTail
  exact mkOfHalfLineSqrtDecay_apply_of_nonneg _ _ _ _ _ hr

end SchwartzMap
