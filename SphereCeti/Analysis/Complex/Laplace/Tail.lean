/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Derivatives of Laplace integrals on a half-line

An exponentially weighted integrable complex kernel has a holomorphic Laplace transform in
the interior of its half-plane of convergence. Every derivative inserts a factor `-t` in the
integrand. The lower endpoint may be any nonnegative real number; in particular it may be `1`,
as for the infinite rays of magic-function contours.

Only one integrable exponential weight is assumed. The strict gap between that weight and the
real part of the parameter controls every polynomial moment, including a locally uniform
majorant for differentiation under the integral. No continuity of the kernel is required.

The proof uses Mathlib's dominated differentiation theorem and exponential-series estimate.
-/

public section

open Filter MeasureTheory Set Metric
open scoped Topology Complex ContDiff

namespace TauCeti

private lemma laplace_pow_exp_bound {d t : ℝ} (hd : 0 < d) (ht : 0 ≤ t) (n : ℕ) :
    t ^ n * Real.exp (-d * t) ≤ (n.factorial : ℝ) / d ^ n := by
  have hp := Real.pow_div_factorial_le_exp (x := d * t) (mul_nonneg hd.le ht) n
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial), mul_pow] at hp
  apply (le_div_iff₀ (pow_pos hd n)).mpr
  calc
    t ^ n * Real.exp (-d * t) * d ^ n = d ^ n * t ^ n * Real.exp (-d * t) := by ring
    _ ≤ Real.exp (d * t) * n.factorial * Real.exp (-d * t) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = n.factorial := by
      rw [mul_right_comm, ← Real.exp_add, show d * t + -d * t = 0 by ring]
      simp

variable {f : ℝ → ℂ} {a σ : ℝ}

private lemma integrableOn_laplace_norm_moment (ha : 0 ≤ a)
    (hw : IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-σ * t)) (Ioi a))
    {b : ℝ} (hb : σ < b) (n : ℕ) :
    IntegrableOn (fun t : ℝ ↦ t ^ n * ‖f t‖ * Real.exp (-b * t)) (Ioi a) := by
  have hm : AEStronglyMeasurable (fun t : ℝ ↦ ‖f t‖) (volume.restrict (Ioi a)) := by
    have := hw.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun t : ℝ ↦ Real.exp (σ * t)).aestronglyMeasurable
    refine this.congr (.of_forall fun t ↦ ?_)
    change ‖f t‖ * Real.exp (-σ * t) * Real.exp (σ * t) = ‖f t‖
    rw [mul_assoc, ← Real.exp_add, show -σ * t + σ * t = 0 by ring]
    simp
  refine (hw.const_mul ((n.factorial : ℝ) / (b - σ) ^ n)).mono'
    (((by fun_prop : Continuous fun t : ℝ ↦ t ^ n).aestronglyMeasurable.mul hm).mul
      (by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-b * t)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := ha.trans ht.le
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    t ^ n * ‖f t‖ * Real.exp (-b * t) =
        (t ^ n * Real.exp (-(b - σ) * t)) * (‖f t‖ * Real.exp (-σ * t)) := by
      rw [mul_mul_mul_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (n.factorial : ℝ) / (b - σ) ^ n * (‖f t‖ * Real.exp (-σ * t)) :=
      mul_le_mul_of_nonneg_right (laplace_pow_exp_bound (sub_pos.mpr hb) ht0 n)
        (by positivity)

/-- Every polynomial moment of a Laplace integrand is integrable strictly inside the
half-plane determined by one integrable exponential weight. -/
theorem integrableOn_pow_mul_cexp_neg_mul_of_integrable_weight (ha : 0 ≤ a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hw : IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-σ * t)) (Ioi a))
    {z : ℂ} (hz : σ < z.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ ↦ (-(t : ℂ)) ^ n * f t * cexp (-z * t)) (Ioi a) := by
  apply (integrableOn_laplace_norm_moment ha hw hz n).mono'
    (((by fun_prop : Continuous fun t : ℝ ↦ (-(t : ℂ)) ^ n).aestronglyMeasurable.mul hf).mul
      (by fun_prop : Continuous fun t : ℝ ↦ cexp (-z * t)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖(-(t : ℂ)) ^ n * f t * cexp (-z * t)‖ ≤ _
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ha.trans ht.le), Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
  exact le_rfl

/-- Differentiating a polynomial moment of a Laplace transform inserts one more factor `-t`.
The domination is uniform on a complex neighborhood of the parameter. -/
theorem hasDerivAt_integral_Ioi_pow_mul_cexp_neg_mul (ha : 0 ≤ a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hw : IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-σ * t)) (Ioi a))
    {z : ℂ} (hz : σ < z.re) (n : ℕ) :
    HasDerivAt (fun w : ℂ ↦ ∫ (t : ℝ) in Ioi a, (-(t : ℂ)) ^ n * f t * cexp (-w * t))
      (∫ (t : ℝ) in Ioi a, (-(t : ℂ)) ^ (n + 1) * f t * cexp (-z * t)) z := by
  let b := (σ + z.re) / 2
  have hb : σ < b := by dsimp [b]; linarith
  have hzb : b < z.re := by dsimp [b]; linarith
  have hm (w : ℂ) : AEStronglyMeasurable
      (fun t : ℝ ↦ (-(t : ℂ)) ^ n * f t * cexp (-w * t)) (volume.restrict (Ioi a)) :=
    ((by fun_prop : Continuous fun t : ℝ ↦ (-(t : ℂ)) ^ n).aestronglyMeasurable.mul hf).mul
      (by fun_prop : Continuous fun t : ℝ ↦ cexp (-w * t)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun (w : ℂ) (t : ℝ) ↦ (-(t : ℂ)) ^ (n + 1) * f t * cexp (-w * t))
    (bound := fun t : ℝ ↦ t ^ (n + 1) * ‖f t‖ * Real.exp (-b * t))
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzb)
    (.of_forall hm) (integrableOn_pow_mul_cexp_neg_mul_of_integrable_weight ha hf hw hz n)
    (integrableOn_pow_mul_cexp_neg_mul_of_integrable_weight ha hf hw hz (n + 1)).aestronglyMeasurable ?_ (integrableOn_laplace_norm_moment ha hw hb (n + 1)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have ht0 : 0 ≤ t := ha.trans ht.le
    simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0, Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
    gcongr
  · exact .of_forall fun t w _ ↦ by
      have h : HasDerivAt (fun v : ℂ ↦ cexp (-v * t))
          (cexp (-w * t) * (-(t : ℂ))) w := by
        simpa only [id_eq, Pi.neg_apply, neg_mul, one_mul] using ((hasDerivAt_id' w).neg.mul_const (t : ℂ)).cexp
      convert h.const_mul ((-(t : ℂ)) ^ n * f t) using 1
      ring

/-- The derivative of the Laplace tail of a complex kernel is its negative first moment. -/
theorem hasDerivAt_integral_Ioi_mul_cexp_neg_mul (ha : 0 ≤ a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hw : IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-σ * t)) (Ioi a))
    {z : ℂ} (hz : σ < z.re) :
    HasDerivAt (fun w : ℂ ↦ ∫ (t : ℝ) in Ioi a, f t * cexp (-w * t))
      (∫ (t : ℝ) in Ioi a, (-(t : ℂ)) * f t * cexp (-z * t)) z := by
  simpa using hasDerivAt_integral_Ioi_pow_mul_cexp_neg_mul ha hf hw hz 0

/-- All complex derivatives of the Laplace tail are given by its polynomial moments. -/
theorem iteratedDeriv_integral_Ioi_mul_cexp_neg_mul (ha : 0 ≤ a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hw : IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-σ * t)) (Ioi a))
    {z : ℂ} (hz : σ < z.re) (n : ℕ) :
    iteratedDeriv n (fun w : ℂ ↦ ∫ (t : ℝ) in Ioi a, f t * cexp (-w * t)) z =
      ∫ (t : ℝ) in Ioi a, (-(t : ℂ)) ^ n * f t * cexp (-z * t) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun w : ℂ ↦ ∫ (t : ℝ) in Ioi a, f t * cexp (-w * t))
        =ᶠ[𝓝 z] (fun w : ℂ ↦ ∫ (t : ℝ) in Ioi a, (-(t : ℂ)) ^ n * f t * cexp (-w * t)) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
      exact ih hw
    rw [heq.deriv_eq]
    exact (hasDerivAt_integral_Ioi_pow_mul_cexp_neg_mul ha hf hw hz n).deriv

/-- The real-parameter moment formula, with an arbitrary complex scale `c`. -/
theorem hasDerivAt_integral_Ioi_pow_mul_cexp_neg_mul_real (ha : 0 ≤ a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hw : IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-σ * t)) (Ioi a))
    (c : ℂ) (n : ℕ) {r : ℝ} (hr : σ < (c * (r : ℂ)).re) :
    HasDerivAt (fun s : ℝ ↦ ∫ (t : ℝ) in Ioi a,
        (-c * (t : ℂ)) ^ n * f t * cexp (-(c * (s : ℂ)) * t))
      (∫ (t : ℝ) in Ioi a,
        (-c * (t : ℂ)) ^ (n + 1) * f t * cexp (-(c * (r : ℂ)) * t)) r := by
  have h := ((hasDerivAt_integral_Ioi_pow_mul_cexp_neg_mul ha hf hw hr n).comp
    (r : ℂ) ((hasDerivAt_id' (r : ℂ)).const_mul c)).comp_ofReal
  simp only [Function.comp_apply, mul_one] at h
  convert h.const_mul (c ^ n) using 1
  · funext s
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  · rw [← integral_mul_const, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring

/-- All real derivatives of a scaled Laplace tail insert powers of `-c t`. -/
theorem iteratedDeriv_integral_Ioi_mul_cexp_neg_mul_real (ha : 0 ≤ a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hw : IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-σ * t)) (Ioi a))
    (c : ℂ) {r : ℝ} (hr : σ < (c * (r : ℂ)).re) (n : ℕ) :
    iteratedDeriv n (fun s : ℝ ↦ ∫ (t : ℝ) in Ioi a,
        f t * cexp (-(c * (s : ℂ)) * t)) r =
      ∫ (t : ℝ) in Ioi a,
        (-c * (t : ℂ)) ^ n * f t * cexp (-(c * (r : ℂ)) * t) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv n (fun s : ℝ ↦ ∫ (t : ℝ) in Ioi a,
        f t * cexp (-(c * (s : ℂ)) * t)) =ᶠ[𝓝 r]
        (fun s : ℝ ↦ ∫ (t : ℝ) in Ioi a,
          (-c * (t : ℂ)) ^ n * f t * cexp (-(c * (s : ℂ)) * t)) := by
      have hopen : IsOpen {s : ℝ | σ < (c * (s : ℂ)).re} :=
        isOpen_lt continuous_const (by fun_prop)
      filter_upwards [hopen.mem_nhds hr] with s hs
      exact ih hs
    rw [heq.deriv_eq]
    exact (hasDerivAt_integral_Ioi_pow_mul_cexp_neg_mul_real ha hf hw c n hr).deriv

/-- A complex Laplace tail is smooth throughout the open half-plane of convergence. -/
theorem contDiffOn_integral_Ioi_mul_cexp_neg_mul (ha : 0 ≤ a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hw : IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-σ * t)) (Ioi a)) :
    ContDiffOn ℂ ∞ (fun z : ℂ ↦ ∫ (t : ℝ) in Ioi a, f t * cexp (-z * t))
      {z | σ < z.re} := by
  have hd : DifferentiableOn ℂ (fun z : ℂ ↦ ∫ (t : ℝ) in Ioi a, f t * cexp (-z * t))
      {z | σ < z.re} := fun z hz ↦
    (hasDerivAt_integral_Ioi_mul_cexp_neg_mul ha hf hw hz).differentiableAt.differentiableWithinAt
  exact hd.contDiffOn (isOpen_lt continuous_const Complex.continuous_re)

/-- A scaled real Laplace tail is smooth on its open domain of convergence. -/
theorem contDiffOn_integral_Ioi_mul_cexp_neg_mul_real (ha : 0 ≤ a)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hw : IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-σ * t)) (Ioi a)) (c : ℂ) :
    ContDiffOn ℝ ∞ (fun s : ℝ ↦ ∫ (t : ℝ) in Ioi a,
      f t * cexp (-(c * (s : ℂ)) * t)) {s | σ < (c * (s : ℂ)).re} :=
  ((contDiffOn_integral_Ioi_mul_cexp_neg_mul ha hf hw).restrict_scalars ℝ).comp
    (contDiff_const.mul Complex.ofRealCLM.contDiff).contDiffOn (fun _ hs ↦ hs)

/-- At `r = 0`, when the kernel has an integrable growing exponential weight, the second
real derivative is the positive squared-scale moment. -/
example (ha : 0 ≤ a) (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hw : IntegrableOn (fun t : ℝ ↦ ‖f t‖ * Real.exp (-σ * t)) (Ioi a))
    (hσ : σ < 0) (c : ℂ) :
    iteratedDeriv 2 (fun s : ℝ ↦ ∫ (t : ℝ) in Ioi a,
      f t * cexp (-(c * (s : ℂ)) * t)) 0 =
      ∫ (t : ℝ) in Ioi a, (c * (t : ℂ)) ^ 2 * f t := by
  simpa using iteratedDeriv_integral_Ioi_mul_cexp_neg_mul_real ha hf hw c
    (r := 0) (by simpa using hσ) 2

end TauCeti
