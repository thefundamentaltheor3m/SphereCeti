/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential

/-!
# Exponential integrals with a bounded coefficient

For an integrable complex kernel `f` and an ae bounded measurable coefficient `g`, the integral
`∫ f(t) exp(z g(t))` is entire. Differentiation inserts a factor `g(t)`, so every complex or real
derivative is a polynomial moment of the same exponential integral. The kernel need not be
continuous and the measure need not be finite.

This is the bounded-coefficient counterpart of the Laplace-tail moment formulas. In particular,
it applies to every finite segment of a contour.
-/

public section

open Filter MeasureTheory Metric
open scoped Topology Complex ContDiff

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℂ} {K : ℝ}

/-- Polynomial moments of an exponential integral with bounded coefficient are integrable. -/
theorem integrable_pow_mul_cexp_mul (hf : Integrable f μ) (hg : AEStronglyMeasurable g μ)
    (hK : 0 ≤ K) (hbound : ∀ᵐ t ∂μ, ‖g t‖ ≤ K) (n : ℕ) (z : ℂ) :
    Integrable (fun t ↦ (g t) ^ n * f t * cexp (z * g t)) μ := by
  refine (hf.norm.const_mul (K ^ n * Real.exp (‖z‖ * K))).mono'
    ((hg.pow n |>.mul hf.aestronglyMeasurable).mul
      (Complex.continuous_exp.comp_aestronglyMeasurable (aestronglyMeasurable_const.mul hg))) ?_
  filter_upwards [hbound] with t ht
  simp only [norm_mul, norm_pow, Complex.norm_exp]
  have hre : (z * g t).re ≤ ‖z‖ * K :=
    (Complex.re_le_norm _).trans (by rw [norm_mul]; gcongr)
  calc
    ‖g t‖ ^ n * ‖f t‖ * Real.exp (z * g t).re ≤
        K ^ n * ‖f t‖ * Real.exp (‖z‖ * K) := by gcongr
    _ = _ := by ring

/-- Differentiation under an exponential integral with bounded coefficient inserts one more
factor of the coefficient. -/
theorem hasDerivAt_integral_pow_mul_cexp_mul (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (hK : 0 ≤ K) (hbound : ∀ᵐ t ∂μ, ‖g t‖ ≤ K)
    (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ ∫ t, (g t) ^ n * f t * cexp (w * g t) ∂μ)
      (∫ t, (g t) ^ (n + 1) * f t * cexp (z * g t) ∂μ) z := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w t ↦ (g t) ^ n * f t * cexp (w * g t))
    (F' := fun w t ↦ (g t) ^ (n + 1) * f t * cexp (w * g t))
    (bound := fun t ↦ (K ^ (n + 1) * Real.exp ((‖z‖ + 1) * K)) * ‖f t‖)
    (ball_mem_nhds z one_pos)
    (.of_forall fun w ↦ (hg.pow n |>.mul hf.aestronglyMeasurable).mul
      (Complex.continuous_exp.comp_aestronglyMeasurable (aestronglyMeasurable_const.mul hg)))
    (integrable_pow_mul_cexp_mul hf hg hK hbound n z)
    (integrable_pow_mul_cexp_mul hf hg hK hbound (n + 1) z).aestronglyMeasurable
    ?_ (hf.norm.const_mul _) (.of_forall fun t w _ ↦ ?_)).2
  · filter_upwards [hbound] with t ht w hw
    have hwN : ‖w‖ ≤ ‖z‖ + 1 := by
      rw [mem_ball_iff_norm] at hw
      have := norm_sub_norm_le w z
      linarith
    have hre : (w * g t).re ≤ (‖z‖ + 1) * K :=
      (Complex.re_le_norm _).trans (by rw [norm_mul]; gcongr)
    simp only [norm_mul, norm_pow, Complex.norm_exp]
    calc
      ‖g t‖ ^ (n + 1) * ‖f t‖ * Real.exp (w * g t).re ≤
          K ^ (n + 1) * ‖f t‖ * Real.exp ((‖z‖ + 1) * K) := by gcongr
      _ = _ := by ring
  · have h : HasDerivAt (fun w : ℂ ↦ cexp (w * g t)) (cexp (w * g t) * g t) w := by
      simpa only [id_eq, one_mul] using ((hasDerivAt_id' w).mul_const (g t)).cexp
    convert h.const_mul ((g t) ^ n * f t) using 1
    ring

/-- All complex derivatives of an exponential integral with bounded coefficient are moments. -/
theorem iteratedDeriv_integral_mul_cexp_mul (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (hK : 0 ≤ K) (hbound : ∀ᵐ t ∂μ, ‖g t‖ ≤ K)
    (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w : ℂ ↦ ∫ t, f t * cexp (w * g t) ∂μ) z =
      ∫ t, (g t) ^ n * f t * cexp (z * g t) ∂μ := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    exact (hasDerivAt_integral_pow_mul_cexp_mul hf hg hK hbound n z).deriv

/-- All real derivatives of an exponential integral with bounded coefficient are moments. -/
theorem iteratedDeriv_integral_mul_cexp_mul_real (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (hK : 0 ≤ K) (hbound : ∀ᵐ t ∂μ, ‖g t‖ ≤ K)
    (n : ℕ) (r : ℝ) :
    iteratedDeriv n (fun s : ℝ ↦ ∫ t, f t * cexp ((s : ℂ) * g t) ∂μ) r =
      ∫ t, (g t) ^ n * f t * cexp ((r : ℂ) * g t) ∂μ := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    have h := (hasDerivAt_integral_pow_mul_cexp_mul hf hg hK hbound n (r : ℂ)).comp_ofReal
    simpa only [mul_one] using h.deriv

/-- The real-parameter integral with bounded coefficient is smooth everywhere. -/
theorem contDiff_integral_mul_cexp_mul_real (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (hK : 0 ≤ K) (hbound : ∀ᵐ t ∂μ, ‖g t‖ ≤ K) :
    ContDiff ℝ ∞ (fun r : ℝ ↦ ∫ t, f t * cexp ((r : ℂ) * g t) ∂μ) := by
  have hd : Differentiable ℂ (fun z : ℂ ↦ ∫ t, f t * cexp (z * g t) ∂μ) := by
    intro z
    simpa only [pow_zero, one_mul] using
      (hasDerivAt_integral_pow_mul_cexp_mul hf hg hK hbound 0 z).differentiableAt
  exact (hd.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff

end TauCeti
