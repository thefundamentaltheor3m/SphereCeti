/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.Complex.LaplaceTransform
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Asymptotics.Defs

import Mathlib.Analysis.Asymptotics.Basic

/-!
# Square-root exponential decay of finite Laplace profiles

A cusp bound `‖f(t)‖ ≤ M exp(-a/t)` on `(0,T]` gives the estimate
`‖∫ f(t) exp(-c r t) dt‖ ≤ M T exp(-2 √a √(Re c) √r)` for `r ≥ 0`, `a > 0`, and
`Re c > 0`. The elementary inequality `a/t + Re(c) r t ≥ 2 √a √(Re c) √r` balances
the cusp decay against the Laplace exponential.

Every derivative satisfies the same decay rate: differentiating inserts `(-ct)^n`, which is
bounded on the finite interval. These are estimates for the profile parameter, independently
of any ambient dimension.
-/

public section

open Filter MeasureTheory Set Asymptotics
open scoped Topology Complex

namespace TauCeti

private lemma laplace_sqrt_balance {a b r t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (ht : 0 < t) :
    2 * Real.sqrt a * Real.sqrt b * Real.sqrt r ≤ a / t + b * r * t := by
  have hs : (Real.sqrt (b * r) * t) ^ 2 = b * r * t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hb hr)]
  have h := sq_nonneg (Real.sqrt a - Real.sqrt (b * r) * t)
  rw [Real.sqrt_mul hb] at h hs
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith [Real.sq_sqrt ha, div_mul_cancel₀ a ht.ne']

/-- An explicit square-root exponential bound for a finite Laplace integral with cusp decay.
The coefficient `c` may have an imaginary part. -/
theorem norm_integral_Ioc_mul_cexp_neg_mul_le_sqrt {f : ℝ → ℂ} {a T M : ℝ}
    (ha : 0 < a) (hT : 0 < T) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Ioc 0 T, ‖f t‖ ≤ M * Real.exp (-a / t))
    (c : ℂ) (hc : 0 < c.re) {r : ℝ} (hr : 0 ≤ r) :
    ‖∫ (t : ℝ) in Ioc 0 T, f t * cexp (-(c * (r : ℂ)) * t)‖ ≤
      M * T * Real.exp (-(2 * Real.sqrt a * Real.sqrt c.re) * Real.sqrt r) := by
  have hpoint (t : ℝ) (ht : t ∈ Ioc 0 T) :
      ‖f t * cexp (-(c * (r : ℂ)) * t)‖ ≤
        M * Real.exp (-(2 * Real.sqrt a * Real.sqrt c.re) * Real.sqrt r) := by
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.re_mul_ofReal, Complex.neg_re]
    calc
      ‖f t‖ * Real.exp (-(c.re * r) * t) ≤
          (M * Real.exp (-a / t)) * Real.exp (-(c.re * r) * t) := by gcongr; exact hbound t ht
      _ = M * Real.exp (-(a / t + c.re * r * t)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ M * Real.exp (-(2 * Real.sqrt a * Real.sqrt c.re) * Real.sqrt r) := by
        gcongr
        have h := laplace_sqrt_balance ha.le hc.le hr ht.1
        nlinarith
  calc
    _ ≤ ∫ (t : ℝ) in Ioc 0 T,
        M * Real.exp (-(2 * Real.sqrt a * Real.sqrt c.re) * Real.sqrt r) :=
      norm_integral_le_of_norm_le (integrableOn_const measure_Ioc_lt_top.ne)
        (ae_restrict_of_forall_mem measurableSet_Ioc hpoint)
    _ = _ := by
      simp only [MeasureTheory.integral_const, MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply_univ, Real.volume_Ioc,
        sub_zero, ENNReal.toReal_ofReal hT.le, smul_eq_mul]
      ring

/-- Cusp decay of the kernel gives square-root exponential decay of its finite Laplace
transform, with the explicit rate `2 √a √(Re c)`. -/
theorem isBigO_integral_Ioc_mul_cexp_neg_mul_sqrt {f : ℝ → ℂ} {a T M : ℝ}
    (ha : 0 < a) (hT : 0 < T) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Ioc 0 T, ‖f t‖ ≤ M * Real.exp (-a / t))
    (c : ℂ) (hc : 0 < c.re) :
    (fun r : ℝ ↦ ∫ (t : ℝ) in Ioc 0 T, f t * cexp (-(c * (r : ℂ)) * t))
      =O[atTop] (fun r ↦ Real.exp (-(2 * Real.sqrt a * Real.sqrt c.re) * Real.sqrt r)) := by
  refine Asymptotics.IsBigO.of_bound (M * T) ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  simpa only [Real.norm_of_nonneg (Real.exp_nonneg _)] using
    norm_integral_Ioc_mul_cexp_neg_mul_le_sqrt ha hT hM hbound c hc hr

/-- Every real derivative of a finite Laplace profile has the same square-root exponential
rate as the profile itself. No differentiability of the kernel is needed. -/
theorem isBigO_iteratedDeriv_integral_Ioc_mul_cexp_neg_mul_sqrt
    {f : ℝ → ℂ} {a T M : ℝ} (ha : 0 < a) (hT : 0 < T) (hM : 0 ≤ M)
    (hf : IntegrableOn f (Ioc 0 T))
    (hbound : ∀ t ∈ Ioc 0 T, ‖f t‖ ≤ M * Real.exp (-a / t))
    (c : ℂ) (hc : 0 < c.re) (n : ℕ) :
    iteratedDeriv n (fun r : ℝ ↦ ∫ (t : ℝ) in Ioc 0 T,
        f t * cexp (-(c * (r : ℂ)) * t))
      =O[atTop] (fun r ↦ Real.exp (-(2 * Real.sqrt a * Real.sqrt c.re) * Real.sqrt r)) := by
  have hn (t : ℝ) (ht : t ∈ Ioc 0 T) :
      ‖(-c * (t : ℂ)) ^ n * f t‖ ≤
        ((‖c‖ * T) ^ n * M) * Real.exp (-a / t) := by
    rw [norm_mul, norm_pow, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht.1]
    calc
      (‖c‖ * t) ^ n * ‖f t‖ ≤ (‖c‖ * T) ^ n * (M * Real.exp (-a / t)) := by
        gcongr
        exacts [mul_nonneg (norm_nonneg c) ht.1.le, ht.2, hbound t ht]
      _ = _ := by ring
  have h := isBigO_integral_Ioc_mul_cexp_neg_mul_sqrt ha hT (by positivity) hn c hc
  convert h using 1
  funext r
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr hf
  simpa only [intervalIntegral.integral_of_le hT.le] using
    iteratedDeriv_intervalIntegral_mul_cexp_neg_mul_real hi c n r

end TauCeti
