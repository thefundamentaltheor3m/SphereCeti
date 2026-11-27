/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.Distribution.SchwartzSpace.SqrtExponentialDecay
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.Compact

/-!
# Schwartz extensions of profiles on a half-line

A profile smooth on `(-ε,∞)` and with square-root exponential derivative decay at `+∞` has a
Schwartz extension agreeing with it on `[0,∞)`. A smooth transition suppresses the unused
negative half-line. This does not change the radial function obtained by substituting `‖x‖²`.

The cutoff argument is adapted from `SpherePacking/ForMathlib/DerivHelpers.lean` in
`thefundamentaltheor3m/Sphere-Packing-Lean@01f23eccf963c50250c9e48dd103e8cc88c36f85`
(Sidharth Hariharan, Apache-2.0), generalized to any `ε > 0` and asymptotic derivative bounds.
-/

public section

open Filter Topology Set Asymptotics
open scoped ContDiff SchwartzMap

namespace SchwartzMap

private noncomputable def halfLineCutoff (ε r : ℝ) : ℂ :=
  (Real.smoothTransition (2 * r / ε + 1) : ℝ)

private lemma halfLineCutoff_zero {ε r : ℝ} (hε : 0 < ε) (hr : r ≤ -ε / 2) :
    halfLineCutoff ε r = 0 := by
  have h : 2 * r / ε + 1 ≤ 0 := by
    have := (div_le_iff₀ hε).mpr (show 2 * r ≤ (-1 : ℝ) * ε by linarith)
    linarith
  simp only [halfLineCutoff, Real.smoothTransition.zero_of_nonpos h, Complex.ofReal_zero]

private lemma halfLineCutoff_one {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    halfLineCutoff ε r = 1 := by
  have h : 1 ≤ 2 * r / ε + 1 := by
    linarith [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr) hε.le]
  simp only [halfLineCutoff, Real.smoothTransition.one_of_one_le h, Complex.ofReal_one]

private lemma halfLineCutoff_smooth (ε : ℝ) : ContDiff ℝ ∞ (halfLineCutoff ε) :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).div_const ε |>.add contDiff_const))

private lemma halfLineCutoff_mul_smooth {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Ioi (-ε))) :
    ContDiff ℝ ∞ (fun r ↦ halfLineCutoff ε r * f r) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r < -ε / 2
  · refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ ↦ (0 : ℂ)) r).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hr] with s hs
    rw [halfLineCutoff_zero hε hs.le, zero_mul]
  · have hr' : -ε < r := by linarith [le_of_not_gt hr]
    exact (halfLineCutoff_smooth ε).contDiffAt.mul (hf.contDiffAt (isOpen_Ioi.mem_nhds hr'))

/-- Extend a smooth profile from `(-ε,∞)` to a Schwartz function agreeing on `[0,∞)`.
Only derivative decay at positive infinity is required. -/
noncomputable def mkOfHalfLineSqrtDecay (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℂ)
    (smooth : ContDiffOn ℝ ∞ f (Ioi (-ε)))
    (decay : ∀ n : ℕ, ∃ b : ℝ, 0 < b ∧
      iteratedDeriv n f =O[atTop] (fun r ↦ Real.exp (-b * Real.sqrt r))) : 𝓢(ℝ, ℂ) :=
  mkOfSqrtExponentialDecay (fun r ↦ halfLineCutoff ε r * f r)
    (halfLineCutoff_mul_smooth hε smooth) fun n ↦ by
      obtain ⟨b, hb, hdecay⟩ := decay n
      obtain ⟨C, hC, hbound⟩ := hdecay.exists_nonneg
      refine ⟨b, hb, Asymptotics.IsBigO.of_bound C ?_⟩
      rw [cocompact_eq_atBot_atTop, eventually_sup]
      constructor
      · filter_upwards [eventually_lt_atBot (-ε)] with r hr
        have heq : (fun s ↦ halfLineCutoff ε s * f s) =ᶠ[𝓝 r] (fun _ ↦ (0 : ℂ)) := by
          filter_upwards [Iio_mem_nhds hr] with s hs
          change s < -ε at hs
          rw [halfLineCutoff_zero hε (by linarith), zero_mul]
        have hd := (heq.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds
        rw [hd, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        change ‖iteratedDeriv n (0 : ℝ → ℂ) r‖ ≤ _
        rw [iteratedDeriv_const_zero, norm_zero]
        exact mul_nonneg hC (norm_nonneg _)
      · filter_upwards [hbound.bound, eventually_gt_atTop (0 : ℝ)] with r hr hpos
        have heq : (fun s ↦ halfLineCutoff ε s * f s) =ᶠ[𝓝 r] f := by
          filter_upwards [Ioi_mem_nhds hpos] with s hs
          rw [halfLineCutoff_one hε hs.le, one_mul]
        rw [(heq.iteratedFDeriv (𝕜 := ℝ) n).eq_of_nhds, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
          Real.norm_of_nonneg hpos.le]
        exact hr

/-- The half-line extension preserves all values at nonnegative arguments. -/
theorem mkOfHalfLineSqrtDecay_apply_of_nonneg (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℂ)
    (smooth : ContDiffOn ℝ ∞ f (Ioi (-ε)))
    (decay : ∀ n : ℕ, ∃ b : ℝ, 0 < b ∧
      iteratedDeriv n f =O[atTop] (fun r ↦ Real.exp (-b * Real.sqrt r)))
    {r : ℝ} (hr : 0 ≤ r) : mkOfHalfLineSqrtDecay ε hε f smooth decay r = f r := by
  simp only [mkOfHalfLineSqrtDecay, mkOfSqrtExponentialDecay_apply]
  rw [halfLineCutoff_one hε hr, one_mul]

end SchwartzMap
