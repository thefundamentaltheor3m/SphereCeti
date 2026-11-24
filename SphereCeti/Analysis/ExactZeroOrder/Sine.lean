/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.ExactZeroOrder
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Exact shell zeros of the squared sine factor

The profile factor `sin²(π r / 2)` has an exact double zero at every even integer `r = 2n`.
Here `r` is a squared-norm profile variable, so these are the shell values used by the E8 and
Leech auxiliary functions. The proof first establishes the simple zeros of `sin(π r / 2)` from
its nonzero derivative, then uses the product and power rules for `HasExactZeroOrder`.

Multiplication by a continuous factor nonzero at `2n` preserves the double zero. The existing
quantitative lower-bound theorem then gives the estimate needed for stability applications.
The hypotheses on the remaining factor must still be established for each concrete kernel;
this does not prove the exact zero sets or multiplicities of the magic functions themselves.

## References

* M. Viazovska, *The sphere packing problem in dimension 8*, arXiv:1603.04246, equation (62),
  contains the squared sine factor `sin²(π r² / 2)`. The variable here is its squared radius.
* README Layer 7, exact local zero orders through nonvanishing cofactors; Layer 9, shell zero
  orders; and MIGRATION K4, preservation of multiplicities and quantitative bounds.

This is an independent proof using Mathlib's trigonometric derivatives and divided differences.
The general exact-order rules extend the real-variable API listed in UPSTREAM A14.
-/

public section

open scoped Topology

namespace SphereCeti

/-- The sine shell factor has a simple zero at each even integer. -/
theorem hasExactZeroOrder_sin_pi_mul_div_two (n : ℤ) :
    HasExactZeroOrder (fun r : ℝ ↦ (Real.sin (Real.pi * r / 2) : ℂ))
      (2 * (n : ℝ)) 1 := by
  have harg : Real.pi * (2 * (n : ℝ)) / 2 = (n : ℝ) * Real.pi := by ring
  have hlin : HasDerivAt (fun r : ℝ ↦ Real.pi * r / 2) (Real.pi / 2) (2 * (n : ℝ)) := by
    simpa using ((hasDerivAt_id (2 * (n : ℝ))).const_mul Real.pi).div_const 2
  have hsin := ((Real.hasDerivAt_sin _).comp (2 * (n : ℝ)) hlin).ofReal_comp
  refine hasExactZeroOrder_one_of_hasDerivAt hsin ?_ ?_
  · simp [harg, Real.sin_int_mul_pi]
  · apply Complex.ofReal_ne_zero.mpr
    apply mul_ne_zero
    · rw [harg, Real.cos_int_mul_pi]
      exact zpow_ne_zero _ (by norm_num)
    · exact div_ne_zero Real.pi_ne_zero (by norm_num)

/-- Squaring the sine shell factor gives an exact double zero at each even integer. -/
theorem hasExactZeroOrder_sin_pi_mul_div_two_sq (n : ℤ) :
    HasExactZeroOrder (fun r : ℝ ↦ (Real.sin (Real.pi * r / 2) : ℂ) ^ 2)
      (2 * (n : ℝ)) 2 := by
  simpa using (hasExactZeroOrder_sin_pi_mul_div_two n).pow 2

/-- A continuous cofactor nonzero at a shell preserves the sine factor's double zero. -/
theorem hasExactZeroOrder_sin_pi_mul_div_two_sq_mul (n : ℤ) {g : ℝ → ℂ}
    (hg : ContinuousAt g (2 * (n : ℝ))) (hgn : g (2 * (n : ℝ)) ≠ 0) :
    HasExactZeroOrder (fun r : ℝ ↦ (Real.sin (Real.pi * r / 2) : ℂ) ^ 2 * g r)
      (2 * (n : ℝ)) 2 :=
  (hasExactZeroOrder_sin_pi_mul_div_two_sq n).mul_continuousAt hg hgn

/-- The shell factor times a nonvanishing continuous cofactor has the quantitative quadratic
lower bound required by the stability roadmap. -/
theorem sin_pi_mul_div_two_sq_mul_quantitativeLowerBound (n : ℤ) {g : ℝ → ℂ}
    (hg : ContinuousAt g (2 * (n : ℝ))) (hgn : g (2 * (n : ℝ)) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r in 𝓝 (2 * (n : ℝ)),
      c * |r - 2 * (n : ℝ)| ^ 2 ≤ ‖(Real.sin (Real.pi * r / 2) : ℂ) ^ 2 * g r‖ :=
  (hasExactZeroOrder_sin_pi_mul_div_two_sq_mul n hg hgn).quantitativeLowerBound

/-! ## Shell normalization checks -/

/-- The first positive shell is at squared norm two. -/
example : HasExactZeroOrder (fun r : ℝ ↦ (Real.sin (Real.pi * r / 2) : ℂ) ^ 2) 2 2 := by
  simpa using hasExactZeroOrder_sin_pi_mul_div_two_sq 1

/-- The same factor has order two at squared norm four, independently of the ambient dimension. -/
example : HasExactZeroOrder (fun r : ℝ ↦ (Real.sin (Real.pi * r / 2) : ℂ) ^ 2) 4 2 := by
  convert hasExactZeroOrder_sin_pi_mul_div_two_sq 2 using 1
  norm_num

end SphereCeti
