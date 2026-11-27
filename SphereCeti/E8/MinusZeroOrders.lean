/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.E8.MinusZeros
public import SphereCeti.Analysis.ExactZeroOrder.Sine

/-!
# Exact double zeros of the E8 minus profile above the first shell

Local domination by an integrable Laplace kernel at a smaller squared radius makes the
Laplace cofactor continuous on `(2, ∞)`. Its strict positivity then preserves the exact
double zeros of the squared sine factor at squared radii `2n`, `n ≥ 2`.

This establishes the component multiplicity needed for the Layer 9 E8 shell analysis,
with quantitative quadratic lower bounds. The first shell and the assembled auxiliary
function require separate arguments.

The proof is independently written from the convergent representation in Viazovska
(2017), Section 5, equation (58), and Mathlib's dominated continuity theorem at
`1b1ccf4b088b32fa3f23f2de1127433254a81e1e`,
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`.
-/

public section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace SphereCeti.E8

/-- The Laplace cofactor varies continuously strictly inside its convergence range. -/
theorem continuousAt_minusLaplaceCofactor {r : ℝ} (hr : 2 < r) :
    ContinuousAt minusLaplaceCofactor r := by
  let s : ℝ := (r + 2) / 2
  have hs : 2 < s := by dsimp [s]; linarith
  have hsr : s < r := by dsimp [s]; linarith
  have hnear : ∀ᶠ x : ℝ in 𝓝 r, s < x := lt_mem_nhds hsr
  have he : minusLaplaceCofactor = fun x : ℝ ↦
      ∫ t : ℝ in Ioi 0, psiIExt (t * I) * cexp (-((π : ℂ) * x) * t) :=
    funext minusLaplaceCofactor_eq_integral
  rw [he]
  refine continuousAt_of_dominated
    (bound := fun t : ℝ ↦ ‖psiIExt (t * I) * cexp (-((π : ℂ) * s) * t)‖)
    ?_ ?_ (integrableOn_psiIExt_mul_exp_Ioi hs).norm ?_
  · filter_upwards [hnear] with x hx
    exact (integrableOn_psiIExt_mul_exp_Ioi (hs.trans hx)).aestronglyMeasurable
  · filter_upwards [hnear] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [norm_mul, norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, mul_zero, sub_zero]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (neg_le_neg (mul_le_mul_of_nonneg_left hx.le Real.pi_pos.le)) (le_of_lt ht)
  · exact .of_forall fun t ↦ by fun_prop

/-- Every later even shell is an exact double zero of the E8 minus profile.
The argument is in the squared-norm variable, not the radius. -/
theorem magicMinusProfile_hasExactZeroOrder (n : ℕ) (hn : 2 ≤ n) :
    HasExactZeroOrder magicMinusProfile (2 * (n : ℝ)) 2 := by
  have ha : (2 : ℝ) < 2 * (n : ℝ) := by exact_mod_cast (by omega : 2 < 2 * n)
  have hs : HasExactZeroOrder (fun r : ℝ ↦ (Real.sin (π * r / 2) : ℂ) ^ 2)
      (2 * (n : ℝ)) 2 := by
    simpa using hasExactZeroOrder_sin_pi_mul_div_two_sq (n : ℤ)
  have hg : ContinuousAt (fun r : ℝ ↦ (-4 * I : ℂ) * minusLaplaceCofactor r)
      (2 * (n : ℝ)) := continuousAt_const.mul (continuousAt_minusLaplaceCofactor ha)
  have hgn : (-4 * I : ℂ) * minusLaplaceCofactor (2 * (n : ℝ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (minusLaplaceCofactor_ne_zero ha)
  obtain ⟨g, hgc, hga, hfactor⟩ :=
    hasExactZeroOrder_iff.mp (hs.mul_continuousAt hg hgn)
  apply hasExactZeroOrder_iff.mpr
  refine ⟨g, hgc, hga, ?_⟩
  filter_upwards [hfactor, lt_mem_nhds ha] with r hrf hr
  rw [magicMinusProfile_eq_laplace hr, ← minusLaplaceCofactor_eq_integral]
  convert hrf using 1; push_cast; ring

example (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r in 𝓝 (2 * (n : ℝ)),
      c * |r - 2 * (n : ℝ)| ^ 2 ≤ ‖magicMinusProfile r‖ :=
  (magicMinusProfile_hasExactZeroOrder n hn).quantitativeLowerBound

end SphereCeti.E8
