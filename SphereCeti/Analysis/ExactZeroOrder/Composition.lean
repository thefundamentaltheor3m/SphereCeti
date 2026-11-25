/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.ExactZeroOrder
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Exact zero orders under changes of variable

Composing a function with a differentiable real change of variable whose derivative is nonzero
preserves its exact zero order. This applies, for example, to the relation between a profile in
the squared radius and its expression in the radius at any nonzero radius.
-/

public section

open Filter
open scoped Topology

namespace SphereCeti

/-- A differentiable change of variable with nonzero derivative preserves exact zero order. -/
theorem HasExactZeroOrder.comp_hasDerivAt {f : ℝ → ℂ} {g : ℝ → ℝ} {a g' : ℝ} {m : ℕ}
    (hf : HasExactZeroOrder f (g a) m) (hg : HasDerivAt g g' a) (hg' : g' ≠ 0) :
    HasExactZeroOrder (fun x => f (g x)) a m := by
  obtain ⟨u, hu, hua, hfu⟩ := hasExactZeroOrder_iff.mp hf
  let v : ℝ → ℝ := dslope g a
  have hv : ContinuousAt (fun x => (v x : ℂ)) a :=
    Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_dslope_same.mpr hg.differentiableAt)
  have hva : (v a : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by simpa only [v, dslope_same, hg.deriv] using hg')
  apply hasExactZeroOrder_iff.mpr
  refine ⟨fun x => (v x : ℂ) ^ m * u (g x),
    (hv.pow m).mul (hu.comp hg.continuousAt),
    mul_ne_zero (pow_ne_zero m hva) hua, ?_⟩
  filter_upwards [hg.continuousAt.eventually hfu] with x hx
  have hdiff : (g x : ℂ) - g a = (x - a) * (v x : ℂ) := by
    have hreal : g x - g a = (x - a) * v x := by
      simpa only [v, smul_eq_mul] using (sub_smul_dslope g a x).symm
    exact_mod_cast hreal
  rw [hx, hdiff, mul_pow]
  ring

end SphereCeti
