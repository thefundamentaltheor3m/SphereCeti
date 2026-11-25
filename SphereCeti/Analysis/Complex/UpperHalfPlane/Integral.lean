/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import TauCeti.Analysis.Complex.UpperHalfPlane.ResToImagAxis

/-!
# Integrability along the imaginary axis

A function `F : ℂ → ℂ` that is continuous on the upper half-plane and is `O(exp(-c Im τ))` at `i∞`
for some `c > 0` is integrable along the imaginary axis above any positive height.

## Main statements

* `UpperHalfPlane.integrableOn_mul_I_Ioi_of_isBigO`: for `0 < a` and `0 < c`,
  `t ↦ F (t I)` is integrable on `(a, ∞)`.
-/

public section

open Complex Filter Asymptotics MeasureTheory

namespace UpperHalfPlane

/-- A function `F : ℂ → ℂ` that is continuous on the upper half-plane and is `O(exp(-c Im τ))`
at `i∞`, with `0 < c`, is integrable along the imaginary axis on `(a, ∞)` for every `0 < a`. -/
theorem integrableOn_mul_I_Ioi_of_isBigO {F : ℂ → ℂ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) :
    IntegrableOn (fun t : ℝ ↦ F (t * Complex.I)) (Set.Ioi a) := by
  have him (t : ℝ) : ((t : ℂ) * Complex.I).im = t := by simp
  have hcoe {t : ℝ} (ht : 0 < t) : (ofComplex ((t : ℂ) * Complex.I) : ℂ) = t * Complex.I := by
    rw [ofComplex_apply_of_im_pos (by rwa [him])]
  have htend : Tendsto (fun t : ℝ ↦ ofComplex ((t : ℂ) * Complex.I)) atTop atImInfty :=
    tendsto_ofComplex_I_mul_atTop_atImInfty.congr fun t ↦ by rw [mul_comm]
  have hO' : (fun t : ℝ ↦ F (t * Complex.I)) =O[atTop] fun t ↦ Real.exp (-c * t) := by
    refine (hO.comp_tendsto htend).congr' ?_ ?_ <;>
      filter_upwards [eventually_gt_atTop 0] with t ht
    · simp only [Function.comp_apply, hcoe ht]
    · simp only [Function.comp_apply, UpperHalfPlane.im, hcoe ht, him]
  have hcont : ContinuousOn (fun t : ℝ ↦ F (t * Complex.I)) (Set.Ici a) :=
    hF.comp (by fun_prop) fun t (ht : a ≤ t) ↦ by
      simpa [Set.mem_ofPred_eq, him] using ha.trans_le ht
  exact (hcont.locallyIntegrableOn measurableSet_Ici |>.integrableOn_of_isBigO_atTop hO'
    ⟨Set.Ioi 0, Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 hc⟩).mono_set Set.Ioi_subset_Ici_self

end UpperHalfPlane
