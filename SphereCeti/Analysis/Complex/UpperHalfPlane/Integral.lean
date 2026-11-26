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

Let `F : ℂ → ℂ` be continuous on the upper half-plane and `O(exp(-c Im τ))` at `i∞` for some
`c > 0`.  Then `t ↦ F (t I) t ^ s` is integrable on `(a, ∞)` for every `a > 0` and every real `s`,
and `t ↦ ‖F (i / t)‖ t ^ s` is integrable on `(0, 1]` for every real `s`.

## Main statements

* `UpperHalfPlane.integrableOn_mul_I_mul_rpow_Ioi_of_isBigO`: for `0 < a` and `0 < c`,
  `t ↦ F (t I) t ^ s` is integrable on `(a, ∞)`.
* `UpperHalfPlane.integrableOn_mul_I_Ioi_of_isBigO`: for `0 < a` and `0 < c`,
  `t ↦ F (t I)` is integrable on `(a, ∞)`.
* `UpperHalfPlane.exists_norm_le_exp_mul_Ici`: a uniform exponential bound on the closed
  imaginary ray, from cusp Big-O and continuity.
* `UpperHalfPlane.integrableOn_norm_inv_mul_I_mul_rpow_Ioc_of_isBigO`: for `0 < c`,
  `t ↦ ‖F (i / t)‖ t ^ s` is integrable on `(0, 1]`.
-/

public section

open Complex Filter Asymptotics MeasureTheory

namespace UpperHalfPlane

/-- A function `F : ℂ → ℂ` that is continuous on the upper half-plane and is `O(exp(-c Im τ))`
at `i∞`, with `0 < c`, has `t ↦ F (t I) t ^ s` integrable on `(a, ∞)` for every `0 < a` and every
real `s`. -/
theorem integrableOn_mul_I_mul_rpow_Ioi_of_isBigO {F : ℂ → ℂ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) (s : ℝ) :
    IntegrableOn (fun t : ℝ ↦ F (t * Complex.I) * (t ^ s : ℝ)) (Set.Ioi a) := by
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
  -- `t ^ s = o(exp(c t / 2))`, so the weighted function is `O(exp(-c t / 2))`.
  have hO'' : (fun t : ℝ ↦ F (t * Complex.I) * (t ^ s : ℝ)) =O[atTop]
      fun t ↦ Real.exp (-(c / 2) * t) :=
    (hO'.mul (Complex.isBigO_ofReal_left.mpr
      (isLittleO_rpow_exp_pos_mul_atTop s (half_pos hc)).isBigO)).congr_right fun t ↦ by
        rw [← Real.exp_add]
        ring_nf
  have hcont : ContinuousOn (fun t : ℝ ↦ F (t * Complex.I) * (t ^ s : ℝ)) (Set.Ici a) := by
    refine .mul (hF.comp (by fun_prop) fun t (ht : a ≤ t) ↦ ?_)
      (continuous_ofReal.comp_continuousOn (continuousOn_id.rpow_const fun t (ht : a ≤ t) ↦ ?_))
    · simpa [Set.mem_ofPred_eq, him] using ha.trans_le ht
    · exact Or.inl (ha.trans_le ht).ne'
  exact (hcont.locallyIntegrableOn measurableSet_Ici |>.integrableOn_of_isBigO_atTop hO''
    ⟨Set.Ioi 0, Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 (half_pos hc)⟩).mono_set
    Set.Ioi_subset_Ici_self

/-- A function `F : ℂ → ℂ` that is continuous on the upper half-plane and is `O(exp(-c Im τ))`
at `i∞`, with `0 < c`, is integrable along the imaginary axis on `(a, ∞)` for every `0 < a`. -/
theorem integrableOn_mul_I_Ioi_of_isBigO {F : ℂ → ℂ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) :
    IntegrableOn (fun t : ℝ ↦ F (t * Complex.I)) (Set.Ioi a) := by
  simpa using integrableOn_mul_I_mul_rpow_Ioi_of_isBigO ha hc hF hO 0

/-- A function `F : ℂ → ℂ` that is continuous on the upper half-plane and is `O(exp(-c Im τ))`
at `i∞`, with `0 < c`, has `t ↦ ‖F (i / t)‖ t ^ s` integrable on `(0, 1]` for every real `s`. -/
theorem integrableOn_norm_inv_mul_I_mul_rpow_Ioc_of_isBigO {F : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) (s : ℝ) :
    IntegrableOn (fun t : ℝ ↦ ‖F ((t⁻¹ : ℝ) * Complex.I)‖ * t ^ s) (Set.Ioc 0 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have himage : (fun u : ℝ ↦ u⁻¹) '' Set.Ioi 1 = Set.Ioo 0 1 := by
    rw [Set.image_inv_eq_inv, Set.inv_Ioi₀ one_pos, inv_one]
  have hderiv : ∀ u ∈ Set.Ioi (1 : ℝ),
      HasDerivWithinAt (fun u : ℝ ↦ u⁻¹) (-(u ^ 2)⁻¹) (Set.Ioi 1) u :=
    fun u hu ↦ (hasDerivAt_inv (one_pos.trans hu).ne').hasDerivWithinAt
  rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
    inv_injective.injOn]
  refine IntegrableOn.congr_fun (integrableOn_mul_I_mul_rpow_Ioi_of_isBigO one_pos hc hF hO
    (-s - 2)).norm (fun u (hu : 1 < u) ↦ ?_) measurableSet_Ioi
  have hu0 : 0 < u := one_pos.trans hu
  simp [abs_of_pos (Real.rpow_pos_of_pos hu0 _), Real.inv_rpow hu0.le, Real.rpow_sub hu0,
    Real.rpow_neg hu0.le]
  ring

/-- An exponential Big-O estimate at the infinite cusp gives a uniform bound on the
closed imaginary ray starting at `i`. The exponent rate may have either sign. -/
theorem exists_norm_le_exp_mul_Ici {F : ℂ → ℂ} {a : ℝ}
    (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (a * τ.im)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Set.Ici (1 : ℝ), ‖F (t * Complex.I)‖ ≤ M * Real.exp (a * t) := by
  have htend : Tendsto (fun t : ℝ ↦ UpperHalfPlane.ofComplex (t * Complex.I)) atTop
      UpperHalfPlane.atImInfty :=
    UpperHalfPlane.tendsto_ofComplex_I_mul_atTop_atImInfty.congr fun t ↦ by rw [mul_comm]
  have hcoe {t : ℝ} (ht : 0 < t) :
      (UpperHalfPlane.ofComplex ((t : ℂ) * Complex.I) : ℂ) = (t : ℂ) * Complex.I := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (z := (t : ℂ) * Complex.I) (by simpa using ht)]
  have hO : (fun t : ℝ ↦ F (t * Complex.I)) =O[atTop] fun t ↦ Real.exp (a * t) := by
    refine (hO.comp_tendsto htend).congr' ?_ ?_ <;>
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    · simp only [Function.comp_apply, hcoe ht]
    · simp only [Function.comp_apply, UpperHalfPlane.im,
        hcoe ht]
      simp
  obtain ⟨C, hC, hbound⟩ := hO.exists_nonneg
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound.bound
  have hcont : ContinuousOn (fun t : ℝ ↦ ‖F (t * Complex.I)‖ * Real.exp (-a * t))
      (Set.Icc 1 (max 1 N)) := by
    refine (hF.comp (by fun_prop) fun t ht ↦ ?_).norm.mul (by fun_prop)
    simpa using (zero_lt_one.trans_le ht.1)
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C D, hC.trans (le_max_left _ _), fun t ht ↦ ?_⟩
  by_cases hNt : N ≤ t
  · have h := hN t hNt
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C D) (Real.exp_nonneg _))
  · have h := hD t ⟨ht, (lt_of_not_ge hNt).le.trans (le_max_right 1 N)⟩
    rw [Real.norm_of_nonneg (by positivity)] at h
    have h' := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (a * t))
    have he : Real.exp (-a * t) * Real.exp (a * t) = 1 := by
      rw [← Real.exp_add]
      have hsum : -a * t + a * t = 0 := by ring
      rw [hsum, Real.exp_zero]
    rw [mul_assoc, he, mul_one] at h'
    exact h'.trans (mul_le_mul_of_nonneg_right (le_max_right C D) (Real.exp_nonneg _))

end UpperHalfPlane
