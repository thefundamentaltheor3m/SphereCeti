/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Analysis.Complex.UpperHalfPlane.Integral
public import SphereCeti.Contour.SegmentContinuity
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# Absolute integrability of contour kernels built from a function decaying at `i∞`

Let `F : ℂ → ℂ` be continuous on the upper half-plane and `O(exp(-c Im τ))` at `i∞` for some
`c > 0`, let `k` be a natural number and let `E` be a finite-dimensional real inner product space.
Along a segment `z(t) = a + t (b - a)`, `0 < t ≤ 1`, a kernel `g` is absolutely integrable when
`‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` is integrable on `E × (0, 1]`.  This holds for the kernel
`F(-1/(z+1)) (z+1)^k` along the left legs `-1 → -1 + i → i`, for the kernel
`F(-1/(z-1)) (z-1)^k` along the right legs `1 → 1 + i → i`, and for the kernel `F(-1/z) z^k`
along the central leg `0 → i`.

## Main statements

* `SphereCeti.Contour.integrable_leftLegs_of_isBigO`: absolute integrability of
  `F(-1/(z+1)) (z+1)^k` along both left legs.
* `SphereCeti.Contour.integrable_rightLegs_of_isBigO`: absolute integrability of
  `F(-1/(z-1)) (z-1)^k` along both right legs.
* `SphereCeti.Contour.integrable_centralLeg_of_isBigO`: absolute integrability of `F(-1/z) z^k`
  along the central leg.
-/

public section

open Complex MeasureTheory Set
open UpperHalfPlane (atImInfty)
open scoped Real UpperHalfPlane

namespace SphereCeti.Contour

variable {F : ℂ → ℂ} {c : ℝ}

/-- `t ↦ ‖F(-1/(it)) (it)^k‖ t ^ s` is integrable on `(0, 1]` for every real `s`. -/
private lemma integrableOn_norm_kernel_mul_I (hc : 0 < c)
    (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) (k : ℕ) (s : ℝ) :
    IntegrableOn (fun t : ℝ ↦ ‖F (-1 / (t * I)) * (t * I) ^ k‖ * t ^ s) (Ioc 0 1) := by
  refine (UpperHalfPlane.integrableOn_norm_inv_mul_I_mul_rpow_Ioc_of_isBigO hc hF hO
    (k + s)).congr_fun (fun t (ht : t ∈ Ioc 0 1) ↦ ?_) measurableSet_Ioc
  have h : -1 / ((t : ℂ) * I) = ((t⁻¹ : ℝ) : ℂ) * I := by
    field_simp
    simp
  simp [h, Real.rpow_add ht.1, abs_of_pos ht.1, mul_assoc]

/-- For a continuous `w : ℝ → ℂ` with values in the upper half-plane,
`t ↦ ‖F(-1/w(t)) w(t)^k‖` is integrable on `(0, 1]`. -/
private lemma integrableOn_norm_kernel_comp (hF : ContinuousOn F {z : ℂ | 0 < z.im}) (k : ℕ)
    {w : ℝ → ℂ} (hw : Continuous w) (him : ∀ t, 0 < (w t).im) :
    IntegrableOn (fun t : ℝ ↦ ‖F (-1 / w t) * w t ^ k‖) (Ioc 0 1) := by
  have hne (t : ℝ) : w t ≠ 0 := fun h ↦ by simpa [h] using him t
  have hcont : Continuous fun t : ℝ ↦ F (-1 / w t) * w t ^ k :=
    (hF.comp_continuous (continuous_const.div hw hne)
      fun t ↦ TauCeti.im_neg_one_div_pos (him t)).mul (hw.pow k)
  exact hcont.norm.integrableOn_Ioc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Let `F : ℂ → ℂ` be continuous on the upper half-plane and `O(exp(-c Im τ))` at `i∞`, with
`0 < c`.  For every `k : ℕ`, the kernel `F(-1/(z+1)) (z+1)^k` satisfies the absolute
integrability of `g(z(t)) exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` along both left legs
`-1 → -1 + i` and `-1 + i → i`. -/
theorem integrable_leftLegs_of_isBigO (hc : 0 < c) (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) (k : ℕ) :
    ∀ p ∈ ({(-1, -1 + I), (-1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦
        ‖F (-1 / (p.1 + q.2 * (p.2 - p.1) + 1)) * (p.1 + q.2 * (p.2 - p.1) + 1) ^ k‖ *
          Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  rintro p (rfl | rfl)
  · refine integrable_prod_of_integrableOn_rpow (g := fun z ↦ F (-1 / (z + 1)) * (z + 1) ^ k)
      (fun t ht ↦ by simpa using ht.1) ?_
    refine (integrableOn_norm_kernel_mul_I hc hF hO k (-(Module.finrank ℝ E / 2 : ℝ))).congr_fun
      (fun t _ ↦ ?_) measurableSet_Ioc
    have h1 : (-1 : ℂ) + t * (-1 + I - -1) + 1 = t * I := by ring
    have h2 : ((-1 : ℂ) + t * (-1 + I - -1)).im = t := by simp
    simp only [h1, h2]
  · refine integrable_prod_of_integrableOn_rpow (g := fun z ↦ F (-1 / (z + 1)) * (z + 1) ^ k)
      (fun t _ ↦ by simp) ?_
    refine (integrableOn_norm_kernel_comp hF k (w := fun t : ℝ ↦ (t : ℂ) + I) (by fun_prop)
      fun t ↦ by simp).congr_fun (fun t _ ↦ ?_) measurableSet_Ioc
    have h1 : (-1 + I : ℂ) + t * (I - (-1 + I)) + 1 = t + I := by ring
    have h2 : ((-1 + I : ℂ) + t * (I - (-1 + I))).im = 1 := by simp
    simp only [h1, h2, Real.one_rpow, mul_one]

/-- Let `F : ℂ → ℂ` be continuous on the upper half-plane and `O(exp(-c Im τ))` at `i∞`, with
`0 < c`.  For every `k : ℕ`, the kernel `F(-1/(z-1)) (z-1)^k` satisfies the absolute
integrability of `g(z(t)) exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` along both right legs
`1 → 1 + i` and `1 + i → i`. -/
theorem integrable_rightLegs_of_isBigO (hc : 0 < c) (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) (k : ℕ) :
    ∀ p ∈ ({(1, 1 + I), (1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦
        ‖F (-1 / (p.1 + q.2 * (p.2 - p.1) - 1)) * (p.1 + q.2 * (p.2 - p.1) - 1) ^ k‖ *
          Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  rintro p (rfl | rfl)
  · refine integrable_prod_of_integrableOn_rpow (g := fun z ↦ F (-1 / (z - 1)) * (z - 1) ^ k)
      (fun t ht ↦ by simpa using ht.1) ?_
    refine (integrableOn_norm_kernel_mul_I hc hF hO k (-(Module.finrank ℝ E / 2 : ℝ))).congr_fun
      (fun t _ ↦ ?_) measurableSet_Ioc
    have h1 : (1 : ℂ) + t * (1 + I - 1) - 1 = t * I := by ring
    have h2 : ((1 : ℂ) + t * (1 + I - 1)).im = t := by simp
    simp only [h1, h2]
  · refine integrable_prod_of_integrableOn_rpow (g := fun z ↦ F (-1 / (z - 1)) * (z - 1) ^ k)
      (fun t _ ↦ by simp) ?_
    refine (integrableOn_norm_kernel_comp hF k (w := fun t : ℝ ↦ -(t : ℂ) + I) (by fun_prop)
      fun t ↦ by simp).congr_fun (fun t _ ↦ ?_) measurableSet_Ioc
    have h1 : (1 + I : ℂ) + t * (I - (1 + I)) - 1 = -(t : ℂ) + I := by ring
    have h2 : ((1 + I : ℂ) + t * (I - (1 + I))).im = 1 := by simp
    simp only [h1, h2, Real.one_rpow, mul_one]

/-- Let `F : ℂ → ℂ` be continuous on the upper half-plane and `O(exp(-c Im τ))` at `i∞`, with
`0 < c`.  For every `k : ℕ`, the kernel `F(-1/z) z^k` satisfies the absolute integrability of
`g(it) exp(-π ‖x‖² t)` on `E × (0, 1]` along the central leg `0 → i`. -/
theorem integrable_centralLeg_of_isBigO (hc : 0 < c) (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (-c * τ.im)) (k : ℕ) :
    Integrable (fun q : E × ℝ ↦
      ‖F (-1 / (q.2 * I)) * (q.2 * I) ^ k‖ * Real.exp (-π * ‖q.1‖ ^ 2 * q.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  simpa only [zero_add, sub_zero, mul_I_im, ofReal_re] using
    integrable_prod_of_integrableOn_rpow (E := E) (a := 0) (b := I)
      (g := fun z ↦ F (-1 / z) * z ^ k) (fun t ht ↦ by simpa using ht.1)
      ((integrableOn_norm_kernel_mul_I hc hF hO k (-(Module.finrank ℝ E / 2 : ℝ))).congr_fun
        (fun t _ ↦ by simp only [zero_add, sub_zero, mul_I_im, ofReal_re]) measurableSet_Ioc)

end SphereCeti.Contour
