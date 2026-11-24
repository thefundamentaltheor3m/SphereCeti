/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.SegmentContinuity
public import SphereCeti.E8.PlusKernels
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Absolute integrability of the `+1` E8 kernels

Let `E` be a real inner product space of dimension `8`.  The Fourier identities of the left and
central legs of the magic contour need the kernel `g` to satisfy the absolute integrability of
`g(z(t)) exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` along each leg `z(t)`.  For the kernels of the
`+1` eigencomponent of the E8 magic function this holds on the two left legs `-1 → -1 + i → i`,
the two right legs `1 → 1 + i → i` and the central leg `0 → i`.

On the first left leg, the first right leg and the central leg the kernels involve `φ₀(i/t)`, which
decays like `exp(-2π/t)` as `t → 0`; on the second leg of each pair the kernel is continuous.

## Main statements

* `SphereCeti.E8.integrableOn_norm_phi0Ext_inv_mul_I`: `t ↦ ‖φ₀(i/t)‖ t⁻²` is integrable on
  `(0, 1]`.
* `SphereCeti.E8.integrable_plusKernelLeft`, `SphereCeti.E8.integrable_plusKernelRight`: absolute
  integrability of the left-leg and right-leg kernels along both legs of each pair.
* `SphereCeti.E8.integrable_plusKernelCentral`: absolute integrability of the central-leg kernel.
-/

public section

open Complex MeasureTheory Set
open scoped Real

namespace SphereCeti.E8

/-- `t ↦ ‖φ₀(i/t)‖ t⁻²` is integrable on `(0, 1]`: the substitution `u = 1/t` turns it into
`u ↦ ‖φ₀(iu)‖` on `(1, ∞)`. -/
theorem integrableOn_norm_phi0Ext_inv_mul_I :
    IntegrableOn (fun t : ℝ ↦ ‖phi0Ext ((t⁻¹ : ℝ) * I)‖ * t ^ (-2 : ℝ)) (Ioc 0 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  have himage : (fun u : ℝ ↦ u⁻¹) '' Ioi 1 = Ioo 0 1 := by
    rw [Set.image_inv_eq_inv, Set.inv_Ioi₀ one_pos, inv_one]
  have hderiv : ∀ u ∈ Ioi (1 : ℝ), HasDerivWithinAt (fun u : ℝ ↦ u⁻¹) (-(u ^ 2)⁻¹) (Ioi 1) u :=
    fun u hu ↦ (hasDerivAt_inv (by linarith [mem_Ioi.mp hu] : u ≠ 0)).hasDerivWithinAt
  rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
    inv_injective.injOn]
  refine IntegrableOn.congr_fun (f := fun u : ℝ ↦ ‖phi0Ext (u * I)‖)
    integrableOn_phi0Ext_mul_I.norm (fun u hu ↦ ?_) measurableSet_Ioi
  have hu : 0 < u := lt_trans one_pos hu
  simp only [smul_eq_mul, abs_neg, inv_inv]
  rw [abs_of_pos (by positivity), Real.inv_rpow hu.le, Real.rpow_neg hu.le, inv_inv,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp

/-- `-1 / (it) = i / t` for real `t`. -/
private lemma neg_one_div_ofReal_mul_I (t : ℝ) : -1 / ((t : ℂ) * I) = ((t⁻¹ : ℝ) : ℂ) * I := by
  rw [neg_div, one_div, ofReal_inv, mul_inv, inv_I]
  ring

/-- For `t > 0`, `‖φ₀(i/t)‖ t² t⁻⁴ = ‖φ₀(i/t)‖ t⁻²`. -/
private lemma rpow_identity {t : ℝ} (ht : 0 < t) (c : ℝ) :
    c * t ^ 2 * t ^ (-(8 / 2 : ℝ)) = c * t ^ (-2 : ℝ) := by
  rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add ht]
  norm_num

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- In dimension `8`, the left-leg kernel `φ₀(-1/(z+1)) (z+1)²` satisfies the absolute
integrability of `g(z(t)) exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` along both left legs
`-1 → -1 + i` and `-1 + i → i`. -/
theorem integrable_plusKernelLeft (hE : Module.finrank ℝ E = 8) :
    ∀ p ∈ ({(-1, -1 + I), (-1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖plusKernelLeft (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  rintro p (rfl | rfl)
  · -- On `-1 → -1 + i`, `z + 1 = it` and the kernel is `-t² φ₀(i/t)`.
    refine Contour.integrable_prod_of_integrableOn_rpow (fun t ht ↦ by simpa using ht.1) ?_
    refine integrableOn_norm_phi0Ext_inv_mul_I.congr_fun (fun t ht ↦ ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    have h1 : (-1 : ℂ) + t * (-1 + I - -1) + 1 = t * I := by ring
    have h2 : ((-1 : ℂ) + t * (-1 + I - -1)).im = t := by simp
    rw [hE, plusKernelLeft_def, h1, h2, neg_one_div_ofReal_mul_I, norm_mul, norm_pow, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le, Nat.cast_ofNat,
      rpow_identity ht0]
  · -- On `-1 + i → i`, `z + 1 = t + i` and the kernel is continuous in `t`.
    refine Contour.integrable_prod_of_integrableOn_rpow (fun t ht ↦ by simp) ?_
    have h1 (t : ℝ) : (-1 + I : ℂ) + t * (I - (-1 + I)) + 1 = t + I := by ring
    have h2 (t : ℝ) : ((-1 + I : ℂ) + t * (I - (-1 + I))).im = 1 := by simp
    have hmem (t : ℝ) : -1 / ((t : ℂ) + I) ∈ {z : ℂ | 0 < z.im} := by
      have hne : (t : ℂ) + I ≠ 0 := fun h ↦ by simpa using congrArg Complex.im h
      show 0 < (-1 / ((t : ℂ) + I)).im
      rw [div_im]
      simp only [neg_re, one_re, neg_im, one_im, neg_zero, zero_mul, zero_div, add_im, ofReal_im,
        I_im, zero_add, mul_one, zero_sub, neg_div, neg_neg]
      exact div_pos one_pos (normSq_pos.mpr hne)
    have hcont : Continuous fun t : ℝ ↦ phi0Ext (-1 / ((t : ℂ) + I)) * ((t : ℂ) + I) ^ 2 :=
      (continuousOn_phi0Ext.comp_continuous (by
        refine Continuous.div continuous_const (by fun_prop) fun t h ↦ ?_
        simpa using congrArg Complex.im h) hmem).mul (by fun_prop)
    refine ((hcont.norm.continuousOn (s := Icc 0 1)).integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self |>.congr_fun (fun t _ ↦ ?_) measurableSet_Ioc
    rw [plusKernelLeft_def, h1, h2, Real.one_rpow, mul_one]

/-- In dimension `8`, the right-leg kernel `φ₀(-1/(z-1)) (z-1)²` satisfies the absolute
integrability of `g(z(t)) exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` along both right legs
`1 → 1 + i` and `1 + i → i`. -/
theorem integrable_plusKernelRight (hE : Module.finrank ℝ E = 8) :
    ∀ p ∈ ({(1, 1 + I), (1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖plusKernelRight (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  rintro p (rfl | rfl)
  · -- On `1 → 1 + i`, `z - 1 = it` and the kernel is `-t² φ₀(i/t)`.
    refine Contour.integrable_prod_of_integrableOn_rpow (fun t ht ↦ by simpa using ht.1) ?_
    refine integrableOn_norm_phi0Ext_inv_mul_I.congr_fun (fun t ht ↦ ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    have h1 : (1 : ℂ) + t * (1 + I - 1) - 1 = t * I := by ring
    have h2 : ((1 : ℂ) + t * (1 + I - 1)).im = t := by simp
    rw [hE, plusKernelRight_def, h1, h2, neg_one_div_ofReal_mul_I, norm_mul, norm_pow, norm_mul,
      Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le, Nat.cast_ofNat,
      rpow_identity ht0]
  · -- On `1 + i → i`, `z - 1 = i - t` and the kernel is continuous in `t`.
    refine Contour.integrable_prod_of_integrableOn_rpow (fun t ht ↦ by simp) ?_
    have h1 (t : ℝ) : (1 + I : ℂ) + t * (I - (1 + I)) - 1 = -(t : ℂ) + I := by ring
    have h2 (t : ℝ) : ((1 + I : ℂ) + t * (I - (1 + I))).im = 1 := by simp
    have hmem (t : ℝ) : -1 / (-(t : ℂ) + I) ∈ {z : ℂ | 0 < z.im} := by
      have hne : -(t : ℂ) + I ≠ 0 := fun h ↦ by simpa using congrArg Complex.im h
      show 0 < (-1 / (-(t : ℂ) + I)).im
      rw [div_im]
      simp only [neg_re, one_re, neg_im, one_im, neg_zero, zero_mul, zero_div, add_im, ofReal_im,
        I_im, zero_add, mul_one, zero_sub, neg_div, neg_neg]
      exact div_pos one_pos (normSq_pos.mpr hne)
    have hcont : Continuous fun t : ℝ ↦ phi0Ext (-1 / (-(t : ℂ) + I)) * (-(t : ℂ) + I) ^ 2 :=
      (continuousOn_phi0Ext.comp_continuous (by
        refine Continuous.div continuous_const (by fun_prop) fun t h ↦ ?_
        simpa using congrArg Complex.im h) hmem).mul (by fun_prop)
    refine ((hcont.norm.continuousOn (s := Icc 0 1)).integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self |>.congr_fun (fun t _ ↦ ?_) measurableSet_Ioc
    rw [plusKernelRight_def, h1, h2, Real.one_rpow, mul_one]

/-- In dimension `8`, the central-leg kernel `-2 φ₀(-1/z) z²` satisfies the absolute
integrability of `g(it) exp(-π ‖x‖² t)` on `E × (0, 1]`. -/
theorem integrable_plusKernelCentral (hE : Module.finrank ℝ E = 8) :
    Integrable (fun q : E × ℝ ↦ ‖plusKernelCentral (q.2 * I)‖ * Real.exp (-π * ‖q.1‖ ^ 2 * q.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  have hg : IntegrableOn (fun t : ℝ ↦ ‖plusKernelCentral (0 + t * (I - 0))‖ *
      (0 + t * (I - 0)).im ^ (-(Module.finrank ℝ E / 2 : ℝ))) (Ioc 0 1) := by
    refine IntegrableOn.congr_fun
      (f := fun t : ℝ ↦ 2 * (‖phi0Ext ((t⁻¹ : ℝ) * I)‖ * t ^ (-2 : ℝ)))
      (integrableOn_norm_phi0Ext_inv_mul_I.const_mul 2) (fun t ht ↦ ?_) measurableSet_Ioc
    have ht0 : 0 < t := ht.1
    have h2 : ((0 : ℂ) + t * (I - 0)).im = t := by simp
    rw [hE, h2, zero_add, sub_zero, plusKernelCentral_def, neg_one_div_ofReal_mul_I, norm_mul,
      norm_neg, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg ht0.le, Complex.norm_two, Nat.cast_ofNat, mul_assoc,
      rpow_identity ht0]
  simpa using Contour.integrable_prod_of_integrableOn_rpow (E := E) (a := 0) (b := I)
    (fun t ht ↦ by simpa using ht.1) hg

end SphereCeti.E8
