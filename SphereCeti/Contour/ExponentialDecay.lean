/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Contour.HalfInfiniteRectangle
public import SphereCeti.Contour.SixPiece
public import SphereCeti.Analysis.Complex.UpperHalfPlane.Integral

/-!
# Exponential decay and deformation of a half-infinite rectangle

Uniform exponential decay at the upper-half-plane cusp controls horizontal edges and every
translated vertical ray. Holomorphy then permits deformation of a horizontal segment at height
one into the two vertical rays. The proof applies the existing top-edge-limit theorem.
-/

public section

open Complex Filter Asymptotics MeasureTheory Set Topology
open scoped Interval

namespace SphereCeti.Contour

/-- Multiplication by the radial exponential subtracts `π r` from a cusp growth exponent. -/
theorem isBigO_expKernel_of_growth {F : ℂ → ℂ} {a : ℝ} (r : ℝ)
    (hO : (fun τ : UpperHalfPlane ↦ F τ) =O[UpperHalfPlane.atImInfty]
      fun τ ↦ Real.exp (a * τ.im)) :
    (fun τ : UpperHalfPlane ↦ expKernel F r τ) =O[UpperHalfPlane.atImInfty]
      fun τ ↦ Real.exp ((a - Real.pi * r) * τ.im) := by
  have he : (fun τ : UpperHalfPlane ↦ cexp (Real.pi * I * r * τ))
      =O[UpperHalfPlane.atImInfty] fun τ ↦ Real.exp (-(Real.pi * r) * τ.im) := by
    apply Asymptotics.isBigO_of_le
    intro τ
    simp [norm_exp, mul_re, mul_im]
  refine ((hO.mul he).congr_left fun τ ↦ (expKernel_apply F r τ).symm).congr_right fun τ ↦ ?_
  rw [← Real.exp_add]
  congr 1
  ring

/-- Uniform exponential cusp decay makes horizontal-edge integrals tend to zero. -/
theorem tendsto_horizontal_integral_of_exp_decay {F : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hO : (fun τ : UpperHalfPlane ↦ F τ) =O[UpperHalfPlane.atImInfty]
      fun τ ↦ Real.exp (-c * τ.im)) (a b : ℝ) :
    Tendsto (fun y : ℝ ↦ ∫ x in a..b, F (x + y * I)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := hO.exists_nonneg
  obtain ⟨N, hN⟩ := (UpperHalfPlane.atImInfty_mem _).mp hbound.bound
  have hlim : Tendsto (fun y : ℝ ↦ C * Real.exp (-c * y) * |b - a|) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul, Function.comp_apply, id_eq] using
      ((Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hc))).const_mul C).mul_const |b - a|
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (max N 1)] with y hy
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x _
  have hpos : 0 < (x + y * I : ℂ).im := by
    simpa using zero_lt_one.trans_le ((le_max_right N 1).trans hy)
  have h := hN ⟨x + y * I, hpos⟩ (by
    simpa using (le_max_left N 1).trans hy)
  simpa only [Set.mem_ofPred_eq, UpperHalfPlane.coe_mk, UpperHalfPlane.im, add_im, ofReal_im,
    mul_im, ofReal_re, I_im,
    mul_one, I_re, mul_zero, add_zero, zero_add, Real.norm_of_nonneg (Real.exp_nonneg _)] using h

/-- Exponential cusp decay gives integrability on every translated vertical ray above height one. -/
theorem integrableOn_shift_mul_I_of_exp_decay {F : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hO : (fun τ : UpperHalfPlane ↦ F τ) =O[UpperHalfPlane.atImInfty]
      fun τ ↦ Real.exp (-c * τ.im)) (a : ℝ) :
    IntegrableOn (fun t : ℝ ↦ F (a + t * I)) (Ioi 1) := by
  obtain ⟨C, _hC, hbound⟩ := hO.exists_nonneg
  obtain ⟨N, hN⟩ := (UpperHalfPlane.atImInfty_mem _).mp hbound.bound
  have hO' : (fun t : ℝ ↦ F (a + t * I)) =O[atTop] fun t ↦ Real.exp (-c * t) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (max N 1)] with t ht
    have hpos : 0 < (a + t * I : ℂ).im := by
      simpa using zero_lt_one.trans_le ((le_max_right N 1).trans ht)
    have h := hN ⟨a + t * I, hpos⟩ (by simpa using (le_max_left N 1).trans ht)
    simpa only [Set.mem_ofPred_eq, UpperHalfPlane.coe_mk, UpperHalfPlane.im, add_im, ofReal_im,
    mul_im, ofReal_re, I_im,
      mul_one, I_re, mul_zero, add_zero, zero_add] using h
  have hcont : ContinuousOn (fun t : ℝ ↦ F (a + t * I)) (Ici 1) :=
    hF.comp (by fun_prop) fun t ht ↦ by simpa using zero_lt_one.trans_le ht
  exact (hcont.locallyIntegrableOn measurableSet_Ici |>.integrableOn_of_isBigO_atTop hO'
    ⟨Ioi 0, Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 hc⟩).mono_set Ioi_subset_Ici_self

/-- Move a horizontal segment at height one to two vertical rays using exponential decay. -/
theorem horizontal_add_vertical_eq_vertical_of_exp_decay {F : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hO : (fun τ : UpperHalfPlane ↦ F τ) =O[UpperHalfPlane.atImInfty]
      fun τ ↦ Real.exp (-c * τ.im)) (a b : ℝ) :
    (∫ x in a..b, F (x + I)) + I * ∫ t in Ioi (1 : ℝ), F (b + t * I) =
      I * ∫ t in Ioi (1 : ℝ), F (a + t * I) := by
  have h := horizontal_add_vertical_eq_vertical_of_tendsto_top (f := F)
    (x₁ := a) (x₂ := b) (y := 1) (s := ∅) countable_empty ?_ ?_
    (integrableOn_shift_mul_I_of_exp_decay hc hF.continuousOn hO a)
    (integrableOn_shift_mul_I_of_exp_decay hc hF.continuousOn hO b)
    (tendsto_horizontal_integral_of_exp_decay hc hO a b)
  · simpa only [ofReal_one, one_mul, smul_eq_mul] using h
  · exact hF.continuousOn.mono fun z hz ↦ zero_lt_one.trans_le hz.2
  · intro z hz
    exact hF.differentiableAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (zero_lt_one.trans hz.1.2))

end SphereCeti.Contour
