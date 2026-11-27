/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.Distribution.SchwartzSpace.Laplace
public import SphereCeti.Contour.SixPiece
public import SphereCeti.Analysis.Complex.UpperHalfPlane.Integral
import SphereCeti.Analysis.Complex.UpperHalfPlane.Cone
import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Schwartz profiles for inverted cusp contours

An exponentially decaying holomorphic kernel gives a Schwartz profile for its six-piece
inverted contour. The inversion power and the ray coefficient remain explicit. The profile
agrees with the contour at every nonnegative argument.

The contour decomposition and cutoff strategy generalize
`SphereCeti/E8/MinusSchwartz.lean` at SphereCeti commit
`6eb8fea47c91e79696bf378e8a5b3ecf5bf8b2f0`. That construction adapts
`SpherePacking/MagicFunction/b/Schwartz/Basic.lean` in Sphere-Packing-Lean commit
`01f23eccf963c50250c9e48dd103e8cc88c36f85` (Sidharth Hariharan, Apache-2.0).
-/

public section

open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology Real SchwartzMap FourierTransform

namespace SphereCeti.Contour

private noncomputable def cuspKernel (F : ℂ → ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  F (-1 / z) * z ^ k

private theorem cuspKernel_cont {F : ℂ → ℂ} (k : ℕ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im}) :
    ContinuousOn (cuspKernel F k) {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.differentiableOn_neg_one_div_mul_pow hF k).continuousOn

private theorem cuspKernel_bound {F : ℂ → ℂ} {b M : ℝ} (k : ℕ) (hM : 0 ≤ M)
    (hbound : ∀ t ∈ Ici (1 : ℝ), ‖F (t * I)‖ ≤ M * Real.exp (-b * t))
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖cuspKernel F k (t * I)‖ ≤ M * Real.exp (-b / t) := by
  have hinv : -1 / ((t : ℂ) * I) = ((t⁻¹ : ℝ) : ℂ) * I := by field_simp; simp
  rw [cuspKernel, hinv, norm_mul, norm_pow, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht.1, norm_I, mul_one]
  have hi : 1 ≤ t⁻¹ := (one_le_inv₀ ht.1).mpr ht.2
  calc
    ‖F ((t⁻¹ : ℝ) * I)‖ * t ^ k ≤ (M * Real.exp (-b * t⁻¹)) * 1 :=
      mul_le_mul (hbound _ hi) (pow_le_one₀ ht.1.le ht.2)
        (pow_nonneg ht.1.le k) (mul_nonneg hM (Real.exp_nonneg _))
    _ = _ := by rw [mul_one, div_eq_mul_inv]

private theorem cuspKernel_integrable {F : ℂ → ℂ} {b M : ℝ} (k : ℕ) (hb : 0 < b)
    (hM : 0 ≤ M) (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hbound : ∀ t ∈ Ici (1 : ℝ), ‖F (t * I)‖ ≤ M * Real.exp (-b * t)) :
    IntegrableOn (fun t : ℝ ↦ cuspKernel F k (t * I)) (Ioc 0 1) := by
  have hcont : ContinuousOn (fun t : ℝ ↦ cuspKernel F k (t * I)) (Ioc (0 : ℝ) 1) :=
    (cuspKernel_cont k hF).comp (by fun_prop) fun t ht ↦ by simpa using ht.1
  refine (integrableOn_const measure_Ioc_lt_top.ne (C := M)).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  refine (cuspKernel_bound k hM hbound t ht).trans ?_
  have he : Real.exp (-b / t) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) ht.1.le)
  exact (mul_le_mul_of_nonneg_left he hM).trans_eq (mul_one _)

private noncomputable def centralProfile {F : ℂ → ℂ} {b M : ℝ} (k : ℕ) (hb : 0 < b)
    (hM : 0 ≤ M) (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hbound : ∀ t ∈ Ici (1 : ℝ), ‖F (t * I)‖ ≤ M * Real.exp (-b * t)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.ofFiniteLaplace hb one_pos (cuspKernel_integrable k hb hM hF hbound)
    (cuspKernel_bound k hM hbound) (π : ℂ) (by simpa using Real.pi_pos)

private theorem centralProfile_apply {F : ℂ → ℂ} {b M : ℝ} (k : ℕ) (hb : 0 < b)
    (hM : 0 ≤ M) (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hbound : ∀ t ∈ Ici (1 : ℝ), ‖F (t * I)‖ ≤ M * Real.exp (-b * t))
    {r : ℝ} (hr : 0 ≤ r) :
    centralProfile k hb hM hF hbound r =
      ∫ (t : ℝ) in Ioc 0 1, cuspKernel F k (t * I) * cexp (-((π : ℂ) * r) * t) := by
  unfold centralProfile
  exact SchwartzMap.ofFiniteLaplace_apply_of_nonneg _ _ _ _ _ _ hr

private theorem shifted_cuspKernel_cont {F : ℂ → ℂ} (k : ℕ)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im}) (a : ℝ) :
    ContinuousOn (fun z : ℂ ↦ cuspKernel F k (z + a)) {z : ℂ | 0 < z.im} :=
  (cuspKernel_cont k hF).comp (by fun_prop) fun z hz ↦ by simpa using hz

private noncomputable def horizontalPoint (a b t : ℝ) : ℂ := a + t * (b - a) + I

private noncomputable def horizontalCoeff (a b t : ℝ) : ℂ := (π : ℂ) * I * horizontalPoint a b t

private lemma horizontalPoint_im (a b t : ℝ) : (horizontalPoint a b t).im = 1 := by
  simp [horizontalPoint]

private lemma horizontalCoeff_re (a b t : ℝ) : (horizontalCoeff a b t).re = -π := by
  simp [horizontalCoeff, mul_re, mul_im, horizontalPoint_im]

private lemma continuous_horizontalPoint (a b : ℝ) : Continuous (horizontalPoint a b) := by
  unfold horizontalPoint
  fun_prop

private lemma continuous_horizontalCoeff (a b : ℝ) : Continuous (horizontalCoeff a b) :=
  continuous_const.mul (continuous_horizontalPoint a b)

private lemma exists_horizontal_bound (a b : ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ t ∈ Ioc (0 : ℝ) 1, ‖horizontalCoeff a b t‖ ≤ K := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuous_horizontalCoeff a b).continuousOn
  exact ⟨max K 0, le_max_right _ _, fun t ht ↦
    (hK t (Ioc_subset_Icc_self ht)).trans (le_max_left _ _)⟩

private lemma integrable_horizontal {g : ℂ → ℂ}
    (hg : ContinuousOn g {z : ℂ | 0 < z.im}) (a b : ℝ) :
    IntegrableOn (fun t : ℝ ↦ g (horizontalPoint a b t) * (b - a : ℝ)) (Ioc 0 1) := by
  have hcont : Continuous (fun t : ℝ ↦ g (horizontalPoint a b t) * (b - a : ℝ)) :=
    (hg.comp_continuous (continuous_horizontalPoint a b)
      (fun t ↦ by simp [horizontalPoint_im])).mul continuous_const
  exact hcont.integrableOn_Ioc

private noncomputable def horizontalSchwartz {g : ℂ → ℂ}
    (hg : ContinuousOn g {z : ℂ | 0 < z.im}) (a b : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.ofExponentialIntegral (integrable_horizontal hg a b)
    (continuous_horizontalCoeff a b).aestronglyMeasurable
    (Classical.choose_spec (exists_horizontal_bound a b)).1
    (ae_restrict_of_forall_mem measurableSet_Ioc
      (Classical.choose_spec (exists_horizontal_bound a b)).2)
    Real.pi_pos (.of_forall fun t ↦ (horizontalCoeff_re a b t).le)

private lemma horizontalSchwartz_apply {g : ℂ → ℂ}
    (hg : ContinuousOn g {z : ℂ | 0 < z.im}) (a b : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    horizontalSchwartz hg a b r = ∫ (t : ℝ) in Ioc 0 1,
      (g (horizontalPoint a b t) * (b - a : ℝ)) * cexp ((r : ℂ) * horizontalCoeff a b t) := by
  unfold horizontalSchwartz
  exact SchwartzMap.ofExponentialIntegral_apply_of_nonneg _ _ _ _ _ _ hr

private noncomputable def rayProfile {F : ℂ → ℂ} {b M : ℝ} (hb : 0 < b)
    (hM : 0 ≤ M) (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hbound : ∀ t ∈ Ici (1 : ℝ), ‖F (t * I)‖ ≤ M * Real.exp (-b * t)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.ofLaplaceTail
    (by
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      exact hF.continuousOn.comp (by fun_prop) fun t ht ↦ by
        simpa using (zero_lt_one.trans ht))
    hb Real.pi_pos hM (fun _t ht ↦ hbound _ ht.le)

private theorem rayProfile_apply {F : ℂ → ℂ} {b M : ℝ} (hb : 0 < b)
    (hM : 0 ≤ M) (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hbound : ∀ t ∈ Ici (1 : ℝ), ‖F (t * I)‖ ≤ M * Real.exp (-b * t))
    {r : ℝ} (hr : 0 ≤ r) :
    rayProfile hb hM hF hbound r =
      ∫ (t : ℝ) in Ioi 1, F (t * I) * cexp (-((π : ℂ) * r) * t) := by
  unfold rayProfile
  exact SchwartzMap.ofLaplaceTail_apply_of_nonneg _ _ _ _ _ hr

/-- A Schwartz profile for the contour with inversion power `k` and ray coefficient `c`.
Its nonnegative values are identified with the prescribed contour below. -/
noncomputable def schwartzProfile {F : ℂ → ℂ} {b M : ℝ} (k : ℕ) (c : ℂ) (hb : 0 < b)
    (hM : 0 ≤ M) (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hbound : ∀ t ∈ Ici (1 : ℝ), ‖F (t * I)‖ ≤ M * Real.exp (-b * t)) : 𝓢(ℝ, ℂ) :=
  (I : ℂ) • (SchwartzMap.smulLeftCLM ℂ (fun r : ℝ ↦ cexp ((-π * r : ℝ) * I))
      (centralProfile k hb hM hF hbound) +
    SchwartzMap.smulLeftCLM ℂ (fun r : ℝ ↦ cexp ((π * r : ℝ) * I))
      (centralProfile k hb hM hF hbound) -
    (2 : ℂ) • centralProfile k hb hM hF hbound) +
    horizontalSchwartz (shifted_cuspKernel_cont k hF 1) (-1) 0 +
    horizontalSchwartz (shifted_cuspKernel_cont k hF (-1)) 1 0 +
    (c * I : ℂ) • rayProfile hb hM hF hbound

/-- Separate the phase along a translated vertical segment. -/
theorem integral_vertical_expKernel (F : ℂ → ℂ) (a r : ℝ) :
    (∫ (t : ℝ) in Ioc 0 1, F ((a : ℂ) + t * I) *
      cexp ((π : ℂ) * I * r * ((a : ℂ) + t * I)) * I) =
      I * cexp ((π * a * r : ℝ) * I) *
        ∫ (t : ℝ) in Ioc 0 1, F ((a : ℂ) + t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  dsimp only
  have he : (π : ℂ) * I * r * ((a : ℂ) + t * I) =
      ((π * a * r : ℝ) : ℂ) * I + -((π : ℂ) * r) * t := by
    push_cast
    ring_nf
    simp [sub_eq_add_neg]
  rw [he, Complex.exp_add]
  ring

/-- Parametrize a horizontal segment in the exponential contour integral. -/
theorem integral_horizontal_expKernel (g : ℂ → ℂ) (a b r : ℝ) :
    (∫ᶜ z in Path.segment ((a : ℂ) + I) ((b : ℂ) + I),
        Contour.scalarOneForm (Contour.expKernel g r) z) =
      ∫ (t : ℝ) in Ioc 0 1, (g (((a : ℂ) + t * (b - a) + I)) * (b - a : ℝ)) *
        cexp ((r : ℂ) * ((π : ℂ) * I * ((a : ℂ) + t * (b - a) + I))) := by
  rw [Contour.curveIntegral_segment_scalarOneForm, intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  dsimp only
  have hz : (a : ℂ) + I + t * ((b + I) - (a + I)) = ((a : ℂ) + t * (b - a) + I) := by
    ring
  have hd : (b + I : ℂ) - (a + I) = ((b - a : ℝ) : ℂ) := by push_cast; ring
  rw [Contour.expKernel_apply, hz, hd]
  have he : (π : ℂ) * I * r * ((a : ℂ) + t * (b - a) + I) =
      (r : ℂ) * ((π : ℂ) * I * ((a : ℂ) + t * (b - a) + I)) := by ring
  rw [he]
  ring


private theorem vertical_cusp (F : ℂ → ℂ) (k : ℕ) (a r : ℝ) :
    (∫ᶜ z in Path.segment (a : ℂ) (a + I),
      scalarOneForm (expKernel (fun z ↦ cuspKernel F k (z - a)) r) z) =
      I * cexp ((π * a * r : ℝ) * I) *
        ∫ (t : ℝ) in Ioc 0 1, cuspKernel F k (t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [curveIntegral_segment_scalarOneForm, intervalIntegral.integral_of_le zero_le_one]
  simp only [expKernel_apply, add_sub_cancel_left]
  simpa only [add_sub_cancel_left] using
    integral_vertical_expKernel (fun z ↦ cuspKernel F k (z - a)) a r

private theorem central_cusp (F : ℂ → ℂ) (k : ℕ) (r : ℝ) :
    centralLeg (expKernel (fun z ↦ -2 * cuspKernel F k z) r) =
      (-2 * I) * ∫ (t : ℝ) in Ioc 0 1,
        cuspKernel F k (t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [centralLeg_def, curveIntegral_segment_scalarOneForm,
    intervalIntegral.integral_of_le zero_le_one]
  simp only [expKernel_apply, sub_zero, zero_add]
  have h := integral_vertical_expKernel (fun z ↦ -2 * cuspKernel F k z) 0 r
  simp only [Complex.ofReal_zero, zero_add, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h
  rw [h, ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  dsimp only
  ring

private theorem ray_cusp (F : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    verticalRay (expKernel (fun z ↦ c * F z) r) =
      (c * I) * ∫ (t : ℝ) in Ioi 1, F (t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [verticalRay_def, ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [expKernel_apply]
  have he : (π : ℂ) * I * r * ((t : ℂ) * I) = -((π : ℂ) * r) * t := by
    ring_nf
    simp
  rw [he]
  ring

/-- The Schwartz profile equals the six-piece inverted cusp contour for every nonnegative
parameter. The ray coefficient `c` is retained, including its sign. -/
theorem schwartzProfile_eq_contour {F : ℂ → ℂ} {b M : ℝ} (k : ℕ) (c : ℂ) (hb : 0 < b)
    (hM : 0 ≤ M) (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hbound : ∀ t ∈ Ici (1 : ℝ), ‖F (t * I)‖ ≤ M * Real.exp (-b * t))
    {r : ℝ} (hr : 0 ≤ r) :
    schwartzProfile k c hb hM hF hbound r =
      leftLegs (expKernel (fun z ↦ F (-1 / (z + 1)) * (z + 1) ^ k) r) +
      rightLegs (expKernel (fun z ↦ F (-1 / (z - 1)) * (z - 1) ^ k) r) +
      centralLeg (expKernel (fun z ↦ -2 * (F (-1 / z) * z ^ k)) r) +
      verticalRay (expKernel (fun z ↦ c * F z) r) := by
  have hphase (a : ℝ) : (fun r : ℝ ↦ cexp ((a * r : ℝ) * I)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)
  have hL := vertical_cusp F k (-1) r
  have hR := vertical_cusp F k 1 r
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one, sub_neg_eq_add, mul_neg_one] at hL
  simp only [Complex.ofReal_one, mul_one] at hR
  have hC := central_cusp F k r
  simp only [cuspKernel] at hL hR hC
  simp only [leftLegs_def, rightLegs_def]
  -- Parametrizing first removes dependent path endpoints before normalizing the casts.
  simp only [curveIntegral_segment_scalarOneForm] at hL hR ⊢
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one] at hL
  rw [hL, hR, hC, ray_cusp]
  have hl := integral_horizontal_expKernel (fun z ↦ cuspKernel F k (z + 1)) (-1) 0 r
  have hr' := integral_horizontal_expKernel (fun z ↦ cuspKernel F k (z - 1)) 1 0 r
  simp only [cuspKernel, curveIntegral_segment_scalarOneForm] at hl hr'
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero, zero_add] at hl hr'
  rw [hl, hr']
  simp only [schwartzProfile, add_apply, sub_apply, smul_apply, smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply (hphase (-π)),
    SchwartzMap.smulLeftCLM_apply_apply (hphase π), centralProfile_apply k hb hM hF hbound hr,
    rayProfile_apply hb hM hF hbound hr,
    horizontalSchwartz_apply (shifted_cuspKernel_cont k hF 1) (-1) 0 hr,
    horizontalSchwartz_apply (shifted_cuspKernel_cont k hF (-1)) 1 0 hr]
  simp only [horizontalPoint, horizontalCoeff, cuspKernel, sub_eq_add_neg]
  push_cast
  ring_nf


/-- Construct the inverted-contour Schwartz profile directly from exponential cusp decay. -/
noncomputable def schwartzProfileOfIsBigO {F : ℂ → ℂ} {b : ℝ} (k : ℕ) (c : ℂ) (hb : 0 < b)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hO : (fun τ : UpperHalfPlane ↦ F τ) =O[UpperHalfPlane.atImInfty]
      fun τ ↦ Real.exp (-b * τ.im)) : 𝓢(ℝ, ℂ) :=
  let h := UpperHalfPlane.exists_norm_le_exp_mul_Ici hF.continuousOn hO
  schwartzProfile k c hb (Classical.choose_spec h).1 hF (Classical.choose_spec h).2

/-- The profile constructed from a cusp Big-O bound has the required contour formula. -/
theorem schwartzProfileOfIsBigO_eq_contour {F : ℂ → ℂ} {b : ℝ} (k : ℕ) (c : ℂ) (hb : 0 < b)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hO : (fun τ : UpperHalfPlane ↦ F τ) =O[UpperHalfPlane.atImInfty]
      fun τ ↦ Real.exp (-b * τ.im)) {r : ℝ} (hr : 0 ≤ r) :
    schwartzProfileOfIsBigO k c hb hF hO r =
      leftLegs (expKernel (fun z ↦ F (-1 / (z + 1)) * (z + 1) ^ k) r) +
      rightLegs (expKernel (fun z ↦ F (-1 / (z - 1)) * (z - 1) ^ k) r) +
      centralLeg (expKernel (fun z ↦ -2 * (F (-1 / z) * z ^ k)) r) +
      verticalRay (expKernel (fun z ↦ c * F z) r) := by
  unfold schwartzProfileOfIsBigO
  exact schwartzProfile_eq_contour _ _ _ _ _ _ hr

end SphereCeti.Contour
