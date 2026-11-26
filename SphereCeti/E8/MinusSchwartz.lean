/-
Copyright (c) 2025 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sidharth Hariharan, Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.Distribution.SchwartzSpace.CompNormSq
public import SphereCeti.E8.MinusKernels
public import SphereCeti.Contour.SixPiece

import SphereCeti.Analysis.Distribution.SchwartzSpace.Laplace
import SphereCeti.E8.MinusEigen
import SphereCeti.E8.MinusKernelRegularity
import SphereCeti.E8.MinusKernelHolomorphic
import SphereCeti.E8.MinusKernelDecay
import TauCeti.Analysis.Complex.UpperHalfPlane.ResToImagAxis
import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# A Schwartz profile for the E8 minus eigencomponent

The finite vertical pieces are modulations of one cusp-decaying Laplace profile. The two
horizontal pieces have uniformly negative real exponential coefficient. The infinite ray is
the Laplace transform of the exponentially decaying `ψ_S`. Smooth extensions of these profiles
are combined without changing their nonnegative values.

The contour decomposition and cutoff strategy are adapted from
`SpherePacking/MagicFunction/b/Schwartz/Basic.lean` in
`thefundamentaltheor3m/Sphere-Packing-Lean@01f23eccf963c50250c9e48dd103e8cc88c36f85`
(Sidharth Hariharan, Apache-2.0). They are expressed using SphereCeti's kernels and common
Laplace constructors. The ray coefficient is `-2`, as in Viazovska's equation (52).
-/

public section

open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology Real SchwartzMap FourierTransform

namespace SphereCeti.E8

private lemma exists_psiS_exponential_bound : ∃ M : ℝ, 0 ≤ M ∧
    ∀ t ∈ Ici (1 : ℝ), ‖psiSExt (t * I)‖ ≤ M * Real.exp (-π * t) := by
  have htend : Tendsto (fun t : ℝ ↦ UpperHalfPlane.ofComplex (t * I)) atTop
      UpperHalfPlane.atImInfty :=
    UpperHalfPlane.tendsto_ofComplex_I_mul_atTop_atImInfty.congr fun t ↦ by rw [mul_comm]
  have hcoe {t : ℝ} (ht : 0 < t) :
      (UpperHalfPlane.ofComplex ((t : ℂ) * I) : ℂ) = (t : ℂ) * I := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (z := (t : ℂ) * I) (by simpa using ht)]
  have hO : (fun t : ℝ ↦ psiSExt (t * I)) =O[atTop] fun t ↦ Real.exp (-π * t) := by
    refine (isBigO_psiSExt.comp_tendsto htend).congr' ?_ ?_ <;>
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    · simp only [Function.comp_apply, hcoe ht]
    · simp only [Function.comp_apply, UpperHalfPlane.im,
        hcoe ht]
      simp
  obtain ⟨C, hC, hbound⟩ := hO.exists_nonneg
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound.bound
  have hcont : ContinuousOn (fun t : ℝ ↦ ‖psiSExt (t * I)‖ * Real.exp (π * t))
      (Icc 1 (max 1 N)) := by
    refine (continuousOn_psiSExt.comp (by fun_prop) fun t ht ↦ ?_).norm.mul (by fun_prop)
    simpa using (zero_lt_one.trans_le ht.1)
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C D, hC.trans (le_max_left _ _), fun t ht ↦ ?_⟩
  by_cases hNt : N ≤ t
  · have h := hN t hNt
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C D) (Real.exp_nonneg _))
  · have h := hD t ⟨ht, (lt_of_not_ge hNt).le.trans (le_max_right 1 N)⟩
    rw [Real.norm_of_nonneg (by positivity)] at h
    have h' := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-π * t))
    have he : Real.exp (π * t) * Real.exp (-π * t) = 1 := by
      rw [← Real.exp_add, show π * t + -π * t = 0 by ring, Real.exp_zero]
    rw [mul_assoc, he, mul_one] at h'
    exact h'.trans (mul_le_mul_of_nonneg_right (le_max_right C D) (Real.exp_nonneg _))

private noncomputable def psiSBound : ℝ := Classical.choose exists_psiS_exponential_bound

private lemma psiSBound_nonneg : 0 ≤ psiSBound :=
  (Classical.choose_spec exists_psiS_exponential_bound).1

private lemma psiS_bound {t : ℝ} (ht : 1 ≤ t) :
    ‖psiSExt (t * I)‖ ≤ psiSBound * Real.exp (-π * t) :=
  (Classical.choose_spec exists_psiS_exponential_bound).2 t ht

private lemma psiI_cusp_bound (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖psiIExt (t * I)‖ ≤ psiSBound * Real.exp (-π / t) := by
  have hinv : -1 / ((t : ℂ) * I) = ((t⁻¹ : ℝ) : ℂ) * I := by field_simp; simp
  rw [psiIExt_eq_psiSExt, hinv, norm_mul, norm_pow, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht.1, norm_I, mul_one]
  have htinv : 1 ≤ t⁻¹ := (one_le_inv₀ ht.1).mpr ht.2
  calc
    ‖psiSExt ((t⁻¹ : ℝ) * I)‖ * t ^ 2 ≤
        (psiSBound * Real.exp (-π * t⁻¹)) * 1 :=
      mul_le_mul (psiS_bound htinv) (pow_le_one₀ ht.1.le ht.2)
        (pow_nonneg ht.1.le 2) (mul_nonneg psiSBound_nonneg (Real.exp_nonneg _))
    _ = _ := by rw [mul_one, div_eq_mul_inv]

/-- The E8 kernel `ψ_I` is integrable on the finite positive imaginary segment. -/
theorem integrableOn_psiIExt_mul_I_Ioc : IntegrableOn (fun t : ℝ ↦ psiIExt (t * I)) (Ioc 0 1) := by
  have hcont : ContinuousOn (fun t : ℝ ↦ psiIExt (t * I)) (Ioc (0 : ℝ) 1) :=
    continuousOn_psiIExt.comp (by fun_prop) fun t ht ↦ by simpa using ht.1
  refine (integrableOn_const measure_Ioc_lt_top.ne (C := psiSBound)).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  refine (psiI_cusp_bound t ht).trans ?_
  have he : Real.exp (-π / t) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) ht.1.le)
  exact (mul_le_mul_of_nonneg_left he psiSBound_nonneg).trans_eq (mul_one _)

private noncomputable def centralSchwartz : 𝓢(ℝ, ℂ) :=
  SchwartzMap.ofFiniteLaplace Real.pi_pos one_pos psiSBound_nonneg integrableOn_psiIExt_mul_I_Ioc
    psiI_cusp_bound (π : ℂ) (by simpa using Real.pi_pos)

private lemma centralSchwartz_apply {r : ℝ} (hr : 0 ≤ r) :
    centralSchwartz r = ∫ (t : ℝ) in Ioc 0 1, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  unfold centralSchwartz
  exact SchwartzMap.ofFiniteLaplace_apply_of_nonneg _ _ _ _ _ _ _ hr

private lemma measurable_psiS_ray :
    AEStronglyMeasurable (fun t : ℝ ↦ psiSExt (t * I)) (volume.restrict (Ioi 1)) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  exact continuousOn_psiSExt.comp (by fun_prop) fun t ht ↦ by
    simpa using (zero_lt_one.trans ht)

private noncomputable def raySchwartz : 𝓢(ℝ, ℂ) :=
  SchwartzMap.ofLaplaceTail measurable_psiS_ray Real.pi_pos Real.pi_pos psiSBound_nonneg
    (fun _t ht ↦ psiS_bound ht.le)

private lemma raySchwartz_apply {r : ℝ} (hr : 0 ≤ r) :
    raySchwartz r = ∫ (t : ℝ) in Ioi 1, psiSExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  unfold raySchwartz
  exact SchwartzMap.ofLaplaceTail_apply_of_nonneg _ _ _ _ _ hr

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

private lemma integrable_horizontal (a b : ℝ) :
    IntegrableOn (fun t : ℝ ↦ psiTExt (horizontalPoint a b t) * (b - a : ℝ)) (Ioc 0 1) := by
  have hcont : Continuous (fun t : ℝ ↦ psiTExt (horizontalPoint a b t) * (b - a : ℝ)) :=
    (continuousOn_psiTExt.comp_continuous (continuous_horizontalPoint a b)
      (fun t ↦ by simp [horizontalPoint_im])).mul continuous_const
  exact hcont.integrableOn_Ioc

private noncomputable def horizontalSchwartz (a b : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.ofExponentialIntegral (integrable_horizontal a b)
    (continuous_horizontalCoeff a b).aestronglyMeasurable
    (Classical.choose_spec (exists_horizontal_bound a b)).1
    (ae_restrict_of_forall_mem measurableSet_Ioc
      (Classical.choose_spec (exists_horizontal_bound a b)).2)
    Real.pi_pos (.of_forall fun t ↦ (horizontalCoeff_re a b t).le)

private lemma horizontalSchwartz_apply (a b : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    horizontalSchwartz a b r = ∫ (t : ℝ) in Ioc 0 1,
      (psiTExt (horizontalPoint a b t) * (b - a : ℝ)) * cexp ((r : ℂ) * horizontalCoeff a b t) := by
  unfold horizontalSchwartz
  exact SchwartzMap.ofExponentialIntegral_apply_of_nonneg _ _ _ _ _ _ hr

private lemma phase_temperate (a : ℝ) :
    (fun r : ℝ ↦ cexp ((a * r : ℝ) * I)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

/-- A one-variable Schwartz profile of the E8 `-1` Fourier eigencomponent. Its nonnegative
values are the six-piece contour integral; the extension at negative arguments is immaterial
when the profile is composed with squared norm. -/
noncomputable def magicMinusProfile : 𝓢(ℝ, ℂ) :=
  (I : ℂ) • (SchwartzMap.smulLeftCLM ℂ (fun r : ℝ ↦ cexp ((-π * r : ℝ) * I)) centralSchwartz +
    SchwartzMap.smulLeftCLM ℂ (fun r : ℝ ↦ cexp ((π * r : ℝ) * I)) centralSchwartz -
    (2 : ℂ) • centralSchwartz) + horizontalSchwartz (-1) 0 + horizontalSchwartz 1 0 -
    (2 * I : ℂ) • raySchwartz

private lemma vertical_integral (F : ℂ → ℂ) (a r : ℝ) :
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

private lemma horizontal_contour (a b r : ℝ) :
    (∫ᶜ z in Path.segment ((a : ℂ) + I) ((b : ℂ) + I),
        Contour.scalarOneForm (Contour.expKernel psiTExt r) z) =
      ∫ (t : ℝ) in Ioc 0 1, (psiTExt (horizontalPoint a b t) * (b - a : ℝ)) *
        cexp ((r : ℂ) * horizontalCoeff a b t) := by
  rw [Contour.curveIntegral_segment_scalarOneForm, intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  dsimp only
  have hz : (a : ℂ) + I + t * ((b + I) - (a + I)) = horizontalPoint a b t := by
    unfold horizontalPoint
    ring
  have hd : (b + I : ℂ) - (a + I) = ((b - a : ℝ) : ℂ) := by push_cast; ring
  rw [Contour.expKernel_apply, hz, hd]
  unfold horizontalCoeff
  rw [show (π : ℂ) * I * r * horizontalPoint a b t =
    (r : ℂ) * ((π : ℂ) * I * horizontalPoint a b t) by ring]
  ring

private lemma left_vertical (r : ℝ) :
    (∫ᶜ z in Path.segment (-1) (-1 + I),
        Contour.scalarOneForm (Contour.expKernel minusKernelLeft r) z) =
      I * cexp ((-π * r : ℝ) * I) *
        ∫ (t : ℝ) in Ioc 0 1, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [Contour.curveIntegral_segment_scalarOneForm, intervalIntegral.integral_of_le zero_le_one]
  simp only [Contour.expKernel_apply, add_sub_cancel_left]
  have h := vertical_integral minusKernelLeft (-1) r
  simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg_one] at h
  rw [h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  dsimp only
  rw [minusKernelLeft_def, psiTExt_eq_psiIExt_add_one]
  congr 2
  ring

private lemma right_vertical (r : ℝ) :
    (∫ᶜ z in Path.segment 1 (1 + I),
        Contour.scalarOneForm (Contour.expKernel minusKernelRight r) z) =
      I * cexp ((π * r : ℝ) * I) *
        ∫ (t : ℝ) in Ioc 0 1, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [Contour.curveIntegral_segment_scalarOneForm, intervalIntegral.integral_of_le zero_le_one]
  simp only [Contour.expKernel_apply, add_sub_cancel_left]
  have h := vertical_integral minusKernelRight 1 r
  simp only [Complex.ofReal_one, mul_one] at h
  rw [h]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  dsimp only
  rw [minusKernelRight_def, psiTExt_eq_psiIExt_sub_one]
  congr 2
  ring

private lemma central_contour (r : ℝ) :
    Contour.centralLeg (Contour.expKernel minusKernelCentral r) =
      (-2 * I) * ∫ (t : ℝ) in Ioc 0 1, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [Contour.centralLeg_def, Contour.curveIntegral_segment_scalarOneForm,
    intervalIntegral.integral_of_le zero_le_one]
  simp only [Contour.expKernel_apply, sub_zero, zero_add]
  have h := vertical_integral minusKernelCentral 0 r
  simp only [Complex.ofReal_zero, zero_add, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h
  rw [h, ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  dsimp only
  rw [minusKernelCentral_def]
  ring

private lemma ray_contour (r : ℝ) :
    Contour.verticalRay (Contour.expKernel minusKernelRay r) =
      (-2 * I) * ∫ (t : ℝ) in Ioi 1, psiSExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [Contour.verticalRay_def, ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [Contour.expKernel_apply, minusKernelRay_def]
  have he : (π : ℂ) * I * r * ((t : ℂ) * I) = -((π : ℂ) * r) * t := by
    ring_nf
    simp
  rw [he]
  ring

/-- At a nonnegative profile parameter, the Schwartz profile is exactly the prescribed
six-piece contour integral, including the negative ray coefficient. -/
theorem magicMinusProfile_eq_contour {r : ℝ} (hr : 0 ≤ r) :
    magicMinusProfile r = Contour.leftLegs (Contour.expKernel minusKernelLeft r) +
      Contour.rightLegs (Contour.expKernel minusKernelRight r) +
      Contour.centralLeg (Contour.expKernel minusKernelCentral r) +
      Contour.verticalRay (Contour.expKernel minusKernelRay r) := by
  rw [Contour.leftLegs_def, Contour.rightLegs_def, left_vertical, right_vertical,
    central_contour, ray_contour]
  have hl : minusKernelLeft = psiTExt := funext minusKernelLeft_def
  have hR : minusKernelRight = psiTExt := funext minusKernelRight_def
  have hLh := horizontal_contour (-1) 0 r
  have hRh := horizontal_contour 1 0 r
  rw [hl, hR]
  simp only [Contour.curveIntegral_segment_scalarOneForm] at hLh hRh ⊢
  simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero, zero_add] at hLh
  simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_add] at hRh
  rw [hLh, hRh]
  simp only [magicMinusProfile, add_apply, sub_apply,
    smul_apply, smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply (phase_temperate (-π)),
    SchwartzMap.smulLeftCLM_apply_apply (phase_temperate π),
    centralSchwartz_apply hr, raySchwartz_apply hr, horizontalSchwartz_apply _ _ hr]
  ring

/-- Split the minus contour into its finite vertical Laplace piece, two horizontal
intervals and the decaying ray. This evaluation interface keeps consumers independent of
the construction of the Schwartz extension at negative arguments. -/
theorem magicMinusProfile_eq_integralPieces {r : ℝ} (hr : 0 ≤ r) :
    magicMinusProfile r =
      I * (cexp ((-π * r : ℝ) * I) + cexp ((π * r : ℝ) * I) - 2) *
        (∫ (t : ℝ) in Ioc 0 1, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)) +
      (∫ x in (-1 : ℝ)..0, psiTExt (x + I) * cexp (π * I * r * (x + I))) +
      (∫ x in (1 : ℝ)..0, psiTExt (x + I) * cexp (π * I * r * (x + I))) -
      (2 * I) * ∫ (t : ℝ) in Ioi 1, psiSExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [magicMinusProfile_eq_contour hr, Contour.leftLegs_def, Contour.rightLegs_def,
    left_vertical, right_vertical, central_contour, ray_contour]
  have hL : minusKernelLeft = psiTExt := funext minusKernelLeft_def
  have hR : minusKernelRight = psiTExt := funext minusKernelRight_def
  rw [hL, hR]
  have hl := Contour.curveIntegral_horizontal_eq_interval (Contour.expKernel psiTExt r) (-1) 0 I
  have hr' := Contour.curveIntegral_horizontal_eq_interval (Contour.expKernel psiTExt r) 1 0 I
  -- Parametrize before normalizing real-to-complex casts in dependent path endpoints.
  simp only [Contour.curveIntegral_segment_scalarOneForm] at hl hr' ⊢
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero, zero_add] at hl hr'
  rw [hl, hr']
  simp only [Contour.expKernel_apply]
  ring

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The E8 minus component as a radial Schwartz function on a real inner product space. -/
noncomputable def magicMinus : 𝓢(E, ℂ) :=
  SchwartzMap.compNormSqCLM ℂ E magicMinusProfile

/-- The radial minus component evaluates the Schwartz profile at squared norm. -/
@[simp]
theorem magicMinus_apply (x : E) : magicMinus x = magicMinusProfile (‖x‖ ^ 2) :=
  SchwartzMap.compNormSqCLM_apply magicMinusProfile x

/-- The minus component is radial in every real inner product space. -/
@[fun_prop]
theorem isRadial_magicMinus : Function.IsRadial (magicMinus (E := E)) :=
  SchwartzMap.isRadial_compNormSqCLM magicMinusProfile

/-- The Schwartz minus component has exactly the prescribed six-piece contour presentation. -/
theorem magicMinus_eq_sixPieceComponent (x : E) :
    magicMinus x = Contour.sixPieceComponent minusKernelLeft minusKernelRight
      minusKernelCentral minusKernelRay x := by
  rw [magicMinus_apply, Contour.sixPieceComponent_def]
  exact magicMinusProfile_eq_contour (sq_nonneg ‖x‖)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In dimension eight, the Schwartz minus component is a `-1` Fourier eigenfunction. -/
theorem fourier_magicMinus (hE : Module.finrank ℝ E = 8) :
    𝓕 (magicMinus (E := E)) = -magicMinus := by
  have heq : (magicMinus : E → ℂ) = Contour.sixPieceComponent minusKernelLeft minusKernelRight
      minusKernelCentral minusKernelRay := funext magicMinus_eq_sixPieceComponent
  ext x
  change (𝓕 (magicMinus : E → ℂ)) x = -magicMinus x
  rw [heq, fourier_sixPiece_minus hE]

example (x : E) : magicMinus x = magicMinusProfile (‖x‖ ^ 2) := by simp

example : Function.IsRadial (magicMinus (E := E)) := by fun_prop

end Radial

end SphereCeti.E8

