/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.E8.MinusLaplace
public import SphereCeti.E8.MinusKernel.Signs

/-!
# Strict signs and the zero set of the E8 minus profile above squared radius two

The Laplace cofactor is strictly positive and real: its integrand is positive on the
positive imaginary axis. Thus the minus profile is purely imaginary, has nonpositive
imaginary part, and vanishes precisely at the even squared radii in `(2, ∞)`.
These component results support the Layer 9 sign and zero targets; they do not assert
the corresponding targets for the assembled auxiliary function or at squared radius two.

The proofs independently combine the library's Laplace representation and kernel signs.
The analytic representation is Viazovska (2017), Section 5, equation (58).
-/

public section

open Complex Filter MeasureTheory Set
open scoped Real ComplexOrder

namespace SphereCeti.E8

/-- The convergent Laplace cofactor of the minus profile for squared radius `r > 2`. -/
noncomputable def minusLaplaceCofactor (r : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)

/-- The defining integral, exposed for downstream analysis. -/
theorem minusLaplaceCofactor_eq_integral (r : ℝ) :
    minusLaplaceCofactor r =
      ∫ t : ℝ in Ioi 0, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [minusLaplaceCofactor]

private theorem laplaceIntegrand_pos (r : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < psiIExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  have hz : 0 < ((t : ℂ) * I).im := by simpa using ht
  rw [psiIExt_of_im_pos hz]
  have he : -((π : ℂ) * r) * t = ((-π * r * t : ℝ) : ℂ) := by push_cast; ring
  rw [he, ← Complex.ofReal_exp]
  exact mul_pos (psiI_pos_of_re_eq_zero ⟨t * I, hz⟩ (by simp))
    (by exact_mod_cast Real.exp_pos (-π * r * t))

/-- The Laplace cofactor is real on its domain of absolute convergence. -/
theorem minusLaplaceCofactor_im {r : ℝ} (hr : 2 < r) :
    (minusLaplaceCofactor r).im = 0 := by
  rw [minusLaplaceCofactor_eq_integral]
  change RCLike.im (K := ℂ) _ = 0
  rw [← integral_im (integrableOn_psiIExt_mul_exp_Ioi hr)]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (Complex.lt_def.mp (laplaceIntegrand_pos r ht)).2.symm

/-- The real part of the Laplace cofactor is strictly positive. -/
theorem minusLaplaceCofactor_re_pos {r : ℝ} (hr : 2 < r) :
    0 < (minusLaplaceCofactor r).re := by
  rw [minusLaplaceCofactor_eq_integral]
  change 0 < RCLike.re (K := ℂ) _
  rw [← integral_re (integrableOn_psiIExt_mul_exp_Ioi hr)]
  have hp : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      0 < (psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)).re := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (Complex.lt_def.mp (laplaceIntegrand_pos r ht)).1
  change 0 < ∫ t : ℝ in Ioi 0,
    (psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)).re
  rw [integral_pos_iff_support_of_nonneg_ae (hp.mono fun _ h ↦ h.le)
    (integrableOn_psiIExt_mul_exp_Ioi hr).re]
  have hs : Function.support (fun t : ℝ ↦
      (psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)).re) =ᵐ[volume.restrict (Ioi 0)]
      (univ : Set ℝ) := by
    filter_upwards [hp] with t ht
    simpa using ne_of_gt ht
  rw [measure_congr hs]
  simp

/-- In particular, the cofactor cannot contribute an additional zero. -/
theorem minusLaplaceCofactor_ne_zero {r : ℝ} (hr : 2 < r) :
    minusLaplaceCofactor r ≠ 0 := by
  intro h
  have hp := minusLaplaceCofactor_re_pos hr
  simp [h] at hp

/-- The minus profile has zero real part above squared radius two. -/
theorem magicMinusProfile_re_eq_zero {r : ℝ} (hr : 2 < r) :
    (magicMinusProfile r).re = 0 := by
  rw [magicMinusProfile_eq_laplace hr, ← minusLaplaceCofactor_eq_integral]
  generalize Real.sin (π * r / 2) = s
  norm_num [mul_re, mul_im, pow_two, minusLaplaceCofactor_im hr]

/-- The imaginary part is the negative sine square times the positive real cofactor. -/
theorem magicMinusProfile_im_eq {r : ℝ} (hr : 2 < r) :
    (magicMinusProfile r).im =
      -4 * Real.sin (π * r / 2) ^ 2 * (minusLaplaceCofactor r).re := by
  rw [magicMinusProfile_eq_laplace hr, ← minusLaplaceCofactor_eq_integral]
  generalize Real.sin (π * r / 2) = s
  norm_num [mul_im, mul_re, pow_two]

/-- The minus profile has nonpositive imaginary part in the Laplace range. -/
theorem magicMinusProfile_im_nonpos {r : ℝ} (hr : 2 < r) :
    (magicMinusProfile r).im ≤ 0 := by
  rw [magicMinusProfile_im_eq hr]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))
    (minusLaplaceCofactor_re_pos hr).le

/-- All zeros in the Laplace range come from the sine factor. -/
theorem magicMinusProfile_eq_zero_iff_sin {r : ℝ} (hr : 2 < r) :
    magicMinusProfile r = 0 ↔ Real.sin (π * r / 2) = 0 := by
  rw [magicMinusProfile_eq_laplace hr, ← minusLaplaceCofactor_eq_integral,
    mul_eq_zero, mul_eq_zero]
  generalize Real.sin (π * r / 2) = s
  simp [minusLaplaceCofactor_ne_zero hr]

/-- Away from the even squared radii, the imaginary part is strictly negative. -/
theorem magicMinusProfile_im_neg_iff {r : ℝ} (hr : 2 < r) :
    (magicMinusProfile r).im < 0 ↔ Real.sin (π * r / 2) ≠ 0 := by
  have hz : magicMinusProfile r = 0 ↔ (magicMinusProfile r).im = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; exact Complex.ext (magicMinusProfile_re_eq_zero hr) h
  rw [lt_iff_le_and_ne]
  simp only [magicMinusProfile_im_nonpos hr, true_and]
  exact not_congr (hz.symm.trans (magicMinusProfile_eq_zero_iff_sin hr))

/-- The exact zero set above squared radius two is the even shells `2n`, `n ≥ 2`. -/
theorem magicMinusProfile_eq_zero_iff {r : ℝ} (hr : 2 < r) :
    magicMinusProfile r = 0 ↔ ∃ n : ℕ, 2 ≤ n ∧ r = 2 * (n : ℝ) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp ((magicMinusProfile_eq_zero_iff_sin hr).mp h)
    have hkr : r = 2 * (k : ℝ) := by nlinarith [Real.pi_pos]
    have hk2 : (2 : ℤ) ≤ k := by
      have : (1 : ℝ) < (k : ℝ) := by linarith
      exact Int.add_one_le_iff.mpr (by exact_mod_cast this)
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (by decide : (0 : ℤ) ≤ 2) hk2)
    exact ⟨n, by exact_mod_cast hk2, by simpa using hkr⟩
  · rintro ⟨n, hn, rfl⟩
    exact magicMinusProfile_two_mul_nat_eq_zero n hn

example : magicMinusProfile 4 = 0 :=
  (magicMinusProfile_eq_zero_iff (by norm_num)).mpr ⟨2, le_rfl, by norm_num⟩

end SphereCeti.E8
