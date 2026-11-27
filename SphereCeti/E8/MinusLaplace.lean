/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.E8.MinusSchwartz
public import SphereCeti.E8.MinusKernel.Growth
import SphereCeti.Contour.ExponentialDecay
import SphereCeti.E8.MinusKernel.Holomorphic
import SphereCeti.E8.MinusKernel.Regularity

/-!
# The Laplace representation of the E8 minus component

Above squared radius two, the minus contour is a sine-squared factor times the Laplace
transform of `ψ_I` on the positive imaginary axis. The convergence threshold follows from
`ψ_I, ψ_T = O(exp(2π Im τ))`. The two horizontal pieces are moved to vertical rays and the
identity `ψ_I = ψ_T + ψ_S` combines the ray terms.

This is Viazovska's Proposition 6, equation (53), in *The sphere packing problem in dimension
8*, Annals of Mathematics 185 (2017), with the contour convention of equation (52).
The formal proof uses SphereCeti's canonical kernels and the corrected negative ray sign.
-/

set_option autoImplicit false

public section

open Complex Filter MeasureTheory Set Asymptotics Topology
open UpperHalfPlane hiding I
open scoped Real

namespace SphereCeti.E8

private theorem expKernel_decay (F : ℂ → ℂ) (r : ℝ)
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (2 * π * τ.im)) :
    (fun τ : ℍ ↦ Contour.expKernel F r τ) =O[atImInfty]
      fun τ ↦ Real.exp (-(π * (r - 2)) * τ.im) := by
  refine (Contour.isBigO_expKernel_of_growth r hO).congr_right fun τ ↦ ?_
  congr 1
  ring

private theorem psiIExt_growth : (fun τ : ℍ ↦ psiIExt τ) =O[atImInfty]
    fun τ ↦ Real.exp (2 * π * τ.im) :=
  isBigO_psiI.congr_left fun τ ↦ (psiIExt_of_im_pos τ.im_pos).symm

private theorem psiTExt_growth : (fun τ : ℍ ↦ psiTExt τ) =O[atImInfty]
    fun τ ↦ Real.exp (2 * π * τ.im) :=
  isBigO_psiT.congr_left fun τ ↦ (psiTExt_of_im_pos τ.im_pos).symm

private theorem exp_on_axis (r t : ℝ) :
    cexp (π * I * r * ((t : ℂ) * I)) = cexp (-((π : ℂ) * r) * t) := by
  congr 1
  ring_nf
  simp

private theorem horizontal_psiT (r : ℝ) (hr : 2 < r) (a b : ℝ) :
    (∫ x in a..b, psiTExt (x + I) * cexp (π * I * r * (x + I))) +
      I * ∫ t in Ioi (1 : ℝ), psiTExt (b + t * I) * cexp (π * I * r * (b + t * I)) =
      I * ∫ t in Ioi (1 : ℝ), psiTExt (a + t * I) * cexp (π * I * r * (a + t * I)) := by
  have hc : 0 < π * (r - 2) := mul_pos Real.pi_pos (sub_pos.mpr hr)
  have hf : DifferentiableOn ℂ (Contour.expKernel psiTExt r) {z : ℂ | 0 < z.im} := by
    rw [funext (Contour.expKernel_apply psiTExt r)]
    exact differentiableOn_psiTExt.mul (by fun_prop)
  have h := Contour.horizontal_add_vertical_eq_vertical_of_exp_decay
    (F := Contour.expKernel psiTExt r) hc hf (expKernel_decay _ r psiTExt_growth) a b
  simpa only [Contour.expKernel_apply] using h

private theorem shifted_psiT_integral (a r : ℝ) (s : Set ℝ)
    (hshift : ∀ t : ℝ, psiTExt (a + t * I) = psiIExt (t * I)) :
    (∫ t in s, psiTExt (a + t * I) * cexp (π * I * r * (a + t * I))) =
      cexp ((π * a * r : ℝ) * I) *
        ∫ t in s, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun t ↦ by
    dsimp only
    rw [hshift]
    have he : (π : ℂ) * I * r * ((a : ℂ) + t * I) =
        ((π * a * r : ℝ) : ℂ) * I + -((π : ℂ) * r) * t := by
      push_cast
      ring_nf
      simp only [I_sq]
      ring
    rw [he, Complex.exp_add]
    ring

private theorem integrable_tail {F : ℂ → ℂ} (r : ℝ) (hr : 2 < r)
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hO : (fun τ : ℍ ↦ F τ) =O[atImInfty] fun τ ↦ Real.exp (2 * π * τ.im)) :
    IntegrableOn (fun t : ℝ ↦ F (t * I) * cexp (-((π : ℂ) * r) * t)) (Ioi 1) := by
  have hc : 0 < π * (r - 2) := mul_pos Real.pi_pos (sub_pos.mpr hr)
  have hf : ContinuousOn (Contour.expKernel F r) {z : ℂ | 0 < z.im} := by
    rw [funext (Contour.expKernel_apply F r)]
    exact hF.continuousOn.mul (by fun_prop)
  simpa only [ofReal_zero, zero_add, Contour.expKernel_apply, exp_on_axis] using
    Contour.integrableOn_shift_mul_I_of_exp_decay hc hf (expKernel_decay _ r hO) 0

private theorem integrable_finite (r : ℝ) (hr : 0 ≤ r) :
    IntegrableOn (fun t : ℝ ↦ psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)) (Ioc 0 1) := by
  refine integrableOn_psiIExt_mul_I_Ioc.norm.mono'
    (integrableOn_psiIExt_mul_I_Ioc.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun t : ℝ ↦ cexp (-((π : ℂ) * r) * t)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simp only [norm_mul, norm_exp, mul_re, neg_re, ofReal_re, ofReal_im,
    mul_zero, sub_zero]
  have he : Real.exp (-(π * r) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg Real.pi_pos.le hr)) ht.1.le)
  exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (mul_one _)

/-- Above squared radius two, the E8 minus Laplace integral is absolutely convergent. -/
theorem integrableOn_psiIExt_mul_exp_Ioi {r : ℝ} (hr : 2 < r) :
    IntegrableOn (fun t : ℝ ↦ psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)) (Ioi 0) := by
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) < 2).trans hr |>.le
  simpa only [Ioc_union_Ioi_eq_Ioi zero_le_one] using
    (integrable_finite r hr0).union
      (integrable_tail r hr differentiableOn_psiIExt psiIExt_growth)

/-- For squared radius `r > 2`, the E8 minus Schwartz profile is its sine-squared
factor times the convergent Laplace integral of `ψ_I`. -/
theorem magicMinusProfile_eq_laplace {r : ℝ} (hr : 2 < r) :
    magicMinusProfile r = (-4 * I : ℂ) * (Real.sin (π * r / 2) ^ 2 : ℝ) *
      ∫ (t : ℝ) in Ioi 0, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
  have hr0 : 0 ≤ r := (by norm_num : (0 : ℝ) < 2).trans hr |>.le
  have hI := integrable_tail r hr differentiableOn_psiIExt psiIExt_growth
  have hT := integrable_tail r hr differentiableOn_psiTExt psiTExt_growth
  have hS : (∫ (t : ℝ) in Ioi 1, psiSExt (t * I) * cexp (-((π : ℂ) * r) * t)) =
      (∫ (t : ℝ) in Ioi 1, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)) -
      ∫ (t : ℝ) in Ioi 1, psiTExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
    rw [← integral_sub hI hT]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    have hz : 0 < ((t : ℂ) * I).im := by simpa using zero_lt_one.trans ht
    rw [psiIExt_of_im_pos hz, psiTExt_of_im_pos hz, psiSExt_of_im_pos hz]
    have h := congrFun psiI_eq_psiT_add_psiS ⟨t * I, hz⟩
    simp only [Pi.add_apply] at h
    rw [h]
    ring
  have hleft := shifted_psiT_integral (-1) r (Ioi 1) (fun t ↦ by
    rw [psiTExt_eq_psiIExt_add_one]
    congr 1
    norm_num)
  have hright := shifted_psiT_integral 1 r (Ioi 1) (fun t ↦ by
    rw [psiTExt_eq_psiIExt_sub_one]
    congr 1
    norm_num)
  simp only [ofReal_neg, ofReal_one, mul_neg_one, mul_one] at hleft hright
  have hl := horizontal_psiT r hr (-1) 0
  have hp := horizontal_psiT r hr 1 0
  simp only [ofReal_neg, ofReal_one, ofReal_zero, zero_add, exp_on_axis] at hl hp
  rw [hleft] at hl
  rw [hright] at hp
  have hsum :
      (∫ (t : ℝ) in Ioc 0 1, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)) +
      (∫ (t : ℝ) in Ioi 1, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)) =
      ∫ (t : ℝ) in Ioi 0, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (integrable_finite r hr0) hI,
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hphase : I * (cexp ((-π * r : ℝ) * I) + cexp ((π * r : ℝ) * I) - 2) =
      (-4 * I : ℂ) * (Real.sin (π * r / 2) ^ 2 : ℝ) := by
    have hc : Real.cos (π * r) = 1 - 2 * Real.sin (π * r / 2) ^ 2 := by
      convert Real.cos_two_mul_eq_one_sub (π * r / 2) using 1; congr 1; ring
    simp only [neg_mul, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, hc]
    push_cast
    ring
  calc
    magicMinusProfile r =
        I * (cexp ((-π * r : ℝ) * I) + cexp ((π * r : ℝ) * I) - 2) *
          ((∫ (t : ℝ) in Ioc 0 1, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)) +
            ∫ (t : ℝ) in Ioi 1, psiIExt (t * I) * cexp (-((π : ℂ) * r) * t)) := by
      rw [magicMinusProfile_eq_integralPieces hr0, hS]
      linear_combination hl + hp
    _ = _ := by rw [hsum, hphase]

/-- The E8 minus profile vanishes at every squared shell radius `2n` with `n ≥ 2`. -/
theorem magicMinusProfile_two_mul_nat_eq_zero (n : ℕ) (hn : 2 ≤ n) :
    magicMinusProfile (2 * (n : ℝ)) = 0 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [magicMinusProfile_eq_laplace (by linarith : (2 : ℝ) < 2 * n)]
  have harg : π * (2 * (n : ℝ)) / 2 = n * π := by ring
  simp only [harg, Real.sin_nat_mul_pi, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, ofReal_zero, mul_zero, zero_mul]

end SphereCeti.E8
