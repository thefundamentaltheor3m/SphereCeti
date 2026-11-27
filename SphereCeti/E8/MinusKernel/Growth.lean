/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.E8.MinusKernel.Basic
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.Estimates
import SphereCeti.E8.MinusKernel.Decay
import Mathlib.Analysis.Asymptotics.Ring

/-!
# Growth of the E8 minus kernels

The leading coefficient of `H₂` controls its reciprocal. The explicit theta formulas for
`ψ_I` and `ψ_T` then give growth `O(exp(2π Im τ))`, which is the convergence threshold for the
Laplace representation above squared radius two.
-/

public section

open Complex Filter Asymptotics Topology
open UpperHalfPlane hiding I
open TauCeti.ModularForm
open scoped Real

namespace SphereCeti.E8

/-- The E8 function `ψ_I` has growth `O(exp(2π Im τ))`. -/
theorem isBigO_psiI : psiI =O[atImInfty] fun τ : ℍ ↦ Real.exp (2 * π * τ.im) := by
  have one_bigO_growth : (fun _τ : ℍ ↦ (1 : ℝ)) =O[atImInfty]
      (fun τ : ℍ ↦ Real.exp (2 * π * τ.im)) := by
    have hlarge : ∀ᶠ τ : ℍ in atImInfty, 0 ≤ τ.im :=
      preimage_mem_comap (Ici_mem_atTop 0)
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hlarge] with τ ht
    simp only [norm_one, one_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hn : (fun τ : ℍ ↦ H₃ τ + H₄ τ) =O[atImInfty] (fun _ ↦ (1 : ℝ)) :=
    (tendsto_H₃_atImInfty.add tendsto_H₄_atImInfty).isBigO_one ℝ
  have hfirst := hn.mul (isBigO_inv_H₂_atImInfty.pow 2)
  have hfirst' : (fun τ : ℍ ↦ (H₃ τ + H₄ τ) * (H₂ τ)⁻¹ ^ 2)
      =O[atImInfty] fun τ : ℍ ↦ Real.exp (2 * π * τ.im) := by
    refine hfirst.congr_right fun τ ↦ ?_
    rw [one_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  have hsecond := ((tendsto_H₄_atImInfty.sub isZeroAtImInfty_H₂).isBigO_one ℝ).mul
    (((tendsto_H₃_atImInfty.inv₀ (by norm_num : (1 : ℂ) ≠ 0)).pow 2).isBigO_one ℝ)
  have hsecond' : (fun τ : ℍ ↦ (H₄ τ - H₂ τ) * (H₃ τ)⁻¹ ^ 2)
      =O[atImInfty] fun τ : ℍ ↦ Real.exp (2 * π * τ.im) :=
    (hsecond.congr_right fun _ ↦ one_mul _).trans one_bigO_growth
  refine ((hfirst'.add hsecond').const_mul_left (128 : ℂ)).congr_left fun τ ↦ ?_
  rw [psiI_eq]
  simp only [Pi.smul_apply, Pi.add_apply, Pi.pow_apply, Pi.sub_apply,
    smul_eq_mul, div_eq_mul_inv, inv_pow, Pi.mul_apply, Pi.inv_apply]

/-- The E8 function `ψ_T` has growth `O(exp(2π Im τ))`. -/
theorem isBigO_psiT : psiT =O[atImInfty] fun τ : ℍ ↦ Real.exp (2 * π * τ.im) := by
  have hlarge : ∀ᶠ τ : ℍ in atImInfty, 0 ≤ τ.im :=
    preimage_mem_comap (Ici_mem_atTop 0)
  have he : (fun τ : ℍ ↦ Real.exp (-π * τ.im)) =O[atImInfty]
      fun τ : ℍ ↦ Real.exp (2 * π * τ.im) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hlarge] with τ ht
    simp only [Real.norm_of_nonneg (Real.exp_nonneg _), one_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have h := isBigO_psiI.sub (isBigO_psiS.trans he)
  refine h.congr_left fun τ ↦ ?_
  have heq := congrFun psiI_eq_psiT_add_psiS τ
  simp only [Pi.add_apply] at heq
  exact (eq_sub_iff_add_eq.mpr heq.symm).symm

end SphereCeti.E8
