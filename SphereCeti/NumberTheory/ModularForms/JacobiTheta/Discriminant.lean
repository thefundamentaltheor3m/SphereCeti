/-
Copyright (c) 2026 Sphere-Packing-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere-Packing-Lean contributors, Bakhyt Momunov
-/

module

public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.LeadingTerm
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.SlashActions
public import Mathlib.NumberTheory.ModularForms.Discriminant

import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The theta product and the modular discriminant

The squared product of the three fourth-power theta constants is `256 Δ`.
In particular, all three theta constants are nonzero throughout the upper half-plane.

Adapted from `thefundamentaltheor3m/Sphere-Packing-Lean` at commit
`bad3de916074748eb88b7d1ee6dbf9494361ad17`,
`SpherePacking/ModularForms/JacobiTheta/JacobiIdentity.lean` (Apache-2.0).
The weight-twelve dimension theorem and discriminant asymptotic are reused from Mathlib/TauCeti.
-/

public section

open Complex Filter Topology ModularGroup SlashAction
open UpperHalfPlane (atImInfty)
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

namespace TauCeti.ModularForm

private noncomputable def thetaProduct : ℍ → ℂ := H₂ * H₃ * H₄

private theorem thetaProduct_apply (τ : ℍ) : thetaProduct τ = H₂ τ * H₃ τ * H₄ τ := rfl

private theorem thetaProduct_S : thetaProduct ∣[(6 : ℤ)] S = -thetaProduct := by
  have houter := _root_.ModularForm.mul_slash_SL2 4 2 S (H₂ * H₃) H₄
  have hinner := _root_.ModularForm.mul_slash_SL2 2 2 S H₂ H₃
  norm_num only [Int.reduceAdd] at houter hinner
  rw [thetaProduct, houter, hinner, H₂_slash_S, H₃_slash_S, H₄_slash_S]
  ext τ
  simp only [Pi.mul_apply, Pi.neg_apply]
  ring

private theorem thetaProduct_T : thetaProduct ∣[(6 : ℤ)] T = -thetaProduct := by
  have houter := _root_.ModularForm.mul_slash_SL2 4 2 T (H₂ * H₃) H₄
  have hinner := _root_.ModularForm.mul_slash_SL2 2 2 T H₂ H₃
  norm_num only [Int.reduceAdd] at houter hinner
  rw [thetaProduct, houter, hinner, H₂_slash_T, H₃_slash_T, H₄_slash_T]
  ext τ
  simp only [Pi.mul_apply, Pi.neg_apply]
  ring

private noncomputable def thetaProductSq : ℍ → ℂ := thetaProduct * thetaProduct

private theorem thetaProductSq_apply (τ : ℍ) :
    thetaProductSq τ = thetaProduct τ * thetaProduct τ := rfl

private theorem thetaProductSq_S : thetaProductSq ∣[(12 : ℤ)] S = thetaProductSq := by
  simpa only [thetaProductSq, Int.reduceAdd, thetaProduct_S, neg_mul_neg] using
    _root_.ModularForm.mul_slash_SL2 6 6 S thetaProduct thetaProduct

private theorem thetaProductSq_T : thetaProductSq ∣[(12 : ℤ)] T = thetaProductSq := by
  simpa only [thetaProductSq, Int.reduceAdd, thetaProduct_T, neg_mul_neg] using
    _root_.ModularForm.mul_slash_SL2 6 6 T thetaProduct thetaProduct

private theorem thetaProductSq_invariant (γ : SL(2, ℤ)) :
    thetaProductSq ∣[(12 : ℤ)] γ = thetaProductSq :=
  _root_.SlashInvariantForm.slash_action_generators_SL2Z thetaProductSq_S thetaProductSq_T γ

private theorem thetaProductSq_tendsto : Tendsto thetaProductSq atImInfty (𝓝 0) := by
  have h2 : Tendsto H₂ atImInfty (𝓝 0) := isZeroAtImInfty_H₂
  have h := (h2.mul tendsto_H₃_atImInfty).mul tendsto_H₄_atImInfty
  have hp : Tendsto thetaProduct atImInfty (𝓝 0) := by
    simpa only [zero_mul] using h.congr (fun τ => (thetaProduct_apply τ).symm)
  simpa only [zero_mul] using (hp.mul hp).congr
    (fun τ => (thetaProductSq_apply τ).symm)

private noncomputable def thetaProductCusp : CuspForm 𝒮ℒ 12 where
  toFun := thetaProductSq
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact thetaProductSq_invariant γ
  holo' := by
    have h := (mdifferentiable_H₂.mul mdifferentiable_H₃).mul mdifferentiable_H₄
    exact h.mul h
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [thetaProductSq_invariant]
    exact thetaProductSq_tendsto

private theorem thetaProductCusp_apply (τ : ℍ) :
    thetaProductCusp τ = thetaProductSq τ := rfl

private theorem thetaProduct_proportional : ∃ c : ℂ, ∀ τ : ℍ,
    c * _root_.ModularForm.discriminant τ = (H₂ τ * H₃ τ * H₄ τ) ^ 2 := by
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve thetaProductCusp
  refine ⟨c, fun τ => ?_⟩
  have h := DFunLike.congr_fun hc τ
  simpa only [smul_apply, smul_eq_mul, CuspForm.coe_discriminant, thetaProductCusp_apply,
    thetaProductSq_apply, thetaProduct_apply, sq] using h

private theorem thetaProduct_leading :
    Tendsto (fun τ : ℍ => (H₂ τ * H₃ τ * H₄ τ) ^ 2 /
      cexp (2 * Real.pi * I * τ)) atImInfty (𝓝 256) := by
  have he (τ : ℍ) : (H₂ τ * H₃ τ * H₄ τ) ^ 2 / cexp (2 * Real.pi * I * τ) =
      (H₂ τ / cexp (Real.pi * I * τ)) ^ 2 * H₃ τ ^ 2 * H₄ τ ^ 2 := by
    have hq : cexp (2 * Real.pi * I * τ) = cexp (Real.pi * I * τ) ^ 2 := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    rw [hq]
    ring
  simp_rw [he]
  convert ((tendsto_H₂_div_exp_atImInfty.pow 2).mul (tendsto_H₃_atImInfty.pow 2)).mul
    (tendsto_H₄_atImInfty.pow 2) using 1
  norm_num

/-- The theta-product formula for the normalized modular discriminant. -/
theorem discriminant_eq_theta_product (τ : ℍ) :
    _root_.ModularForm.discriminant τ = (H₂ τ * H₃ τ * H₄ τ) ^ 2 / 256 := by
  obtain ⟨c, hc⟩ := thetaProduct_proportional
  have hdelta : Tendsto (fun τ : ℍ => _root_.ModularForm.discriminant τ /
      cexp (2 * Real.pi * I * τ)) atImInfty (𝓝 1) := by
    simpa only [Function.Periodic.qParam, ofReal_one, div_one] using
      tendsto_discriminant_div_qParam_atImInfty
  have hlim : Tendsto (fun τ : ℍ => c * (_root_.ModularForm.discriminant τ /
      cexp (2 * Real.pi * I * τ))) atImInfty (𝓝 c) := by
    simpa only [mul_one] using hdelta.const_mul c
  have he (τ : ℍ) : c * (_root_.ModularForm.discriminant τ /
      cexp (2 * Real.pi * I * τ)) =
      (H₂ τ * H₃ τ * H₄ τ) ^ 2 / cexp (2 * Real.pi * I * τ) := by
    rw [← mul_div_assoc, hc]
  have hc256 : c = 256 := tendsto_nhds_unique (hlim.congr he) thetaProduct_leading
  have h := hc τ
  rw [hc256] at h
  exact (eq_div_iff (by norm_num : (256 : ℂ) ≠ 0)).mpr (by simpa only [mul_comm] using h)

/-- None of the three fourth-power theta constants vanishes on the upper half-plane. -/
theorem theta_constants_ne_zero (τ : ℍ) : H₂ τ ≠ 0 ∧ H₃ τ ≠ 0 ∧ H₄ τ ≠ 0 := by
  have hp : H₂ τ * H₃ τ * H₄ τ ≠ 0 := by
    intro h
    have hd := _root_.ModularForm.discriminant_ne_zero τ
    rw [discriminant_eq_theta_product, h, zero_pow (by decide : 2 ≠ 0), zero_div] at hd
    exact hd rfl
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).2, (mul_ne_zero_iff.mp hp).2⟩

-- The nonvanishing theorem permits the rational numerator used by the minus kernels.
example : MDiff (fun τ => (H₃ τ + H₄ τ) / H₂ τ ^ 2) :=
  (mdifferentiable_H₃.add mdifferentiable_H₄).div (mdifferentiable_H₂.pow 2)
    (fun τ => pow_ne_zero 2 (theta_constants_ne_zero τ).1)

end TauCeti.ModularForm
