/-
Copyright (c) 2026 Sphere-Packing-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere-Packing-Lean contributors, Bakhyt Momunov
-/

module

public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.SlashActions

import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Jacobi's quartic theta identity

The classical theta constants satisfy `H₂ + H₄ = H₃`. The square of their difference
is a weight-four cusp form for the full modular group, and that space is zero.

Adapted from `thefundamentaltheor3m/Sphere-Packing-Lean` at commit
`bad3de916074748eb88b7d1ee6dbf9494361ad17`,
`SpherePacking/ModularForms/JacobiTheta/JacobiIdentity.lean` (Apache-2.0).
The proof uses Mathlib's level-one slash-generator and dimension theorems directly.
-/

public section

open Complex Filter Topology ModularGroup SlashAction
open UpperHalfPlane (atImInfty)
open scoped UpperHalfPlane ModularForm MatrixGroups

namespace TauCeti.ModularForm

private noncomputable def defect : ℍ → ℂ := H₂ + H₄ - H₃

private theorem defect_S : defect ∣[(2 : ℤ)] S = -defect := by
  simp only [defect, sub_eq_add_neg, add_slash, neg_slash,
    H₂_slash_S, H₃_slash_S, H₄_slash_S]
  ext τ
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

private theorem defect_T : defect ∣[(2 : ℤ)] T = -defect := by
  simp only [defect, sub_eq_add_neg, add_slash, neg_slash,
    H₂_slash_T, H₃_slash_T, H₄_slash_T]
  ext τ
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

private noncomputable def defectSq : ℍ → ℂ := defect * defect

private theorem defectSq_S : defectSq ∣[(4 : ℤ)] S = defectSq := by
  rw [defectSq, show (4 : ℤ) = 2 + 2 by norm_num,
    _root_.ModularForm.mul_slash_SL2, defect_S, neg_mul_neg]

private theorem defectSq_T : defectSq ∣[(4 : ℤ)] T = defectSq := by
  rw [defectSq, show (4 : ℤ) = 2 + 2 by norm_num,
    _root_.ModularForm.mul_slash_SL2, defect_T, neg_mul_neg]

private theorem defectSq_invariant (γ : SL(2, ℤ)) : defectSq ∣[(4 : ℤ)] γ = defectSq :=
  _root_.SlashInvariantForm.slash_action_generators_SL2Z defectSq_S defectSq_T γ

private theorem defect_tendsto : Tendsto defect atImInfty (𝓝 0) := by
  have h2 : Tendsto H₂ atImInfty (𝓝 0) := isZeroAtImInfty_H₂
  change Tendsto (fun τ => H₂ τ + H₄ τ - H₃ τ) _ _
  simpa only [zero_add, sub_self] using (h2.add tendsto_H₄_atImInfty).sub tendsto_H₃_atImInfty

private theorem defectSq_tendsto : Tendsto defectSq atImInfty (𝓝 0) := by
  change Tendsto (fun τ => defect τ * defect τ) _ _
  simpa only [mul_zero] using defect_tendsto.mul defect_tendsto

private noncomputable def defectCusp : CuspForm 𝒮ℒ 4 where
  toFun := defectSq
  slash_action_eq' A hA := by
    obtain ⟨γ, rfl⟩ := hA
    exact defectSq_invariant γ
  holo' := by
    have hg := (mdifferentiable_H₂.add mdifferentiable_H₄).sub mdifferentiable_H₃
    exact hg.mul hg
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [defectSq_invariant]
    exact defectSq_tendsto

/-- **Jacobi's quartic identity:** `Θ₂⁴ + Θ₄⁴ = Θ₃⁴`. -/
theorem jacobi_identity : H₂ + H₄ = H₃ := by
  have hzero : defectCusp = 0 :=
    (rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num : (4 : ℤ) < 12))) defectCusp
  ext τ
  have h := DFunLike.congr_fun hzero τ
  change (H₂ τ + H₄ τ - H₃ τ) * (H₂ τ + H₄ τ - H₃ τ) = 0 at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).elim id id)

-- The identity exposes the positive difference used in the minus-kernel formulas.
example (τ : ℍ) : H₃ τ - H₂ τ = H₄ τ := by
  have h := congrFun jacobi_identity τ
  simp only [Pi.add_apply] at h
  linear_combination -h

end TauCeti.ModularForm
