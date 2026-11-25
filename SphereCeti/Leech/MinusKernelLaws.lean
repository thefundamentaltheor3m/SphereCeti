/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors, Bakhyt Momunov
-/

module

public import SphereCeti.Leech.MinusKernels
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.JacobiIdentity

import Mathlib.NumberTheory.ModularForms.Identities
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# The remaining signed laws of the Leech minus kernels

Jacobi's quartic identity gives `ψ_I = ψ_T + ψ_S`. Slashing that relation by `S`
and `T` gives the two anti-invariance laws, including the left/right contour-kernel law.

The signed-relation and extension arguments are adapted from SphereCeti commit
`4ac9c927524a84ecbb54b1b7abd403c4abdb724e`, `SphereCeti/E8/MinusKernels.lean`
(Apache-2.0, SphereCeti contributors). The Leech polynomial identity uses the formulas from
SphereCeti commit `926b247f07e0b9a2a7923e9763bed9f4ab785141`,
`SphereCeti/Leech/MinusKernels.lean`, with Jacobi's identity.
-/

public section

open Complex ModularForm ModularGroup TauCeti.ModularForm
open UpperHalfPlane hiding I

namespace SphereCeti.Leech

/-- The three Leech minus-component modular functions satisfy `ψ_I = ψ_T + ψ_S`. -/
theorem psiI_eq_psiT_add_psiS : psiI = psiT + psiS := by
  rw [psiI_def, psiT_eq, psiS_eq]
  ext τ
  simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
    Pi.pow_apply, Pi.neg_apply, smul_eq_mul]
  have hj := congrFun jacobi_identity τ
  simp only [Pi.add_apply] at hj
  rw [← hj]
  ring

/-- The translated Leech modular function is anti-invariant under inversion. -/
theorem psiT_slash_S : psiT ∣[(-10 : ℤ)] S = -psiT := by
  rw [eq_sub_of_add_eq psiI_eq_psiT_add_psiS.symm, SlashAction.sub_slash,
    psiS_slash_S, ← psiS_def, neg_sub]

/-- The inverted Leech modular function is anti-invariant under translation by one. -/
theorem psiS_slash_T : psiS ∣[(-10 : ℤ)] T = -psiS := by
  rw [eq_sub_of_add_eq' psiI_eq_psiT_add_psiS.symm, SlashAction.sub_slash,
    psiT_slash_T, ← psiT_def, neg_sub]

/-- The left/right law of the Leech `-1` kernels, including the negative eigenvalue. -/
theorem minusKernel_law_leftRight (z : ℂ) :
    (I / z) ^ 12 * minusKernelLeft z = -(z ^ 2)⁻¹ * minusKernelRight (-z⁻¹) := by
  rcases le_or_gt z.im 0 with hz | hz
  · have hz' : (-z⁻¹).im ≤ 0 := by
      rw [neg_im, inv_im, neg_div, neg_neg]
      exact div_nonpos_of_nonpos_of_nonneg hz (normSq_nonneg z)
    rw [minusKernelLeft_def, minusKernelRight_def, psiTExt_of_im_nonpos hz,
      psiTExt_of_im_nonpos hz', mul_zero, mul_zero]
  · have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
    have hz' : 0 < (-z⁻¹).im := by
      rw [neg_im, inv_im, neg_div, neg_neg]
      exact div_pos hz (normSq_pos.mpr hz0)
    have h := congrFun psiT_slash_S ⟨z, hz⟩
    simp only [SlashInvariantForm.slash_S_apply, Pi.neg_apply, inv_neg, neg_neg, zpow_ofNat] at h
    rw [minusKernelLeft_def, minusKernelRight_def, psiTExt_of_im_pos hz, psiTExt_of_im_pos hz']
    generalize psiT ⟨-z⁻¹, hz'⟩ = a at h ⊢
    generalize psiT ⟨z, hz⟩ = b at h ⊢
    rw [div_pow, (by norm_num [pow_mul, I_pow_four] : I ^ 12 = 1)]
    field_simp
    linear_combination h

-- The pointwise relation can be used in a concrete kernel numerator.
example (τ : ℍ) : psiI τ - psiS τ = psiT τ := by
  have h := congrFun psiI_eq_psiT_add_psiS τ
  simp only [Pi.add_apply] at h
  linear_combination h

end SphereCeti.Leech
