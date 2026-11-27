/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.E8.MinusKernel.Holomorphic
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.Estimates

import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.NumberTheory.ModularForms.Petersson

/-!
# Exponential decay of the E8 minus-component function `ψ_S`

The constant terms in `(H₄ - H₂) / H₃² - (H₂ + H₃) / H₄²` cancel.
The remaining numerator factors through `H₄ - H₃` and `H₂`, both of exponential size
`O(exp(-π Im τ))`, while the denominator tends to one. Thus `ψ_S` has the same decay rate.

The proof is an independent algebraic factorization using the existing theta estimates.
-/

public section

open Complex Filter Topology Asymptotics
open UpperHalfPlane hiding I
open TauCeti.ModularForm

namespace SphereCeti.E8

/-- The inverted E8 minus-component function has exponential decay at the infinite cusp. -/
theorem isBigO_psiS : psiS =O[atImInfty] fun τ : ℍ => Real.exp (-Real.pi * τ.im) := by
  have h43 : (fun τ : ℍ => H₄ τ - H₃ τ) =O[atImInfty]
      (fun τ : ℍ => Real.exp (-Real.pi * τ.im)) := by
    simpa only [sub_sub_sub_cancel_right] using
      isBigO_H₄_sub_one_atImInfty.sub isBigO_H₃_sub_one_atImInfty
  have hB : Tendsto (fun τ : ℍ => H₄ τ ^ 2 + H₄ τ * H₃ τ + H₃ τ ^ 2)
      atImInfty (𝓝 3) := by
    convert ((tendsto_H₄_atImInfty.pow 2).add
      (tendsto_H₄_atImInfty.mul tendsto_H₃_atImInfty)).add
      (tendsto_H₃_atImInfty.pow 2) using 1
    norm_num
  have hC : Tendsto (fun τ : ℍ => H₄ τ ^ 2 + H₃ τ ^ 2) atImInfty (𝓝 2) := by
    convert (tendsto_H₄_atImInfty.pow 2).add (tendsto_H₃_atImInfty.pow 2) using 1
    norm_num
  have hN : (fun τ : ℍ => (H₄ τ - H₃ τ) *
      (H₄ τ ^ 2 + H₄ τ * H₃ τ + H₃ τ ^ 2) - H₂ τ * (H₄ τ ^ 2 + H₃ τ ^ 2))
      =O[atImInfty] (fun τ : ℍ => Real.exp (-Real.pi * τ.im)) := by
    simpa only [mul_one] using
      (h43.mul (hB.isBigO_one ℝ)).sub (isBigO_H₂_atImInfty.mul (hC.isBigO_one ℝ))
  have hD : Tendsto (fun τ : ℍ => (H₃ τ ^ 2 * H₄ τ ^ 2)⁻¹) atImInfty (𝓝 1) := by
    simpa using ((tendsto_H₃_atImInfty.pow 2).mul
      (tendsto_H₄_atImInfty.pow 2)).inv₀ (by norm_num : (1 : ℂ) ^ 2 * 1 ^ 2 ≠ 0)
  refine ((hN.mul (hD.isBigO_one ℝ)).const_mul_left (128 : ℂ)).congr_left (fun τ => ?_)
    |>.congr_right (fun τ => by simp only [mul_one])
  rw [psiS_eq]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply, Pi.add_apply, smul_eq_mul]
  have h3 := (theta_constants_ne_zero τ).2.1
  have h4 := (theta_constants_ne_zero τ).2.2
  field_simp
  ring

/-- The exponential estimate for `ψ_S` extended by zero to the complex plane. -/
theorem isBigO_psiSExt : (fun τ : ℍ => psiSExt τ) =O[atImInfty]
    (fun τ : ℍ => Real.exp (-Real.pi * τ.im)) :=
  isBigO_psiS.congr_left fun τ => (psiSExt_of_im_pos τ.im_pos).symm

/-- The extension of `ψ_S` is bounded at the infinite cusp. -/
theorem isBoundedAtImInfty_psiSExt : IsBoundedAtImInfty (fun τ : ℍ => psiSExt τ) :=
  (IsZeroAtImInfty.of_exp_decay ⟨Real.pi, Real.pi_pos, isBigO_psiSExt⟩).isBoundedAtImInfty

-- The constant factor in the corrected ray kernel preserves the decay rate.
example : (fun τ : ℍ => minusKernelRay τ) =O[atImInfty]
    (fun τ : ℍ => Real.exp (-Real.pi * τ.im)) := by
  simpa only [minusKernelRay_def] using isBigO_psiSExt.const_mul_left (-2 : ℂ)

end SphereCeti.E8
