/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.LeadingTerm

import SphereCeti.Analysis.Asymptotics.Pow
import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Exponential estimates for the fourth-power theta constants

As the imaginary part tends to infinity, `H₂`, `H₃ - 1`, and `H₄ - 1` are all
`O(exp(-π im τ))`. These estimates retain the exponential rate needed for integrability
of rational theta kernels. They follow from the normalized leading term of `H₂`,
Mathlib's one-variable theta estimate, and translation by one.

-/

public section

open Complex Filter Topology Asymptotics
open UpperHalfPlane (atImInfty)
open scoped UpperHalfPlane

namespace TauCeti.ModularForm

/-- The second fourth-power theta constant decays at least as fast as `exp(-π im τ)`. -/
theorem isBigO_H₂_atImInfty :
    H₂ =O[atImInfty] (fun τ : ℍ => Real.exp (-Real.pi * τ.im)) := by
  have h : H₂ =O[atImInfty] (fun τ : ℍ => cexp (Real.pi * I * τ)) :=
    isBigO_of_div_tendsto_nhds
      (.of_forall fun τ h => (Complex.exp_ne_zero _ h).elim) 16 tendsto_H₂_div_exp_atImInfty
  have he (τ : ℍ) : ‖cexp (Real.pi * I * τ)‖ = Real.exp (-Real.pi * τ.im) := by
    simp [Complex.norm_exp]
  simpa only [he] using h.norm_right

/-- The error in the constant term of `H₃` decays exponentially with rate `π`. -/
theorem isBigO_H₃_sub_one_atImInfty :
    (fun τ : ℍ => H₃ τ - 1) =O[atImInfty]
      (fun τ : ℍ => Real.exp (-Real.pi * τ.im)) := by
  have htheta : (fun τ : ℍ => Θ₃ τ - 1) =O[atImInfty]
      (fun τ : ℍ => Real.exp (-Real.pi * τ.im)) := by
    simpa only [Function.comp_def, Θ₃_def, UpperHalfPlane.coe_im] using
      isBigO_at_im_infty_jacobiTheta_sub_one.comp_tendsto UpperHalfPlane.tendsto_coe_atImInfty
  simpa only [H₃_def, one_pow] using (htheta.pow_sub_pow_of_tendsto tendsto_Θ₃_atImInfty 4)

/-- The error in the constant term of `H₄` has the same exponential rate as `H₃`. -/
theorem isBigO_H₄_sub_one_atImInfty :
    (fun τ : ℍ => H₄ τ - 1) =O[atImInfty]
      (fun τ : ℍ => Real.exp (-Real.pi * τ.im)) := by
  have ht : Tendsto (fun τ : ℍ => (1 : ℝ) +ᵥ τ) atImInfty atImInfty := by
    simpa [UpperHalfPlane.atImInfty, tendsto_comap_iff, Function.comp_def] using
      (tendsto_comap : Tendsto UpperHalfPlane.im atImInfty atTop)
  simpa only [Function.comp_def, H₃_def, H₄_def, Θ₃_one_vadd, UpperHalfPlane.vadd_im] using
    isBigO_H₃_sub_one_atImInfty.comp_tendsto ht

-- Cancellation of constant terms preserves the exponential error rate.
example : (fun τ : ℍ => H₃ τ - H₄ τ) =O[atImInfty]
    (fun τ : ℍ => Real.exp (-Real.pi * τ.im)) := by
  simpa only [sub_sub_sub_cancel_right] using
    isBigO_H₃_sub_one_atImInfty.sub isBigO_H₄_sub_one_atImInfty

end TauCeti.ModularForm
