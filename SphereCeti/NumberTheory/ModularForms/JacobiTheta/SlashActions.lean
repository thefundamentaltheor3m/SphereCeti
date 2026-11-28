/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.NumberTheory.ModularForms.SlashActions
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.Basic
import Mathlib.NumberTheory.ModularForms.Identities
import TauCeti.NumberTheory.ModularForms.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Slash actions on the fourth powers of the Jacobi thetanullwerte

In weight `2`, the generators `T = [[1, 1], [0, 1]]` and `S = [[0, -1], [1, 0]]` of `SL(2, ℤ)`
act on the fourth powers `H₂ = Θ₂⁴`, `H₃ = Θ₃⁴` and `H₄ = Θ₄⁴` of the Jacobi thetanullwerte by
signed permutations:

* `H₂ ∣[2] T = -H₂`, `H₃ ∣[2] T = H₄` and `H₄ ∣[2] T = H₃`;
* `H₂ ∣[2] S = -H₄`, `H₃ ∣[2] S = -H₃` and `H₄ ∣[2] S = -H₂`.

The central element `-1` acts trivially on all three.

## Main statements

* `TauCeti.ModularForm.H₂_slash_T`, `TauCeti.ModularForm.H₃_slash_T`,
  `TauCeti.ModularForm.H₄_slash_T`: the action of `T`.
* `TauCeti.ModularForm.H₂_slash_S`, `TauCeti.ModularForm.H₃_slash_S`,
  `TauCeti.ModularForm.H₄_slash_S`: the action of `S`.
* `TauCeti.ModularForm.H₂_slash_neg_one`, `TauCeti.ModularForm.H₃_slash_neg_one`,
  `TauCeti.ModularForm.H₄_slash_neg_one`: the action of `-1`.

## References

* D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer (2008), §3.1.
* D. Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser (1983),
  Chapter I.
* The statements follow the `gauss2` branch of Sphere-Packing-Lean at commit
  `01f23eccf963c50250c9e48dd103e8cc88c36f85`, file
  `SpherePacking/ModularForms/JacobiTheta/SlashActions.lean` (`H₂_T_action`, `H₃_T_action`,
  `H₄_T_action`, `H₂_S_action`, `H₃_S_action`, `H₄_S_action` and the `negI` actions). The proofs
  in this file were written independently of that source; no proof text is copied from it.
-/

public section

open Complex ModularGroup
open UpperHalfPlane hiding I
open scoped Real ModularForm MatrixGroups

namespace TauCeti.ModularForm

/-! ### The translation `T` -/

/-- `H₂ ∣[2] T = -H₂`. -/
theorem H₂_slash_T : H₂ ∣[(2 : ℤ)] T = -H₂ := by
  ext τ
  have h4 : cexp (π * I / 4) ^ 4 = -1 := by
    rw [← Complex.exp_nat_mul, (by push_cast; ring : ((4 : ℕ) : ℂ) * (π * I / 4) = π * I),
      exp_pi_mul_I]
  rw [← zpow_one T, slash_T_zpow_apply, Int.cast_one, Pi.neg_apply, H₂_def, H₂_def, Θ₂_one_vadd,
    mul_pow, h4, neg_one_mul]

/-- `H₃ ∣[2] T = H₄`. -/
theorem H₃_slash_T : H₃ ∣[(2 : ℤ)] T = H₄ := by
  ext τ
  rw [← zpow_one T, slash_T_zpow_apply, Int.cast_one, H₃_def, H₄_def, Θ₃_one_vadd]

/-- `H₄ ∣[2] T = H₃`. -/
theorem H₄_slash_T : H₄ ∣[(2 : ℤ)] T = H₃ := by
  ext τ
  rw [← zpow_one T, slash_T_zpow_apply, Int.cast_one, H₄_def, H₃_def, Θ₄_one_vadd]

/-! ### The inversion `S` -/

/-- `H₃ ∣[2] S = -H₃`. -/
theorem H₃_slash_S : H₃ ∣[(2 : ℤ)] S = -H₃ := by
  ext τ
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hpow : ((-I * τ) ^ (1 / 2 : ℂ)) ^ 4 = -τ ^ 2 := by
    rw [← cpow_mul_nat, (by norm_num : (1 / 2 : ℂ) * (4 : ℕ) = 2), cpow_two, mul_pow, neg_sq, I_sq,
      neg_one_mul]
  rw [ModularForm.SL_slash_apply, denom_S, Pi.neg_apply, H₃_def, H₃_def, Θ₃_def, Θ₃_def,
    jacobiTheta_S_smul, mul_pow, hpow]
  field_simp

/-- `H₄ ∣[2] S = -H₂`. -/
theorem H₄_slash_S : H₄ ∣[(2 : ℤ)] S = -H₂ := by
  ext τ
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have e1 : -I * (-(τ : ℂ))⁻¹ = I / τ := by rw [inv_neg, neg_mul_neg, div_eq_mul_inv]
  have e2 : -π * I * (1 / 2) ^ 2 / (-(τ : ℂ))⁻¹ = π * I * τ / 4 := by rw [div_inv_eq_mul]; ring
  have e3 : 1 / 2 / (-(τ : ℂ))⁻¹ = -(τ / 2) := by rw [div_inv_eq_mul]; ring
  have e4 : -1 / (-(τ : ℂ))⁻¹ = τ := by rw [div_inv_eq_mul]; ring
  -- the functional equation of `jacobiTheta₂` at `z = 1 / 2` and the point `-1 / τ`
  have hθ : jacobiTheta₂ (1 / 2) (-τ : ℂ)⁻¹ = 1 / (I / τ) ^ (1 / 2 : ℂ) * Θ₂ τ := by
    rw [jacobiTheta₂_functional_equation, e1, e2, e3, e4, jacobiTheta₂_neg_left, Θ₂_def,
      mul_assoc (1 / (I / (τ : ℂ)) ^ (1 / 2 : ℂ))]
  have hpow : ((I / τ) ^ (1 / 2 : ℂ)) ^ 4 = -1 / τ ^ 2 := by
    rw [← cpow_mul_nat, (by norm_num : (1 / 2 : ℂ) * (4 : ℕ) = 2), cpow_two, div_pow, I_sq]
  rw [SlashInvariantForm.slash_S_apply, Pi.neg_apply, H₄_def, Θ₄_def, coe_mk, hθ, mul_pow, div_pow,
    one_pow, hpow, H₂_def]
  field_simp

/-- `H₂ ∣[2] S = -H₄`. -/
theorem H₂_slash_S : H₂ ∣[(2 : ℤ)] S = -H₄ := by
  have h := SL_slash_S_slash_S 2 H₄
  rw [H₄_slash_S, SlashAction.neg_slash, neg_eq_iff_eq_neg] at h
  rw [h]
  norm_num

/-! ### The central element `-1` -/

/-- `H₂ ∣[2] (-1) = H₂`. -/
theorem H₂_slash_neg_one : H₂ ∣[(2 : ℤ)] (-1 : SL(2, ℤ)) = H₂ := by
  rw [SL_slash_neg, SlashAction.slash_one]
  norm_num

/-- `H₃ ∣[2] (-1) = H₃`. -/
theorem H₃_slash_neg_one : H₃ ∣[(2 : ℤ)] (-1 : SL(2, ℤ)) = H₃ := by
  rw [SL_slash_neg, SlashAction.slash_one]
  norm_num

/-- `H₄ ∣[2] (-1) = H₄`. -/
theorem H₄_slash_neg_one : H₄ ∣[(2 : ℤ)] (-1 : SL(2, ℤ)) = H₄ := by
  rw [SL_slash_neg, SlashAction.slash_one]
  norm_num

end TauCeti.ModularForm
