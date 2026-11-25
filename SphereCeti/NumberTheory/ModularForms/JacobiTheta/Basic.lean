/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Basic
import SphereCeti.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp

/-!
# The Jacobi thetanullwerte and their fourth powers

The Jacobi thetanullwerte are the three functions on the upper half-plane

* `Θ₂ τ = ∑_{n ∈ ℤ} exp (π i (n + 1 / 2)² τ)`,
* `Θ₃ τ = ∑_{n ∈ ℤ} exp (π i n² τ)`,
* `Θ₄ τ = ∑_{n ∈ ℤ} (-1)ⁿ exp (π i n² τ)`,

classically `θ₁₀`, `θ₀₀` and `θ₀₁`. They are defined here through Mathlib's two-variable theta
function `jacobiTheta₂ z τ = ∑_{n ∈ ℤ} exp (2 π i n z + π i n² τ)`: `Θ₂ τ` is
`exp (π i τ / 4) jacobiTheta₂ (τ / 2) τ`, `Θ₃ τ` is `jacobiTheta τ = jacobiTheta₂ 0 τ`, and `Θ₄ τ`
is `jacobiTheta₂ (1 / 2) τ`. Their fourth powers are `H₂ = Θ₂⁴`, `H₃ = Θ₃⁴` and `H₄ = Θ₄⁴`. As
lattice theta series, `Θ₃` is the theta series of `ℤ ⊆ ℝ` (`ZLattice.thetaSeries_span_one`) and
`Θ₂` is the theta series of its translate `1 / 2 + ℤ`.

For every `τ ∈ ℍ`, `Θ₂ (τ + 1) = exp (π i / 4) Θ₂ τ`, `Θ₃ (τ + 1) = Θ₄ τ` and
`Θ₄ (τ + 1) = Θ₃ τ`. All six functions are holomorphic on `ℍ`. As `im τ → ∞`, `Θ₂ τ → 0`,
`Θ₃ τ → 1` and `Θ₄ τ → 1`, so `H₂`, `H₃` and `H₄` are bounded at `i∞`. The transformation laws
of `H₂`, `H₃` and `H₄` under `SL(2, ℤ)` are in
`SphereCeti.NumberTheory.ModularForms.JacobiTheta.SlashActions`.

## Main definitions

* `TauCeti.ModularForm.Θ₂`, `TauCeti.ModularForm.Θ₃`, `TauCeti.ModularForm.Θ₄`: the
  thetanullwerte on `ℍ`.
* `TauCeti.ModularForm.H₂`, `TauCeti.ModularForm.H₃`, `TauCeti.ModularForm.H₄`: their fourth
  powers.

## Main statements

* `TauCeti.ModularForm.Θ₂_eq_tsum`, `TauCeti.ModularForm.Θ₃_eq_tsum`,
  `TauCeti.ModularForm.Θ₄_eq_tsum`: the series over `ℤ`.
* `TauCeti.ModularForm.Θ₂_eq_thetaCoset`: `Θ₂` is the theta series of `1 / 2 + ℤ`.
* `TauCeti.ModularForm.Θ₂_one_vadd`, `TauCeti.ModularForm.Θ₃_one_vadd`,
  `TauCeti.ModularForm.Θ₄_one_vadd`: translation by `1`.
* `TauCeti.ModularForm.mdifferentiable_Θ₂` and its siblings: holomorphy on `ℍ`.
* `TauCeti.ModularForm.isZeroAtImInfty_Θ₂`, `TauCeti.ModularForm.tendsto_Θ₃_atImInfty`,
  `TauCeti.ModularForm.tendsto_Θ₄_atImInfty`: the limits at `i∞`, and their analogues for the
  fourth powers.
* `TauCeti.ModularForm.isBoundedAtImInfty_H₂`, `TauCeti.ModularForm.isBoundedAtImInfty_H₃`,
  `TauCeti.ModularForm.isBoundedAtImInfty_H₄`: boundedness at `i∞`.

## References

* D. Zagier, *Elliptic modular forms and their applications*, in *The 1-2-3 of Modular Forms*,
  Universitext, Springer (2008), §3.1.
* D. Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser (1983),
  Chapter I.
* The definitions and statements follow the `gauss2` branch of Sphere-Packing-Lean at commit
  `01f23eccf963c50250c9e48dd103e8cc88c36f85`, files
  `SpherePacking/ModularForms/JacobiTheta/Basic.lean` and
  `SpherePacking/ModularForms/JacobiTheta/SlashActions.lean`. The proofs in this file were written
  independently of that source; no proof text is copied from it.
-/

public section

open Complex Filter Topology Submodule
open UpperHalfPlane (atImInfty IsBoundedAtImInfty IsZeroAtImInfty)
open scoped Real UpperHalfPlane Manifold

namespace TauCeti.ModularForm

/-- The Jacobi thetanullwert `Θ₂ τ = ∑_{n ∈ ℤ} exp (π i (n + 1 / 2)² τ)` on the upper half-plane,
defined as `exp (π i τ / 4) jacobiTheta₂ (τ / 2) τ`; the series is `Θ₂_eq_tsum`. -/
noncomputable def Θ₂ (τ : ℍ) : ℂ := cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ

/-- The Jacobi thetanullwert `Θ₃ τ = ∑_{n ∈ ℤ} exp (π i n² τ)` on the upper half-plane: Mathlib's
`jacobiTheta` restricted to `ℍ`. -/
noncomputable def Θ₃ (τ : ℍ) : ℂ := jacobiTheta τ

/-- The Jacobi thetanullwert `Θ₄ τ = ∑_{n ∈ ℤ} (-1)ⁿ exp (π i n² τ)` on the upper half-plane,
defined as `jacobiTheta₂ (1 / 2) τ`; the series is `Θ₄_eq_tsum`. -/
noncomputable def Θ₄ (τ : ℍ) : ℂ := jacobiTheta₂ (1 / 2) τ

/-- The fourth power `H₂ = Θ₂⁴` of the Jacobi thetanullwert `Θ₂`. -/
noncomputable def H₂ (τ : ℍ) : ℂ := Θ₂ τ ^ 4

/-- The fourth power `H₃ = Θ₃⁴` of the Jacobi thetanullwert `Θ₃`. -/
noncomputable def H₃ (τ : ℍ) : ℂ := Θ₃ τ ^ 4

/-- The fourth power `H₄ = Θ₄⁴` of the Jacobi thetanullwert `Θ₄`. -/
noncomputable def H₄ (τ : ℍ) : ℂ := Θ₄ τ ^ 4

/-- The defining formula of `Θ₂`. -/
theorem Θ₂_def (τ : ℍ) : Θ₂ τ = cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ := (rfl)

/-- The defining formula of `Θ₃`. -/
theorem Θ₃_def (τ : ℍ) : Θ₃ τ = jacobiTheta τ := (rfl)

/-- The defining formula of `Θ₄`. -/
theorem Θ₄_def (τ : ℍ) : Θ₄ τ = jacobiTheta₂ (1 / 2) τ := (rfl)

/-- The defining formula of `H₂`. -/
theorem H₂_def (τ : ℍ) : H₂ τ = Θ₂ τ ^ 4 := (rfl)

/-- The defining formula of `H₃`. -/
theorem H₃_def (τ : ℍ) : H₃ τ = Θ₃ τ ^ 4 := (rfl)

/-- The defining formula of `H₄`. -/
theorem H₄_def (τ : ℍ) : H₄ τ = Θ₄ τ ^ 4 := (rfl)

/-! ### The series -/

/-- `Θ₂ τ = ∑_{n ∈ ℤ} exp (π i (n + 1 / 2)² τ)` for every `τ ∈ ℍ`. -/
theorem Θ₂_eq_tsum (τ : ℍ) : Θ₂ τ = ∑' n : ℤ, cexp (π * I * (n + 1 / 2) ^ 2 * τ) := by
  rw [Θ₂_def, jacobiTheta₂, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  ring_nf

/-- `Θ₃ τ = ∑_{n ∈ ℤ} exp (π i n² τ)` for every `τ ∈ ℍ`. -/
theorem Θ₃_eq_tsum (τ : ℍ) : Θ₃ τ = ∑' n : ℤ, cexp (π * I * n ^ 2 * τ) := by
  rw [Θ₃_def, jacobiTheta]

/-- `Θ₄ τ = ∑_{n ∈ ℤ} (-1)ⁿ exp (π i n² τ)` for every `τ ∈ ℍ`. -/
theorem Θ₄_eq_tsum (τ : ℍ) : Θ₄ τ = ∑' n : ℤ, (-1) ^ n * cexp (π * I * n ^ 2 * τ) := by
  rw [Θ₄_def, jacobiTheta₂]
  refine tsum_congr fun n ↦ ?_
  rw [jacobiTheta₂_term, ← exp_pi_mul_I, ← exp_int_mul, ← Complex.exp_add]
  ring_nf

/-- `Θ₂` is the theta series of the translate `1 / 2 + ℤ` of the lattice `ℤ ⊆ ℝ`:
`Θ₂ τ = ∑_{v ∈ ℤ} exp (π i (1 / 2 + v)² τ)` for every `τ ∈ ℍ`. -/
theorem Θ₂_eq_thetaCoset (τ : ℍ) :
    Θ₂ τ = ZLattice.thetaCoset (span ℤ {1} : Submodule ℤ ℝ) (1 / 2) τ := by
  rw [Θ₂_eq_tsum, ZLattice.thetaCoset_apply,
    ← (LinearEquiv.toSpanNonzeroSingleton ℤ ℝ 1 one_ne_zero).toEquiv.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp [Real.norm_eq_abs, sq_abs, add_comm]

/-! ### Translation by one -/

/-- `Θ₂ (τ + 1) = exp (π i / 4) Θ₂ τ` for every `τ ∈ ℍ`. -/
theorem Θ₂_one_vadd (τ : ℍ) : Θ₂ ((1 : ℝ) +ᵥ τ) = cexp (π * I / 4) * Θ₂ τ := by
  have h : ((τ : ℂ) + 1) / 2 + 1 / 2 = τ / 2 + 1 := by ring
  rw [Θ₂_def, Θ₂_def, UpperHalfPlane.coe_vadd, ofReal_one, add_comm (1 : ℂ),
    TauCeti.jacobiTheta₂_add_one_right, h, jacobiTheta₂_add_left, ← mul_assoc, ← Complex.exp_add]
  ring_nf

/-- `Θ₃ (τ + 1) = Θ₄ τ` for every `τ ∈ ℍ`. -/
theorem Θ₃_one_vadd (τ : ℍ) : Θ₃ ((1 : ℝ) +ᵥ τ) = Θ₄ τ := by
  rw [Θ₃_def, Θ₄_def, jacobiTheta_eq_jacobiTheta₂, UpperHalfPlane.coe_vadd, ofReal_one,
    add_comm (1 : ℂ), TauCeti.jacobiTheta₂_add_one_right, zero_add]

/-- `Θ₄ (τ + 1) = Θ₃ τ` for every `τ ∈ ℍ`. -/
theorem Θ₄_one_vadd (τ : ℍ) : Θ₄ ((1 : ℝ) +ᵥ τ) = Θ₃ τ := by
  rw [Θ₄_def, Θ₃_def, jacobiTheta_eq_jacobiTheta₂, UpperHalfPlane.coe_vadd, ofReal_one,
    add_comm (1 : ℂ), TauCeti.jacobiTheta₂_add_one_right, add_halves, ← zero_add 1,
    jacobiTheta₂_add_left]

/-! ### Holomorphy -/

/-- `Θ₂` is holomorphic on `ℍ`. -/
theorem mdifferentiable_Θ₂ : MDiff Θ₂ := by
  rw [funext Θ₂_eq_thetaCoset]
  exact ZLattice.mdifferentiable_thetaCoset _ _

/-- `Θ₃` is holomorphic on `ℍ`. -/
theorem mdifferentiable_Θ₃ : MDiff Θ₃ := by
  rw [funext Θ₃_def]
  exact mdifferentiable_jacobiTheta

/-- `Θ₄` is holomorphic on `ℍ`. -/
theorem mdifferentiable_Θ₄ : MDiff Θ₄ := by
  rw [funext Θ₄_def]
  exact fun τ ↦
    (differentiableAt_jacobiTheta₂_snd (1 / 2) τ.2).mdifferentiableAt.comp τ τ.mdifferentiable_coe

/-- `H₂` is holomorphic on `ℍ`. -/
theorem mdifferentiable_H₂ : MDiff H₂ := by
  rw [funext H₂_def]
  exact mdifferentiable_Θ₂.pow 4

/-- `H₃` is holomorphic on `ℍ`. -/
theorem mdifferentiable_H₃ : MDiff H₃ := by
  rw [funext H₃_def]
  exact mdifferentiable_Θ₃.pow 4

/-- `H₄` is holomorphic on `ℍ`. -/
theorem mdifferentiable_H₄ : MDiff H₄ := by
  rw [funext H₄_def]
  exact mdifferentiable_Θ₄.pow 4

/-! ### Behaviour at `i∞` -/

/-- `Θ₂ τ → 0` as `im τ → ∞`. -/
theorem isZeroAtImInfty_Θ₂ : IsZeroAtImInfty Θ₂ := by
  rw [funext Θ₂_eq_thetaCoset]
  refine ZLattice.isZeroAtImInfty_thetaCoset _ fun h ↦ ?_
  -- `1 / 2` is not an integer
  obtain ⟨n, hn⟩ := mem_span_singleton.mp h
  rw [zsmul_eq_mul, mul_one] at hn
  have : 2 * n = 1 := by exact_mod_cast (by linarith : (2 * n : ℝ) = 1)
  omega

/-- `Θ₃ τ → 1` as `im τ → ∞`. -/
theorem tendsto_Θ₃_atImInfty : Tendsto Θ₃ atImInfty (𝓝 1) := by
  rw [funext Θ₃_def]
  exact TauCeti.tendsto_jacobiTheta_comap_im_atTop.comp UpperHalfPlane.tendsto_coe_atImInfty

/-- `Θ₄ τ → 1` as `im τ → ∞`. -/
theorem tendsto_Θ₄_atImInfty : Tendsto Θ₄ atImInfty (𝓝 1) := by
  have h : Tendsto (fun τ : ℍ ↦ (1 : ℝ) +ᵥ τ) atImInfty atImInfty := by
    rw [UpperHalfPlane.atImInfty, tendsto_comap_iff]
    simpa [Function.comp_def, UpperHalfPlane.vadd_im] using tendsto_comap
  simpa [Function.comp_def, Θ₃_one_vadd] using tendsto_Θ₃_atImInfty.comp h

/-- `H₂ τ → 0` as `im τ → ∞`. -/
theorem isZeroAtImInfty_H₂ : IsZeroAtImInfty H₂ := by
  have h : Tendsto (fun τ ↦ Θ₂ τ ^ 4) atImInfty (𝓝 0) := by
    simpa using isZeroAtImInfty_Θ₂.pow 4
  rwa [funext H₂_def]

/-- `H₃ τ → 1` as `im τ → ∞`. -/
theorem tendsto_H₃_atImInfty : Tendsto H₃ atImInfty (𝓝 1) := by
  rw [funext H₃_def]
  simpa using tendsto_Θ₃_atImInfty.pow 4

/-- `H₄ τ → 1` as `im τ → ∞`. -/
theorem tendsto_H₄_atImInfty : Tendsto H₄ atImInfty (𝓝 1) := by
  rw [funext H₄_def]
  simpa using tendsto_Θ₄_atImInfty.pow 4

/-- `H₂` is bounded at `i∞`. -/
theorem isBoundedAtImInfty_H₂ : IsBoundedAtImInfty H₂ :=
  isZeroAtImInfty_H₂.isBoundedAtImInfty

/-- `H₃` is bounded at `i∞`. -/
theorem isBoundedAtImInfty_H₃ : IsBoundedAtImInfty H₃ :=
  tendsto_H₃_atImInfty.isBigO_one ℝ

/-- `H₄` is bounded at `i∞`. -/
theorem isBoundedAtImInfty_H₄ : IsBoundedAtImInfty H₄ :=
  tendsto_H₄_atImInfty.isBigO_one ℝ

end TauCeti.ModularForm
