/-
Copyright (c) 2026 Sphere-Packing-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere-Packing-Lean contributors, Bakhyt Momunov
-/

module

public import SphereCeti.ModularForms.ThetaConstants.Basic
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold

import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Holomorphy of the classical theta constants

The fourth powers `H2`, `H3`, and `H4` are holomorphic on the upper half-plane.
For `H2`, both variables of `jacobiTheta₂` vary, so the proof uses its joint derivative.

Adapted from `thefundamentaltheor3m/Sphere-Packing-Lean` at commit
`bad3de916074748eb88b7d1ee6dbf9494361ad17`,
`SpherePacking/ModularForms/JacobiTheta/MDifferentiable.lean` (Apache-2.0).
The custom slash-invariant-form wrappers in that source are not needed here.
-/

public section

open Complex
open scoped UpperHalfPlane Manifold

namespace SphereCeti.ThetaConstants

private theorem differentiableAt_theta_half (τ : ℍ) :
    DifferentiableAt ℂ (fun z : ℂ => jacobiTheta₂ (z / 2) z) (τ : ℂ) := by
  let f : ℂ → ℂ × ℂ := fun z => (z / 2, z)
  have hf : DifferentiableAt ℂ f (τ : ℂ) :=
    (differentiableAt_id.mul_const ((2 : ℂ)⁻¹)).prodMk differentiableAt_id
  have hg : DifferentiableAt ℂ (fun p : ℂ × ℂ => jacobiTheta₂ p.1 p.2) (f τ) :=
    (hasFDerivAt_jacobiTheta₂ ((τ : ℂ) / 2) τ.2).differentiableAt
  exact hg.comp (τ : ℂ) hf

/-- The fourth power of `θ₂` is holomorphic. -/
theorem mdifferentiable_H2 : MDiff H2 := by
  intro τ
  have he : DifferentiableAt ℂ (fun z : ℂ => cexp (Real.pi * I * z / 4)) (τ : ℂ) :=
    ((differentiableAt_id.const_mul (Real.pi * I)).div_const 4).cexp
  exact ((he.mul (differentiableAt_theta_half τ)).pow 4).mdifferentiableAt.comp
    τ (UpperHalfPlane.mdifferentiable_coe τ)

/-- The fourth power of `θ₃` is holomorphic. -/
theorem mdifferentiable_H3 : MDiff H3 := mdifferentiable_jacobiTheta.pow 4

/-- The fourth power of `θ₄` is holomorphic. -/
theorem mdifferentiable_H4 : MDiff H4 := by
  intro τ
  exact ((differentiableAt_jacobiTheta₂_snd (1 / 2 : ℂ) τ.2).pow 4).mdifferentiableAt.comp
    τ (UpperHalfPlane.mdifferentiable_coe τ)

-- Polynomial kernel numerators inherit holomorphy.
example : MDiff (fun τ => (H3 τ + H4 τ) * H2 τ ^ 2) :=
  (mdifferentiable_H3.add mdifferentiable_H4).mul (mdifferentiable_H2.pow 2)

end SphereCeti.ThetaConstants
