/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors, Bakhyt Momunov
-/

module

public import SphereCeti.E8.MinusKernels
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.Discriminant

import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.NumberTheory.ModularForms.Identities
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# Holomorphy of the E8 minus-component modular functions

The theta-product formula for the discriminant ensures that `H₂` has no zeros on the upper
half-plane. Hence `h = 128 (H₃ + H₄) / H₂²` is holomorphic, and so are `ψ_I`, `ψ_S`, and `ψ_T`.
Their extensions by zero remain holomorphic and continuous on the open upper half-plane.

The quotient argument uses the theta nonvanishing theorem and pinned Mathlib holomorphy.
The extension and slash arguments are adapted from SphereCeti commit
`926b247f07e0b9a2a7923e9763bed9f4ab785141`, `SphereCeti/Leech/MinusKernels.lean`
(Apache-2.0, SphereCeti contributors).
-/

public section

open Complex ModularForm ModularGroup TauCeti.ModularForm
open UpperHalfPlane hiding I
open scoped Manifold

namespace SphereCeti.E8

/-- Viazovska's rational theta function `h` is holomorphic on the upper half-plane. -/
theorem mdifferentiable_hTheta : MDiff hTheta := by
  rw [hTheta_def]
  exact ((mdifferentiable_H₃.add mdifferentiable_H₄).div (mdifferentiable_H₂.pow 2)
    (fun τ => pow_ne_zero 2 (theta_constants_ne_zero τ).1)).const_smul 128

/-- The E8 modular function `ψ_I` is holomorphic. -/
theorem mdifferentiable_psiI : MDiff psiI := by
  rw [psiI_def, ModularForm.SL_slash]
  exact mdifferentiable_hTheta.sub (mdifferentiable_hTheta.slash _ _)

/-- The E8 modular function `ψ_S` is holomorphic. -/
theorem mdifferentiable_psiS : MDiff psiS := by
  rw [psiS_def, ModularForm.SL_slash]
  exact mdifferentiable_psiI.slash _ _

/-- The E8 modular function `ψ_T` is holomorphic. -/
theorem mdifferentiable_psiT : MDiff psiT := by
  rw [psiT_def, ModularForm.SL_slash]
  exact mdifferentiable_psiI.slash _ _

/-- The extension of `ψ_I` by zero is holomorphic on the open upper half-plane. -/
theorem differentiableOn_psiIExt : DifferentiableOn ℂ psiIExt {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_psiI).congr fun z (hz : 0 < z.im) => by
    rw [psiIExt_of_im_pos hz, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- The extension of `ψ_S` by zero is holomorphic on the open upper half-plane. -/
theorem differentiableOn_psiSExt : DifferentiableOn ℂ psiSExt {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_psiS).congr fun z (hz : 0 < z.im) => by
    rw [psiSExt_of_im_pos hz, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- The extension of `ψ_T` by zero is holomorphic on the open upper half-plane. -/
theorem differentiableOn_psiTExt : DifferentiableOn ℂ psiTExt {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_psiT).congr fun z (hz : 0 < z.im) => by
    rw [psiTExt_of_im_pos hz, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- `ψ_I`, extended by zero, is continuous on the open upper half-plane. -/
theorem continuousOn_psiIExt : ContinuousOn psiIExt {z : ℂ | 0 < z.im} :=
  differentiableOn_psiIExt.continuousOn

/-- `ψ_S`, extended by zero, is continuous on the open upper half-plane. -/
theorem continuousOn_psiSExt : ContinuousOn psiSExt {z : ℂ | 0 < z.im} :=
  differentiableOn_psiSExt.continuousOn

/-- `ψ_T`, extended by zero, is continuous on the open upper half-plane. -/
theorem continuousOn_psiTExt : ContinuousOn psiTExt {z : ℂ | 0 < z.im} :=
  differentiableOn_psiTExt.continuousOn

-- Multiplying by the contour Gaussian preserves holomorphy in its open domain.
example (r : ℝ) : DifferentiableOn ℂ
    (fun z : ℂ => psiTExt z * cexp (Real.pi * I * r * z)) {z : ℂ | 0 < z.im} :=
  differentiableOn_psiTExt.mul (by fun_prop)

end SphereCeti.E8
