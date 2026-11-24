/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# Closed scalar one-forms of holomorphic functions

A contour integral `∫_γ F(z) dz` of a function `F : ℂ → ℂ` is the curve integral of the scalar
one-form `z ↦ (v ↦ F z * v)`.  Deforming a contour without changing the integral requires this
one-form to be closed on the region swept out by the deformation, which is the content of the
curve-integral Poincaré lemma.  For a one-form `ω : ℂ → (ℂ →L[ℂ] ℂ)` on a set `s ⊆ ℂ`, closedness
means here: `ω` is real-differentiable on `s` and continuous on its closure, and at every point
`x ∈ s` the within-derivative of `ω` is symmetric on pairs of tangent vectors to `s` at `x`.

The main result is that the scalar one-form of a holomorphic function is closed: if `F` is complex
differentiable on `s` and continuous on the closure of `s`, then `scalarOneForm F` is closed on
`s`.  No openness or unique-differentiability hypothesis on `s` is needed.

## Main definitions

* `SphereCeti.Contour.scalarOneForm F`: the one-form `z ↦ (v ↦ F z * v)`.
* `SphereCeti.Contour.ClosedOneFormOn ω s`: closedness of the one-form `ω` on `s`, in the sense
  above.

## Main results

* `SphereCeti.Contour.ClosedOneFormOn.of_diffContOnCl`: if `F` is complex differentiable on `s`
  and continuous on its closure, then `scalarOneForm F` is closed on `s`.

## Provenance

The definitions and the statement follow the `gauss2` branch of Sphere-Packing-Lean at commit
`01f23eccf963c50250c9e48dd103e8cc88c36f85`, file
`SpherePacking/Contour/MobiusInv/WedgeSetContour.lean`.  The proofs in this file were written
independently of that source; no proof text is copied from it.
-/

public section

namespace SphereCeti.Contour

/-- The scalar one-form `v ↦ F z * v` of a function `F : ℂ → ℂ`, whose curve integral along a
path `γ` is the contour integral `∫_γ F(z) dz`. -/
noncomputable def scalarOneForm (F : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z => F z • ContinuousLinearMap.id ℂ ℂ

/-- The scalar one-form as a continuous linear map: `F z` times the identity of `ℂ`. -/
theorem scalarOneForm_def (F : ℂ → ℂ) (z : ℂ) :
    scalarOneForm F z = F z • ContinuousLinearMap.id ℂ ℂ := (rfl)

/-- Evaluation of the scalar one-form: `scalarOneForm F z v = F z * v`. -/
@[simp]
theorem scalarOneForm_apply (F : ℂ → ℂ) (z v : ℂ) : scalarOneForm F z v = F z * v := (rfl)

example (F : ℂ → ℂ) (z : ℂ) : scalarOneForm F z 1 = F z := by simp

/-- A one-form `ω` is closed on `s` if it is real-differentiable on `s` and continuous on the
closure of `s`, and at each `x ∈ s` its within-derivative is symmetric on tangent vectors to `s`
at `x`.  These are the hypotheses of Mathlib's curve-integral Poincaré lemma, combined into one
structure. -/
structure ClosedOneFormOn (ω : ℂ → ℂ →L[ℂ] ℂ) (s : Set ℂ) : Prop where
  diffContOnCl : DiffContOnCl ℝ ω s
  symm : ∀ x ∈ s, ∀ u ∈ tangentConeAt ℝ s x, ∀ v ∈ tangentConeAt ℝ s x,
    fderivWithin ℝ ω s x u v = fderivWithin ℝ ω s x v u

/-- The scalar one-form of a holomorphic function is closed: if `F` is complex differentiable on
`s` and continuous on the closure of `s`, then `scalarOneForm F` is closed on `s`. -/
theorem ClosedOneFormOn.of_diffContOnCl {F : ℂ → ℂ} {s : Set ℂ}
    (hF : DiffContOnCl ℂ F s) : ClosedOneFormOn (scalarOneForm F) s := by
  -- `scalarOneForm F = L ∘ F` for the continuous `ℂ`-linear map `L c = c • id`.
  set L : ℂ →L[ℂ] ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMap.id ℂ ℂ)
  have hω : scalarOneForm F = fun z => L (F z) := by
    funext z
    ext
    simp [L]
  have hFℝ : DiffContOnCl ℝ F s := ⟨hF.differentiableOn.restrictScalars ℝ, hF.continuousOn⟩
  refine ⟨?_, ?_⟩
  · rw [hω]
    exact (L.restrictScalars ℝ).differentiable.comp_diffContOnCl hFℝ
  · intro x hx u hu v hv
    -- Any real derivative of the one-form agrees on the tangent cone with the one obtained from
    -- the complex derivative of `F`, and the latter is symmetric since `ℂ` is commutative.
    -- A real derivative of the one-form built from the complex derivative of `F`.
    have hD : HasFDerivWithinAt (scalarOneForm F)
        ((L.comp (fderivWithin ℂ F s x)).restrictScalars ℝ) s x := by
      rw [hω]
      exact (L.hasFDerivAt.comp_hasFDerivWithinAt x
        (hF.differentiableOn x hx).hasFDerivWithinAt).restrictScalars ℝ
    have hdiff : DifferentiableWithinAt ℝ (scalarOneForm F) s x := hD.differentiableWithinAt
    have huniq := hdiff.hasFDerivWithinAt.unique_on hD
    rw [huniq hu, huniq hv]
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_comp,
      Function.comp_apply, L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      smul_apply, smul_eq_mul]
    have hu' : fderivWithin ℂ F s x u = u * fderivWithin ℂ F s x 1 := by
      rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
    have hv' : fderivWithin ℂ F s x v = v * fderivWithin ℂ F s x 1 := by
      rw [← smul_eq_mul, ← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]
    rw [hu', hv']
    ring

end SphereCeti.Contour
