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

The finite branch of the Layer 8 contour deformation integrates scalar one-forms
`v ↦ F z * v` along paths and deforms those paths with Mathlib's curve-integral Poincaré lemma.
That lemma takes two hypotheses on a one-form `ω` on a set `s`: differentiability with
continuity up to the closure, and symmetry of the within-derivative on tangent vectors.  This file
packages the two hypotheses as `ClosedOneFormOn` and proves that the scalar one-form of a
function that is complex differentiable on `s` and continuous on its closure satisfies them.

The symmetry is proved at every point of `s`, without assuming that `s` is open or has unique
differentials: any real derivative of the one-form agrees on the tangent cone with the one
obtained from the complex derivative of `F`, and the latter is symmetric.

## Main definitions and results

* `SphereCeti.Contour.scalarOneForm` and `SphereCeti.Contour.scalarOneForm_apply`: the roadmap's
  `SphereCeti.Suggested.Contour.scalarOneForm` and its evaluation lemma, with the same formulas.
* `SphereCeti.Contour.ClosedOneFormOn`: the roadmap structure of the same name, with the same
  fields.
* `SphereCeti.Contour.ClosedOneFormOn.of_diffContOnCl`: the roadmap target of the same name, with
  the same statement.

This is an independent formalization; no proof text is adapted from another repository.
-/

public section

namespace SphereCeti.Contour

/-- The scalar one-form `v ↦ F z * v` of a function `F : ℂ → ℂ`. -/
@[expose]
noncomputable def scalarOneForm (F : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z => F z • ContinuousLinearMap.id ℂ ℂ

@[simp]
theorem scalarOneForm_apply (F : ℂ → ℂ) (z v : ℂ) : scalarOneForm F z v = F z * v := rfl

example (F : ℂ → ℂ) (z : ℂ) : scalarOneForm F z 1 = F z := by simp

/-- Closedness of a one-form on a set, as one structure combining two hypotheses: differentiability
with continuity up to the closure, and symmetry of the within-derivative on tangent vectors.  This
local structure packages the hypotheses of Mathlib's curve-integral Poincaré lemma, which takes them
separately. -/
structure ClosedOneFormOn (ω : ℂ → ℂ →L[ℂ] ℂ) (s : Set ℂ) : Prop where
  diffContOnCl : DiffContOnCl ℝ ω s
  symm : ∀ x ∈ s, ∀ u ∈ tangentConeAt ℝ s x, ∀ v ∈ tangentConeAt ℝ s x,
    fderivWithin ℝ ω s x u v = fderivWithin ℝ ω s x v u

/-- Sufficient condition: complex differentiability (holomorphy) of `F` on `s` with continuity on
the closure makes its scalar one-form closed.  The converse is not a target. -/
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
