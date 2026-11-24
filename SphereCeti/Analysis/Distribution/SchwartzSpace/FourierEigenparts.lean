/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic.Module

/-!
# The positive and negative Fourier eigenparts of radial Schwartz functions

The continuous linear maps `SchwartzMap.fourierPlusCLM` and `SchwartzMap.fourierMinusCLM` send
`f` to `(f + 𝓕 f) / 2` and `(f - 𝓕 f) / 2`. They reconstruct every Schwartz function. On even
Schwartz functions, where the Fourier transform is an involution, they are complementary
projections onto the Fourier eigenspaces with eigenvalues `+1` and `-1`. In particular they
preserve radiality and give the unique such decomposition of a radial Schwartz function.

This implements the Fourier eigenspace operations of README Layer 7 and MIGRATION J1, using
the Fourier invariance and involution results of PR #121. The operators are defined on the
existing Schwartz space, so no second radial-function type or Fourier transform is introduced.

## Main statements

* `SchwartzMap.fourierPlusCLM_add_fourierMinusCLM`: the two parts sum to the original function.
* `SchwartzMap.fourier_fourierPlusCLM`, `SchwartzMap.fourier_fourierMinusCLM`: the Fourier
  eigenfunction identities for an even input.
* `SchwartzMap.isRadial_fourierPlusCLM`, `SchwartzMap.isRadial_fourierMinusCLM`: both parts of
  a radial function are radial.
* `SchwartzMap.fourierPlusCLM_idempotent`, `SchwartzMap.fourierMinusCLM_idempotent`: each
  projection fixes its own output for an even input; the two mixed compositions vanish.
* `SchwartzMap.fourier_eigenparts_unique`: any decomposition into `+1` and `-1` eigenfunctions
  agrees with these two parts.

## Provenance

The formulas are the Fourier eigenspace operations described by `selfAdjointPart_eq` and
`skewAdjointPart_eq` in `thefundamentaltheor3m/Sphere-Packing-Lean`, commit
`f8733f4c4ecb6bd6cd4d093746b30a22f675fa00`, file
`SpherePacking/ForMathlib/RadialSchwartz/Basic.lean` (Sidharth Hariharan and Seewoo Lee,
Apache-2.0). The proofs here apply the existing Schwartz Fourier linear map directly, without
introducing the production file's Fourier-as-star instances. The underlying Fourier transform
is Mathlib's, with the normalization fixed by SphereCeti's CONVENTIONS §10.

The intended upstream home is Mathlib's Schwartz Fourier API (UPSTREAM A7).
-/

public section

open FourierTransform
open scoped SchwartzMap

namespace SchwartzMap

variable (𝕜 : Type*) [RCLike 𝕜]
  {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]

/-- The positive Fourier eigenpart, `(f + 𝓕 f) / 2`, as a continuous linear map. It is a
projection on the even Schwartz functions. -/
noncomputable def fourierPlusCLM : 𝓢(V, E) →L[𝕜] 𝓢(V, E) :=
  (1 / 2 : 𝕜) • (ContinuousLinearMap.id 𝕜 _ + fourierCLM 𝕜 _)

/-- The negative Fourier eigenpart, `(f - 𝓕 f) / 2`, as a continuous linear map. It is a
projection on the even Schwartz functions. -/
noncomputable def fourierMinusCLM : 𝓢(V, E) →L[𝕜] 𝓢(V, E) :=
  (1 / 2 : 𝕜) • (ContinuousLinearMap.id 𝕜 _ - fourierCLM 𝕜 _)

/-- Evaluation of the positive Fourier eigenpart. -/
@[simp]
theorem fourierPlusCLM_apply (f : 𝓢(V, E)) :
    fourierPlusCLM 𝕜 f = (1 / 2 : 𝕜) • (f + 𝓕 f) := by
  simp [fourierPlusCLM]

/-- Evaluation of the negative Fourier eigenpart. -/
@[simp]
theorem fourierMinusCLM_apply (f : 𝓢(V, E)) :
    fourierMinusCLM 𝕜 f = (1 / 2 : 𝕜) • (f - 𝓕 f) := by
  simp [fourierMinusCLM]

/-- The two Fourier eigenparts reconstruct every Schwartz function. -/
theorem fourierPlusCLM_add_fourierMinusCLM (f : 𝓢(V, E)) :
    fourierPlusCLM 𝕜 f + fourierMinusCLM 𝕜 f = f := by
  simp only [fourierPlusCLM_apply, fourierMinusCLM_apply]
  module

/-- The positive part fixes a Fourier eigenfunction of eigenvalue `+1`. -/
theorem fourierPlusCLM_of_fourier_eq {f : 𝓢(V, E)} (hf : 𝓕 f = f) :
    fourierPlusCLM 𝕜 f = f := by
  rw [fourierPlusCLM_apply, hf]
  module

/-- The negative part kills a Fourier eigenfunction of eigenvalue `+1`. -/
theorem fourierMinusCLM_of_fourier_eq {f : 𝓢(V, E)} (hf : 𝓕 f = f) :
    fourierMinusCLM 𝕜 f = 0 := by
  simp [hf]

/-- The positive part kills a Fourier eigenfunction of eigenvalue `-1`. -/
theorem fourierPlusCLM_of_fourier_eq_neg {f : 𝓢(V, E)} (hf : 𝓕 f = -f) :
    fourierPlusCLM 𝕜 f = 0 := by
  simp [hf]

/-- The negative part fixes a Fourier eigenfunction of eigenvalue `-1`. -/
theorem fourierMinusCLM_of_fourier_eq_neg {f : 𝓢(V, E)} (hf : 𝓕 f = -f) :
    fourierMinusCLM 𝕜 f = f := by
  rw [fourierMinusCLM_apply, hf]
  module

/-- The positive Fourier eigenpart of a radial Schwartz function is radial. -/
theorem isRadial_fourierPlusCLM {f : 𝓢(V, E)} (hf : (⇑f).IsRadial) :
    (⇑(fourierPlusCLM 𝕜 f)).IsRadial := by
  rw [Function.isRadial_def]
  intro x y hxy
  simp only [fourierPlusCLM_apply, smul_apply, add_apply]
  rw [hf hxy, isRadial_fourier hf hxy]

/-- The negative Fourier eigenpart of a radial Schwartz function is radial. -/
theorem isRadial_fourierMinusCLM {f : 𝓢(V, E)} (hf : (⇑f).IsRadial) :
    (⇑(fourierMinusCLM 𝕜 f)).IsRadial := by
  rw [Function.isRadial_def]
  intro x y hxy
  simp only [fourierMinusCLM_apply, smul_apply, sub_apply]
  rw [hf hxy, isRadial_fourier hf hxy]

/-- Any splitting into Fourier eigenfunctions with eigenvalues `+1` and `-1` is the splitting
given by the two continuous linear maps. -/
theorem fourier_eigenparts_unique {f g h : 𝓢(V, E)} (hsum : g + h = f)
    (hg : 𝓕 g = g) (hh : 𝓕 h = -h) :
    g = fourierPlusCLM 𝕜 f ∧ h = fourierMinusCLM 𝕜 f := by
  subst f
  constructor
  · rw [map_add, fourierPlusCLM_of_fourier_eq 𝕜 hg,
      fourierPlusCLM_of_fourier_eq_neg 𝕜 hh, add_zero]
  · rw [map_add, fourierMinusCLM_of_fourier_eq 𝕜 hg,
      fourierMinusCLM_of_fourier_eq_neg 𝕜 hh, zero_add]

variable [CompleteSpace E]

/-- The positive Fourier eigenpart of an even Schwartz function has Fourier eigenvalue `+1`.
Radial inputs satisfy the hypothesis by `Function.IsRadial.even`. -/
theorem fourier_fourierPlusCLM (f : 𝓢(V, E)) (hf : Function.Even ⇑f) :
    𝓕 (fourierPlusCLM 𝕜 f) = fourierPlusCLM 𝕜 f := by
  rw [fourierPlusCLM_apply, FourierTransform.fourier_smul, FourierTransform.fourier_add,
    fourier_fourier_of_even f hf]
  module

/-- The negative Fourier eigenpart of an even Schwartz function has Fourier eigenvalue `-1`.
Radial inputs satisfy the hypothesis by `Function.IsRadial.even`. -/
theorem fourier_fourierMinusCLM (f : 𝓢(V, E)) (hf : Function.Even ⇑f) :
    𝓕 (fourierMinusCLM 𝕜 f) = -fourierMinusCLM 𝕜 f := by
  simp only [fourierMinusCLM_apply, sub_eq_add_neg]
  rw [FourierTransform.fourier_smul, FourierTransform.fourier_add,
    FourierTransform.fourier_neg, fourier_fourier_of_even f hf]
  module

/-- The positive projection is idempotent on even Schwartz functions. -/
theorem fourierPlusCLM_idempotent (f : 𝓢(V, E)) (hf : Function.Even ⇑f) :
    fourierPlusCLM 𝕜 (fourierPlusCLM 𝕜 f) = fourierPlusCLM 𝕜 f :=
  fourierPlusCLM_of_fourier_eq 𝕜 (fourier_fourierPlusCLM 𝕜 f hf)

/-- The negative projection kills the positive part of an even Schwartz function. -/
theorem fourierMinusCLM_fourierPlusCLM (f : 𝓢(V, E)) (hf : Function.Even ⇑f) :
    fourierMinusCLM 𝕜 (fourierPlusCLM 𝕜 f) = 0 :=
  fourierMinusCLM_of_fourier_eq 𝕜 (fourier_fourierPlusCLM 𝕜 f hf)

/-- The positive projection kills the negative part of an even Schwartz function. -/
theorem fourierPlusCLM_fourierMinusCLM (f : 𝓢(V, E)) (hf : Function.Even ⇑f) :
    fourierPlusCLM 𝕜 (fourierMinusCLM 𝕜 f) = 0 :=
  fourierPlusCLM_of_fourier_eq_neg 𝕜 (fourier_fourierMinusCLM 𝕜 f hf)

/-- The negative projection is idempotent on even Schwartz functions. -/
theorem fourierMinusCLM_idempotent (f : 𝓢(V, E)) (hf : Function.Even ⇑f) :
    fourierMinusCLM 𝕜 (fourierMinusCLM 𝕜 f) = fourierMinusCLM 𝕜 f :=
  fourierMinusCLM_of_fourier_eq_neg 𝕜 (fourier_fourierMinusCLM 𝕜 f hf)

/-! ## Behavior checks -/

/-- The evaluation simp lemmas expose the pointwise formulas. -/
example (f : 𝓢(V, E)) (x : V) :
    fourierPlusCLM 𝕜 f x = (1 / 2 : 𝕜) • (f x + 𝓕 f x) ∧
      fourierMinusCLM 𝕜 f x = (1 / 2 : 𝕜) • (f x - 𝓕 f x) := by
  simp

/-- The decomposition can be used directly on a radial input. -/
example (f : 𝓢(V, E)) (hf : (⇑f).IsRadial) :
    𝓕 (fourierPlusCLM 𝕜 f) = fourierPlusCLM 𝕜 f ∧
      𝓕 (fourierMinusCLM 𝕜 f) = -fourierMinusCLM 𝕜 f :=
  ⟨fourier_fourierPlusCLM 𝕜 f hf.even, fourier_fourierMinusCLM 𝕜 f hf.even⟩

end SchwartzMap
