/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Group.RadialFunction

/-!
# Composition of one-variable Schwartz functions with the squared norm

On a real inner product space `E`, composing a one-variable Schwartz function `f : 𝓢(ℝ, F)` with
the squared norm `x ↦ ‖x‖ ^ 2` yields a radial Schwartz function on `E`.  Because the squared norm
is smooth of temperate growth and satisfies `‖x‖ ≤ 1 + ‖x‖ ^ 2`, precomposition with `‖·‖ ^ 2`
defines a continuous linear map `SchwartzMap.compNormSqCLM : 𝓢(ℝ, F) →L[𝕜] 𝓢(E, F)` without any
finite-dimensionality assumption on `E`.

Radiality itself remains Mathlib's `Function.IsRadial`, factoring through `‖·‖`; this file
provides the squared-norm profile constructor used to build radial Schwartz functions, such as
auxiliary functions in sphere packing, from one-variable profiles in `‖x‖ ^ 2`.

## Main definitions

* `SchwartzMap.compNormSqCLM`: the continuous `𝕜`-linear map `𝓢(ℝ, F) →L[𝕜] 𝓢(E, F)` sending
  `f` to `x ↦ f (‖x‖ ^ 2)`.

## Main statements

* `SchwartzMap.compNormSqCLM_apply`: pointwise evaluation `(compNormSqCLM 𝕜 E f) x = f (‖x‖ ^ 2)`.
* `SchwartzMap.coe_compNormSqCLM`: function-level coercion of `compNormSqCLM 𝕜 E f`.
* `SchwartzMap.isRadial_compNormSqCLM`: every `compNormSqCLM 𝕜 E f` is radial
  (`Function.IsRadial`).
* `SchwartzMap.compNormSqCLM_eq_of_eqOn`, `SchwartzMap.compNormSqCLM_eq_iff`: `compNormSqCLM 𝕜 E f`
  depends only on the restriction of `f` to `[0, ∞)`, and on a nontrivial space is determined by
  that restriction.
-/

public section

open scoped SchwartzMap

namespace SchwartzMap

section CompNormSq

variable (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

/-- Compose a one-variable Schwartz function on `ℝ` with the squared norm `x ↦ ‖x‖ ^ 2` on a
real inner product space, as a continuous `𝕜`-linear map `𝓢(ℝ, F) →L[𝕜] 𝓢(E, F)`. -/
noncomputable def compNormSqCLM : 𝓢(ℝ, F) →L[𝕜] 𝓢(E, F) :=
  compCLM 𝕜 (Function.hasTemperateGrowth_norm_sq E)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, norm_pow, norm_norm]
      nlinarith [sq_nonneg (‖x‖ - 1)]⟩

variable {𝕜 E}

/-- Pointwise evaluation of a Schwartz function composed with the squared norm. -/
@[simp]
theorem compNormSqCLM_apply (f : 𝓢(ℝ, F)) (x : E) :
    compNormSqCLM 𝕜 E f x = f (‖x‖ ^ 2) := by
  simp [compNormSqCLM]

/-- Coercion of `compNormSqCLM 𝕜 E f` to a function `E → F`. -/
theorem coe_compNormSqCLM (f : 𝓢(ℝ, F)) :
    ⇑(compNormSqCLM 𝕜 E f) = fun x : E => f (‖x‖ ^ 2) :=
  funext (compNormSqCLM_apply f)

/-- Every Schwartz function obtained by composing a one-variable profile with the squared norm
is radial. -/
@[fun_prop]
theorem isRadial_compNormSqCLM (f : 𝓢(ℝ, F)) :
    Function.IsRadial (compNormSqCLM 𝕜 E f) := by
  rw [coe_compNormSqCLM]
  exact (Function.isRadial_norm_sq E).comp_right (g := f)

/-- Two one-variable Schwartz profiles that agree on `[0, ∞)` define the same squared-norm
Schwartz function. -/
theorem compNormSqCLM_eq_of_eqOn {f g : 𝓢(ℝ, F)} (h : Set.EqOn f g (Set.Ici 0)) :
    compNormSqCLM 𝕜 E f = compNormSqCLM 𝕜 E g := by
  ext x
  simpa using h (sq_nonneg ‖x‖)

/-- On a nontrivial real inner product space, two one-variable Schwartz profiles define the same
squared-norm Schwartz function if and only if they agree on `[0, ∞)`. -/
theorem compNormSqCLM_eq_iff [Nontrivial E] {f g : 𝓢(ℝ, F)} :
    compNormSqCLM 𝕜 E f = compNormSqCLM 𝕜 E g ↔ Set.EqOn f g (Set.Ici 0) := by
  refine ⟨fun h t ht => ?_, compNormSqCLM_eq_of_eqOn⟩
  obtain ⟨x, hx⟩ := exists_norm_eq E (Real.sqrt_nonneg t)
  simpa [hx, Real.sq_sqrt ht] using DFunLike.congr_fun h x

/-! ### Automation behavior checks -/

example (f : 𝓢(ℝ, F)) (x : E) : compNormSqCLM 𝕜 E f x = f (‖x‖ ^ 2) := by simp

example (f : 𝓢(ℝ, F)) : compNormSqCLM 𝕜 E f 0 = f 0 := by simp

example (f g : 𝓢(ℝ, F)) (c : 𝕜) (x : E) :
    compNormSqCLM 𝕜 E (c • f + g) x = c • f (‖x‖ ^ 2) + g (‖x‖ ^ 2) := by simp

example (f : 𝓢(ℝ, F)) : Function.IsRadial (compNormSqCLM 𝕜 E f) := by fun_prop

example {G : Type*} (f : 𝓢(ℝ, F)) (h : F → G) :
    Function.IsRadial (fun x : E => h (compNormSqCLM 𝕜 E f x)) := by fun_prop

end CompNormSq

end SchwartzMap
