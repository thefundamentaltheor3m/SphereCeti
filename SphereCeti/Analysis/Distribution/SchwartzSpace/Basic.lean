/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Constructing Schwartz functions from bounds at infinity

`SchwartzMap.mkOfCocompact` constructs a Schwartz function from a smooth function whose
polynomially weighted derivatives are bounded outside compact sets. Continuity bounds each
weighted derivative on the remaining compact set, giving the global Schwartz bounds.

This is the general constructor needed by the magic-function Schwartz proofs (MIGRATION J3,
UPSTREAM A6). It has no finite-dimensionality assumption on the domain.

## Main definitions and results

* `SchwartzMap.mkOfCocompact`: construct a Schwartz function from cocompact decay bounds.
* `SchwartzMap.mkOfCocompact_apply`: evaluation agrees with the original function.

## Source

Adapted from `thefundamentaltheor3m/Sphere-Packing-Lean` at commit
`bad3de916074748eb88b7d1ee6dbf9494361ad17`, file
`SpherePacking/ForMathlib/RadialSchwartz/SchwartzMap.lean` (Apache-2.0, Bhavik Mehta).
The original license and author header are retained.
-/

public section

open Filter Topology
open scoped ContDiff SchwartzMap

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Construct a Schwartz function from a smooth function whose polynomial derivative bounds
hold outside compact sets. Continuity supplies the bounds on each remaining compact set. -/
@[expose]
def mkOfCocompact (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ k n : ℕ, ∃ C : ℝ,
      ∀ᶠ x in cocompact E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) : 𝓢(E, F) where
  toFun := f
  smooth' := smooth
  decay' k n := by
    obtain ⟨C, hC⟩ := decay k n
    obtain ⟨K, hK, hbound⟩ := mem_cocompact.mp hC
    let g : E → ℝ := fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
    have hg : Continuous g :=
      (continuous_norm.pow k).mul
        (smooth.continuous_iteratedFDeriv (m := n) (by simp)).norm
    obtain ⟨C', hC'⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨max C C', fun x => ?_⟩
    by_cases hx : x ∈ K
    · exact (Real.le_norm_self (g x)).trans ((hC' x hx).trans (le_max_right C C'))
    · exact (hbound hx).trans (le_max_left C C')

/-- Evaluation of a Schwartz function constructed from cocompact bounds. -/
@[simp]
theorem mkOfCocompact_apply (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ k n : ℕ, ∃ C : ℝ,
      ∀ᶠ x in cocompact E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : E) :
    mkOfCocompact f smooth decay x = f x := rfl

-- The evaluation rule simplifies under an arbitrary function without expanding decay bounds.
example {G : Type*} (h : F → G) (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ k n : ℕ, ∃ C : ℝ,
      ∀ᶠ x in cocompact E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : E) :
    h (mkOfCocompact f smooth decay x) = h (f x) := by simp

end SchwartzMap
