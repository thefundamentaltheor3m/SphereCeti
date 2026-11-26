/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Constructing Schwartz functions from bounds at infinity

`SchwartzMap.mkOfCocompact` constructs a Schwartz function from a smooth function whose
polynomially weighted derivatives are bounded outside compact sets. It has no
finite-dimensionality assumption on the domain.

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
hold outside compact sets. -/
def mkOfCocompact (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ k n : ℕ, ∃ C : ℝ,
      ∀ᶠ x in cocompact E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) : 𝓢(E, F) where
  toFun := f
  smooth' := smooth
  decay' k n := by
    obtain ⟨C, hC⟩ := decay k n
    let g : E → ℝ := fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
    have hg : Continuous g :=
      (continuous_norm.pow k).mul
        (smooth.continuous_iteratedFDeriv (m := n) (by simp)).norm
    have hg0 (x : E) : 0 ≤ g x :=
      mul_nonneg (pow_nonneg (norm_nonneg x) k) (norm_nonneg _)
    have hO : g =O[cocompact E] (1 : E → ℝ) := by
      refine Asymptotics.IsBigO.of_bound C ?_
      filter_upwards [hC] with x hx
      simpa only [Pi.one_apply, norm_one, mul_one, Real.norm_of_nonneg (hg0 x)] using hx
    obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (hg.isBounded_range_iff_isBigO.mpr hO)
    exact ⟨B, fun x => (Real.le_norm_self (g x)).trans (hB (g x) ⟨x, rfl⟩)⟩

/-- Evaluation of a Schwartz function constructed from cocompact bounds. -/
@[simp]
theorem mkOfCocompact_apply (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ k n : ℕ, ∃ C : ℝ,
      ∀ᶠ x in cocompact E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : E) :
    mkOfCocompact f smooth decay x = f x := (rfl)

-- The evaluation rule simplifies under an arbitrary function without expanding decay bounds.
example {G : Type*} (h : F → G) (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ k n : ℕ, ∃ C : ℝ,
      ∀ᶠ x in cocompact E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) (x : E) :
    h (mkOfCocompact f smooth decay x) = h (f x) := by simp

end SchwartzMap
