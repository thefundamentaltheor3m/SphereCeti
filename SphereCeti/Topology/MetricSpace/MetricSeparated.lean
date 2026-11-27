/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Finiteness of separated sets

In a pseudometric space, a totally bounded set whose distinct points are at distance at least
`r > 0` is finite.  In a proper pseudometric space every bounded set is totally bounded, so a
bounded set with this separation is finite.

## Main statements

* `Metric.finite_of_totallyBounded_of_pairwise_le_dist`: a totally bounded set whose distinct
  points are at distance at least `r > 0` is finite.
* `Metric.finite_of_isBounded_of_pairwise_le_dist`: in a proper pseudometric space, a bounded set
  whose distinct points are at distance at least `r > 0` is finite.
-/

public section

open Bornology Set

namespace Metric

variable {α : Type*} [PseudoMetricSpace α] {S : Set α} {r : ℝ}

/-- A totally bounded set in a pseudometric space whose distinct points are at distance at least
`r > 0` is finite. -/
theorem finite_of_totallyBounded_of_pairwise_le_dist (hS : TotallyBounded S) (hr : 0 < r)
    (hsep : S.Pairwise fun x y ↦ r ≤ dist x y) : S.Finite := by
  -- A finite subset `t` of `S` whose balls of radius `r` cover `S` contains every point of `S`.
  obtain ⟨t, hts, ht, hcover⟩ := finite_approx_of_totallyBounded hS r hr
  refine ht.subset fun x hx ↦ ?_
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  by_contra hxt
  exact (mem_ball.mp hxy).not_ge (hsep hx (hts hy) fun h ↦ hxt (h ▸ hy))

/-- In a proper pseudometric space, a bounded set whose distinct points are at distance at least
`r > 0` is finite. -/
theorem finite_of_isBounded_of_pairwise_le_dist [ProperSpace α] (hS : IsBounded S) (hr : 0 < r)
    (hsep : S.Pairwise fun x y ↦ r ≤ dist x y) : S.Finite :=
  finite_of_totallyBounded_of_pairwise_le_dist
    (hS.isCompact_closure.totallyBounded.subset subset_closure) hr hsep

end Metric
