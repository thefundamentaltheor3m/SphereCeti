/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Top-edge integrals under uniform decay

The half-infinite rectangle deformation of Layer 8 controls the top edge of the rectangle by
convergence of the top-edge integrals to zero.  This file proves that this hypothesis follows from
uniform decay of the integrand along the edge as the imaginary part grows.

## Main results

* `SphereCeti.Contour.tendsto_top_edge_of_uniform_decay`: the roadmap target
  `SphereCeti.Suggested.Contour.tendsto_top_edge_of_uniform_decay`, with the same conclusion and
  without its interval-integrability hypothesis.

The roadmap target also assumes interval integrability of every horizontal edge.  That hypothesis
is not needed: uniform decay bounds the norm of the interval integral whether or not the integrand
is integrable, because a non-integrable integral takes the junk value `0`.  The `example` at the
end of this file checks that the target, with its full hypothesis list, follows.

## Proof

For `ε > 0`, uniform convergence gives, for all large `m`, the bound `‖f (x + m i)‖ < ε` on
`[[x₁, x₂]]`.  Then `intervalIntegral.norm_integral_le_of_norm_le_const` bounds the top-edge
integral by `ε * |x₂ - x₁|`.

This is an independent formalization; no proof text is adapted from another repository.
-/

public section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace SphereCeti.Contour

/-- The top-edge integrals of a half-infinite rectangle tend to zero when `f` decays uniformly on
the edge as the imaginary part grows.  No integrability hypothesis is needed: the bound on the
interval integral holds also for its junk value. -/
theorem tendsto_top_edge_of_uniform_decay
    {f : ℂ → ℂ} {x₁ x₂ : ℝ}
    (hdecay : TendstoUniformlyOn (fun m : ℝ => fun x : ℝ => f (x + m * Complex.I)) 0 atTop
      (Set.uIcc x₁ x₂)) :
    Tendsto (fun m : ℝ => ∫ x in x₁..x₂, f (x + m * Complex.I)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / (|x₂ - x₁| + 1)
  have hden : 0 < |x₂ - x₁| + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hdecay δ hδ] with m hm
  have hbound : ‖∫ x in x₁..x₂, f (x + m * Complex.I)‖ ≤ δ * |x₂ - x₁| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    have := hm x (Set.uIoc_subset_uIcc hx)
    simpa [dist_eq_norm] using this.le
  have hlt : δ * |x₂ - x₁| < ε := by
    calc δ * |x₂ - x₁| < δ * (|x₂ - x₁| + 1) := by gcongr; linarith
      _ = ε := div_mul_cancel₀ ε hden.ne'
  simpa [dist_eq_norm] using hbound.trans_lt hlt

/-- The roadmap target, with its full hypothesis list, follows. -/
example {f : ℂ → ℂ} {x₁ x₂ : ℝ}
    (_hint : ∀ m : ℝ, IntervalIntegrable (fun x : ℝ => f (x + m * Complex.I)) volume x₁ x₂)
    (hdecay : TendstoUniformlyOn (fun m : ℝ => fun x : ℝ => f (x + m * Complex.I)) 0 atTop
      (Set.uIcc x₁ x₂)) :
    Tendsto (fun m : ℝ => ∫ x in x₁..x₂, f (x + m * Complex.I)) atTop (𝓝 0) :=
  tendsto_top_edge_of_uniform_decay hdecay

end SphereCeti.Contour
