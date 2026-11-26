/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measures of large balls for an additive Haar measure

Let `μ` be an additive Haar measure on a finite-dimensional real normed space `E` of dimension
`n`.  For fixed `c : ℝ`, the closed balls of radii `T + c` and `T` about a point have measure
ratio `((T + c) / T)ⁿ` when `T > 0` and `T + c ≥ 0`, and this ratio tends to `1` as `T → ∞`:
enlarging a large ball by a fixed amount changes its measure by a factor close to one.

## Main statements

* `MeasureTheory.Measure.tendsto_addHaar_closedBall_add_div`: the ratio
  `μ (closedBall x (T + c)) / μ (closedBall x T)` tends to `1` as `T → ∞`.
-/

public section

open Filter Metric Module Topology
open scoped ENNReal

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- For an additive Haar measure `μ` on a finite-dimensional real normed space, the closed balls
of radii `T + c` and `T` about a point have measure ratio tending to one as `T → ∞`. -/
theorem tendsto_addHaar_closedBall_add_div (x : E) (c : ℝ) :
    Tendsto (fun T : ℝ ↦ μ (closedBall x (T + c)) / μ (closedBall x T)) atTop (𝓝 1) := by
  -- The ratio is `((T + c) / T) ^ n` for `n = finrank ℝ E`, and `(T + c) / T = 1 + c / T → 1`.
  have hlim : Tendsto (fun T : ℝ ↦ ((T + c) / T) ^ finrank ℝ E) atTop (𝓝 1) := by
    have h : Tendsto (fun T : ℝ ↦ 1 + c / T) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := c)).div_atTop tendsto_id).const_add 1
    refine (by simpa using h.pow (finrank ℝ E) :
      Tendsto (fun T : ℝ ↦ (1 + c / T) ^ finrank ℝ E) atTop (𝓝 1)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [add_div, div_self hT.ne']
  have h1 : μ (closedBall (0 : E) 1) ≠ 0 := (measure_closedBall_pos μ 0 one_pos).ne'
  have h1' : μ (closedBall (0 : E) 1) ≠ ∞ := measure_closedBall_lt_top.ne
  rw [← ENNReal.ofReal_one]
  refine (ENNReal.tendsto_ofReal hlim).congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 (-c))] with T hT
  have hT0 : 0 < T := (le_max_left _ _).trans_lt hT
  have hTc : 0 ≤ T + c := by linarith [le_max_right 0 (-c)]
  rw [addHaar_closedBall' μ x hTc, addHaar_closedBall' μ x hT0.le,
    ENNReal.mul_div_mul_right _ _ h1 h1', div_pow, ENNReal.ofReal_div_of_pos (pow_pos hT0 _)]

end MeasureTheory.Measure
