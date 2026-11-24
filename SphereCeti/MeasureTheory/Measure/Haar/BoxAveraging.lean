/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.MeasureTheory.Group.LIntegral
public import SphereCeti.MeasureTheory.Measure.Haar.EuclideanSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Averaging over translates of a coordinate box

Let `S` be a finite set in the closed ball of radius `T > 0` about the origin of `ℝ^ι`, and let
`B` be the centered coordinate box of half-width `R ≥ 0`.  Every point of `B` has norm at most
`√(card ι) * R`, so every difference `s - q` with `s ∈ S` and `q ∈ B` lies in the closed ball of
radius `ρ = T + √(card ι) * R`.  By the first moment method for translates, some translate
`a + B` with `‖a‖ ≤ ρ` contains at least `#S * vol(B) / vol(B(ρ))` points of `S`.

In the periodic approximation of sphere packings, `S` is the set of centers of a packing in a
large ball, so some translate of a box carries at least the density of the packing in that ball,
up to the factor `vol(B(T)) / vol(B(ρ))`, which tends to one as `T → ∞` for fixed `R`.

## Main statements

* `EuclideanSpace.norm_le_of_mem_centeredBox`: points of the box of half-width `R` have norm at
  most `√(card ι) * R`.
* `EuclideanSpace.exists_encard_mul_volume_centeredBox_le`: some translate of the box contains at
  least `#S * vol(B) / vol(B(ρ))` points of `S`.
* `EuclideanSpace.tendsto_volume_closedBall_add_div_volume`: `vol B(T + c) / vol B(T) → 1` as
  `T → ∞`.
-/

public section

open Filter Metric MeasureTheory Topology
open scoped Pointwise ENNReal

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι]

/-- A point of the centered box of half-width `R ≥ 0` has norm at most `√(card ι) * R`. -/
theorem norm_le_of_mem_centeredBox {R : ℝ} (hR : 0 ≤ R) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ centeredBox ι R) : ‖x‖ ≤ √(Fintype.card ι) * R := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hR, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : ι, R ^ 2 := Finset.sum_le_sum fun i _ ↦ by
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (mem_centeredBox.mp hx i) 2
    _ = Fintype.card ι * R ^ 2 := by simp

/-- **Averaging over translates of a box.**  For a finite set `S` in the closed ball of radius
`T > 0` about the origin, some translate `a + B` of the centered box `B` of half-width `R ≥ 0`,
with `‖a‖ ≤ ρ = T + √(card ι) * R`, contains at least `#S * vol(B) / vol(B(ρ))` points of `S`. -/
theorem exists_encard_mul_volume_centeredBox_le {S : Set (EuclideanSpace ℝ ι)} (hS : S.Finite)
    {T R : ℝ} (hT : 0 < T) (hR : 0 ≤ R) (hST : S ⊆ closedBall 0 T) :
    ∃ a ∈ closedBall (0 : EuclideanSpace ℝ ι) (T + √(Fintype.card ι) * R),
      S.encard * volume (centeredBox ι R) ≤ (S ∩ (a +ᵥ centeredBox ι R)).encard *
        volume (closedBall (0 : EuclideanSpace ℝ ι) (T + √(Fintype.card ι) * R)) := by
  have hρ : 0 < T + √(Fintype.card ι) * R := by positivity
  refine exists_encard_mul_le_encard_inter_vadd_mul hS (measurableSet_centeredBox R)
    measurableSet_closedBall (measure_closedBall_pos volume 0 hρ).ne'
    measure_closedBall_lt_top.ne fun s hs q hq ↦ ?_
  rw [mem_closedBall_zero_iff]
  calc ‖s - q‖ ≤ ‖s‖ + ‖q‖ := norm_sub_le s q
    _ ≤ T + √(Fintype.card ι) * R :=
      add_le_add (mem_closedBall_zero_iff.mp (hST hs)) (norm_le_of_mem_centeredBox hR hq)

/-- The closed balls of radii `T + c` and `T` about the origin have volume ratio tending to one as
`T → ∞`. -/
theorem tendsto_volume_closedBall_add_div_volume (c : ℝ) :
    Tendsto (fun T : ℝ ↦ volume (closedBall (0 : EuclideanSpace ℝ ι) (T + c)) /
      volume (closedBall (0 : EuclideanSpace ℝ ι) T)) atTop (𝓝 1) := by
  set n := Module.finrank ℝ (EuclideanSpace ℝ ι)
  -- The ratio is `((T + c) / T) ^ n`, and `(T + c) / T = 1 + c / T → 1`.
  have hlim : Tendsto (fun T : ℝ ↦ ((T + c) / T) ^ n) atTop (𝓝 1) := by
    have h : Tendsto (fun T : ℝ ↦ 1 + c / T) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds (x := c)).div_atTop tendsto_id).const_add 1
    refine (by simpa using h.pow n : Tendsto (fun T : ℝ ↦ (1 + c / T) ^ n) atTop (𝓝 1)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [add_div, div_self hT.ne']
  have h1 : volume (closedBall (0 : EuclideanSpace ℝ ι) 1) ≠ 0 :=
    (measure_closedBall_pos volume 0 one_pos).ne'
  have h1' : volume (closedBall (0 : EuclideanSpace ℝ ι) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [← ENNReal.ofReal_one]
  refine (ENNReal.tendsto_ofReal hlim).congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 (-c))] with T hT
  have hT0 : 0 < T := lt_of_le_of_lt (le_max_left _ _) hT
  have hTc : 0 ≤ T + c := by linarith [le_max_right 0 (-c)]
  rw [Measure.addHaar_closedBall' volume 0 hTc, Measure.addHaar_closedBall' volume 0 hT0.le,
    ENNReal.mul_div_mul_right _ _ h1 h1', div_pow,
    ENNReal.ofReal_div_of_pos (pow_pos hT0 n)]

end EuclideanSpace
