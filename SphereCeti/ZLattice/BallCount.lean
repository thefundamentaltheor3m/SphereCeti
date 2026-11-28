/-
Copyright (c) 2026 The Tau Ceti contributors, SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, SphereCeti contributors
-/

module

public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Topology.MetricSpace.DiscreteAddSubgroup

/-!
# Lattice points in balls

The number of points of a full lattice `L` in the closed ball of radius `R` about the origin of a
finite-dimensional real inner product space, divided by the volume of the ball, tends to
`1 / covol(L)` as `R → ∞`.  The same holds for a translate `p + L`, whose points in the ball of
radius `R` are squeezed between the lattice points in the balls of radii `R ∓ ‖p‖`.  Hence for
finitely many points `p q`, pairwise incongruent modulo `L`, the union of the cosets `p q + L` has
asymptotically `N / covol(L)` points per unit volume in large balls, where `N` is the number of
cosets.

In the theory of periodic sphere packings, the centers form finitely many cosets of the period
lattice, so this is the count behind the density formula: a periodic packing with `N` orbits,
period lattice `L` and balls of radius `ρ` has density `N / covol(L)` times the volume of a ball
of radius `ρ`.

## Main statements

* `ZLattice.tendsto_ncard_closedBall_inter_div_volume`: `#(B(R) ∩ L) / vol B(R) → 1 / covol(L)`.
* `ZLattice.tendsto_ncard_closedBall_inter_vadd_div_volume`: the same for a translate `p + L`.
* `ZLattice.tendsto_ncard_closedBall_inter_iUnion_vadd_div_volume`: for finitely many pairwise
  incongruent points `p q`, `#(B(R) ∩ ⋃ q, (p q + L)) / vol B(R) → N / covol(L)`.

## Provenance

The proof of `ZLattice.tendsto_ncard_closedBall_inter_div_volume` is adapted from the proof of
`ZLattice.ncard_closedBall_inter_isBigO` in TauCeti (`TauCetiProject/TauCeti`) at commit
`83769e442d55cda9d85b3927a93b286831c595ff`, file `TauCeti/Algebra/Module/ZLattice/Covolume.lean`.
-/
public section

open Filter Function Metric MeasureTheory Module Topology
open scoped Pointwise

namespace ZLattice

/-- A translate `p + L` of a discrete `ℤ`-submodule `L` of a proper normed additive group has
finitely many points in each closed ball. -/
theorem finite_closedBall_inter_vadd {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] (p : E) (R : ℝ) :
    (closedBall (0 : E) R ∩ (p +ᵥ (L : Set E))).Finite := by
  have h : closedBall (0 : E) R ∩ (p +ᵥ (L : Set E)) = p +ᵥ (closedBall (-p) R ∩ (L : Set E)) := by
    rw [Set.vadd_set_inter, Metric.vadd_closedBall, vadd_eq_add, add_neg_cancel]
  rw [h]
  exact (L.toAddSubgroup.finite_inter isBounded_closedBall).vadd_set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Lattice points in balls.** The number of points of a full lattice `L` in the closed ball of
radius `R` about the origin, divided by the volume of the ball, tends to `1 / covol(L)` as
`R → ∞`. -/
theorem tendsto_ncard_closedBall_inter_div_volume [Nontrivial E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    Tendsto (fun R : ℝ ↦
        ((closedBall (0 : E) R ∩ L).ncard : ℝ) / volume.real (closedBall (0 : E) R))
      atTop (𝓝 (ZLattice.covolume L)⁻¹) := by
  set n := finrank ℝ E
  have hn : n ≠ 0 := finrank_pos.ne'
  -- The sublevel sets of `x ↦ ‖x‖ ^ n` are the closed balls.
  have hball : ∀ R, 0 ≤ R → {x : E | x ∈ Set.univ ∧ ‖x‖ ^ n ≤ R ^ n} = closedBall 0 R := by
    intro R hR
    ext x
    simp [pow_le_pow_iff_left₀ (norm_nonneg x) hR hn]
  have h1 : {x : E | x ∈ Set.univ ∧ ‖x‖ ^ n ≤ 1} = closedBall 0 1 := by
    simpa using hball 1 zero_le_one
  -- Mathlib's asymptotic count of lattice points in the dilates of the unit ball.
  have key := ZLattice.covolume.tendsto_card_le_div' L (X := Set.univ) (F := fun x ↦ ‖x‖ ^ n)
    (fun _ _ _ _ ↦ Set.mem_univ _) (fun x r hr ↦ by rw [norm_smul, Real.norm_of_nonneg hr, mul_pow])
    (h1 ▸ isBounded_closedBall) (h1 ▸ measurableSet_closedBall)
    (h1 ▸ (convex_closedBall (0 : E) 1).addHaar_frontier volume)
  rw [h1] at key
  -- Along `c = R ^ n`, the count is that of the closed ball of radius `R`.
  have h2 : Tendsto (fun R : ℝ ↦ ((closedBall (0 : E) R ∩ L).ncard : ℝ) / R ^ n) atTop
      (𝓝 (volume.real (closedBall (0 : E) 1) / covolume L)) := by
    refine (key.comp (tendsto_pow_atTop hn)).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with R hR
    simp only [Function.comp_apply, Nat.card_coe_set_eq, hball R hR]
  -- The ball of radius `R` has volume `R ^ n * vol(B₁)`.
  have hB (R : ℝ) (hR : 0 ≤ R) :
      volume.real (closedBall (0 : E) R) = R ^ n * volume.real (closedBall (0 : E) 1) :=
    Measure.addHaar_real_closedBall' volume 0 hR
  have hB1 : 0 < volume.real (closedBall (0 : E) 1) :=
    ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne' measure_closedBall_lt_top.ne
  have h3 := h2.div_const (volume.real (closedBall (0 : E) 1))
  rw [div_div_cancel_left' hB1.ne'] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with R hR
  rw [hB R hR, div_div]

/-- Changing the radius by a constant does not change the asymptotic count. -/
private theorem tendsto_ncard_closedBall_add_inter_div_volume [Nontrivial E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (c : ℝ) :
    Tendsto (fun R : ℝ ↦
        ((closedBall (0 : E) (R + c) ∩ L).ncard : ℝ) / volume.real (closedBall (0 : E) R))
      atTop (𝓝 (ZLattice.covolume L)⁻¹) := by
  set n := finrank ℝ E
  have hcount := (tendsto_ncard_closedBall_inter_div_volume L).comp
    (tendsto_atTop_add_const_right atTop c tendsto_id)
  -- The volumes of the balls of radii `R + c` and `R` have ratio `(1 + c / R) ^ n`.
  have hratio : Tendsto (fun R : ℝ ↦
      volume.real (closedBall (0 : E) (R + c)) / volume.real (closedBall (0 : E) R))
      atTop (𝓝 1) := by
    have hlim : Tendsto (fun R : ℝ ↦ (1 + c / R) ^ n) atTop (𝓝 1) := by
      simpa using (((tendsto_const_nhds (x := c)).div_atTop tendsto_id).const_add 1).pow n
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (max 0 (-c))] with R hR
    have hR0 : 0 < R := lt_of_le_of_lt (le_max_left _ _) hR
    have hRc : 0 ≤ R + c := by linarith [le_max_right 0 (-c)]
    have hB1 : 0 < volume.real (closedBall (0 : E) 1) :=
      ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne' measure_closedBall_lt_top.ne
    rw [Measure.addHaar_real_closedBall' volume 0 hRc,
      Measure.addHaar_real_closedBall' volume 0 hR0.le, mul_div_mul_right _ _ hB1.ne', ← div_pow,
      add_div, div_self hR0.ne']
  have hprod := hcount.mul hratio
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 (-c))] with R hR
  have hRc : 0 < R + c := by linarith [le_max_right 0 (-c)]
  have hpos : volume.real (closedBall (0 : E) (R + c)) ≠ 0 :=
    (ENNReal.toReal_pos (measure_closedBall_pos volume 0 hRc).ne' measure_closedBall_lt_top.ne).ne'
  simp only [Function.comp_apply, id]
  rw [div_mul_div_cancel₀ hpos]

/-- **Translated lattice points in balls.** For a full lattice `L` and any `p`, the number of points
of `p + L` in the closed ball of radius `R` about the origin, divided by the volume of the ball,
tends to `1 / covol(L)` as `R → ∞`. -/
theorem tendsto_ncard_closedBall_inter_vadd_div_volume [Nontrivial E] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (p : E) :
    Tendsto (fun R : ℝ ↦ ((closedBall (0 : E) R ∩ (p +ᵥ (L : Set E))).ncard : ℝ) /
        volume.real (closedBall (0 : E) R))
      atTop (𝓝 (ZLattice.covolume L)⁻¹) := by
  -- Translation by `-p` carries `B(R) ∩ (p + L)` onto the lattice points of the ball of radius `R`
  -- about `-p`, which lies between the balls of radii `R ∓ ‖p‖` about the origin.
  have hcard (R : ℝ) : (closedBall (0 : E) R ∩ (p +ᵥ (L : Set E))).ncard =
      (closedBall (-p) R ∩ (L : Set E)).ncard := by
    rw [← Set.ncard_vadd_set (-p), Set.vadd_set_inter, Metric.vadd_closedBall, vadd_vadd,
      neg_add_cancel, zero_vadd, vadd_eq_add, add_zero]
  have hlow (R : ℝ) : (closedBall (0 : E) (R + -‖p‖) ∩ L).ncard ≤
      (closedBall (0 : E) R ∩ (p +ᵥ (L : Set E))).ncard :=
    hcard R ▸ Set.ncard_le_ncard (Set.inter_subset_inter_left _
      (closedBall_subset_closedBall' (by simp))) (L.toAddSubgroup.finite_inter isBounded_closedBall)
  have hupp (R : ℝ) : (closedBall (0 : E) R ∩ (p +ᵥ (L : Set E))).ncard ≤
      (closedBall (0 : E) (R + ‖p‖) ∩ L).ncard :=
    hcard R ▸ Set.ncard_le_ncard (Set.inter_subset_inter_left _
      (closedBall_subset_closedBall' (by simp))) (L.toAddSubgroup.finite_inter isBounded_closedBall)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_ncard_closedBall_add_inter_div_volume L (-‖p‖))
    (tendsto_ncard_closedBall_add_inter_div_volume L ‖p‖) (Eventually.of_forall fun R ↦ ?_)
    (Eventually.of_forall fun R ↦ ?_)
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hlow R)) measureReal_nonneg
  · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hupp R)) measureReal_nonneg

/-- **Points of finitely many lattice cosets in balls.**  Let `p : ι → E` be finitely many points,
pairwise incongruent modulo a full lattice `L`.  The number of points of `⋃ q, (p q + L)` in the
closed ball of radius `R` about the origin, divided by the volume of the ball, tends to
`card ι / covol(L)` as `R → ∞`. -/
theorem tendsto_ncard_closedBall_inter_iUnion_vadd_div_volume [Nontrivial E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
    (p : ι → E) (hp : ∀ q q', p q - p q' ∈ L → q = q') :
    Tendsto (fun R : ℝ ↦ ((closedBall (0 : E) R ∩ ⋃ q, (p q +ᵥ (L : Set E))).ncard : ℝ) /
        volume.real (closedBall (0 : E) R))
      atTop (𝓝 (Fintype.card ι / ZLattice.covolume L)) := by
  -- The cosets are pairwise disjoint, so the count is the sum of the counts of the cosets.
  have hcount (R : ℝ) : ((closedBall (0 : E) R ∩ ⋃ q, (p q +ᵥ (L : Set E))).ncard : ℝ) =
      ∑ q, ((closedBall (0 : E) R ∩ (p q +ᵥ (L : Set E))).ncard : ℝ) := by
    have hdisj : Pairwise (Disjoint on fun q ↦ closedBall (0 : E) R ∩ (p q +ᵥ (L : Set E))) := by
      intro q q' hqq'
      refine Set.disjoint_left.mpr fun y hy hy' ↦ hqq' (hp q q' ?_)
      obtain ⟨x, hx, rfl⟩ := hy.2
      obtain ⟨x', hx', hxx'⟩ := hy'.2
      simp only [vadd_eq_add] at hxx'
      have : p q - p q' = x' - x := by
        rw [sub_eq_sub_iff_add_eq_add, ← hxx', add_comm]
      rw [this]
      exact L.sub_mem hx' hx
    rw [Set.inter_iUnion,
      Set.ncard_iUnion_of_finite (fun q ↦ finite_closedBall_inter_vadd L (p q) R) hdisj,
      finsum_eq_sum_of_fintype, Nat.cast_sum]
  simp_rw [hcount, Finset.sum_div]
  have hsum := tendsto_finsetSum Finset.univ fun q _ ↦
    tendsto_ncard_closedBall_inter_vadd_div_volume L (p q)
  simpa [Finset.sum_const, Finset.card_univ, div_eq_mul_inv] using hsum

end ZLattice
