/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Coordinate boxes and their boundary layers

The centered coordinate box of radius `R` in `ℝ^d` is the set of points all of whose coordinates
have absolute value at most `R`; its volume is `(2R)^d`.  The boundary layer of thickness `t` is the
box of radius `R + t` with the box of radius `R - t` removed, of volume
`(2(R + t))^d - (2(R - t))^d`.  For fixed `t`, the boundary layer is negligible compared with the
box as `R → ∞`: the ratio of volumes is `(1 + t / R)^d - (1 - t / R)^d`, which tends to `0`.

Boxes are the patches from which a sphere packing is approximated by periodic packings: the
centers in a box are repeated periodically, and only the centers near the boundary of the box
are lost.

## Main definitions

* `SphereCeti.PeriodicSpherePacking.centeredBox d R`: the centered coordinate box of radius `R`.
* `SphereCeti.PeriodicSpherePacking.boxBoundaryLayer d R t`: its boundary layer of thickness `t`.

## Main statements

* `SphereCeti.PeriodicSpherePacking.volume_centeredBox`: the box of radius `R` has volume
  `(2R)^d`.
* `SphereCeti.PeriodicSpherePacking.boundaryLayer_volume_div_volume_tendsto_zero`: the volume of
  the boundary layer of fixed thickness is negligible compared with that of the box.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace SphereCeti.PeriodicSpherePacking

/-- The centered coordinate box of radius `R` in `ℝ^d`: the points whose coordinates all have
absolute value at most `R`. -/
def centeredBox (d : ℕ) (R : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, |x i| ≤ R}

/-- The boundary layer of thickness `t` of the centered coordinate box of radius `R`: the box of
radius `R + t` with the box of radius `R - t` removed. -/
def boxBoundaryLayer (d : ℕ) (R t : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  centeredBox d (R + t) \ centeredBox d (R - t)

/-- The centered box is the preimage of a product of intervals under `WithLp.ofLp`. -/
theorem centeredBox_eq_preimage (d : ℕ) (R : ℝ) :
    centeredBox d R = WithLp.ofLp ⁻¹' Set.pi univ fun _ ↦ Icc (-R) R := by
  ext x
  simp [centeredBox, abs_le, Pi.le_def, forall_and]

theorem measurableSet_centeredBox (d : ℕ) (R : ℝ) : MeasurableSet (centeredBox d R) := by
  rw [centeredBox_eq_preimage]
  exact (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).preimage (by fun_prop)

theorem centeredBox_mono {d : ℕ} {R R' : ℝ} (h : R ≤ R') : centeredBox d R ⊆ centeredBox d R' :=
  fun _ hx i ↦ (hx i).trans h

/-- The centered box of radius `R` in `ℝ^d` has volume `(2R)^d`. -/
theorem volume_centeredBox (d : ℕ) (R : ℝ) :
    volume (centeredBox d R) = ENNReal.ofReal (2 * R) ^ d := by
  rw [centeredBox_eq_preimage, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).nullMeasurableSet, volume_pi_pi]
  simp [Real.volume_Icc, two_mul]

/-- For `t ≥ 0`, the boundary layer of thickness `t` of the box of radius `R` has volume
`(2(R + t))^d - (2(R - t))^d`. -/
theorem volume_boxBoundaryLayer {d : ℕ} (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    volume (boxBoundaryLayer d R t) =
      ENNReal.ofReal (2 * (R + t)) ^ d - ENNReal.ofReal (2 * (R - t)) ^ d := by
  have hfin : volume (centeredBox d (R - t)) ≠ ∞ := by
    rw [volume_centeredBox]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [boxBoundaryLayer, measure_sdiff (centeredBox_mono (by linarith))
    (measurableSet_centeredBox d _).nullMeasurableSet hfin, volume_centeredBox,
    volume_centeredBox]

/-- A boundary layer of fixed thickness is negligible compared with the box: the ratio of their
volumes tends to `0` as the radius tends to infinity. -/
theorem boundaryLayer_volume_div_volume_tendsto_zero {d : ℕ} (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ volume (boxBoundaryLayer d R t) / volume (centeredBox d R)) atTop
      (𝓝 0) := by
  -- The ratio is `(1 + t / R) ^ d - (1 - t / R) ^ d` once `R > t`.
  have hreal : Tendsto (fun R : ℝ ↦ (1 + t / R) ^ d - (1 - t / R) ^ d) atTop (𝓝 0) := by
    have h : Tendsto (fun R : ℝ ↦ t / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa using ((h.const_add 1).pow d).sub ((h.const_sub 1).pow d)
  have heq : ∀ᶠ R in atTop, ENNReal.ofReal ((1 + t / R) ^ d - (1 - t / R) ^ d) =
      volume (boxBoundaryLayer d R t) / volume (centeredBox d R) := by
    filter_upwards [eventually_gt_atTop t] with R hR
    have hR0 : 0 < R := ht.trans_lt hR
    rw [volume_boxBoundaryLayer R ht, volume_centeredBox,
      ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_pow (by linarith),
      ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_sub _ (by positivity),
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    have h₁ : (1 + t / R) * (2 * R) = 2 * (R + t) := by field_simp
    have h₂ : (1 - t / R) * (2 * R) = 2 * (R - t) := by field_simp
    rw [eq_div_iff (by positivity), sub_mul, ← mul_pow, ← mul_pow, h₁, h₂]
  simpa using (ENNReal.tendsto_ofReal hreal).congr' heq
