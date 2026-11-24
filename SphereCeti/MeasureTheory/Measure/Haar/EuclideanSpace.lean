/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Coordinate boxes in Euclidean space and their boundary layers

The centered coordinate box of radius `R` in `EuclideanSpace ℝ ι`, for a finite index type `ι` of
cardinality `n`, is the set of points all of whose coordinates have absolute value at most `R`;
for `R ≥ 0` its volume is `(2R)^n`.  For `R < 0` it is empty when `ι` is nonempty; when `ι` is
empty every box is the whole one-point space, of volume `1`.  The boundary layer of thickness `t`
is the box of radius `R + t` with the box of radius `R - t` removed; for `R ≥ t ≥ 0` its volume is
`(2(R + t))^n - (2(R - t))^n`.  For fixed `t ≥ 0`, the boundary layer is negligible compared with
the box as `R → ∞`: for `R > t` the ratio of volumes is `(1 + t / R)^n - (1 - t / R)^n`, which
tends to `0`.

Boxes are the patches from which a sphere packing is approximated by periodic packings: the
centers in a box are repeated periodically, and only the centers near the boundary of the box
are lost.

## Main definitions

* `EuclideanSpace.centeredBox ι R`: the centered coordinate box of radius `R`.
* `EuclideanSpace.boxBoundaryLayer ι R t`: its boundary layer of thickness `t`.

## Main statements

* `EuclideanSpace.mem_centeredBox`, `EuclideanSpace.mem_boxBoundaryLayer`: membership in a box and
  in its boundary layer.
* `EuclideanSpace.volume_centeredBox`: the box of radius `R` has volume `ENNReal.ofReal (2R) ^ n`,
  that is `(2R)^n` for `R ≥ 0`, and `0` for `R < 0` when `ι` is nonempty.
* `EuclideanSpace.boundaryLayer_volume_div_volume_tendsto_zero`: the volume of the boundary layer
  of fixed thickness is negligible compared with that of the box.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace EuclideanSpace

/-- The centered coordinate box of radius `R` in `EuclideanSpace ℝ ι`: the points whose
coordinates all have absolute value at most `R`. -/
def centeredBox (ι : Type*) (R : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, |x i| ≤ R}

/-- The boundary layer of thickness `t` of the centered coordinate box of radius `R`: the box of
radius `R + t` with the box of radius `R - t` removed. -/
def boxBoundaryLayer (ι : Type*) (R t : ℝ) : Set (EuclideanSpace ℝ ι) :=
  centeredBox ι (R + t) \ centeredBox ι (R - t)

variable {ι : Type*}

/-- The centered box is the set of points whose coordinates all have absolute value at most
`R`. -/
theorem centeredBox_def (R : ℝ) : centeredBox ι R = {x | ∀ i, |x i| ≤ R} :=
  (rfl)

/-- A point lies in the centered box of radius `R` when all of its coordinates have absolute value
at most `R`. -/
@[simp]
theorem mem_centeredBox {R : ℝ} {x : EuclideanSpace ℝ ι} :
    x ∈ centeredBox ι R ↔ ∀ i, |x i| ≤ R :=
  Iff.rfl

/-- The boundary layer is the box of radius `R + t` with the box of radius `R - t` removed. -/
theorem boxBoundaryLayer_def (R t : ℝ) :
    boxBoundaryLayer ι R t = centeredBox ι (R + t) \ centeredBox ι (R - t) :=
  (rfl)

/-- A point lies in the boundary layer when it lies in the box of radius `R + t` but not in the box
of radius `R - t`. -/
@[simp]
theorem mem_boxBoundaryLayer {R t : ℝ} {x : EuclideanSpace ℝ ι} :
    x ∈ boxBoundaryLayer ι R t ↔ x ∈ centeredBox ι (R + t) ∧ x ∉ centeredBox ι (R - t) :=
  Iff.rfl

/-- Check that `simp` reduces membership in a boundary layer to coordinate bounds. -/
example {R t : ℝ} {x : EuclideanSpace ℝ ι} :
    x ∈ boxBoundaryLayer ι R t ↔ (∀ i, |x i| ≤ R + t) ∧ ∃ i, R - t < |x i| := by
  simp

/-- The centered box is the preimage of a product of intervals under `WithLp.ofLp`. -/
theorem centeredBox_eq_preimage (R : ℝ) :
    centeredBox ι R = WithLp.ofLp ⁻¹' Set.pi univ fun _ ↦ Icc (-R) R := by
  ext x
  simp [abs_le, Pi.le_def, forall_and]

theorem centeredBox_mono {R R' : ℝ} (h : R ≤ R') : centeredBox ι R ⊆ centeredBox ι R' :=
  fun _ hx ↦ mem_centeredBox.mpr fun i ↦ (mem_centeredBox.mp hx i).trans h

variable [Fintype ι]

theorem measurableSet_centeredBox (R : ℝ) : MeasurableSet (centeredBox ι R) := by
  rw [centeredBox_eq_preimage]
  exact (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).preimage (by fun_prop)

/-- The centered box of radius `R` in `EuclideanSpace ℝ ι` has volume
`ENNReal.ofReal (2R) ^ Fintype.card ι`: this is `(2R)^n` for `R ≥ 0`, and `0` for `R < 0` when `ι`
is nonempty, when the box is empty.  When `ι` is empty the box is the whole one-point space, of
volume `1` for every `R`. -/
theorem volume_centeredBox (R : ℝ) :
    volume (centeredBox ι R) = ENNReal.ofReal (2 * R) ^ Fintype.card ι := by
  rw [centeredBox_eq_preimage, (PiLp.volume_preserving_ofLp ι).measure_preimage
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).nullMeasurableSet, volume_pi_pi]
  simp [Real.volume_Icc, two_mul]

/-- For `t ≥ 0`, the boundary layer of thickness `t` of the box of radius `R` has volume
`ENNReal.ofReal (2(R + t)) ^ n - ENNReal.ofReal (2(R - t)) ^ n`, where `n = Fintype.card ι`: this
is `(2(R + t))^n - (2(R - t))^n` for `R ≥ t`. -/
theorem volume_boxBoundaryLayer (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    volume (boxBoundaryLayer ι R t) =
      ENNReal.ofReal (2 * (R + t)) ^ Fintype.card ι -
        ENNReal.ofReal (2 * (R - t)) ^ Fintype.card ι := by
  have hfin : volume (centeredBox ι (R - t)) ≠ ∞ := by
    rw [volume_centeredBox]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [boxBoundaryLayer_def, measure_sdiff (centeredBox_mono (by linarith))
    (measurableSet_centeredBox _).nullMeasurableSet hfin, volume_centeredBox,
    volume_centeredBox]

/-- A boundary layer of fixed thickness is negligible compared with the box: the ratio of their
volumes tends to `0` as the radius tends to infinity. -/
theorem boundaryLayer_volume_div_volume_tendsto_zero (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ volume (boxBoundaryLayer ι R t) / volume (centeredBox ι R)) atTop
      (𝓝 0) := by
  -- The ratio is `(1 + t / R) ^ n - (1 - t / R) ^ n` once `R > t`, for `n = Fintype.card ι`.
  have hreal : Tendsto (fun R : ℝ ↦ (1 + t / R) ^ Fintype.card ι - (1 - t / R) ^ Fintype.card ι)
      atTop (𝓝 0) := by
    have h : Tendsto (fun R : ℝ ↦ t / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa using ((h.const_add 1).pow (Fintype.card ι)).sub ((h.const_sub 1).pow (Fintype.card ι))
  have heq : ∀ᶠ R in atTop,
      ENNReal.ofReal ((1 + t / R) ^ Fintype.card ι - (1 - t / R) ^ Fintype.card ι) =
        volume (boxBoundaryLayer ι R t) / volume (centeredBox ι R) := by
    filter_upwards [eventually_gt_atTop t] with R hR
    have hR : 0 < R := ht.trans_lt hR
    have hplus : 0 ≤ 2 * (R + t) := by linarith
    have hminus : 0 ≤ 2 * (R - t) := by linarith
    have hbox : 0 < 2 * R := by linarith
    simp only [volume_boxBoundaryLayer R ht, volume_centeredBox, ← ENNReal.ofReal_pow hplus,
      ← ENNReal.ofReal_pow hminus, ← ENNReal.ofReal_pow hbox.le,
      ← ENNReal.ofReal_sub _ (pow_nonneg hminus (Fintype.card ι)),
      ← ENNReal.ofReal_div_of_pos (pow_pos hbox (Fintype.card ι))]
    congr 1
    -- Both bases are quotients by the side length `2R` of the box.
    have hplus' : 1 + t / R = 2 * (R + t) / (2 * R) := by field_simp
    have hminus' : 1 - t / R = 2 * (R - t) / (2 * R) := by field_simp
    rw [hplus', hminus', div_pow, div_pow, sub_div]
  simpa using (ENNReal.tendsto_ofReal hreal).congr' heq

end EuclideanSpace
