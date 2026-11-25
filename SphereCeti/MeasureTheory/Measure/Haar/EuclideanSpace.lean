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
are lost.  The periodic repetition of a set `S` along the lattice `c ℤ^ι` is the set of points
`s + c z` with `s ∈ S` and `z : ι → ℤ`; it contains `S` and is invariant under translation by
`c ℤ^ι`.  The repetition of a `ρ`-separated subset of a translated box of radius `R` with period
`2(R + ρ)` is again `ρ`-separated, for all real `R` and `ρ`.  For `R ≥ 0` and `ρ ≥ 0`, this period
leaves a guard band of width `2ρ` between neighboring copies of the box; for `ρ < 0`, every set
is `ρ`-separated, since distances are nonnegative.

## Main definitions

* `EuclideanSpace.centeredBox ι R`: the centered coordinate box of radius `R`.
* `EuclideanSpace.boxBoundaryLayer ι R t`: its boundary layer of thickness `t`.
* `EuclideanSpace.periodicRepetition S c`: the periodic repetition of `S` along `c ℤ^ι`.

## Main statements

* `EuclideanSpace.mem_centeredBox`, `EuclideanSpace.mem_boxBoundaryLayer`: membership in a box and
  in its boundary layer.
* `EuclideanSpace.volume_centeredBox`: the box of radius `R` has volume `ENNReal.ofReal (2R) ^ n`,
  that is `(2R)^n` for `R ≥ 0`, and `0` for `R < 0` when `ι` is nonempty.
* `EuclideanSpace.boundaryLayer_volume_div_volume_tendsto_zero`: the volume of the boundary layer
  of fixed thickness is negligible compared with that of the box.
* `EuclideanSpace.subset_periodicRepetition`: the periodic repetition of `S` contains `S`.
* `EuclideanSpace.toLp_add_mem_periodicRepetition_iff`: the periodic repetition along `c ℤ^ι` is
  invariant under translation by `c ℤ^ι`.
* `EuclideanSpace.abs_sub_two_mul_le_dist`: points of a translated box of radius `R` shifted by
  distinct vectors of `c ℤ^ι` are at distance at least `|c| - 2R`.
* `EuclideanSpace.pairwise_le_dist_periodicRepetition`: the repetition of a `ρ`-separated subset
  of a translated box of radius `R` along `2(R + ρ) ℤ^ι` is `ρ`-separated.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Pointwise Topology

namespace EuclideanSpace

/-- The centered coordinate box of radius `R` in `EuclideanSpace ℝ ι`: the points whose
coordinates all have absolute value at most `R`. -/
def centeredBox (ι : Type*) (R : ℝ) : Set (EuclideanSpace ℝ ι) :=
  {x | ∀ i, |x i| ≤ R}

/-- The boundary layer of thickness `t` of the centered coordinate box of radius `R`: the box of
radius `R + t` with the box of radius `R - t` removed. -/
def boxBoundaryLayer (ι : Type*) (R t : ℝ) : Set (EuclideanSpace ℝ ι) :=
  centeredBox ι (R + t) \ centeredBox ι (R - t)

/-- The periodic repetition of a set `S` along the lattice `c ℤ^ι`: the points `s + c z` with
`s ∈ S` and `z : ι → ℤ`. -/
def periodicRepetition {ι : Type*} (S : Set (EuclideanSpace ℝ ι)) (c : ℝ) :
    Set (EuclideanSpace ℝ ι) :=
  {x | ∃ z : ι → ℤ, ∃ s ∈ S, x.ofLp = s.ofLp + fun i ↦ c * z i}

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

/-- The periodic repetition of `S` along `c ℤ^ι` is the set of points `s + c z` with `s ∈ S` and
`z : ι → ℤ`. -/
theorem periodicRepetition_def (S : Set (EuclideanSpace ℝ ι)) (c : ℝ) :
    periodicRepetition S c = {x | ∃ z : ι → ℤ, ∃ s ∈ S, x.ofLp = s.ofLp + fun i ↦ c * z i} :=
  (rfl)

/-- A point lies in the periodic repetition of `S` along `c ℤ^ι` when it is `s + c z` for some
`s ∈ S` and `z : ι → ℤ`. -/
@[simp]
theorem mem_periodicRepetition {S : Set (EuclideanSpace ℝ ι)} {c : ℝ} {x : EuclideanSpace ℝ ι} :
    x ∈ periodicRepetition S c ↔ ∃ z : ι → ℤ, ∃ s ∈ S, x.ofLp = s.ofLp + fun i ↦ c * z i :=
  Iff.rfl

/-- Check that `simp` reduces membership in a periodic repetition to its defining formula. -/
example {S : Set (EuclideanSpace ℝ ι)} {c : ℝ} {x : EuclideanSpace ℝ ι} :
    x ∈ periodicRepetition S c ↔ ∃ z : ι → ℤ, ∃ s ∈ S, x.ofLp = s.ofLp + fun i ↦ c * z i := by
  simp

/-- A set is contained in its periodic repetition. -/
theorem subset_periodicRepetition (S : Set (EuclideanSpace ℝ ι)) (c : ℝ) :
    S ⊆ periodicRepetition S c :=
  fun s hs ↦ ⟨0, s, hs, by ext i; simp⟩

-- A pre-lemma (`↓`): otherwise `mem_periodicRepetition` unfolds the membership first.
/-- The periodic repetition of `S` along `c ℤ^ι` is invariant under translation by the vector
`c z` of `c ℤ^ι`, for every `z : ι → ℤ`. -/
@[simp ↓]
theorem toLp_add_mem_periodicRepetition_iff {S : Set (EuclideanSpace ℝ ι)} {c : ℝ} {z : ι → ℤ}
    {x : EuclideanSpace ℝ ι} :
    WithLp.toLp 2 (fun i ↦ c * z i) + x ∈ periodicRepetition S c ↔
      x ∈ periodicRepetition S c := by
  constructor
  · rintro ⟨w, s, hs, h⟩
    refine ⟨w - z, s, hs, funext fun i ↦ ?_⟩
    have hi := congrFun h i
    simp only [WithLp.ofLp_add, Pi.add_apply] at hi
    simp only [Pi.add_apply, Pi.sub_apply, Int.cast_sub]
    linarith
  · rintro ⟨w, s, hs, h⟩
    refine ⟨z + w, s, hs, funext fun i ↦ ?_⟩
    simp only [WithLp.ofLp_add, h, Pi.add_apply, Int.cast_add]
    ring

/-- Check that `simp` removes a translation by a vector of `c ℤ^ι` from a membership. -/
example {S : Set (EuclideanSpace ℝ ι)} {c : ℝ} {z : ι → ℤ} {x : EuclideanSpace ℝ ι}
    (hx : x ∈ periodicRepetition S c) :
    WithLp.toLp 2 (fun i ↦ c * z i) + x ∈ periodicRepetition S c := by
  simpa using hx

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

/-- Points of a translated box of radius `R`, shifted by the vectors `c z` and `c z'` of the
lattice `c ℤ^ι` with `z ≠ z'`, are at distance at least `|c| - 2R`. -/
theorem abs_sub_two_mul_le_dist {a s s' x x' : EuclideanSpace ℝ ι} {R c : ℝ}
    (hs : s ∈ a +ᵥ centeredBox ι R) (hs' : s' ∈ a +ᵥ centeredBox ι R) {z z' : ι → ℤ}
    (hz : z ≠ z') (hx : x.ofLp = s.ofLp + fun i ↦ c * z i)
    (hx' : x'.ofLp = s'.ofLp + fun i ↦ c * z' i) :
    |c| - 2 * R ≤ dist x x' := by
  -- At a coordinate `i` where `z` and `z'` differ, the shifts differ by at least `|c|`, and the
  -- points of the box by at most `2R`.
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, mem_centeredBox] at hs hs'
  have hsi := hs i
  have hs'i := hs' i
  simp only [PiLp.add_apply, PiLp.neg_apply] at hsi hs'i
  have hzi : (1 : ℝ) ≤ |(z i : ℝ) - z' i| := by
    rw [← Int.cast_sub, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hi)
  have hxi : x i - x' i = s i - s' i + c * ((z i : ℝ) - z' i) := by
    have h := congrFun hx i
    have h' := congrFun hx' i
    simp only [Pi.add_apply] at h h'
    rw [h, h']
    ring
  have hss : |s i - s' i| ≤ 2 * R := by
    calc |s i - s' i| = |(-a i + s i) - (-a i + s' i)| := by ring_nf
      _ ≤ |-a i + s i| + |-a i + s' i| := abs_sub _ _
      _ ≤ 2 * R := by linarith
  have hsum : |c * ((z i : ℝ) - z' i)| ≤ |x i - x' i| + |s i - s' i| := by
    calc |c * ((z i : ℝ) - z' i)| = |(x i - x' i) - (s i - s' i)| := by rw [hxi]; ring_nf
      _ ≤ |x i - x' i| + |s i - s' i| := abs_sub _ _
  have hc : |c| ≤ |c * ((z i : ℝ) - z' i)| := by
    rw [abs_mul]
    exact le_mul_of_one_le_right (abs_nonneg c) hzi
  calc |c| - 2 * R ≤ |x i - x' i| := by linarith
    _ = dist (x i) (x' i) := (Real.dist_eq _ _).symm
    _ ≤ dist x x' := PiLp.dist_apply_le x x' i

/-- Repeating a `ρ`-separated subset of a translated box of radius `R` along the lattice
`2 (R + ρ) ℤ^ι` gives a `ρ`-separated set, for all real `R` and `ρ`.  For `R ≥ 0` and `ρ ≥ 0`, this
lattice leaves a guard band of width `2ρ` between neighboring copies of the box; for `ρ < 0`,
every set is `ρ`-separated, since distances are nonnegative. -/
theorem pairwise_le_dist_periodicRepetition {S : Set (EuclideanSpace ℝ ι)}
    {a : EuclideanSpace ℝ ι} {R ρ : ℝ} (hS : S ⊆ a +ᵥ centeredBox ι R)
    (hsep : Pairwise (ρ ≤ dist · · : S → S → Prop)) :
    Pairwise (ρ ≤ dist · · :
      periodicRepetition S (2 * (R + ρ)) → periodicRepetition S (2 * (R + ρ)) → Prop) := by
  rintro ⟨x, z, s, hsS, hx⟩ ⟨x', z', s', hs'S, hx'⟩ hne
  simp only [Subtype.dist_eq]
  rcases lt_or_ge ρ 0 with hρ | hρ
  · exact hρ.le.trans dist_nonneg
  by_cases hz : z = z'
  · -- The same lattice shift: `x - x' = s - s'`, and `s ≠ s'` since `x ≠ x'`.
    subst hz
    have hss : (⟨s, hsS⟩ : S) ≠ ⟨s', hs'S⟩ := by
      rintro ⟨⟩
      exact hne (Subtype.ext (WithLp.ofLp_injective 2 (hx.trans hx'.symm)))
    have hsub : x - x' = s - s' := by
      apply WithLp.ofLp_injective 2
      rw [WithLp.ofLp_sub, WithLp.ofLp_sub, hx, hx', add_sub_add_right_eq_sub]
    have hdist : dist x x' = dist s s' := by rw [dist_eq_norm, dist_eq_norm, hsub]
    have h := hsep hss
    simp only [Subtype.dist_eq] at h
    rwa [hdist]
  · -- Distinct lattice shifts: the guard band separates the copies by `2ρ ≥ ρ`.
    have h := abs_sub_two_mul_le_dist (hS hsS) (hS hs'S) hz hx hx'
    have hc := le_abs_self (2 * (R + ρ))
    linarith

end EuclideanSpace
