/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Upper asymptotic ball density under additive Haar measure

For a set `s` in a pseudometric measure space `(E, μ)` and a basepoint `a : E`, the upper
asymptotic ball density of `s` at `a` is
`limsup (fun R : ℝ ↦ μ (s ∩ ball a R) / μ (ball a R)) atTop`.

These lemmas provide the geometric measure theory behind asymptotic packing densities: they show
that upper density is independent of the choice of expanding-ball center, is invariant under
congruences (isometries and translations) and similarities (nonzero real scalings), and that
strictly positive upper density forces the underlying set to have positive measure and hence be
nonempty.

On any measurable space `(E, μ)`, positive upper density along any family of sets, denominator
family, and filter implies positive measure.

On a finite-dimensional real normed space equipped with an additive Haar measure `μ`:

* the ball volume ratio `μ (ball a (R + d)) / μ (ball b R)` tends to `1` as `R → ∞` for any
  centers `a, b` and fixed radius shift `d : ℝ` (including in dimension `0`), from which it
  follows that the upper asymptotic ball density of an arbitrary set `s` is independent of the
  basepoint;
* Mathlib's `Measure.addHaar_singleton_add_smul_div_singleton_add_smul` shows that nonzero real
  dilations `c • s` (`c ≠ 0`) preserve finite-radius density ratios, and combining this with
  basepoint independence yields scaling invariance of upper asymptotic ball density in every
  finite dimension (including dimension `0`);
* Haar uniqueness (`Measure.isAddLeftInvariant_eq_smul`) and `Isometry.hausdorffMeasure_image`
  show that every self-isometry `f : E → E` preserves `μ` without assuming surjectivity (the
  general additive-Haar analogue of `Isometry.euclideanHausdorffMeasure_image` in
  `Mathlib.Geometry.Euclidean.Volume.Measure`), yielding invariance of upper asymptotic ball
  density under all self-isometries and all isometric additive actions `v +ᵥ s` (in particular,
  translations).

## Main statements

* `MeasureTheory.Measure.measure_pos_of_limsup_measure_inter_div_pos`: positive upper density
  along any family of sets, denominator family, and filter forces positive measure.
* `MeasureTheory.Measure.tendsto_addHaar_ball_add_const_div_addHaar_ball`: the ratio of Haar
  measures `μ (ball a (R + d)) / μ (ball b R)` tends to `1` as `R → ∞`.
* `MeasureTheory.Measure.limsup_addHaar_inter_ball_div_eq`: basepoint independence of upper
  asymptotic ball density.
* `MeasureTheory.Measure.addHaar_smul_inter_ball_div`,
  `MeasureTheory.Measure.limsup_addHaar_smul_inter_ball_div`: finite-radius and asymptotic
  invariance under nonzero real scaling.
* `MeasureTheory.Measure.addHaar_image_of_isometry`,
  `MeasureTheory.Measure.limsup_addHaar_image_inter_ball_div_of_isometry`,
  `MeasureTheory.Measure.limsup_addHaar_vadd_inter_ball_div`: invariance under self-isometries
  and isometric additive actions.
-/

public section

open Filter Metric Module Set
open scoped ENNReal Pointwise Topology

namespace MeasureTheory

namespace Measure

private theorem limsup_comp_of_map_eq {α : Type*} {l : Filter α} {g : α → α}
    (hg : Filter.map g l = l) (u : α → ℝ≥0∞) :
    limsup (fun x ↦ u (g x)) l = limsup u l := by
  simpa only [hg, Function.comp_def] using Filter.limsup_comp u g l

section General

variable {E ι : Type*} [MeasurableSpace E] (μ : Measure E)

/-- Positive upper density along any family of sets, denominator family, and filter implies
positive measure. -/
theorem measure_pos_of_limsup_measure_inter_div_pos {s : Set E}
    {t : ι → Set E} {d : ι → ℝ≥0∞} {l : Filter ι}
    (h : 0 < limsup (fun i ↦ μ (s ∩ t i) / d i) l) :
    0 < μ s := by
  by_contra h0
  rw [not_lt, nonpos_iff_eq_zero] at h0
  -- `l` may be the trivial filter `⊥`, so `limsup_const` does not apply; use `limsup_const_bot`.
  have hzero : (fun i ↦ μ (s ∩ t i) / d i) = fun _ ↦ (⊥ : ℝ≥0∞) := by
    ext i
    rw [measure_inter_null_of_null_left (t i) h0, ENNReal.zero_div, ENNReal.bot_eq_zero]
  have hlim : limsup (fun i ↦ μ (s ∩ t i) / d i) l = 0 := by
    rw [hzero, limsup_const_bot, ENNReal.bot_eq_zero]
  exact h.ne' hlim

end General

section AddHaar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- For an additive Haar measure on a finite-dimensional real normed space, the volume ratio
`μ (ball a (R + d)) / μ (ball b R)` tends to `1` as `R → ∞`, for any centers `a, b` and fixed
radius shift `d`. -/
theorem tendsto_addHaar_ball_add_const_div_addHaar_ball (a b : E) (d : ℝ) :
    Tendsto (fun R : ℝ ↦ μ (ball a (R + d)) / μ (ball b R)) atTop (𝓝 1) := by
  have hreal : Tendsto (fun R : ℝ ↦ (1 + d / R) ^ finrank ℝ E) atTop (𝓝 1) := by
    have h : Tendsto (fun R : ℝ ↦ d / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa using ((h.const_add 1).pow (finrank ℝ E))
  have heq : ∀ᶠ R in atTop,
      ENNReal.ofReal ((1 + d / R) ^ finrank ℝ E) = μ (ball a (R + d)) / μ (ball b R) := by
    filter_upwards [eventually_gt_atTop (max 0 (-d))] with R hR
    have hR0 : 0 < R := (le_max_left 0 (-d)).trans_lt hR
    have hRd : 0 < R + d := by linarith [(le_max_right 0 (-d)).trans_lt hR]
    have hmul : (1 + d / R) * R = R + d := by field_simp
    have hpos : 0 < 1 + d / R := pos_of_mul_pos_left (by rwa [hmul]) hR0.le
    rw [← hmul, μ.addHaar_ball_mul_of_pos a hpos R, μ.addHaar_ball_center b R,
      ENNReal.mul_div_cancel_right (measure_ball_pos μ 0 hR0).ne' measure_ball_lt_top.ne]
  simpa using (ENNReal.tendsto_ofReal hreal).congr' heq

private theorem limsup_addHaar_inter_ball_div_le (s : Set E) (a b : E) :
    limsup (fun R : ℝ ↦ μ (s ∩ ball a R) / μ (ball a R)) atTop ≤
      limsup (fun R : ℝ ↦ μ (s ∩ ball b R) / μ (ball b R)) atTop := by
  have hle : ∀ᶠ R in atTop,
      μ (s ∩ ball a R) / μ (ball a R) ≤
        (μ (s ∩ ball b (R + dist a b)) / μ (ball b (R + dist a b))) *
          (μ (ball b (R + dist a b)) / μ (ball a R)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hRd : 0 < R + dist a b := add_pos_of_pos_of_nonneg hR dist_nonneg
    rw [← mul_div_assoc, ENNReal.div_mul_cancel (measure_ball_pos μ b hRd).ne'
      measure_ball_lt_top.ne]
    exact ENNReal.div_le_div_right
      (measure_mono <| inter_subset_inter_right s <| ball_subset_ball' le_rfl) _
  have h1 : limsup (fun R : ℝ ↦ μ (ball b (R + dist a b)) / μ (ball a R)) atTop = 1 :=
    (μ.tendsto_addHaar_ball_add_const_div_addHaar_ball b a (dist a b)).limsup_eq
  calc
    limsup (fun R : ℝ ↦ μ (s ∩ ball a R) / μ (ball a R)) atTop
      ≤ limsup (fun R : ℝ ↦ (μ (s ∩ ball b (R + dist a b)) / μ (ball b (R + dist a b))) *
          (μ (ball b (R + dist a b)) / μ (ball a R))) atTop := limsup_le_limsup hle
    _ ≤ limsup (fun R : ℝ ↦ μ (s ∩ ball b (R + dist a b)) / μ (ball b (R + dist a b))) atTop *
          limsup (fun R : ℝ ↦ μ (ball b (R + dist a b)) / μ (ball a R)) atTop :=
        ENNReal.limsup_mul_le'
          (Or.inr (by rw [h1]; exact ENNReal.one_ne_top))
          (Or.inr (by rw [h1]; exact one_ne_zero))
    _ = limsup (fun R : ℝ ↦ μ (s ∩ ball b R) / μ (ball b R)) atTop := by
        rw [h1, mul_one]
        exact limsup_comp_of_map_eq (Filter.map_add_atTop_eq (dist a b))
          (fun R : ℝ ↦ μ (s ∩ ball b R) / μ (ball b R))

/-- The upper asymptotic ball density of a set with respect to an additive Haar measure is
independent of the basepoint. -/
theorem limsup_addHaar_inter_ball_div_eq (s : Set E) (a b : E) :
    limsup (fun R : ℝ ↦ μ (s ∩ ball a R) / μ (ball a R)) atTop =
      limsup (fun R : ℝ ↦ μ (s ∩ ball b R) / μ (ball b R)) atTop :=
  le_antisymm (μ.limsup_addHaar_inter_ball_div_le s a b)
    (μ.limsup_addHaar_inter_ball_div_le s b a)

/-- Scaling both a set and a ball by a nonzero real scalar preserves the finite-radius Haar density
ratio. -/
theorem addHaar_smul_inter_ball_div {c : ℝ} (hc : c ≠ 0) (s : Set E) (a : E) (R : ℝ) :
    μ ((c • s) ∩ ball (c • a) (|c| * R)) / μ (ball (c • a) (|c| * R)) =
      μ (s ∩ ball a R) / μ (ball a R) := by
  have hball : c • ball a R = ball (c • a) (|c| * R) := by
    simpa [Real.norm_eq_abs] using _root_.smul_ball hc a R
  rw [← hball, ← smul_set_inter₀ hc]
  simpa only [Set.singleton_zero, zero_add] using
    μ.addHaar_singleton_add_smul_div_singleton_add_smul hc 0 0 (s ∩ ball a R) (ball a R)

/-- Nonzero real scaling preserves the upper asymptotic ball density of a set with respect to an
additive Haar measure, in every finite dimension (including dimension `0`). -/
theorem limsup_addHaar_smul_inter_ball_div {c : ℝ} (hc : c ≠ 0) (s : Set E) (a : E) :
    limsup (fun R : ℝ ↦ μ ((c • s) ∩ ball a R) / μ (ball a R)) atTop =
      limsup (fun R : ℝ ↦ μ (s ∩ ball a R) / μ (ball a R)) atTop := by
  have hmap : Filter.map (fun R : ℝ ↦ |c| * R) atTop = atTop :=
    (OrderIso.mulLeft₀ |c| (abs_pos.mpr hc)).map_atTop
  rw [μ.limsup_addHaar_inter_ball_div_eq (c • s) a (c • a),
    ← limsup_comp_of_map_eq hmap
      (fun R : ℝ ↦ μ ((c • s) ∩ ball (c • a) R) / μ (ball (c • a) R))]
  simp_rw [μ.addHaar_smul_inter_ball_div hc s a]

/-- Every self-isometry of a finite-dimensional real normed space preserves every additive Haar
measure. -/
theorem addHaar_image_of_isometry {f : E → E} (hf : Isometry f) (s : Set E) :
    μ (f '' s) = μ s := by
  rw [isAddLeftInvariant_eq_smul μ (hausdorffMeasure (finrank ℝ E)),
    coe_nnreal_smul_apply, coe_nnreal_smul_apply,
    hf.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg (finrank ℝ E)))]

/-- Self-isometries preserve the upper asymptotic ball density of a set with respect to an additive
Haar measure. -/
theorem limsup_addHaar_image_inter_ball_div_of_isometry
    {f : E → E} (hf : Isometry f) (s : Set E) (a : E) :
    limsup (fun R : ℝ ↦ μ (f '' s ∩ ball a R) / μ (ball a R)) atTop =
      limsup (fun R : ℝ ↦ μ (s ∩ ball a R) / μ (ball a R)) atTop := by
  rw [μ.limsup_addHaar_inter_ball_div_eq (f '' s) a (f a)]
  simp_rw [← Set.image_inter_preimage, hf.preimage_ball, μ.addHaar_image_of_isometry hf,
    μ.addHaar_ball_center (f a), μ.addHaar_ball_center a]

/-- Isometric additive actions (in particular, translations) preserve the upper asymptotic ball
density of a set with respect to an additive Haar measure. -/
theorem limsup_addHaar_vadd_inter_ball_div
    {G : Type*} [VAdd G E] [IsIsometricVAdd G E] (v : G) (s : Set E) (a : E) :
    limsup (fun R : ℝ ↦ μ ((v +ᵥ s) ∩ ball a R) / μ (ball a R)) atTop =
      limsup (fun R : ℝ ↦ μ (s ∩ ball a R) / μ (ball a R)) atTop := by
  simp_rw [← Set.image_vadd]
  exact μ.limsup_addHaar_image_inter_ball_div_of_isometry (isometry_vadd E v) s a

end AddHaar

end Measure

end MeasureTheory
