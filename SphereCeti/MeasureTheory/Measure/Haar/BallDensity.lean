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
congruences (isometries and translations) and similarities (nonzero scalings), and that strictly
positive upper density forces the underlying set to have positive measure and hence be nonempty.

On any measurable space `(E, μ)`, null sets have zero upper density along any family of test sets,
denominator family, and filter, so positive upper density implies positive measure.

On a finite-dimensional real normed space equipped with an additive Haar measure `μ`:

* the ball volume ratio `μ (ball a (R + d)) / μ (ball b R)` tends to `1` as `R → ∞` for any
  centers `a, b` and fixed shift `d : ℝ` (including in dimension `0`), from which it follows that
  the upper asymptotic ball density of an arbitrary set `s` is independent of the basepoint;
* Haar uniqueness and Hausdorff-measure scaling show that nonzero scalar dilations `c • s` over
  any normed division ring `𝕜` acting isometrically by norm on `E` multiply `μ` by
  `‖c‖₊ ^ finrank ℝ E` and preserve finite-radius density ratios; combining this with basepoint
  independence yields scaling invariance of upper asymptotic ball density in every finite dimension
  (including dimension `0`);
* Haar uniqueness and Hausdorff-measure isometry invariance show that every surjective isometry
  `f : E → F` into an extended metric additive topological group `F` with isometric left
  translation preserves ratios of additive Haar measures, and when `F` is a metric space carries
  upper asymptotic ball density between arbitrary additive Haar measures and arbitrary basepoints;
  on `E` itself, every isometry `f : E → E` preserves `μ` directly without assuming surjectivity,
  yielding invariance of upper asymptotic ball density under all self-isometries and all isometric
  additive actions `v +ᵥ s` (in particular, translations).

## Main statements

* `MeasureTheory.Measure.limsup_measure_inter_div_eq_zero_of_null`,
  `MeasureTheory.Measure.measure_pos_of_limsup_measure_inter_div_pos`: null sets have zero upper
  density along any family of sets and filter, so positive upper density forces positive measure.
* `MeasureTheory.Measure.tendsto_addHaar_ball_add_div_addHaar_ball`: the ratio of Haar measures
  `μ (ball a (R + d)) / μ (ball b R)` tends to `1` as `R → ∞`.
* `MeasureTheory.Measure.limsup_addHaar_inter_ball_div_eq`: basepoint independence of upper
  asymptotic ball density.
* `MeasureTheory.Measure.addHaar_smul₀`,
  `MeasureTheory.Measure.limsup_addHaar_smul_inter_ball_div`: Haar scaling and invariance of upper
  asymptotic ball density under nonzero scaling over any normed division ring.
* `MeasureTheory.Measure.addHaar_image_div_of_isometry`,
  `MeasureTheory.Measure.limsup_addHaar_image_inter_ball_div_eq_of_isometry`: invariance of
  additive Haar measure ratios (into an extended metric group) and upper asymptotic ball density
  (into a metric group) under surjective isometries.
* `MeasureTheory.Measure.addHaar_image_of_isometry`,
  `MeasureTheory.Measure.limsup_addHaar_image_inter_ball_div_of_isometry`,
  `MeasureTheory.Measure.limsup_addHaar_vadd_inter_ball_div`: invariance on a single space under
  arbitrary self-isometries and isometric additive actions.
-/

public section

open Filter Metric Module Set
open scoped ENNReal NNReal Pointwise Topology

namespace MeasureTheory

namespace Measure

section General

variable {E ι : Type*} [MeasurableSpace E] (μ : Measure E)

/-- A null set has zero upper density along any family of sets, denominator family, and filter. -/
theorem limsup_measure_inter_div_eq_zero_of_null {s : Set E} (hs : μ s = 0)
    (t : ι → Set E) (d : ι → ℝ≥0∞) (l : Filter ι) :
    limsup (fun i ↦ μ (s ∩ t i) / d i) l = 0 := by
  have hzero : (fun i ↦ μ (s ∩ t i) / d i) = fun _ ↦ (⊥ : ℝ≥0∞) := by
    ext i
    rw [measure_inter_null_of_null_left (t i) hs, ENNReal.zero_div, ENNReal.bot_eq_zero]
  rw [hzero, limsup_const_bot, ENNReal.bot_eq_zero]

/-- Positive upper density along any family of sets, denominator family, and filter implies
positive measure. -/
theorem measure_pos_of_limsup_measure_inter_div_pos {s : Set E}
    {t : ι → Set E} {d : ι → ℝ≥0∞} {l : Filter ι}
    (h : 0 < limsup (fun i ↦ μ (s ∩ t i) / d i) l) :
    0 < μ s := by
  by_contra h0
  rw [not_lt, nonpos_iff_eq_zero] at h0
  exact h.ne' (μ.limsup_measure_inter_div_eq_zero_of_null h0 t d l)

end General

section AddHaar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- For an additive Haar measure on a finite-dimensional real normed space, the volume ratio
`μ (ball a (R + d)) / μ (ball b R)` tends to `1` as `R → ∞`, for any centers `a, b` and fixed
radius shift `d`. -/
theorem tendsto_addHaar_ball_add_div_addHaar_ball (a b : E) (d : ℝ) :
    Tendsto (fun R : ℝ ↦ μ (ball a (R + d)) / μ (ball b R)) atTop (𝓝 1) := by
  have hreal : Tendsto (fun R : ℝ ↦ (1 + d / R) ^ finrank ℝ E) atTop (𝓝 1) := by
    have h : Tendsto (fun R : ℝ ↦ d / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    simpa using ((h.const_add 1).pow (finrank ℝ E))
  have heq : ∀ᶠ R in atTop,
      ENNReal.ofReal ((1 + d / R) ^ finrank ℝ E) = μ (ball a (R + d)) / μ (ball b R) := by
    filter_upwards [eventually_gt_atTop (max 0 (-d))] with R hR
    have hR0 : 0 < R := (le_max_left 0 (-d)).trans_lt hR
    have hRd : 0 < R + d := by linarith [(le_max_right 0 (-d)).trans_lt hR]
    rw [μ.addHaar_ball_of_pos a hRd, μ.addHaar_ball_of_pos b hR0,
      ENNReal.mul_div_mul_right _ _ (measure_ball_pos μ 0 zero_lt_one).ne' measure_ball_lt_top.ne,
      ← ENNReal.ofReal_div_of_pos (pow_pos hR0 (finrank ℝ E)), ← div_pow]
    congr 2
    field_simp
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
    (μ.tendsto_addHaar_ball_add_div_addHaar_ball b a (dist a b)).limsup_eq
  calc
    limsup (fun R : ℝ ↦ μ (s ∩ ball a R) / μ (ball a R)) atTop
      ≤ limsup (fun R : ℝ ↦ (μ (s ∩ ball b (R + dist a b)) / μ (ball b (R + dist a b))) *
          (μ (ball b (R + dist a b)) / μ (ball a R))) atTop := limsup_le_limsup hle
    _ ≤ limsup (fun R : ℝ ↦ μ (s ∩ ball b (R + dist a b)) / μ (ball b (R + dist a b))) atTop *
          limsup (fun R : ℝ ↦ μ (ball b (R + dist a b)) / μ (ball a R)) atTop :=
        ENNReal.limsup_mul_le' (Or.inr (h1 ▸ ENNReal.one_ne_top)) (Or.inr (h1 ▸ one_ne_zero))
    _ = limsup (fun R : ℝ ↦ μ (s ∩ ball b R) / μ (ball b R)) atTop := by
        rw [h1, mul_one]
        exact (Filter.limsup_comp (fun R : ℝ ↦ μ (s ∩ ball b R) / μ (ball b R))
          (· + dist a b) atTop).trans (by rw [Filter.map_add_atTop_eq])

/-- The upper asymptotic ball density of a set with respect to an additive Haar measure is
independent of the basepoint. -/
theorem limsup_addHaar_inter_ball_div_eq (s : Set E) (a b : E) :
    limsup (fun R : ℝ ↦ μ (s ∩ ball a R) / μ (ball a R)) atTop =
      limsup (fun R : ℝ ↦ μ (s ∩ ball b R) / μ (ball b R)) atTop :=
  le_antisymm (μ.limsup_addHaar_inter_ball_div_le s a b)
    (μ.limsup_addHaar_inter_ball_div_le s b a)

/-- Scaling a set by a nonzero scalar over a normed division ring multiplies any additive Haar
measure by `‖c‖₊ ^ finrank ℝ E`. -/
theorem addHaar_smul₀ {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    {c : 𝕜} (hc : c ≠ 0) (s : Set E) :
    μ (c • s) = ‖c‖₊ ^ finrank ℝ E • μ s := by
  rw [isAddLeftInvariant_eq_smul μ (hausdorffMeasure (finrank ℝ E)),
    coe_nnreal_smul_apply, coe_nnreal_smul_apply,
    hausdorffMeasure_smul₀ (Nat.cast_nonneg (finrank ℝ E)) hc, NNReal.rpow_natCast,
    ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- Scaling both a set and a ball by a nonzero scalar over a normed division ring preserves the
finite-radius Haar density ratio. -/
theorem addHaar_smul_inter_ball_div {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E]
    [NormSMulClass 𝕜 E] {c : 𝕜} (hc : c ≠ 0) (s : Set E) (a : E) (R : ℝ) :
    μ ((c • s) ∩ ball (c • a) (‖c‖ * R)) / μ (ball (c • a) (‖c‖ * R)) =
      μ (s ∩ ball a R) / μ (ball a R) := by
  have hball : c • ball a R = ball (c • a) (‖c‖ * R) := by
    rw [← Set.image_smul, Metric.smul_image_ball hc a R]
  have hcr : ((‖c‖₊ ^ finrank ℝ E : ℝ≥0) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (nnnorm_pos.mpr hc).ne')
  rw [← hball, ← smul_set_inter₀ hc, μ.addHaar_smul₀ hc, μ.addHaar_smul₀ hc,
    ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
    ENNReal.mul_div_mul_left _ _ hcr ENNReal.coe_ne_top]

/-- Nonzero scaling over any normed division ring preserves the upper asymptotic ball density of a
set with respect to an additive Haar measure, in every finite dimension (including dimension
`0`). -/
theorem limsup_addHaar_smul_inter_ball_div {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 E]
    [NormSMulClass 𝕜 E] {c : 𝕜} (hc : c ≠ 0) (s : Set E) (a : E) :
    limsup (fun R : ℝ ↦ μ ((c • s) ∩ ball a R) / μ (ball a R)) atTop =
      limsup (fun R : ℝ ↦ μ (s ∩ ball a R) / μ (ball a R)) atTop := by
  have hmap : Filter.map (fun R : ℝ ↦ ‖c‖ * R) atTop = atTop := by
    simpa [div_eq_mul_inv, mul_comm] using
      Filter.map_div_atTop_eq ‖c‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr hc))
  have hcomp :
      limsup (fun R : ℝ ↦ μ ((c • s) ∩ ball (c • a) (‖c‖ * R)) /
        μ (ball (c • a) (‖c‖ * R))) atTop =
      limsup (fun R : ℝ ↦ μ ((c • s) ∩ ball (c • a) R) / μ (ball (c • a) R)) atTop := by
    simpa only [hmap, Function.comp_def] using Filter.limsup_comp
      (fun R : ℝ ↦ μ ((c • s) ∩ ball (c • a) R) / μ (ball (c • a) R))
      (fun R : ℝ ↦ ‖c‖ * R) atTop
  rw [μ.limsup_addHaar_inter_ball_div_eq (c • s) a (c • a), ← hcomp]
  simp_rw [μ.addHaar_smul_inter_ball_div hc s a]

/-- Surjective isometries from a finite-dimensional real normed space to an extended metric
additive topological group with isometric left translation preserve ratios of additive Haar
measures. -/
theorem addHaar_image_div_of_isometry
    {F : Type*} [EMetricSpace F] [AddGroup F] [IsTopologicalAddGroup F] [IsIsometricVAdd F F]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
    {f : E → F} (hf : Isometry f) (hsurj : Function.Surjective f) (s t : Set E) :
    ν (f '' s) / ν (f '' t) = μ s / μ t := by
  let e : E ≃ᵢ F := ⟨Equiv.ofBijective f ⟨hf.injective, hsurj⟩, hf⟩
  have he : ⇑e.toHomeomorph = f := by
    rw [IsometryEquiv.coe_toHomeomorph, ← IsometryEquiv.coe_toEquiv]
    exact Equiv.coe_ofBijective f ⟨hf.injective, hsurj⟩
  have : LocallyCompactSpace F := e.toHomeomorph.locallyCompactSpace_iff.mp inferInstance
  have : SecondCountableTopology F := e.symm.toHomeomorph.secondCountableTopology
  have : IsAddHaarMeasure (hausdorffMeasure (finrank ℝ E) : Measure F) :=
    { lt_top_of_isCompact K hK := by
        rw [← Set.image_preimage_eq K hsurj, hf.hausdorffMeasure_image (Or.inr hsurj), ← he]
        exact (e.toHomeomorph.isCompact_preimage.mpr hK).measure_lt_top
      open_pos U hU hU' := by
        rw [← Set.image_preimage_eq U hsurj, hf.hausdorffMeasure_image (Or.inr hsurj)]
        exact (hU.preimage hf.continuous).measure_ne_zero _ (hU'.preimage hsurj) }
  have hcν : (addHaarScalarFactor ν (hausdorffMeasure (finrank ℝ E)) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have hcμ : (addHaarScalarFactor μ (hausdorffMeasure (finrank ℝ E)) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  rw [isAddLeftInvariant_eq_smul ν (hausdorffMeasure (finrank ℝ E)),
    isAddLeftInvariant_eq_smul μ (hausdorffMeasure (finrank ℝ E))]
  simp only [coe_nnreal_smul_apply,
    ENNReal.mul_div_mul_left _ _ hcν ENNReal.coe_ne_top,
    ENNReal.mul_div_mul_left _ _ hcμ ENNReal.coe_ne_top,
    hf.hausdorffMeasure_image (Or.inr hsurj)]

section Isometry

variable {F : Type*} [MetricSpace F] [AddGroup F] [IsTopologicalAddGroup F] [IsIsometricVAdd F F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]

/-- Transporting a set and a ball by a surjective isometry preserves finite-radius additive Haar
density ratios between any two additive Haar measures. -/
theorem addHaar_image_inter_ball_div_of_isometry
    {f : E → F} (hf : Isometry f) (hsurj : Function.Surjective f)
    (s : Set E) (a : E) (R : ℝ) :
    ν (f '' s ∩ ball (f a) R) / ν (ball (f a) R) = μ (s ∩ ball a R) / μ (ball a R) := by
  have hball : f '' ball a R = ball (f a) R := by
    rw [← hf.preimage_ball a R, Set.image_preimage_eq _ hsurj]
  rw [← hball, ← image_inter hf.injective]
  exact μ.addHaar_image_div_of_isometry ν hf hsurj (s ∩ ball a R) (ball a R)

/-- Surjective isometries carry upper asymptotic ball density between any two additive Haar
measures and arbitrary basepoints. -/
theorem limsup_addHaar_image_inter_ball_div_eq_of_isometry
    {f : E → F} (hf : Isometry f) (hsurj : Function.Surjective f)
    (s : Set E) (a : F) (b : E) :
    limsup (fun R : ℝ ↦ ν (f '' s ∩ ball a R) / ν (ball a R)) atTop =
      limsup (fun R : ℝ ↦ μ (s ∩ ball b R) / μ (ball b R)) atTop := by
  obtain ⟨a₀, rfl⟩ := hsurj a
  simp_rw [μ.addHaar_image_inter_ball_div_of_isometry ν hf hsurj s a₀]
  exact μ.limsup_addHaar_inter_ball_div_eq s a₀ b

end Isometry

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
