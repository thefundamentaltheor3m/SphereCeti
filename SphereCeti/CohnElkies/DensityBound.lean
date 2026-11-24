/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Analysis.Distribution.SchwartzSpace.FourierPositivity
public import SphereCeti.CohnElkies.PeriodicBound
public import SphereCeti.MeasureTheory.Measure.Haar.BoxAveraging
public import SphereCeti.ZLattice.PeriodicRepetition

/-!
# The Cohn–Elkies bound for separated sets

Let `f` be a Schwartz function on `ℝⁿ` with `Re f ≤ 0` at distance at least `r > 0` from the
origin, `Re 𝓕 f ≥ 0` everywhere and `Re 𝓕 f(0) > 0`, and let `κ = Re f(0) / Re 𝓕 f(0)`.

A finite set of points at mutual distance at least `r` in a translated coordinate box of radius
`R ≥ 0` has at most `(2 (R + r))ⁿ κ` points.  A set `X` of points at mutual distance at least `r`
has at most `κ` points per unit volume in large balls: the number of points of `X` in the closed
ball of radius `T` about the origin, divided by the volume of the ball, has limit superior at most
`κ` as `T → ∞`.  For the centers of a sphere packing with center separation `r`, this is the
Cohn–Elkies bound on the center density.

## Main statements

* `SphereCeti.CohnElkies.ncard_le_of_subset_vadd_centeredBox`: a finite set of points at mutual
  distance at least `r` in a translated box of radius `R` has at most `(2 (R + r))ⁿ κ` points.
* `SphereCeti.CohnElkies.limsup_encard_inter_closedBall_div_volume_le`: a set of points at mutual
  distance at least `r` has at most `κ` points per unit volume in large balls, in the sense of the
  limit superior.

## References

* H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714, Section 3.
-/

public section

open Filter Metric MeasureTheory Submodule
open scoped ENNReal FourierTransform Pointwise SchwartzMap Topology

namespace SphereCeti.CohnElkies

variable {ι : Type*} [Fintype ι]

/-- A finite set of points at mutual distance at least `r > 0` in a translated box of radius
`R ≥ 0` has at most `(2 (R + r))ⁿ Re f(0) / Re 𝓕 f(0)` points, for a Schwartz function `f` with
`Re f ≤ 0` at distance at least `r` from the origin, `Re 𝓕 f ≥ 0` and `Re 𝓕 f(0) > 0`. -/
theorem ncard_le_of_subset_vadd_centeredBox {S : Set (EuclideanSpace ℝ ι)} (hS : S.Finite)
    {a : EuclideanSpace ℝ ι} {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r)
    (hSbox : S ⊆ a +ᵥ EuclideanSpace.centeredBox ι R)
    (hsep : Pairwise (r ≤ dist · · : S → S → Prop))
    {f : 𝓢(EuclideanSpace ℝ ι, ℂ)} (hf : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0)
    (hfourier : ∀ y, 0 ≤ (𝓕 f y).re) (hf0 : 0 < (𝓕 f 0).re) :
    (S.ncard : ℝ) ≤ (2 * (R + r)) ^ Fintype.card ι * ((f 0).re / (𝓕 f 0).re) := by
  have hκ : 0 < (f 0).re / (𝓕 f 0).re :=
    div_pos (f.re_apply_zero_pos_of_fourier_nonneg hfourier hf0) hf0
  have hc : 0 < 2 * (R + r) := by positivity
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Set.ncard_empty, Nat.cast_zero]
    positivity
  set c := 2 * (R + r) with hcdef
  have : NeZero c := ⟨hc.ne'⟩
  have : Fintype S := hS.fintype
  have : Nonempty S := hne.to_subtype
  set L : Submodule ℤ (EuclideanSpace ℝ ι) :=
    c • span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)
  have hcR : 2 * R < |c| := by
    rw [abs_of_pos hc, hcdef]
    linarith
  have hp : ∀ q q' : S, (q : EuclideanSpace ℝ ι) - q' ∈ L → q = q' := fun q q' h ↦
    Subtype.ext (EuclideanSpace.eq_of_sub_mem_smul_span_basisFun (hSbox q.2) (hSbox q'.2) hcR h)
  -- The repetition of `S` along `L` keeps the separation `r`.
  have hrep := EuclideanSpace.pairwise_le_dist_periodicRepetition hSbox hsep
  have hmem (s : S) : (s : EuclideanSpace ℝ ι) ∈ EuclideanSpace.periodicRepetition S c :=
    EuclideanSpace.mem_periodicRepetition.mpr ⟨0, s, s.2, by ext i; simp⟩
  have hsep' : ∀ (z : L) (q q' : S), (z : EuclideanSpace ℝ ι) + q - q' ≠ 0 →
      r ≤ ‖(z : EuclideanSpace ℝ ι) + q - q'‖ := by
    intro z q q' hzqq'
    have hzq := EuclideanSpace.add_mem_periodicRepetition z.2 (hmem q)
    have hne' : (⟨_, hzq⟩ : EuclideanSpace.periodicRepetition S c) ≠ ⟨_, hmem q'⟩ := by
      intro h
      exact hzqq' (sub_eq_zero.mpr (congrArg Subtype.val h))
    have h := hrep hne'
    simp only [Subtype.dist_eq] at h
    rwa [dist_eq_norm] at h
  have h := card_div_covolume_le L hp hf hsep'
    (fun y _ ↦ by simpa [SchwartzMap.fourier_coe] using hfourier y) hf0
  rw [EuclideanSpace.covolume_smul_span_basisFun, abs_of_pos hc, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at h
  rwa [div_le_iff₀ (by positivity), mul_comm] at h

/-- **The Cohn–Elkies bound for separated sets.**  For a set `X` of points at mutual distance at
least `r > 0` and a Schwartz function `f` with `Re f ≤ 0` at distance at least `r` from the origin,
`Re 𝓕 f ≥ 0` and `Re 𝓕 f(0) > 0`, the number of points of `X` in the ball of radius `T` about the
origin, divided by the volume of the ball, has limit superior at most `Re f(0) / Re 𝓕 f(0)` as
`T → ∞`. -/
theorem limsup_encard_inter_closedBall_div_volume_le {X : Set (EuclideanSpace ℝ ι)} {r : ℝ}
    (hr : 0 < r) (hsep : Pairwise (r ≤ dist · · : X → X → Prop))
    {f : 𝓢(EuclideanSpace ℝ ι, ℂ)} (hf : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0)
    (hfourier : ∀ y, 0 ≤ (𝓕 f y).re) (hf0 : 0 < (𝓕 f 0).re) :
    limsup (fun T : ℝ ↦ (X ∩ closedBall 0 T).encard /
      volume (closedBall (0 : EuclideanSpace ℝ ι) T)) atTop ≤
      ENNReal.ofReal ((f 0).re / (𝓕 f 0).re) := by
  set κ := (f 0).re / (𝓕 f 0).re with hκdef
  have hκ : 0 < κ := div_pos (f.re_apply_zero_pos_of_fourier_nonneg hfourier hf0) hf0
  -- Subsets of `X` inherit the separation.
  have hsepS {S : Set (EuclideanSpace ℝ ι)} (hS : S ⊆ X) :
      Pairwise (r ≤ dist · · : S → S → Prop) := fun x y hxy ↦
    hsep (i := ⟨x, hS x.2⟩) (j := ⟨y, hS y.2⟩) fun h ↦ hxy (Subtype.ext (Subtype.mk.inj h))
  -- A ball of radius `T ≥ 0` lies in the box of radius `T`.
  have hball (T : ℝ) : closedBall (0 : EuclideanSpace ℝ ι) T ⊆
      (0 : EuclideanSpace ℝ ι) +ᵥ EuclideanSpace.centeredBox ι T := by
    intro x hx
    rw [zero_vadd, EuclideanSpace.mem_centeredBox]
    intro i
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le x i).trans (mem_closedBall_zero_iff.mp hx)
  -- `X` meets every ball in a finite set: otherwise it would contain finite subsets of the ball
  -- with more points than the box bound allows.
  have hfin (T : ℝ) : (X ∩ closedBall (0 : EuclideanSpace ℝ ι) T).Finite := by
    rcases lt_or_ge T 0 with hT | hT
    · simp [closedBall_eq_empty.mpr hT]
    by_contra hinf
    obtain ⟨S, hSsub, hSfin, hScard⟩ :=
      Set.Infinite.exists_subset_ncard_eq hinf (⌈(2 * (T + r)) ^ Fintype.card ι * κ⌉₊ + 1)
    have h := ncard_le_of_subset_vadd_centeredBox hSfin hT hr
      (hSsub.trans (Set.inter_subset_right.trans (hball T)))
      (hsepS (hSsub.trans Set.inter_subset_left)) hf hfourier hf0
    rw [hScard, Nat.cast_add, Nat.cast_one] at h
    linarith [Nat.le_ceil ((2 * (T + r)) ^ Fintype.card ι * κ)]
  -- For each box radius `R > 0`, the limit superior is at most `κ ((R + r) / R)ⁿ`.
  have hboundR (R : ℝ) (hR : 0 < R) :
      limsup (fun T : ℝ ↦ (X ∩ closedBall 0 T).encard /
        volume (closedBall (0 : EuclideanSpace ℝ ι) T)) atTop ≤
        ENNReal.ofReal ((2 * (R + r)) ^ Fintype.card ι * κ) /
          volume (EuclideanSpace.centeredBox ι R) := by
    set c := √(Fintype.card ι : ℝ) * R
    set K := ENNReal.ofReal ((2 * (R + r)) ^ Fintype.card ι * κ) /
      volume (EuclideanSpace.centeredBox ι R)
    have hbox0 : volume (EuclideanSpace.centeredBox ι R) ≠ 0 := by
      rw [EuclideanSpace.volume_centeredBox]
      exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hboxtop : volume (EuclideanSpace.centeredBox ι R) ≠ ⊤ := by
      rw [EuclideanSpace.volume_centeredBox]
      exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hK : K ≠ ⊤ := ENNReal.div_ne_top ENNReal.ofReal_ne_top hbox0
    have hbound : ∀ᶠ T in atTop, (X ∩ closedBall 0 T).encard /
        volume (closedBall (0 : EuclideanSpace ℝ ι) T) ≤
        K * (volume (closedBall (0 : EuclideanSpace ℝ ι) (T + c)) /
          volume (closedBall (0 : EuclideanSpace ℝ ι) T)) := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      obtain ⟨a, -, ha⟩ := EuclideanSpace.exists_encard_mul_volume_centeredBox_le (hfin T) hT
        hR.le Set.inter_subset_right
      have hcount : ((X ∩ closedBall 0 T) ∩ (a +ᵥ EuclideanSpace.centeredBox ι R)).encard ≤
          ENNReal.ofReal ((2 * (R + r)) ^ Fintype.card ι * κ) := by
        have hSfin : ((X ∩ closedBall 0 T) ∩ (a +ᵥ EuclideanSpace.centeredBox ι R)).Finite :=
          (hfin T).subset Set.inter_subset_left
        rw [← hSfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (ncard_le_of_subset_vadd_centeredBox hSfin hR.le hr
          Set.inter_subset_right (hsepS (Set.inter_subset_left.trans Set.inter_subset_left)) hf
          hfourier hf0)
      have h1 : (X ∩ closedBall 0 T).encard ≤
          ENNReal.ofReal ((2 * (R + r)) ^ Fintype.card ι * κ) *
            volume (closedBall (0 : EuclideanSpace ℝ ι) (T + c)) /
              volume (EuclideanSpace.centeredBox ι R) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hbox0) (Or.inl hboxtop)]
        exact ha.trans (by gcongr)
      calc (X ∩ closedBall 0 T).encard / volume (closedBall (0 : EuclideanSpace ℝ ι) T)
          ≤ ENNReal.ofReal ((2 * (R + r)) ^ Fintype.card ι * κ) *
              volume (closedBall (0 : EuclideanSpace ℝ ι) (T + c)) /
                volume (EuclideanSpace.centeredBox ι R) /
                  volume (closedBall (0 : EuclideanSpace ℝ ι) T) :=
            ENNReal.div_le_div_right h1 _
        _ = K * (volume (closedBall (0 : EuclideanSpace ℝ ι) (T + c)) /
              volume (closedBall (0 : EuclideanSpace ℝ ι) T)) := by
            simp only [K, div_eq_mul_inv]
            ac_rfl
    have hlim : Tendsto (fun T : ℝ ↦ K * (volume (closedBall (0 : EuclideanSpace ℝ ι) (T + c)) /
        volume (closedBall (0 : EuclideanSpace ℝ ι) T))) atTop (𝓝 (K * 1)) :=
      ENNReal.Tendsto.const_mul (EuclideanSpace.tendsto_volume_closedBall_add_div_volume c)
        (Or.inr hK)
    calc limsup (fun T : ℝ ↦ (X ∩ closedBall 0 T).encard /
          volume (closedBall (0 : EuclideanSpace ℝ ι) T)) atTop
        ≤ limsup (fun T : ℝ ↦ K * (volume (closedBall (0 : EuclideanSpace ℝ ι) (T + c)) /
            volume (closedBall (0 : EuclideanSpace ℝ ι) T))) atTop := limsup_le_limsup hbound
      _ = K := by rw [hlim.limsup_eq, mul_one]
  -- Letting `R → ∞`, the bounds `κ ((R + r) / R)ⁿ` tend to `κ`.
  have hlimR : Tendsto (fun R : ℝ ↦ ENNReal.ofReal ((2 * (R + r)) ^ Fintype.card ι * κ) /
      volume (EuclideanSpace.centeredBox ι R)) atTop (𝓝 (ENNReal.ofReal κ)) := by
    have hreal : Tendsto (fun R : ℝ ↦ (1 + r / R) ^ Fintype.card ι * κ) atTop (𝓝 κ) := by
      have h : Tendsto (fun R : ℝ ↦ 1 + r / R) atTop (𝓝 1) := by
        simpa using ((tendsto_const_nhds (x := r)).div_atTop tendsto_id).const_add 1
      simpa using (h.pow (Fintype.card ι)).mul_const κ
    refine (ENNReal.tendsto_ofReal hreal).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with R hR
    rw [EuclideanSpace.volume_centeredBox, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    have h2R : (2 * R) ^ Fintype.card ι ≠ 0 := by positivity
    have hR0 : R ≠ 0 := hR.ne'
    rw [eq_div_iff h2R, mul_right_comm, ← mul_pow,
      show (1 + r / R) * (2 * R) = 2 * (R + r) by field_simp]
  exact ge_of_tendsto hlimR
    (by filter_upwards [eventually_gt_atTop 0] with R hR using hboundR R hR)

end SphereCeti.CohnElkies
