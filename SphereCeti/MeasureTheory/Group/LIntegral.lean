/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.MeasureTheory.Integral.Lebesgue.Encard

/-!
# Points of a set in the translates of a set

Let `μ` be a measure on an additive commutative group that is invariant under translations and
under negation, such as Lebesgue measure on a finite-dimensional real vector space.  For a
countable set `S` and a measurable set `Q`, integrating over `a` the number of points of `S` in
the translate `a +ᵥ Q` gives `#S * μ Q`: a point `s` lies in `a +ᵥ Q` exactly when `a` lies in
`s +ᵥ -Q`, a set of measure `μ Q`.  Hence if `S` is finite and a measurable set `K` of finite
positive measure contains every difference `s - q` with `s ∈ S` and `q ∈ Q`, the average over
`a ∈ K` of the number of points of `S` in `a +ᵥ Q` is `#S * μ Q / μ K`, so some translate with
`a ∈ K` contains at least that many points of `S`.

In the periodic approximation of sphere packings, `S` is the set of centers of a packing in a
large ball and `Q` is a coordinate box, so some translate of the box contains at least its
proportional share of those centers.

## Main statements

* `MeasureTheory.lintegral_encard_inter_vadd`: `∫⁻ a, #(S ∩ (a +ᵥ Q)) ∂μ = #S * μ Q`.
* `MeasureTheory.exists_encard_mul_le_encard_inter_vadd_mul`: some `a ∈ K` has
  `#S * μ Q ≤ #(S ∩ (a +ᵥ Q)) * μ K`.
-/

public section

open scoped Pointwise ENNReal

namespace MeasureTheory

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd G] [MeasurableNeg G]
  {μ : Measure G} [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

/-- For a countable set `S` and a measurable set `Q`, integrating over `a` the number of points of
`S` in the translate `a +ᵥ Q` gives `#S * μ Q`. -/
theorem lintegral_encard_inter_vadd {S : Set G} (hS : S.Countable) {Q : Set G}
    (hQ : MeasurableSet Q) :
    ∫⁻ a, ((S ∩ (a +ᵥ Q)).encard : ℝ≥0∞) ∂μ = S.encard * μ Q := by
  have := hS.to_subtype
  -- A point `s` lies in `a +ᵥ Q` exactly when `a` lies in `s +ᵥ -Q`, a set of measure `μ Q`.
  have hset (s : G) : {a | s ∈ a +ᵥ Q} = s +ᵥ -Q := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_neg, vadd_eq_add]
    rw [show -(-s + a) = -a + s by abel]
  -- Count the points of `S` in `a +ᵥ Q` as elements of the subtype `S`.
  have hcount (a : G) : (S ∩ (a +ᵥ Q)).encard = {s : S | (s : G) ∈ a +ᵥ Q}.encard := by
    rw [← Subtype.image_preimage_coe, Subtype.val_injective.encard_image]
    rfl
  simp_rw [hcount]
  rw [lintegral_encard_setOf_eq_tsum (P := fun (s : S) a ↦ (s : G) ∈ a +ᵥ Q) μ
    fun s ↦ by simpa only [hset] using hQ.neg.const_vadd (s : G)]
  simp only [hset, measure_vadd, Measure.measure_neg, ENNReal.tsum_const, ENat.card_coe_set_eq]

/-- **First moment method for translates.**  If `S` is finite and a measurable set `K` of finite
positive measure contains every difference `s - q` with `s ∈ S` and `q ∈ Q`, then some translate
`a +ᵥ Q` with `a ∈ K` contains at least `#S * μ Q / μ K` points of `S`. -/
theorem exists_encard_mul_le_encard_inter_vadd_mul {S : Set G} (hS : S.Finite) {Q K : Set G}
    (hQ : MeasurableSet Q) (hK : MeasurableSet K) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ∞)
    (hSQK : ∀ s ∈ S, ∀ q ∈ Q, s - q ∈ K) :
    ∃ a ∈ K, S.encard * μ Q ≤ (S ∩ (a +ᵥ Q)).encard * μ K := by
  set f : G → ℝ≥0∞ := fun a ↦ ((S ∩ (a +ᵥ Q)).encard : ℝ≥0∞) with hf
  -- The count vanishes off `K`: a point `a + q` of `S` gives `a = (a + q) - q ∈ K`.
  have hsupp : Function.support f ⊆ K := by
    intro a ha
    obtain ⟨s, hsS, hsQ⟩ : (S ∩ (a +ᵥ Q)).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr fun h ↦ ha (by simp [hf, h])
    obtain ⟨q, hq, rfl⟩ := hsQ
    simpa using hSQK _ hsS q hq
  have hint : ∫⁻ a in K, f a ∂μ = S.encard * μ Q := by
    rw [setLIntegral_eq_of_support_subset hsupp, lintegral_encard_inter_vadd hS.countable hQ]
  -- The count is at most the finite `#S`, so its integral over `K` is finite.
  have hfin : ∫⁻ a in K, f a ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENat.toENNReal_lt_top.mpr hS.encard_lt_top).ne hKtop) ?_
    calc ∫⁻ a in K, f a ∂μ ≤ ∫⁻ _ in K, (S.encard : ℝ≥0∞) ∂μ :=
          lintegral_mono fun a ↦ ENat.toENNReal_le.mpr (Set.encard_le_encard Set.inter_subset_left)
      _ = S.encard * μ K := setLIntegral_const K _
  obtain ⟨a, ha, hle⟩ := exists_setLAverage_le hK0 hK.nullMeasurableSet hfin
  refine ⟨a, ha, ?_⟩
  rw [setLAverage_eq, hint, ENNReal.div_le_iff hK0 hKtop] at hle
  exact hle

end MeasureTheory
