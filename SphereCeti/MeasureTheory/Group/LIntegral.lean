/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Points of a finite set in the translates of a set

Let `μ` be a measure on an additive commutative group that is invariant under translations and
under negation, such as Lebesgue measure on a finite-dimensional real vector space.  For a finite
set `S` and a measurable set `Q`, integrating over `a` the number of points of `S` in the
translate `a +ᵥ Q` gives `#S * μ Q`: a point `s` lies in `a +ᵥ Q` exactly when `a` lies in
`s +ᵥ -Q`, a set of measure `μ Q`.  Hence if a measurable set `K` of finite positive measure
contains every difference `s - q` with `s ∈ S` and `q ∈ Q`, some translate `a +ᵥ Q` with `a ∈ K`
contains at least `#S * μ Q / μ K` points of `S`.

In the periodic approximation of sphere packings, `S` is the set of centers of a packing in a
large ball and `Q` is a coordinate box, so some translate of the box contains at least its
proportional share of those centers.

## Main statements

* `MeasureTheory.lintegral_card_filter_mem_vadd`: `∫⁻ a, #{s ∈ S | s ∈ a +ᵥ Q} ∂μ = #S * μ Q`.
* `MeasureTheory.exists_card_mul_le_card_filter_mem_vadd_mul`: some `a ∈ K` has
  `#S * μ Q ≤ #{s ∈ S | s ∈ a +ᵥ Q} * μ K`.
-/

public section

open scoped Pointwise ENNReal Finset

namespace MeasureTheory

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd G] [MeasurableNeg G]
  {μ : Measure G} [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

open Classical in
/-- On average over `a`, the translate `a +ᵥ Q` of a measurable set `Q` contains `#S * μ Q`
points of a finite set `S`. -/
theorem lintegral_card_filter_mem_vadd (S : Finset G) {Q : Set G} (hQ : MeasurableSet Q) :
    ∫⁻ a, (#{s ∈ S | s ∈ a +ᵥ Q} : ℝ≥0∞) ∂μ = #S * μ Q := by
  -- A point `s` lies in `a +ᵥ Q` exactly when `a` lies in `s +ᵥ -Q`.
  have hmem (a s : G) : s ∈ a +ᵥ Q ↔ a ∈ s +ᵥ -Q := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_neg,
      vadd_eq_add, vadd_eq_add, neg_add, neg_neg, add_comm]
  have hT (s : G) : MeasurableSet (s +ᵥ -Q) := hQ.neg.const_vadd s
  calc ∫⁻ a, (#{s ∈ S | s ∈ a +ᵥ Q} : ℝ≥0∞) ∂μ
      = ∫⁻ a, ∑ s ∈ S, (s +ᵥ -Q).indicator 1 a ∂μ := by
        refine lintegral_congr fun a ↦ ?_
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun s _ ↦ ?_
        simp only [hmem, Set.indicator_apply, Pi.one_apply, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero]
    _ = ∑ s ∈ S, μ (s +ᵥ -Q) := by
        rw [lintegral_finsetSum _ fun s _ ↦ measurable_one.indicator (hT s)]
        exact Finset.sum_congr rfl fun s _ ↦ lintegral_indicator_one (hT s)
    _ = #S * μ Q := by
        simp [measure_vadd, Measure.measure_neg]

open Classical in
/-- **First moment method for translates.**  If a measurable set `K` of finite positive measure
contains every difference `s - q` with `s ∈ S` and `q ∈ Q`, then some translate `a +ᵥ Q` with
`a ∈ K` contains at least `#S * μ Q / μ K` points of `S`. -/
theorem exists_card_mul_le_card_filter_mem_vadd_mul (S : Finset G) {Q K : Set G}
    (hQ : MeasurableSet Q) (hK : MeasurableSet K) (hK0 : μ K ≠ 0) (hKtop : μ K ≠ ∞)
    (hSQK : ∀ s ∈ S, ∀ q ∈ Q, s - q ∈ K) :
    ∃ a ∈ K, #S * μ Q ≤ #{s ∈ S | s ∈ a +ᵥ Q} * μ K := by
  set f : G → ℝ≥0∞ := fun a ↦ #{s ∈ S | s ∈ a +ᵥ Q} with hf
  -- The count vanishes off `K`: a point `a + q` of `S` gives `a = (a + q) - q ∈ K`.
  have hsupp : Function.support f ⊆ K := by
    intro a ha
    have hne : ({s ∈ S | s ∈ a +ᵥ Q} : Finset G).Nonempty := by
      rw [← Finset.card_pos, Nat.pos_iff_ne_zero]
      exact fun h ↦ ha (by simp [hf, h])
    obtain ⟨s, hs⟩ := hne
    rw [Finset.mem_filter, Set.mem_vadd_set] at hs
    obtain ⟨hsS, q, hq, rfl⟩ := hs
    simpa using hSQK _ hsS q hq
  have hint : ∫⁻ a in K, f a ∂μ = #S * μ Q := by
    rw [setLIntegral_eq_of_support_subset hsupp, lintegral_card_filter_mem_vadd S hQ]
  -- The count is at most `#S`, so its integral over `K` is finite.
  have hfin : ∫⁻ a in K, f a ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top #S) hKtop) ?_
    calc ∫⁻ a in K, f a ∂μ ≤ ∫⁻ _ in K, (#S : ℝ≥0∞) ∂μ :=
          lintegral_mono fun a ↦ Nat.cast_le.mpr (Finset.card_filter_le _ _)
      _ = #S * μ K := setLIntegral_const K _
  obtain ⟨a, ha, hle⟩ := exists_setLAverage_le hK0 hK.nullMeasurableSet hfin
  refine ⟨a, ha, ?_⟩
  rwa [setLAverage_eq, hint, ENNReal.div_le_iff hK0 hKtop] at hle

end MeasureTheory
