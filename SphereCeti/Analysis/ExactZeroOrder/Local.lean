/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.ExactZeroOrder

/-!
# Local properties of exact zero orders

A function with an exact zero order at a point is continuous there and is nonzero on a
punctured neighborhood. The order is unique, so two local power factorizations with continuous
nonvanishing cofactors cannot assign different multiplicities to the same function.

## Source

The uniqueness argument is adapted to real-domain, complex-valued functions from
`TauCetiProject/TauCeti@83769e442d55cda9d85b3927a93b286831c595ff`,
`TauCeti/Analysis/Complex/Wirtinger/Similarity.lean`,
`eq_of_eventually_sub_pow_mul_eq` (Apache-2.0). The continuity and isolation arguments follow
the local-factorization arguments in `TauCeti/Analysis/Complex/ContinuousLog/ArgumentPrinciple.lean`
at the same commit. The original license and author credit are retained.
-/

public section

open Filter
open scoped Topology

namespace SphereCeti

/-- A local power factorization with a continuous cofactor gives continuity at its center. -/
theorem HasExactZeroOrder.continuousAt {f : ℝ → ℂ} {a : ℝ} {m : ℕ}
    (hf : HasExactZeroOrder f a m) : ContinuousAt f a := by
  obtain ⟨u, hu, -, hfu⟩ := hasExactZeroOrder_iff.mp hf
  have hc : ContinuousAt (fun x : ℝ => (x - a : ℂ) ^ m * u x) a :=
    ((Complex.continuous_ofReal.continuousAt.sub continuousAt_const).pow m).mul hu
  exact hc.congr_of_eventuallyEq hfu

/-- A function with an exact zero order is nonzero on a punctured neighborhood of the center. -/
theorem HasExactZeroOrder.eventually_ne_zero {f : ℝ → ℂ} {a : ℝ} {m : ℕ}
    (hf : HasExactZeroOrder f a m) : ∀ᶠ x in 𝓝[≠] a, f x ≠ 0 := by
  obtain ⟨u, hu, hua, hfu⟩ := hasExactZeroOrder_iff.mp hf
  filter_upwards [nhdsWithin_le_nhds (hu.eventually_ne hua),
    nhdsWithin_le_nhds hfu, self_mem_nhdsWithin] with x hux hfx hxa
  have hxa' : (x - a : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hxa
  rw [hfx]
  exact mul_ne_zero (pow_ne_zero m hxa') hux

/-- Two exact zero orders of the same function at the same point agree. -/
theorem HasExactZeroOrder.unique {f : ℝ → ℂ} {a : ℝ} {m n : ℕ}
    (hf : HasExactZeroOrder f a m) (hf' : HasExactZeroOrder f a n) : m = n := by
  wlog hmn : m < n generalizing m n
  · rcases (not_lt.mp hmn).eq_or_lt with h | h
    · exact h.symm
    · exact (this hf' hf h).symm
  exfalso
  obtain ⟨u, hu, hua, hfu⟩ := hasExactZeroOrder_iff.mp hf
  obtain ⟨v, hv, -, hfv⟩ := hasExactZeroOrder_iff.mp hf'
  -- Cancel the smaller power away from the base point.
  have hlim : Tendsto (fun x : ℝ => (x - a : ℂ) ^ (n - m) * v x)
      (𝓝[≠] a) (𝓝 (u a)) := by
    refine (hu.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds hfu, nhdsWithin_le_nhds hfv,
      self_mem_nhdsWithin] with x hfx hfx' hxa
    have hxa' : (x - a : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hxa
    apply mul_left_cancel₀ (pow_ne_zero m hxa')
    rw [← hfx, hfx', ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn.le]
  have hzero : Tendsto (fun x : ℝ => (x - a : ℂ) ^ (n - m) * v x)
      (𝓝[≠] a) (𝓝 0) := by
    have hc : ContinuousAt (fun x : ℝ => (x - a : ℂ) ^ (n - m) * v x) a :=
      ((Complex.continuous_ofReal.continuousAt.sub continuousAt_const).pow _).mul hv
    simpa [zero_pow (Nat.sub_ne_zero_of_lt hmn)] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  exact hua (tendsto_nhds_unique hlim hzero)

end SphereCeti
