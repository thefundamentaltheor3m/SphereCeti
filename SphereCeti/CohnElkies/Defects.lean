/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.CohnElkies.StructureFactor

/-!
# Defects of the periodic Cohn–Elkies bound

Let `L` be a full lattice in a finite-dimensional real inner product space `E`, let `p : ι → E`
be a family of `N` points that are pairwise incongruent modulo `L`, such as representatives of
the orbits of the centers of a periodic sphere packing under its period lattice, and let `f` be a
Schwartz function.  The real part of the structure-factor form of Poisson summation
`SphereCeti.CohnElkies.tsum_sum_sum_eq_tsum_dual_fourier_mul_structureFactor` is the exact identity

`N * Re f(0) - N² / covol(L) * Re 𝓕 f(0) = D_Fourier + D_direct`,

in which the terms of the `N` vanishing differences `z + p q - p q'` and of the zero frequency,
where the structure factor is `N²`, appear on the left.

The Fourier defect `D_Fourier` is `covol(L)⁻¹` times the sum of `Re 𝓕 f(y) * S_p(y)` over the
nonzero dual frequencies `y`; it is nonnegative when `Re 𝓕 f ≥ 0` there.  The direct defect
`D_direct` is minus the sum of `Re f` over the nonzero differences `z + p q - p q'`; it is
nonnegative when `Re f ≤ 0` at distance at least `r` from the origin and the nonzero differences
have norm at least `r`.  For a Cohn–Elkies certificate of radius `r`, the first condition holds,
and the second holds when every nonzero difference `z + p q - p q'` has norm at least `r`, as for
the orbit representatives of a periodic packing with center separation `r`.  Under that
separation hypothesis the identity is the periodic bound `N / covol(L) ≤ Re f(0) / Re 𝓕 f(0)`
together with its exact gap.

## Main definitions

* `SphereCeti.CohnElkies.directDefect L p f`: minus the sum of `Re f` over the nonzero
  differences `z + p q - p q'`.
* `SphereCeti.CohnElkies.fourierDefect L p f`: `covol(L)⁻¹` times the sum of
  `Re 𝓕 f(y) * S_p(y)` over the nonzero dual frequencies `y`.

## Main statements

* `SphereCeti.CohnElkies.fourierDefect_nonneg`: the Fourier defect is nonnegative when
  `Re 𝓕 f ≥ 0` at the nonzero dual frequencies.
* `SphereCeti.CohnElkies.directDefect_nonneg`: the direct defect is nonnegative when `Re f ≤ 0` at
  distance at least `r` from the origin and every nonzero difference `z + p q - p q'` has norm
  at least `r`.
* `SphereCeti.CohnElkies.defect_identity`: the exact identity above.
* `SphereCeti.CohnElkies.normalized_gap_eq_defects`: the gap
  `Re f(0) / Re 𝓕 f(0) - N / covol(L)` is the sum of the defects divided by `N * Re 𝓕 f(0)`.

## References

* H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714, proof of Theorem 3.2.
-/

public section

open Complex
open scoped Real RealInnerProductSpace SchwartzMap FourierTransform

namespace SphereCeti.CohnElkies

section Direct

variable {E : Type*} {ι : Type*} [Fintype ι]

open Classical in
/-- The direct defect of `f` on the translates `L + p q`: minus the sum of the real parts of `f`
over the nonzero differences `z + p q - p q'` with `z ∈ L`. -/
noncomputable def directDefect [AddCommGroup E] (L : Submodule ℤ E) (p : ι → E) (f : E → ℂ) :
    ℝ :=
  -∑' z : L, ∑ q, ∑ q',
    if (z : E) + p q - p q' = 0 then 0 else (f ((z : E) + p q - p q')).re

open Classical in
/-- The direct defect is minus the sum of `Re f` over the nonzero differences. -/
theorem directDefect_def [AddCommGroup E] (L : Submodule ℤ E) (p : ι → E) (f : E → ℂ) :
    directDefect L p f = -∑' z : L, ∑ q, ∑ q',
      if (z : E) + p q - p q' = 0 then 0 else (f ((z : E) + p q - p q')).re :=
  (rfl)

/-- The direct defect is nonnegative when `Re f ≤ 0` at distance at least `r` from the origin and
every nonzero difference `z + p q - p q'` has norm at least `r`. -/
theorem directDefect_nonneg [SeminormedAddCommGroup E] {L : Submodule ℤ E} {p : ι → E}
    {f : E → ℂ} {r : ℝ}
    (hf : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0)
    (hsep : ∀ (z : L) (q q' : ι), (z : E) + p q - p q' ≠ 0 → r ≤ ‖(z : E) + p q - p q'‖) :
    0 ≤ directDefect L p f := by
  rw [directDefect_def, neg_nonneg]
  refine tsum_nonpos fun z ↦ Finset.sum_nonpos fun q _ ↦ Finset.sum_nonpos fun q' _ ↦ ?_
  split_ifs with h
  · exact le_rfl
  · exact hf _ (hsep z q q' h)

end Direct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι]

open Classical in
/-- The Fourier defect of `f` on the translates `L + p q`: `(covolume L)⁻¹` times the sum of
`Re 𝓕 f(y) * S_p(y)` over the nonzero frequencies `y` of the dual lattice, where `S_p` is the
structure factor of `p`. -/
noncomputable def fourierDefect (L : Submodule ℤ E) (p : ι → E) (f : E → ℂ) : ℝ :=
  (ZLattice.covolume L)⁻¹ * ∑' y : ZLattice.dual L,
    if y = 0 then 0 else (𝓕 f (y : E)).re * structureFactor p (y : E)

open Classical in
/-- The Fourier defect is `(covolume L)⁻¹` times the sum of `Re 𝓕 f(y) * S_p(y)` over the nonzero
dual frequencies. -/
theorem fourierDefect_def (L : Submodule ℤ E) (p : ι → E) (f : E → ℂ) :
    fourierDefect L p f = (ZLattice.covolume L)⁻¹ * ∑' y : ZLattice.dual L,
      if y = 0 then 0 else (𝓕 f (y : E)).re * structureFactor p (y : E) :=
  (rfl)

/-- The Fourier defect is nonnegative when `Re 𝓕 f ≥ 0` at the nonzero dual frequencies. -/
theorem fourierDefect_nonneg {L : Submodule ℤ E} {p : ι → E} {f : E → ℂ}
    (hf : ∀ y : ZLattice.dual L, y ≠ 0 → 0 ≤ (𝓕 f (y : E)).re) :
    0 ≤ fourierDefect L p f := by
  rw [fourierDefect_def]
  -- The covolume is the real value of an extended nonnegative real, hence nonnegative.
  have hcov : 0 ≤ ZLattice.covolume L := by
    rw [ZLattice.covolume]
    exact ENNReal.toReal_nonneg
  refine mul_nonneg (inv_nonneg.mpr hcov) (tsum_nonneg fun y ↦ ?_)
  split_ifs with hy
  · exact le_rfl
  · exact mul_nonneg (hf y hy) (structureFactor_nonneg p _)

/-- **The defect identity of the periodic Cohn–Elkies bound.**  For a full lattice `L`, a family
of `N` points pairwise incongruent modulo `L`, and a Schwartz function `f`,
`N * Re f(0) - N² / covol(L) * Re 𝓕 f(0) = D_Fourier + D_direct`. -/
theorem defect_identity (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {p : ι → E}
    (hp : ∀ q q', p q - p q' ∈ L → q = q') (f : 𝓢(E, ℂ)) :
    (Fintype.card ι : ℝ) * (f 0).re -
        (Fintype.card ι : ℝ) ^ 2 / ZLattice.covolume L * (𝓕 f 0).re =
      fourierDefect L p f + directDefect L p f := by
  classical
  -- The only vanishing differences `z + p q - p q'` are those with `z = 0` and `q = q'`.
  have hzero (z : L) (q q' : ι) : (z : E) + p q - p q' = 0 ↔ z = 0 ∧ q = q' := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h.1, h.2]⟩
    have hmem : p q - p q' ∈ L := by
      rw [add_sub_assoc] at h
      rw [eq_neg_of_add_eq_zero_right h]
      exact L.neg_mem z.2
    obtain rfl := hp q q' hmem
    exact ⟨by simpa using h, rfl⟩
  -- Each term splits into its value at a vanishing difference and its nonzero-difference part.
  have hsplit (z : L) : ∑ q, ∑ q', (f ((z : E) + p q - p q')).re =
      (if z = 0 then (Fintype.card ι : ℝ) * (f 0).re else 0) + ∑ q, ∑ q',
        if (z : E) + p q - p q' = 0 then 0 else (f ((z : E) + p q - p q')).re := by
    have hterm (q q' : ι) : (f ((z : E) + p q - p q')).re =
        (if z = 0 ∧ q = q' then (f 0).re else 0) +
          if (z : E) + p q - p q' = 0 then 0 else (f ((z : E) + p q - p q')).re := by
      by_cases h : (z : E) + p q - p q' = 0
      · simp [(hzero z q q').mp h]
      · simp [h, mt (hzero z q q').mpr h]
    calc ∑ q, ∑ q', (f ((z : E) + p q - p q')).re
        = ∑ q, ∑ q', ((if z = 0 ∧ q = q' then (f 0).re else 0) +
            if (z : E) + p q - p q' = 0 then 0 else (f ((z : E) + p q - p q')).re) :=
          Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun q' _ ↦ hterm q q'
      _ = _ := by
          simp only [Finset.sum_add_distrib]
          congr 1
          split_ifs with hz <;> simp [hz]
  -- Real parts of the structure-factor form of Poisson summation.
  have hP := congrArg re (tsum_sum_sum_eq_tsum_dual_fourier_mul_structureFactor L p f)
  rw [re_tsum (summable_sum_sum_translates L p f), ← ofReal_inv, re_ofReal_mul,
    re_tsum (summable_fourier_mul_structureFactor L p f)] at hP
  simp only [re_sum, re_mul_ofReal] at hP
  -- Direct side: separate the vanishing differences.
  have ha : Summable fun z : L ↦ ∑ q, ∑ q', (f ((z : E) + p q - p q')).re := by
    simpa only [Function.comp_def, reCLM_apply, re_sum] using
      (summable_sum_sum_translates L p f).mapL reCLM
  have hc : Summable fun z : L ↦ if z = 0 then (Fintype.card ι : ℝ) * (f 0).re else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun z hz ↦ by simp_all
  have hb : Summable fun z : L ↦ ∑ q, ∑ q',
      if (z : E) + p q - p q' = 0 then 0 else (f ((z : E) + p q - p q')).re :=
    (ha.sub hc).congr fun z ↦ by simp only [hsplit z]; ring
  rw [tsum_congr hsplit, Summable.tsum_add hc hb, tsum_ite_eq] at hP
  -- Fourier side: separate the zero frequency.
  have hF : Summable fun y : ZLattice.dual L ↦ ((𝓕 f) (y : E)).re * structureFactor p (y : E) := by
    simpa only [Function.comp_def, reCLM_apply, re_mul_ofReal] using
      (summable_fourier_mul_structureFactor L p f).mapL reCLM
  rw [hF.tsum_eq_add_tsum_ite 0] at hP
  simp only [ZeroMemClass.coe_zero, structureFactor_zero] at hP
  rw [fourierDefect_def, directDefect_def]
  simp only [SchwartzMap.fourier_coe] at hP ⊢
  linear_combination hP

/-- **The normalized gap of the periodic Cohn–Elkies bound.**  For a nonempty family of `N` points
pairwise incongruent modulo `L` and a Schwartz function `f` with `Re 𝓕 f(0) ≠ 0`, the gap
`Re f(0) / Re 𝓕 f(0) - N / covol(L)` is the sum of the two defects divided by
`N * Re 𝓕 f(0)`. -/
theorem normalized_gap_eq_defects (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    [Nonempty ι] {p : ι → E} (hp : ∀ q q', p q - p q' ∈ L → q = q') (f : 𝓢(E, ℂ))
    (hf : (𝓕 f 0).re ≠ 0) :
    (f 0).re / (𝓕 f 0).re - (Fintype.card ι : ℝ) / ZLattice.covolume L =
      (fourierDefect L p f + directDefect L p f) / ((Fintype.card ι : ℝ) * (𝓕 f 0).re) := by
  rw [← defect_identity L hp f]
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc : ZLattice.covolume L ≠ 0 := (ZLattice.covolume_pos L).ne'
  field_simp

end SphereCeti.CohnElkies
