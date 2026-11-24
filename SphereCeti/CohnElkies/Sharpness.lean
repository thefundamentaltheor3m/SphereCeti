/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.CohnElkies.Defects

/-!
# Vanishing of the Cohn–Elkies defects

Let `L` be a full lattice in a finite-dimensional real inner product space `E`, let `p : ι → E`
be a finite family of points, and let `f` be a Schwartz function.  The direct defect and the
Fourier defect of `f` on the translates `L + p q` are absolutely convergent sums, and each of them
vanishes exactly when all of its terms do, provided its terms have one sign:

* if `Re f ≤ 0` at distance at least `r` from the origin and every nonzero difference
  `z + p q - p q'` with `z ∈ L` has norm at least `r`, the direct defect vanishes exactly when
  `Re f` vanishes at every such nonzero difference;
* if `Re 𝓕 f ≥ 0` at the nonzero frequencies of the dual lattice, the Fourier defect vanishes
  exactly when `Re 𝓕 f(y) * S_p(y)` vanishes at every nonzero dual frequency `y`, where `S_p` is
  the structure factor of `p`.  This allows `Re 𝓕 f(y) ≠ 0` at frequencies where `S_p(y) = 0`.

If moreover the points are pairwise incongruent modulo `L`, both defects vanish exactly when the
periodic bound is attained, that is `N * Re f(0) = N² / covol(L) * Re 𝓕 f(0)` for `N` points.
So under these hypotheses, equality in the periodic Cohn–Elkies bound holds exactly when `Re f`
vanishes at the nonzero differences and `Re 𝓕 f * S_p` vanishes at the nonzero dual frequencies.

## Main statements

* `SphereCeti.CohnElkies.directDefect_eq_zero_iff`: under the sign condition on `Re f` and the
  separation of the nonzero differences, the direct defect vanishes exactly when `Re f` vanishes
  at the nonzero differences.
* `SphereCeti.CohnElkies.fourierDefect_eq_zero_iff`: under the sign condition on `Re 𝓕 f`, the
  Fourier defect vanishes exactly when `Re 𝓕 f * S_p` vanishes at the nonzero dual frequencies.
* `SphereCeti.CohnElkies.directDefect_eq_zero_and_fourierDefect_eq_zero_iff`: under both sign
  conditions, the separation, and incongruence of the points modulo `L`, both defects vanish
  exactly when the periodic bound is attained.

## References

* H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714, Section 8.
-/

public section

open Complex
open scoped Real RealInnerProductSpace SchwartzMap FourierTransform

namespace SphereCeti.CohnElkies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

open Classical in
/-- The terms of the direct defect of a Schwartz function are summable. -/
private lemma summable_directDefect_terms (L : Submodule ℤ E) [DiscreteTopology L] (p : ι → E)
    (f : 𝓢(E, ℂ)) : Summable fun z : L ↦ ∑ q, ∑ q',
      if (z : E) + p q - p q' = 0 then 0 else (f ((z : E) + p q - p q')).re := by
  refine Summable.of_norm_bounded (g := fun z : L ↦ ∑ q, ∑ q', ‖f ((z : E) + p q - p q')‖)
    (summable_sum fun q _ ↦ summable_sum fun q' _ ↦
      (ZLattice.summable_norm_poisson_left L f (p q - p q')).congr fun z ↦ by
        rw [add_sub_assoc, add_comm]) fun z ↦ ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ ↦
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun q' _ ↦ ?_))
  split_ifs
  · simp
  · exact (Real.norm_eq_abs _).trans_le (abs_re_le_norm _)

/-- Under the sign conditions of a Cohn–Elkies certificate with radius `r`, when every nonzero
difference `z + p q - p q'` has norm at least `r`, the direct defect of a Schwartz function `f`
vanishes exactly when `Re f` vanishes at every nonzero difference. -/
theorem directDefect_eq_zero_iff (L : Submodule ℤ E) [DiscreteTopology L] {p : ι → E}
    {f : 𝓢(E, ℂ)} {r : ℝ} (hf : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0)
    (hsep : ∀ (z : L) (q q' : ι), (z : E) + p q - p q' ≠ 0 → r ≤ ‖(z : E) + p q - p q'‖) :
    directDefect L p f = 0 ↔ ∀ (z : L) (q q' : ι),
      (z : E) + p q - p q' ≠ 0 → (f ((z : E) + p q - p q')).re = 0 := by
  classical
  have hterm (z : L) (q q' : ι) :
      (if (z : E) + p q - p q' = 0 then 0 else (f ((z : E) + p q - p q')).re) ≤ 0 := by
    split_ifs with h
    · exact le_rfl
    · exact hf _ (hsep z q q' h)
  have hnonneg (z : L) : 0 ≤ -∑ q, ∑ q',
      (if (z : E) + p q - p q' = 0 then 0 else (f ((z : E) + p q - p q')).re) :=
    neg_nonneg.mpr (Finset.sum_nonpos fun q _ ↦ Finset.sum_nonpos fun q' _ ↦ hterm z q q')
  rw [directDefect_def, ← tsum_neg, ← (summable_directDefect_terms L p f).neg.hasSum_iff,
    hasSum_zero_iff_of_nonneg hnonneg]
  simp only [funext_iff, Pi.zero_apply, neg_eq_zero]
  refine forall_congr' fun z ↦ ?_
  rw [Finset.sum_eq_zero_iff_of_nonpos fun q _ ↦ Finset.sum_nonpos fun q' _ ↦ hterm z q q']
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun q ↦ ?_
  rw [Finset.sum_eq_zero_iff_of_nonpos fun q' _ ↦ hterm z q q']
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun q' ↦ ?_
  split_ifs with h <;> simp [h]

variable [MeasurableSpace E] [BorelSpace E]

/-- When `Re 𝓕 f ≥ 0` at the nonzero dual frequencies, the Fourier defect of a Schwartz function
`f` vanishes exactly when `Re 𝓕 f(y) * S_p(y)` vanishes at every nonzero dual frequency `y`. -/
theorem fourierDefect_eq_zero_iff (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {p : ι → E} {f : 𝓢(E, ℂ)}
    (hf : ∀ y : ZLattice.dual L, y ≠ 0 → 0 ≤ (𝓕 (f : E → ℂ) (y : E)).re) :
    fourierDefect L p f = 0 ↔ ∀ y : ZLattice.dual L, y ≠ 0 →
      (𝓕 (f : E → ℂ) (y : E)).re * structureFactor p (y : E) = 0 := by
  classical
  have hsum : Summable fun y : ZLattice.dual L ↦
      (𝓕 (f : E → ℂ) (y : E)).re * structureFactor p (y : E) := by
    simpa only [Function.comp_def, reCLM_apply, re_mul_ofReal, SchwartzMap.fourier_coe] using
      (summable_fourier_mul_structureFactor L p f).mapL reCLM
  have hsum' : Summable fun y : ZLattice.dual L ↦
      if y = 0 then 0 else (𝓕 (f : E → ℂ) (y : E)).re * structureFactor p (y : E) :=
    (hsum.update 0 0).congr fun y ↦ by rw [Function.update_apply]
  have hnonneg (y : ZLattice.dual L) :
      0 ≤ if y = 0 then 0 else (𝓕 (f : E → ℂ) (y : E)).re * structureFactor p (y : E) := by
    split_ifs with hy
    · exact le_rfl
    · exact mul_nonneg (hf y hy) (structureFactor_nonneg p _)
  rw [fourierDefect_def, mul_eq_zero, inv_eq_zero,
    or_iff_right (ZLattice.covolume_pos L MeasureTheory.volume).ne',
    ← hsum'.hasSum_iff, hasSum_zero_iff_of_nonneg hnonneg]
  simp only [funext_iff, Pi.zero_apply]
  refine forall_congr' fun y ↦ ?_
  split_ifs with hy <;> simp [hy]

/-- **Equality in the periodic Cohn–Elkies bound.**  For a family of `N` points pairwise
incongruent modulo `L` and a Schwartz function `f` with the sign conditions of a Cohn–Elkies
certificate of radius `r`, where every nonzero difference `z + p q - p q'` has norm at least `r`,
both defects vanish exactly when the periodic bound is attained:
`N * Re f(0) = N² / covol(L) * Re 𝓕 f(0)`. -/
theorem directDefect_eq_zero_and_fourierDefect_eq_zero_iff (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {p : ι → E} (hp : ∀ q q', p q - p q' ∈ L → q = q')
    {f : 𝓢(E, ℂ)} {r : ℝ} (hf : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0)
    (hsep : ∀ (z : L) (q q' : ι), (z : E) + p q - p q' ≠ 0 → r ≤ ‖(z : E) + p q - p q'‖)
    (hfourier : ∀ y : ZLattice.dual L, y ≠ 0 → 0 ≤ (𝓕 (f : E → ℂ) (y : E)).re) :
    directDefect L p f = 0 ∧ fourierDefect L p f = 0 ↔
      (Fintype.card ι : ℝ) * (f 0).re =
        (Fintype.card ι : ℝ) ^ 2 / ZLattice.covolume L * (𝓕 f 0).re := by
  rw [iff_comm, ← sub_eq_zero, defect_identity L hp f, add_eq_zero_iff_of_nonneg
    (fourierDefect_nonneg hfourier) (directDefect_nonneg hf hsep), and_comm]

end SphereCeti.CohnElkies
