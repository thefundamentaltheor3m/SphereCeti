/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Algebra.Module.ZLattice.Integral

/-!
# Integral and even spans

The `ℤ`-span of a set `S` of vectors in a real inner product space is an integral lattice exactly
when the inner product of any two points of `S` is an integer, and an even lattice exactly when,
moreover, every point of `S` has even squared norm.

If `S` contains `0` and every squared distance `‖x - y‖²` between two of its points is an even
integer, polarization, `2⟪x, y⟫ = ‖x‖² + ‖y‖² - ‖x - y‖²`, gives both conditions, so the `ℤ`-span
of `S` is an even lattice.

## Main statements

* `ZLattice.isIntegral_span_iff`: the `ℤ`-span of `S` is integral exactly when the points of `S`
  have integral inner products.
* `ZLattice.isEven_span_iff`: the `ℤ`-span of `S` is even exactly when, moreover, the points of
  `S` have even squared norms.
* `ZLattice.isEven_span_of_even_sq_dist`: a set containing `0` with even integral squared
  distances spans an even lattice.

## References

* H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714, Lemma 8.2.
-/

public section

open Submodule
open scoped InnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {S : Set E}

/-- The `ℤ`-span of a set is an integral lattice exactly when the inner product of any two of its
points is an integer. -/
theorem isIntegral_span_iff :
    IsIntegral (span ℤ S) ↔ ∀ x ∈ S, ∀ y ∈ S, ∃ m : ℤ, ⟪x, y⟫_ℝ = m := by
  -- The integers are the `ℤ`-span of `1` in `ℝ`.
  have hint (r : ℝ) : r ∈ span ℤ {(1 : ℝ)} ↔ ∃ m : ℤ, r = m := by
    simp only [mem_span_singleton, zsmul_eq_mul, mul_one, eq_comm]
  rw [isIntegral_iff]
  refine ⟨fun h x hx y hy ↦ h x (subset_span hx) y (subset_span hy), fun h x hx y hy ↦ ?_⟩
  exact (hint _).mp (LinearMap.BilinMap.apply_apply_mem_of_mem_span (span ℤ {(1 : ℝ)}) S S
    ((innerₗ E).restrictScalars₁₂ ℤ ℤ) (fun x hx y hy ↦ (hint _).mpr (h x hx y hy)) x y hx hy)

/-- The `ℤ`-span of a set is an even lattice exactly when every point of the set has even
integral squared norm and the inner product of any two of its points is an integer. -/
theorem isEven_span_iff :
    IsEven (span ℤ S) ↔
      (∀ x ∈ S, ∃ m : ℤ, ‖x‖ ^ 2 = 2 * m) ∧ ∀ x ∈ S, ∀ y ∈ S, ∃ m : ℤ, ⟪x, y⟫_ℝ = m := by
  refine ⟨fun h ↦ ⟨fun x hx ↦ isEven_iff.mp h x (subset_span hx),
    isIntegral_span_iff.mp h.isIntegral⟩, fun ⟨hnorm, hinner⟩ ↦ ?_⟩
  have hint := isIntegral_iff.mp (isIntegral_span_iff.mpr hinner)
  refine isEven_iff.mpr fun x hx ↦ ?_
  induction hx using span_induction with
  | mem x hx => exact hnorm x hx
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy hx' hy' =>
    obtain ⟨m, hm⟩ := hx'
    obtain ⟨n, hn⟩ := hy'
    obtain ⟨k, hk⟩ := hint x hx y hy
    exact ⟨m + n + k, by rw [norm_add_sq_real, hm, hn, hk]; push_cast; ring⟩
  | smul c x _ hx' =>
    obtain ⟨m, hm⟩ := hx'
    refine ⟨c ^ 2 * m, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, mul_pow, hm, Real.norm_eq_abs, sq_abs]
    push_cast
    ring

/-- A set containing `0` in which every squared distance between two points is an even integer
spans an even lattice over `ℤ`. -/
theorem isEven_span_of_even_sq_dist (hzero : 0 ∈ S)
    (heven : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, ‖x - y‖ ^ 2 = 2 * n) :
    IsEven (span ℤ S) := by
  refine isEven_span_iff.mpr ⟨fun x hx ↦ by simpa using heven x hx 0 hzero, fun x hx y hy ↦ ?_⟩
  -- Polarization: `2⟪x, y⟫ = ‖x‖² + ‖y‖² - ‖x - y‖²`.
  obtain ⟨a, ha⟩ := heven x hx 0 hzero
  obtain ⟨b, hb⟩ := heven y hy 0 hzero
  obtain ⟨c, hc⟩ := heven x hx y hy
  rw [sub_zero] at ha hb
  rw [norm_sub_sq_real] at hc
  exact ⟨a + b - c, by push_cast; linarith⟩

end ZLattice
