/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Lattice.Generated

/-!
# Integrality in the rigidity argument

Two facts about integral lattices used in the uniqueness argument of Cohn and Elkies.

* If every squared distance between two points of a set `X` is an even integer, then after
  translating any point `x₀` of `X` to the origin, every inner product `⟪x - x₀, y - x₀⟫` of two
  translated points is an integer.  This is polarization, applied to the translated set, which
  contains `0`.
* An integral full lattice has covolume at least one: its squared covolume is its determinant,
  a positive integer.

## Main statements

* `SphereCeti.Rigidity.integral_inner_of_even_distanceSpectrum`: integral inner products after
  translation.
* `SphereCeti.Rigidity.one_le_covolume_of_isIntegral`: an integral full lattice has covolume at
  least one.

## References

* H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714, Section 8.
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace SphereCeti.Rigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- If all squared distances between points of `X` are even integers, then for any `x₀ ∈ X` the
inner products `⟪x - x₀, y - x₀⟫` of points of `X` translated by `-x₀` are integers. -/
theorem integral_inner_of_even_distanceSpectrum (X : Set E) (x₀ : E) (hx₀ : x₀ ∈ X)
    (heven : ∀ x ∈ X, ∀ y ∈ X, ∃ n : ℤ, ‖x - y‖ ^ 2 = 2 * n) :
    ∀ x ∈ X, ∀ y ∈ X, ∃ n : ℤ, ⟪x - x₀, y - x₀⟫_ℝ = n := by
  -- The translated set contains `0` and has the same pairwise distances.
  have hS : ZLattice.IsEven (Submodule.span ℤ ((fun x ↦ x - x₀) '' X)) := by
    refine EuclideanLattice.isEven_span_of_even_sq_dist ⟨x₀, hx₀, sub_self x₀⟩ ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa using heven x hx y hy
  intro x hx y hy
  exact EuclideanLattice.isIntegral_span_iff.mp hS.isIntegral _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

/-- An integral full lattice has covolume at least one: its squared covolume is its determinant,
which is at least one. -/
theorem one_le_covolume_of_isIntegral [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Λ : Submodule ℤ E} [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h : ZLattice.IsIntegral Λ) :
    1 ≤ ZLattice.covolume Λ := by
  have hdet := h.one_le_det
  rw [ZLattice.det_def] at hdet
  nlinarith [ZLattice.covolume_pos Λ volume]

end SphereCeti.Rigidity
