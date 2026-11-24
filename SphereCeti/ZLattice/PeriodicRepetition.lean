/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.MeasureTheory.Measure.Haar.EuclideanSpace
public import TauCeti.Algebra.Module.ZLattice.Determinant
public import TauCeti.Algebra.Module.ZLattice.Integral
public import TauCeti.Algebra.Module.ZLattice.Scaling

/-!
# The period lattice of a periodic repetition

For `c : ℝ`, the lattice `c ℤ^ι` in `EuclideanSpace ℝ ι` is the scaled cubic lattice
`c • span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)`: its vectors are those whose
coordinates are `c z` for some `z : ι → ℤ`, and its covolume is `|c|ⁿ` in dimension `n`.  The
periodic repetition `EuclideanSpace.periodicRepetition S c` of a set `S` along `c ℤ^ι` is the union
of the cosets `s + c ℤ^ι` for `s ∈ S`.  When `S` lies in a translated coordinate box of radius `R`
and `2R < |c|`, distinct points of `S` are incongruent modulo `c ℤ^ι`, so these cosets are
pairwise distinct.  These are the period lattice and the orbit representatives of the periodic
packing obtained by repeating the centers in a box.

## Main statements

* `EuclideanSpace.mem_smul_span_basisFun_iff`: a vector lies in `c ℤ^ι` if and only if its
  coordinates are `c z` for some `z : ι → ℤ`.
* `EuclideanSpace.covolume_smul_span_basisFun`: `c ℤ^ι` has covolume `|c|ⁿ`.
* `EuclideanSpace.periodicRepetition_eq_iUnion_vadd`: the periodic repetition of `S` along `c ℤ^ι`
  is the union of the cosets `s + c ℤ^ι` for `s ∈ S`.
* `EuclideanSpace.add_mem_periodicRepetition`: the periodic repetition is invariant under
  translation by `c ℤ^ι`.
* `EuclideanSpace.eq_of_sub_mem_smul_span_basisFun`: two points of a translated box of radius `R`
  that are congruent modulo `c ℤ^ι` with `2R < |c|` are equal.
-/

public section

open Module Submodule
open scoped Pointwise

namespace EuclideanSpace

variable {ι : Type*} [Fintype ι]

/-- A vector lies in the lattice `c ℤ^ι` if and only if its coordinates are `c z` for some
`z : ι → ℤ`. -/
theorem mem_smul_span_basisFun_iff {c : ℝ} {v : EuclideanSpace ℝ ι} :
    v ∈ c • span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis) ↔
      ∃ z : ι → ℤ, v.ofLp = fun i ↦ c * z i := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Module.Basis.mem_span_iff_repr_mem] at hw
    choose z hz using hw
    refine ⟨z, funext fun i ↦ ?_⟩
    have := hz i
    simp only [OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      algebraMap_int_eq, eq_intCast] at this
    simp [this]
  · rintro ⟨z, hz⟩
    refine ⟨WithLp.toLp 2 fun i ↦ (z i : ℝ), ?_, ?_⟩
    · rw [Module.Basis.mem_span_iff_repr_mem]
      intro i
      exact ⟨z i, by simp⟩
    · apply WithLp.ofLp_injective 2
      rw [hz]
      ext i
      simp

/-- The lattice `c ℤ^ι` has covolume `|c|ⁿ`, where `n` is the cardinality of `ι`. -/
theorem covolume_smul_span_basisFun (c : ℝ) :
    ZLattice.covolume (c • span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)) =
      |c| ^ Fintype.card ι := by
  have hU := ZLattice.isUnimodular_span_orthonormalBasis (EuclideanSpace.basisFun ι ℝ)
  rw [← (EuclideanSpace.basisFun ι ℝ).coe_toBasis] at hU
  refine (ZLattice.covolume_smul (span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis))
    (c := c)).trans ?_
  rw [hU.covolume_eq_one, mul_one, finrank_euclideanSpace]

/-- The periodic repetition of `S` along `c ℤ^ι` is the union of the cosets `s + c ℤ^ι` for
`s ∈ S`. -/
theorem periodicRepetition_eq_iUnion_vadd (S : Set (EuclideanSpace ℝ ι)) (c : ℝ) :
    periodicRepetition S c = ⋃ s ∈ S, s +ᵥ
      ((c • span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis) :
        Submodule ℤ (EuclideanSpace ℝ ι)) : Set (EuclideanSpace ℝ ι)) := by
  ext x
  simp only [mem_periodicRepetition, Set.mem_iUnion, Set.mem_vadd_set, SetLike.mem_coe,
    mem_smul_span_basisFun_iff, vadd_eq_add, exists_prop]
  constructor
  · rintro ⟨z, s, hs, hx⟩
    refine ⟨s, hs, WithLp.toLp 2 fun i ↦ c * z i, ⟨z, rfl⟩, ?_⟩
    apply WithLp.ofLp_injective 2
    rw [WithLp.ofLp_add, hx]
  · rintro ⟨s, hs, v, ⟨z, hv⟩, rfl⟩
    exact ⟨z, s, hs, by rw [WithLp.ofLp_add, hv]⟩

/-- The periodic repetition of `S` along `c ℤ^ι` is invariant under translation by `c ℤ^ι`. -/
theorem add_mem_periodicRepetition {S : Set (EuclideanSpace ℝ ι)} {c : ℝ}
    {v x : EuclideanSpace ℝ ι}
    (hv : v ∈ c • span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis))
    (hx : x ∈ periodicRepetition S c) : v + x ∈ periodicRepetition S c := by
  obtain ⟨w, hw⟩ := mem_smul_span_basisFun_iff.mp hv
  obtain ⟨z, s, hs, hx⟩ := mem_periodicRepetition.mp hx
  refine mem_periodicRepetition.mpr ⟨w + z, s, hs, ?_⟩
  rw [WithLp.ofLp_add, hw, hx]
  ext i
  simp only [Pi.add_apply, Int.cast_add]
  ring

/-- Two points of a translated box of radius `R` that are congruent modulo `c ℤ^ι` with
`2R < |c|` are equal. -/
theorem eq_of_sub_mem_smul_span_basisFun {a s s' : EuclideanSpace ℝ ι} {R c : ℝ}
    (hs : s ∈ a +ᵥ centeredBox ι R) (hs' : s' ∈ a +ᵥ centeredBox ι R) (hc : 2 * R < |c|)
    (h : s - s' ∈ c • span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)) : s = s' := by
  obtain ⟨z, hz⟩ := mem_smul_span_basisFun_iff.mp h
  by_contra hne
  -- The point `s` is both `s + c • 0` and `s' + c z`, with `z ≠ 0`.
  have hz0 : (0 : ι → ℤ) ≠ z := by
    rintro rfl
    apply hne
    apply WithLp.ofLp_injective 2
    rw [← sub_eq_zero, ← WithLp.ofLp_sub, hz]
    ext i
    simp
  have hx : s.ofLp = s.ofLp + fun i ↦ c * ((0 : ι → ℤ) i : ℝ) := by
    ext i
    simp
  have hx' : s.ofLp = s'.ofLp + fun i ↦ c * z i := by
    rw [← hz, WithLp.ofLp_sub, add_sub_cancel]
  have := abs_sub_two_mul_le_dist hs hs' hz0 hx hx'
  rw [dist_self] at this
  linarith

end EuclideanSpace
