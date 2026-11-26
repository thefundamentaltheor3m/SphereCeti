/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import SphereCeti.Topology.MetricSpace.MetricSeparated

/-!
# Lattice-invariant separated sets meet finitely many cosets

Let `L` be a full lattice in a finite-dimensional real normed space `E`, and let `X ⊆ E` be a set
that is invariant under translation by `L` and whose distinct points are at distance at least
`r > 0`.  Then `X` meets only finitely many cosets of `L`: every point of `X` can be translated by
a vector of `L` into a bounded fundamental domain of `L`, and a bounded set whose distinct points
are at distance at least `r` is finite.

Invariance cannot be dropped: in `ℝ`, for irrational `θ ∈ (0, 1)`, the points `n + {nθ}` with
`n ∈ ℕ` are at distance at least `θ` from each other but lie in infinitely many cosets of `ℤ`.

In the theory of periodic sphere packings, `X` is the set of centers and `L` the period lattice,
so the packing has finitely many center orbits.

## Main statements

* `ZLattice.finite_image_mk_of_pairwise_le_dist`: a lattice-invariant set whose distinct points are
  at distance at least `r > 0` meets finitely many cosets of the lattice.
-/

public section

open Module

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A set invariant under translation by a full lattice `L`, whose distinct points are at distance
at least `r > 0`, meets only finitely many cosets of `L`. -/
theorem finite_image_mk_of_pairwise_le_dist (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] {X : Set E} (hX : ∀ x ∈ X, ∀ l ∈ L, x + l ∈ X) {r : ℝ} (hr : 0 < r)
    (hsep : X.Pairwise fun x y ↦ r ≤ dist x y) :
    ((QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) '' X).Finite := by
  -- A basis of `L` gives a bounded fundamental domain `F`.
  let b := (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L := Basis.ofZLatticeBasis_span ℝ L _
  set F := ZSpan.fundamentalDomain b
  -- Every point of `X` is congruent modulo `L` to a point of `X ∩ F`.
  have hsub : (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) '' X ⊆
      (QuotientAddGroup.mk : E → E ⧸ L.toAddSubgroup) '' (X ∩ F) := by
    rintro _ ⟨x, hx, rfl⟩
    have hfloor : (ZSpan.floor b x : E) ∈ L := hspan.le (ZSpan.floor b x).2
    refine ⟨ZSpan.fract b x, ⟨?_, ZSpan.fract_mem_fundamentalDomain b x⟩, ?_⟩
    · rw [ZSpan.fract_apply, sub_eq_add_neg]
      exact hX x hx _ (L.neg_mem hfloor)
    · rw [QuotientAddGroup.eq_iff_sub_mem, ZSpan.fract_apply, sub_sub_cancel_left]
      exact L.toAddSubgroup.neg_mem hfloor
  refine (Set.Finite.image _ ?_).subset hsub
  exact Metric.finite_of_isBounded_of_pairwise_le_dist
    ((ZSpan.fundamentalDomain_isBounded b).subset Set.inter_subset_right) hr
    (hsep.mono Set.inter_subset_left)

end ZLattice
