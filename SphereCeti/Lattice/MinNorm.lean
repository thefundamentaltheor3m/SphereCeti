/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Lattice.IntegralPresentation
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minimum

/-!
# Minimum squared norms of lattices

A lattice `Λ` has minimum squared norm at least `a` when every nonzero vector of `Λ` has squared
norm at least `a`, and minimum squared norm `a` when moreover some nonzero vector attains `a`.  For
a sphere packing with centers at the points of a nonzero lattice `Λ`, the minimum squared norm is
the square of the least distance between two distinct centers.

For a presented lattice in `ℝ^d`, TauCeti's minimum `TauCeti.IntegralLattice.minimum` of the
lattice in Gram coordinates bounds the squared norms of the nonzero vectors from below.  When the
lattice has a nonzero vector, that is when `d ≥ 1`, it is the minimum squared norm.  The
coordinate identification `IntegralPresentation.carrierEquiv` carries squared norms to the rational
norm.

In an even lattice every squared norm is an even integer, so every nonzero vector has squared norm
at least `2`, and at least `4` if no vector has squared norm `2`.

## Main definitions

* `SphereCeti.EuclideanLattice.MinNormSqAtLeast Λ a`: every nonzero vector of `Λ` has squared norm
  at least `a`.
* `SphereCeti.EuclideanLattice.HasMinNormSq Λ a`: the least squared norm of a nonzero vector of
  `Λ` is `a`.

## Main statements

* `SphereCeti.EuclideanLattice.minNormSqAtLeast_iff`,
  `SphereCeti.EuclideanLattice.hasMinNormSq_iff`: the defining characterizations of the two
  predicates.
* `SphereCeti.EuclideanLattice.IntegralPresentation.hasMinNormSq_minimum`: a nontrivial presented
  lattice has minimum squared norm the minimum of its lattice in Gram coordinates.
* `ZLattice.IsEven.minNormSqAtLeast_two`, `ZLattice.IsEven.minNormSqAtLeast_four`: an even lattice
  has minimum squared norm at least `2`, and at least `4` without vectors of squared norm `2`.
-/

public section

namespace SphereCeti.EuclideanLattice

variable {E : Type*} [SeminormedAddCommGroup E]

/-- Every nonzero vector of `Λ` has squared norm at least `a`. -/
def MinNormSqAtLeast (Λ : Submodule ℤ E) (a : ℝ) : Prop :=
  ∀ x : Λ, x ≠ 0 → a ≤ ‖(x : E)‖ ^ 2

/-- The least squared norm of a nonzero vector of `Λ` is `a`: it is a lower bound for the squared
norms of nonzero vectors, and some nonzero vector attains it. -/
def HasMinNormSq (Λ : Submodule ℤ E) (a : ℝ) : Prop :=
  MinNormSqAtLeast Λ a ∧ ∃ x : Λ, x ≠ 0 ∧ ‖(x : E)‖ ^ 2 = a

/-- `Λ` has minimum squared norm at least `a` if and only if every nonzero vector of `Λ` has
squared norm at least `a`. -/
theorem minNormSqAtLeast_iff {Λ : Submodule ℤ E} {a : ℝ} :
    MinNormSqAtLeast Λ a ↔ ∀ x : Λ, x ≠ 0 → a ≤ ‖(x : E)‖ ^ 2 :=
  Iff.rfl

/-- `Λ` has minimum squared norm `a` if and only if `a` is a lower bound for the squared norms of
its nonzero vectors that some nonzero vector attains. -/
theorem hasMinNormSq_iff {Λ : Submodule ℤ E} {a : ℝ} :
    HasMinNormSq Λ a ↔ MinNormSqAtLeast Λ a ∧ ∃ x : Λ, x ≠ 0 ∧ ‖(x : E)‖ ^ 2 = a :=
  Iff.rfl

/-- A lower bound on the squared norms of the nonzero vectors of `Λ` applies to each of them. -/
@[grind! =>]
theorem normSq_lower_bound {Λ : Submodule ℤ E} {a : ℝ} (h : MinNormSqAtLeast Λ a) (x : Λ)
    (hx : x ≠ 0) : a ≤ ‖(x : E)‖ ^ 2 :=
  minNormSqAtLeast_iff.mp h x hx

/-- Check that `grind` applies a minimum-norm bound to a nonzero lattice vector. -/
example {Λ : Submodule ℤ E} (h : MinNormSqAtLeast Λ 4) (x : Λ) (hx : x ≠ 0)
    (hsmall : ‖(x : E)‖ ^ 2 < 4) : False := by
  grind

namespace IntegralPresentation

variable {d : ℕ} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))} [DiscreteTopology Λ]
  [IsZLattice ℝ Λ]

/-- Every nonzero vector of a presented lattice has squared norm at least the minimum of the
lattice in Gram coordinates. -/
theorem minNormSqAtLeast_minimum (P : IntegralPresentation Λ) :
    MinNormSqAtLeast Λ P.toIntegralLattice.minimum := by
  refine minNormSqAtLeast_iff.mpr fun x hx ↦ ?_
  have hle := P.isPosDef.isPosSemidef.minimum_le_integralNorm
    ((LinearEquiv.map_ne_zero_iff P.carrierEquiv).mpr hx)
  rw [← P.norm_carrierEquiv, ← TauCeti.IntegralLattice.integralNorm_cast]
  exact_mod_cast hle

/-- A nontrivial presented lattice has minimum squared norm the minimum of its lattice in Gram
coordinates. -/
theorem hasMinNormSq_minimum (P : IntegralPresentation Λ) [Nontrivial Λ] :
    HasMinNormSq Λ P.toIntegralLattice.minimum := by
  have : Nontrivial P.toIntegralLattice.carrier := P.carrierEquiv.symm.toEquiv.nontrivial
  obtain ⟨y, hy, hmin⟩ := P.isPosDef.isPosSemidef.exists_ne_zero_integralNorm_eq_minimum
  refine hasMinNormSq_iff.mpr ⟨P.minNormSqAtLeast_minimum, P.carrierEquiv.symm y,
    (LinearEquiv.map_ne_zero_iff _).mpr hy, ?_⟩
  rw [← P.norm_carrierEquiv, LinearEquiv.apply_symm_apply,
    ← TauCeti.IntegralLattice.integralNorm_cast, hmin]
  norm_cast

end IntegralPresentation

end SphereCeti.EuclideanLattice

namespace ZLattice.IsEven

open SphereCeti.EuclideanLattice

variable {E : Type*} [NormedAddCommGroup E] {L : Submodule ℤ E}

/-- Every nonzero vector of an even lattice has squared norm at least `2`. -/
theorem minNormSqAtLeast_two (h : ZLattice.IsEven L) : MinNormSqAtLeast L 2 := by
  intro x hx
  obtain ⟨m, hm⟩ := ZLattice.isEven_iff.mp h x x.2
  -- The squared norm `2m` is positive, so `m ≥ 1`.
  have hpos : 0 < ‖(x : E)‖ ^ 2 := by
    have : (x : E) ≠ 0 := fun h0 ↦ hx (Subtype.ext h0)
    positivity
  rw [hm] at hpos ⊢
  have : (1 : ℤ) ≤ m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  have : (1 : ℝ) ≤ m := by exact_mod_cast this
  linarith

/-- Every nonzero vector of an even lattice without vectors of squared norm `2` has squared norm at
least `4`. -/
theorem minNormSqAtLeast_four (h : ZLattice.IsEven L) (hroot : ∀ x ∈ L, ‖x‖ ^ 2 ≠ 2) :
    MinNormSqAtLeast L 4 := by
  intro x hx
  obtain ⟨m, hm⟩ := ZLattice.isEven_iff.mp h x x.2
  -- The squared norm `2m` is at least `2` and not `2`, so `m ≥ 2`.
  have h2 := h.minNormSqAtLeast_two x hx
  have hne := hroot x x.2
  rw [hm] at h2 hne ⊢
  have h1 : (1 : ℝ) ≤ m := by linarith
  have hm1 : m ≠ 1 := fun h1' ↦ hne (by rw [h1']; norm_num)
  have : (2 : ℤ) ≤ m := by
    have : (1 : ℤ) ≤ m := by exact_mod_cast h1
    omega
  have : (2 : ℝ) ≤ m := by exact_mod_cast this
  linarith

end ZLattice.IsEven
