/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Minimum squared norms of Euclidean lattices

This file records lower bounds and attained minimum values for the squared norms of nonzero
vectors in a Euclidean lattice. Squared norms match the indexing convention of TauCeti's lattice
shells and avoid square roots in the E8 and Leech minimum statements.

## Main definitions

* `SphereCeti.EuclideanLattice.MinNormSqAtLeast`: every nonzero lattice vector has squared norm at
  least a specified value.
* `SphereCeti.EuclideanLattice.HasMinNormSq`: the lower bound is attained by a nonzero vector.

## Main statements

* `SphereCeti.EuclideanLattice.normSq_lower_bound`: extract the lower bound for a given nonzero
  lattice vector.
-/

public section

namespace SphereCeti.EuclideanLattice

/-- Every nonzero vector of `Λ` has squared norm at least `a`. -/
def MinNormSqAtLeast {d : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (a : ℝ) : Prop :=
  ∀ x : Λ, x ≠ 0 → a ≤ ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2

/-- The minimum nonzero squared norm of `Λ` is `a`: it is a lower bound and is attained. -/
def HasMinNormSq {d : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (a : ℝ) : Prop :=
  MinNormSqAtLeast Λ a ∧
    ∃ x : Λ, x ≠ 0 ∧ ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2 = a

/-- Apply a minimum squared-norm lower bound to a nonzero lattice vector. -/
@[grind =>]
theorem normSq_lower_bound {d : ℕ} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))} {a : ℝ}
    (h : MinNormSqAtLeast Λ a) (x : Λ) (hx : x ≠ 0) :
    a ≤ ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2 :=
  h x hx

/-- Check that `grind` applies a minimum squared-norm lower bound. -/
example {d : ℕ} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))} {a : ℝ}
    (h : MinNormSqAtLeast Λ a) (x : Λ) (hx : x ≠ 0) :
    a ≤ ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2 := by
  grind

end SphereCeti.EuclideanLattice
