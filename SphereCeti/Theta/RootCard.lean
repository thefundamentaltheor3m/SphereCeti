/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Algebra.Module.ZLattice.Shell

/-!
# Root counts of Euclidean lattices

The root count of a Euclidean lattice is TauCeti's representation number at squared norm `2`.  If
the lattice is discrete, TauCeti's shell finiteness theorem ensures that this representation number
is the actual finite number of lattice vectors of squared norm `2`.
-/

public section

namespace SphereCeti.Theta

/-- Root count, defined as TauCeti's representation number at squared norm `2`.  For a discrete
lattice, this is the cardinality of a finite shell. -/
noncomputable def rootCard {d : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) : ℕ :=
  ZLattice.representationNumber Λ 2

/-- The root count is TauCeti's representation number at squared norm `2`. -/
theorem rootCard_eq_representationNumber {d : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) :
    rootCard Λ = ZLattice.representationNumber Λ 2 :=
  (rfl)

end SphereCeti.Theta
