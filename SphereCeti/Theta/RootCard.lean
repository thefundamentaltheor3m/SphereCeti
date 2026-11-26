/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Algebra.Module.ZLattice.Shell

/-!
# Root counts of Euclidean lattices

The root count of a Euclidean lattice is the number of lattice vectors of squared norm `2`, using
TauCeti's representation number.
-/

public section

namespace SphereCeti.Theta

/-- Root count, the number of lattice vectors of squared norm `2`. -/
@[expose]
noncomputable def rootCard {d : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) : ℕ :=
  ZLattice.representationNumber Λ 2

end SphereCeti.Theta
