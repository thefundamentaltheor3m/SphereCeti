/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.E8.Lattice
public import SphereCeti.Theta.RootCard

/-!
# The E8 root count

The Euclidean E8 lattice has exactly `240` vectors of squared norm `2`.  The count is transported
through the integral-lattice isometry of `SphereCeti.E8.Lattice` from TauCeti's enumeration of the
roots of its canonical E8 lattice.
-/

public section

namespace SphereCeti.E8

/-- The E8 lattice has exactly `240` roots. -/
theorem rootCard : Theta.rootCard lattice = 240 := by
  rw [Theta.rootCard_eq_representationNumber, representationNumber_lattice_two]

end SphereCeti.E8
