/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Leech.Lattice
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.MinimalVectors

/-!
# The first shells of the Euclidean Leech lattice

The Euclidean Leech lattice `SphereCeti.Leech.lattice ⊆ ℝ^24` has no vectors of squared norm `2`
(it is rootless) and exactly `196560` vectors of squared norm `4`.  Both counts are transported
from TauCeti's rational Leech lattice along `SphereCeti.Leech.representationNumber_lattice`, which
identifies the real shells of `lattice` with the shells of `TauCeti.leechLattice`.

## Main results

* `SphereCeti.Leech.representationNumber_lattice_two`: the lattice has no vector of squared
  norm `2`.
* `SphereCeti.Leech.representationNumber_lattice_four`: the lattice has `196560` vectors of
  squared norm `4`.

## Source

The shell counts are TauCeti's (repository `TauCetiProject/TauCeti`, commit
`83769e442d55cda9d85b3927a93b286831c595ff`): `TauCeti.vectorsOfNorm_two_leechLattice` in
`TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/Minimum.lean`, which follows from
`TauCeti.minimum_leechLattice`, and `TauCeti.ncard_vectorsOfNorm_four_leechLattice` in
`TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/MinimalVectors.lean`, proved by enumerating
the minimal vectors.  See also Conway and Sloane, *Sphere Packings, Lattices and Groups*,
Chapter 4, §11.
-/

public section

namespace SphereCeti.Leech

/-- **The Euclidean Leech lattice is rootless**: it has no vector of squared norm `2`.  This is the
roadmap's `rootCard lattice = 0`, since the roadmap's root count is the representation number of
`2`. -/
theorem representationNumber_lattice_two : ZLattice.representationNumber lattice 2 = 0 := by
  simpa [TauCeti.IntegralLattice.representationNumber_def] using representationNumber_lattice 2

/-- **The Euclidean Leech lattice has `196560` vectors of squared norm `4`**, the kissing number
of the Leech lattice.  This is the roadmap's `shellCard_four`. -/
theorem representationNumber_lattice_four : ZLattice.representationNumber lattice 4 = 196560 := by
  simpa [TauCeti.IntegralLattice.representationNumber_def,
    TauCeti.ncard_vectorsOfNorm_four_leechLattice] using representationNumber_lattice 4

end SphereCeti.Leech
