/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Leech.Lattice
public import SphereCeti.Leech.ResidueCoordinates

/-!
# Residue-class coordinates of the Euclidean Leech lattice

A vector of `EuclideanSpace ℝ (Fin 24)` lies in the Euclidean Leech lattice
`SphereCeti.Leech.lattice` exactly when it has the form `a / √8` for an integer vector
`a : Fin 24 → ℤ` satisfying the Conway–Sloane residue-class condition
`SphereCeti.Leech.IsLeechIntegralCoordinate` relative to TauCeti's extended binary Golay code
`TauCeti.BinaryGolay.code`, with no coordinate permutation.

This reduces membership in the Euclidean Leech lattice to integer arithmetic: with the
normalization `x = a / √8` (squared norm `4` for the minimal vectors), a real vector is a lattice
vector exactly when its integer coordinate vector `a` satisfies two congruence conditions: for each
residue `r` modulo `4`, the coordinates `i` with `aᵢ ≡ r (mod 4)` form the support of a Golay
codeword, and `∑ⱼ aⱼ ≡ 4 aᵢ (mod 8)` for every `i`.
It is the Euclidean form of the rational characterization
`SphereCeti.Leech.mem_leechLattice_carrier_iff_isLeechIntegralCoordinate` (vectors `a / 2` of
`TauCeti.leechLattice.carrier`), since `SphereCeti.Leech.embedding` sends `a / 2` to `a / √8`.

## Main statements

* `SphereCeti.Leech.mem_lattice_iff_isLeechIntegralCoordinate`: exact residue-class description
  of the Euclidean Leech lattice.

## Sources

`TauCeti.leechLattice` and `TauCeti.BinaryGolay.code` are TauCeti's (repository
`TauCetiProject/TauCeti`, commit `83769e442d55cda9d85b3927a93b286831c595ff`, files
`TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/Basic.lean` and
`TauCeti/InformationTheory/Coding/Binary/Golay/Basic.lean`).

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11.
-/

public section

namespace SphereCeti.Leech

/-- A vector of `ℝ^24` lies in the Euclidean Leech lattice exactly when it is `a / √8` for an
integer vector `a` satisfying the residue-class condition for TauCeti's binary Golay code, with no
coordinate permutation. -/
theorem mem_lattice_iff_isLeechIntegralCoordinate (x : EuclideanSpace ℝ (Fin 24)) :
    x ∈ lattice ↔ ∃ a : Fin 24 → ℤ, IsLeechIntegralCoordinate TauCeti.BinaryGolay.code a ∧
      x = WithLp.toLp 2 fun i => (a i : ℝ) / Real.sqrt 8 := by
  rw [mem_lattice_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (mem_leechLattice_carrier_iff_isLeechIntegralCoordinate y).mp hy
    exact ⟨a, ha, embedding_div_two a⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, (intCast_div_two_mem_leechLattice_carrier_iff a).mpr ha, embedding_div_two a⟩

end SphereCeti.Leech
