/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Leech.Lattice
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Minimum

/-!
# The congruence model of the Euclidean Leech lattice

A vector `x ∈ ℝ^24` lies in the Euclidean Leech lattice `SphereCeti.Leech.lattice` exactly when
`x = (2 * b + m • 1) / √8` for some shift `m ∈ {0, 1}` and some integer vector `b` whose reduction
modulo `2` is a word of the extended binary Golay code `TauCeti.BinaryGolay.code`, subject to the
coordinate-sum congruence `∑ i, (2 * b i + m) ≡ 4 * m [ZMOD 8]`.

This is TauCeti's congruence model of its rational Leech lattice, in which the same data describe
the points `(2 * b + m • 1) / 2` of `ℚ^24`, transported along the isometric embedding
`SphereCeti.Leech.embedding` (`x ↦ x / √2`), which sends `a / 2` to `a / √8`.

## Main results

* `SphereCeti.Leech.mem_lattice_iff_exists`: the congruence model of the Euclidean Leech lattice.

## Source

The rational congruence model is TauCeti's `TauCeti.mem_leechLattice_carrier_iff_exists`
(repository `TauCetiProject/TauCeti`, commit `83769e442d55cda9d85b3927a93b286831c595ff`, file
`TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/Minimum.lean`).  See also J. H. Conway and
N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11.
-/

public section

namespace SphereCeti.Leech

/-- The congruence model of the Euclidean Leech lattice: its points are the vectors
`(2 * b + m • 1) / √8` with `m ∈ {0, 1}`, `b mod 2` in the binary Golay code, and coordinate sum
congruent to `4 * m` modulo `8`. -/
theorem mem_lattice_iff_exists (x : EuclideanSpace ℝ (Fin 24)) :
    x ∈ lattice ↔ ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ ∃ b : Fin 24 → ℤ,
      (fun i => (b i : ZMod 2)) ∈ TauCeti.BinaryGolay.code ∧
      ∑ i, (2 * b i + m) ≡ 4 * m [ZMOD 8] ∧
      x = WithLp.toLp 2 fun i => ((2 * b i + m : ℤ) : ℝ) / Real.sqrt 8 := by
  rw [mem_lattice_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨m, hm, b, hb, hsum, rfl⟩ := (TauCeti.mem_leechLattice_carrier_iff_exists y).mp hy
    exact ⟨m, hm, b, hb, hsum, embedding_div_two fun i => 2 * b i + m⟩
  · rintro ⟨m, hm, b, hb, hsum, rfl⟩
    exact ⟨_, (TauCeti.mem_leechLattice_carrier_iff_exists _).mpr ⟨m, hm, b, hb, hsum, rfl⟩,
      embedding_div_two fun i => 2 * b i + m⟩

end SphereCeti.Leech
