/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.LinearAlgebra.IntegralLattice.Norm

/-!
# Rootless integral lattices

An integral lattice is rootless when it has no vector of norm two.  For an even lattice the
vectors of norm two are its roots, so an even lattice is rootless exactly when it has no roots.

## Main definitions

* `TauCeti.IntegralLattice.IsRootless`: an integral lattice is rootless when it has no vector of
  norm two.

## Main statements

* `TauCeti.IntegralLattice.isRootless_iff`: a lattice is rootless exactly when its set of vectors
  of norm two is empty.
* `TauCeti.IntegralLattice.isRootless_iff_forall_norm_ne`: a lattice is rootless exactly when no
  vector has norm two.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer
  (1999), Chapter 18.
-/

public section

namespace TauCeti.IntegralLattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- An integral lattice is rootless when it has no vector of norm two. -/
def IsRootless (L : IntegralLattice W) : Prop :=
  L.vectorsOfNorm 2 = ∅

/-- An integral lattice is rootless if and only if its set of vectors of norm two is empty. -/
theorem isRootless_iff {L : IntegralLattice W} : L.IsRootless ↔ L.vectorsOfNorm 2 = ∅ :=
  Iff.rfl

/-- An integral lattice is rootless if and only if none of its vectors has norm two. -/
theorem isRootless_iff_forall_norm_ne {L : IntegralLattice W} :
    L.IsRootless ↔ ∀ x : L, L.norm x ≠ 2 := by
  simp [isRootless_iff, Set.eq_empty_iff_forall_notMem]

end TauCeti.IntegralLattice
