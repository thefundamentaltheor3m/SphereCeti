/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.CohnElkies.StructureFactor

/-!
# Structure factors on the quotient by a lattice

Let `L` be a subgroup of a real inner product space `E`, such as the period lattice of a periodic
sphere packing, and let `y` be a frequency in the dual lattice `L^∨`.  The phase
`exp (2πi ⟪y, s⟫)` depends only on the class of `s` in `E ⧸ L`, so it descends to a function
`orbitPhase L y` on the quotient.  For a finite set `Q` of classes, such as the orbits of the
centers of a periodic packing under its period lattice, the orbit structure factor at `y` is the
squared norm `‖∑ c ∈ Q, orbitPhase L y c‖²`.  It is defined without choosing representatives.

If a finite family of points `p : ι → E` contains exactly one representative of each class in
`Q`, then its structure factor `S_p(y)` at the dual frequency `y` equals the orbit structure factor
of `Q`.  The structure factor at a dual frequency therefore does not depend on which
representatives of the classes are chosen, and the dual side of Poisson summation over finitely
many lattice translates,
`SphereCeti.CohnElkies.tsum_sum_sum_eq_tsum_dual_fourier_mul_structureFactor`, depends only on the
classes of the points.

## Main definitions

* `SphereCeti.CohnElkies.orbitPhase L y`: the phase `exp (2πi ⟪y, ·⟫)` on `E ⧸ L` at a dual
  frequency `y`.
* `SphereCeti.CohnElkies.orbitStructureFactor L y Q`: the squared norm of the sum of the phases
  of the classes in `Q`.

## Main statements

* `SphereCeti.CohnElkies.orbitPhase_mk`: the phase of the class of `s` is `exp (2πi ⟪y, s⟫)`.
* `SphereCeti.CohnElkies.structureFactor_eq_orbitStructureFactor`: the structure factor of a
  family with one representative in each class of `Q` is the orbit structure factor of `Q`.

## References

* H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714, proof of Theorem 3.2.
-/

public section

open Complex
open scoped Real RealInnerProductSpace

namespace SphereCeti.CohnElkies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The phase `exp (2πi ⟪y, s⟫)` at a frequency `y` of the dual lattice of `L`, as a function of
the class of `s` in `E ⧸ L`. -/
noncomputable def orbitPhase (L : Submodule ℤ E) (y : ZLattice.dual L) :
    E ⧸ L.toAddSubgroup → ℂ :=
  fun c ↦ Quotient.liftOn' c (fun s ↦ cexp (2 * π * I * ⟪(y : E), s⟫)) fun a b h ↦ by
    -- Two representatives of one class differ by a vector of `L`.
    rw [QuotientAddGroup.leftRel_apply] at h
    refine (ZLattice.phase_eq_of_sub_mem_lattice y.2 (s := b) (t := a) ?_).symm
    simpa [sub_eq_neg_add] using h

/-- The phase of the class of `s` in `E ⧸ L` at a dual frequency `y` is `exp (2πi ⟪y, s⟫)`. -/
@[simp]
theorem orbitPhase_mk (L : Submodule ℤ E) (y : ZLattice.dual L) (s : E) :
    orbitPhase L y (s : E ⧸ L.toAddSubgroup) = cexp (2 * π * I * ⟪(y : E), s⟫) :=
  (rfl)

/-- Check that `simp` evaluates the phase of a class at its representative. -/
example (L : Submodule ℤ E) (y : ZLattice.dual L) (s : E) (c : ℂ) :
    c * orbitPhase L y (QuotientAddGroup.mk s) = c * cexp (2 * π * I * ⟪(y : E), s⟫) := by
  simp

/-- The orbit structure factor of a finite set `Q` of classes in `E ⧸ L` at a dual frequency `y`:
the squared norm of the sum of the phases of the classes in `Q`. -/
noncomputable def orbitStructureFactor (L : Submodule ℤ E) (y : ZLattice.dual L)
    (Q : Finset (E ⧸ L.toAddSubgroup)) : ℝ :=
  ‖∑ c ∈ Q, orbitPhase L y c‖ ^ 2

/-- The orbit structure factor is the squared norm of the sum of the phases of the classes. -/
theorem orbitStructureFactor_def (L : Submodule ℤ E) (y : ZLattice.dual L)
    (Q : Finset (E ⧸ L.toAddSubgroup)) :
    orbitStructureFactor L y Q = ‖∑ c ∈ Q, orbitPhase L y c‖ ^ 2 :=
  (rfl)

/-- The orbit structure factor is nonnegative. -/
theorem orbitStructureFactor_nonneg (L : Submodule ℤ E) (y : ZLattice.dual L)
    (Q : Finset (E ⧸ L.toAddSubgroup)) : 0 ≤ orbitStructureFactor L y Q :=
  sq_nonneg _

/-- At a dual frequency `y`, the structure amplitude of a family `p` is the sum of the phases of
the classes of its points. -/
theorem structureAmplitude_eq_sum_orbitPhase {ι : Type*} [Fintype ι] (L : Submodule ℤ E)
    (y : ZLattice.dual L) (p : ι → E) :
    structureAmplitude p (y : E) = ∑ q, orbitPhase L y (p q : E ⧸ L.toAddSubgroup) := by
  simp [structureAmplitude_def]

/-- **The structure factor depends only on the classes of the points.**  Let `p : ι → E` be a
finite family of points, pairwise incongruent modulo `L`, whose classes in `E ⧸ L` are exactly
the elements of the finite set `Q`.  At every dual frequency `y`, the structure factor of `p` is
the orbit structure factor of `Q`. -/
theorem structureFactor_eq_orbitStructureFactor {ι : Type*} [Fintype ι] (L : Submodule ℤ E)
    {p : ι → E} (hp : ∀ q q', p q - p q' ∈ L → q = q') {Q : Finset (E ⧸ L.toAddSubgroup)}
    (hQ : ∀ c, c ∈ Q ↔ ∃ q, (p q : E ⧸ L.toAddSubgroup) = c) (y : ZLattice.dual L) :
    structureFactor p (y : E) = orbitStructureFactor L y Q := by
  rw [structureFactor_def, orbitStructureFactor_def, structureAmplitude_eq_sum_orbitPhase L y p]
  congr 2
  -- Incongruent points have distinct classes, so `q ↦ [p q]` is a bijection from `ι` onto `Q`.
  refine Finset.sum_nbij (fun q ↦ (p q : E ⧸ L.toAddSubgroup)) (fun q _ ↦ (hQ _).mpr ⟨q, rfl⟩)
    (fun q _ q' _ h ↦ hp q q' ?_) (fun c hc ↦ ?_) fun _ _ ↦ rfl
  · rwa [QuotientAddGroup.eq_iff_sub_mem] at h
  · obtain ⟨q, rfl⟩ := (hQ c).mp hc
    exact ⟨q, Finset.mem_coe.mpr (Finset.mem_univ q), rfl⟩

end SphereCeti.CohnElkies
