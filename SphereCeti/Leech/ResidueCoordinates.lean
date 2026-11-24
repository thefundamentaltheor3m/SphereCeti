/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Minimum

/-!
# Residue-class coordinate characterization of the Leech lattice

Relative to a binary code `C` on a finite coordinate type `ι`, the Conway–Sloane residue-class
condition on an integer vector `a : ι → ℤ` asks that:

1. every coordinate `a i` satisfies `(∑ j, a j : ZMod 8) = 4 * (a i : ZMod 8)`;
2. for each residue class `r : ZMod 4`, the binary word selecting coordinates with
   `(a i : ZMod 4) = r` lies in `C`.

For any binary code containing the all-ones word, this condition is equivalent to the shifted
parity congruence model `a = 2 * b + m • 1` with `m ∈ {0, 1}`, `(b mod 2) ∈ C`, and
`∑ i, a i ≡ 4 * m [ZMOD 8]`.  Specializing to `C = TauCeti.BinaryGolay.code` on `Fin 24`
identifies the rational Leech lattice `TauCeti.leechLattice.carrier` with the halved vectors
`a / 2` (and hence the Euclidean Leech lattice with `a / √8`), with no coordinate permutation.

## Main definitions

* `SphereCeti.Leech.residueWord`: binary word selecting the coordinates of an integer vector in a
  given residue class modulo `4`.
* `SphereCeti.Leech.IsLeechIntegralCoordinate`: the residue-class and modulo-eight coordinate-sum
  condition relative to a binary code `C`.

## Main statements

* `SphereCeti.Leech.residueWord_apply`: entrywise evaluation of `residueWord`.
* `SphereCeti.Leech.residueWord_two_mul_add`: explicit formula for the modulo-four residue words
  of `i ↦ 2 * b i + m`.
* `SphereCeti.Leech.isLeechIntegralCoordinate_iff`: defining equivalence for
  `IsLeechIntegralCoordinate`.
* `SphereCeti.Leech.isLeechIntegralCoordinate_iff_exists`: equivalence with the shifted
  congruence model for any binary code containing the all-ones word.
* `SphereCeti.Leech.mem_leechLattice_carrier_iff_isLeechIntegralCoordinate`: exact membership
  characterization of `TauCeti.leechLattice.carrier` in residue-class coordinates.
* `SphereCeti.Leech.intCast_div_two_mem_leechLattice_carrier_iff`: membership of `a / 2` in
  `TauCeti.leechLattice.carrier` is equivalent to
  `IsLeechIntegralCoordinate TauCeti.BinaryGolay.code a`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11, and
  Chapter 10, §1.
-/

public section

namespace SphereCeti.Leech

/-- Binary word selecting coordinates in one residue class modulo four. -/
def residueWord {ι : Type*} (a : ι → ℤ) (r : ZMod 4) : ι → ZMod 2 := fun i =>
  if (a i : ZMod 4) = r then 1 else 0

/-- Entrywise evaluation of `residueWord`. -/
@[simp]
theorem residueWord_apply {ι : Type*} (a : ι → ℤ) (r : ZMod 4) (i : ι) :
    residueWord a r i = if (a i : ZMod 4) = r then 1 else 0 :=
  (rfl)

/-- For any integer shift `m`, the modulo-four residue words of `i ↦ 2 * b i + m` are
`1 + (b mod 2)` at residue `m`, `(b mod 2)` at residue `2 + m`, and `0` otherwise. -/
theorem residueWord_two_mul_add {ι : Type*} (b : ι → ℤ) (m : ℤ) (r : ZMod 4) :
    residueWord (fun i => 2 * b i + m) r =
      if (m : ZMod 4) = r then 1 + fun i => (b i : ZMod 2)
      else if (2 : ZMod 4) + (m : ZMod 4) = r then fun i => (b i : ZMod 2)
      else 0 := by
  funext i
  simp only [residueWord_apply, ite_apply, Pi.add_apply, Pi.one_apply, Pi.zero_apply,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  rw [← ZMod.cast_intCast (R := ZMod 2) (by decide : 2 ∣ 4) (b i)]
  exact (by decide : ∀ x y r : ZMod 4,
    (if 2 * x + y = r then (1 : ZMod 2) else 0) =
      if y = r then 1 + (ZMod.cast x : ZMod 2)
      else if 2 + y = r then (ZMod.cast x : ZMod 2)
      else 0) (b i : ZMod 4) (m : ZMod 4) r

/-- Residue-class coordinate condition on `a : ι → ℤ` relative to a binary code `C`: every
coordinate satisfies `(∑ j, a j : ZMod 8) = 4 * (a i : ZMod 8)` and each modulo-four residue word
`residueWord a r` lies in `C`.  When `C` is an extended binary Golay code on 24 coordinates (in
particular `TauCeti.BinaryGolay.code` on `Fin 24`), the `1 / 2` scaling describes the rational
Leech lattice and the `1 / √8` scaling its Euclidean realization. -/
def IsLeechIntegralCoordinate {ι : Type*} [Fintype ι]
    (C : Submodule (ZMod 2) (ι → ZMod 2)) (a : ι → ℤ) : Prop :=
  (∀ i, ((∑ j, a j : ℤ) : ZMod 8) = 4 * (a i : ZMod 8)) ∧
    ∀ r : ZMod 4, residueWord a r ∈ C

/-- Defining characterization of `IsLeechIntegralCoordinate`. -/
theorem isLeechIntegralCoordinate_iff {ι : Type*} [Fintype ι]
    {C : Submodule (ZMod 2) (ι → ZMod 2)} {a : ι → ℤ} :
    IsLeechIntegralCoordinate C a ↔
      (∀ i, ((∑ j, a j : ℤ) : ZMod 8) = 4 * (a i : ZMod 8)) ∧
        ∀ r : ZMod 4, residueWord a r ∈ C :=
  Iff.rfl

private theorem forall_residueWord_two_mul_add_mem_iff {ι : Type*}
    {C : Submodule (ZMod 2) (ι → ZMod 2)} (h1 : (1 : ι → ZMod 2) ∈ C)
    (m : ℤ) (b : ι → ℤ) :
    (∀ r : ZMod 4, residueWord (fun i => 2 * b i + m) r ∈ C) ↔
      (fun i => (b i : ZMod 2)) ∈ C := by
  have hne : (m : ZMod 4) ≠ 2 + (m : ZMod 4) := right_ne_add.mpr (by decide)
  refine ⟨fun h => ?_, fun hb r => ?_⟩
  · simpa [residueWord_two_mul_add, hne] using h (2 + (m : ZMod 4))
  · rw [residueWord_two_mul_add]
    split_ifs
    · exact C.add_mem h1 hb
    · exact hb
    · exact C.zero_mem

/-- For any binary code containing the all-ones word, the residue-class coordinate condition is
equivalent to the shifted parity congruence model `a = 2 * b + m • 1` (`m ∈ {0, 1}`). -/
theorem isLeechIntegralCoordinate_iff_exists {ι : Type*} [Fintype ι]
    {C : Submodule (ZMod 2) (ι → ZMod 2)} (h1 : (1 : ι → ZMod 2) ∈ C)
    {a : ι → ℤ} :
    IsLeechIntegralCoordinate C a ↔
      ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ ∃ b : ι → ℤ,
        (fun i => (b i : ZMod 2)) ∈ C ∧
        ∑ i, (2 * b i + m) ≡ 4 * m [ZMOD 8] ∧
        a = fun i => 2 * b i + m := by
  constructor
  · intro ha
    rw [isLeechIntegralCoordinate_iff] at ha
    rcases ha with ⟨hsum, hres⟩
    by_cases hne : Nonempty ι
    · obtain ⟨i₀⟩ := hne
      set m : ℤ := a i₀ % 2
      have hpar (i : ι) : a i % 2 = m := by
        have h8 : ((4 * a i : ℤ) : ZMod 8) = ((4 * a i₀ : ℤ) : ZMod 8) := by
          push_cast; rw [← hsum i, hsum i₀]
        have hmod := (ZMod.intCast_eq_intCast_iff _ _ 8).mp h8
        rw [Int.ModEq] at hmod; omega
      set b : ι → ℤ := fun i => (a i - m) / 2
      have hab : a = fun i => 2 * b i + m := funext fun i => by
        have := hpar i; dsimp only [b]; omega
      refine ⟨m, Int.emod_two_eq_zero_or_one (a i₀), b, ?_, ?_, hab⟩
      · rw [hab] at hres
        exact (forall_residueWord_two_mul_add_mem_iff h1 m b).mp hres
      · have h8 : ((∑ j, (2 * b j + m) : ℤ) : ZMod 8) = ((4 * a i₀ : ℤ) : ZMod 8) := by
          rw [← hab, hsum i₀]; push_cast; rfl
        have hmod := (ZMod.intCast_eq_intCast_iff _ _ 8).mp h8
        rw [Int.ModEq] at hmod ⊢; omega
    · have : IsEmpty ι := not_nonempty_iff.mp hne
      refine ⟨0, Or.inl rfl, IsEmpty.elim this, ?_, by simp, funext (IsEmpty.elim this)⟩
      rw [Subsingleton.elim (fun i : ι => ((IsEmpty.elim this i : ℤ) : ZMod 2)) 0]
      exact C.zero_mem
  · rintro ⟨m, _, b, hb, hsum, rfl⟩
    rw [isLeechIntegralCoordinate_iff]
    refine ⟨fun i => ?_, (forall_residueWord_two_mul_add_mem_iff h1 m b).mpr hb⟩
    have hmod : ∑ j, (2 * b j + m) ≡ 4 * (2 * b i + m) [ZMOD 8] := by
      rw [Int.ModEq] at hsum ⊢; omega
    simpa only [Int.cast_mul, Int.cast_ofNat] using (ZMod.intCast_eq_intCast_iff _ _ 8).mpr hmod

/-- Exact residue-class coordinate characterization of `TauCeti.leechLattice.carrier`, with no
coordinate permutation. -/
theorem mem_leechLattice_carrier_iff_isLeechIntegralCoordinate (x : Fin 24 → ℚ) :
    x ∈ TauCeti.leechLattice.carrier ↔
      ∃ a : Fin 24 → ℤ, IsLeechIntegralCoordinate TauCeti.BinaryGolay.code a ∧
        x = fun i => (a i : ℚ) / 2 := by
  rw [TauCeti.mem_leechLattice_carrier_iff_exists]
  have h1 : (1 : Fin 24 → ZMod 2) ∈ TauCeti.BinaryGolay.code :=
    TauCeti.BinaryCode.one_mem_of_isSelfDual TauCeti.BinaryGolay.isSelfDual_code
  constructor
  · rintro ⟨m, hm, b, hb, hsum, rfl⟩
    exact ⟨fun i => 2 * b i + m,
      (isLeechIntegralCoordinate_iff_exists h1).mpr ⟨m, hm, b, hb, hsum, rfl⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨m, hm, b, hb, hsum, rfl⟩ := (isLeechIntegralCoordinate_iff_exists h1).mp ha
    exact ⟨m, hm, b, hb, hsum, rfl⟩

/-- A halved integer vector `a / 2` lies in `TauCeti.leechLattice.carrier` if and only if `a`
satisfies the residue-class coordinate condition for `TauCeti.BinaryGolay.code`. -/
theorem intCast_div_two_mem_leechLattice_carrier_iff (a : Fin 24 → ℤ) :
    (fun i => (a i : ℚ) / 2) ∈ TauCeti.leechLattice.carrier ↔
      IsLeechIntegralCoordinate TauCeti.BinaryGolay.code a := by
  rw [mem_leechLattice_carrier_iff_isLeechIntegralCoordinate]
  constructor
  · rintro ⟨a', ha', h⟩
    have ha : a' = a := funext fun i => by
      have hi : ((a i : ℚ) / 2) = (a' i : ℚ) / 2 := congrFun h i
      exact_mod_cast (div_left_inj' (two_ne_zero (α := ℚ))).mp hi.symm
    exact ha ▸ ha'
  · intro ha
    exact ⟨a, ha, rfl⟩

/-! ### Automation and witness checks -/

example {ι : Type*} (a : ι → ℤ) (r : ZMod 4) (i : ι) :
    residueWord a r i = if (a i : ZMod 4) = r then 1 else 0 := by
  simp

example : IsLeechIntegralCoordinate TauCeti.BinaryGolay.code
    (fun i : Fin 24 => if i = 0 then -3 else 1) := by
  rw [← intCast_div_two_mem_leechLattice_carrier_iff]
  have hshift : (fun i : Fin 24 => ((if i = 0 then (-3 : ℤ) else 1 : ℤ) : ℚ) / 2) =
      TauCeti.leechShift := by
    funext i
    by_cases hi : i = 0
    · simp [hi]; norm_num
    · simp [hi]
  rw [hshift]
  exact TauCeti.leechShift_mem_leechLattice_carrier

end SphereCeti.Leech
