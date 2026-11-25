/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Leech.BasisMatrix
public import SphereCeti.Leech.Lattice
public import SphereCeti.Leech.ResidueCoordinates

/-!
# The published basis of the Leech lattice

Conway and Sloane's standard generator matrix `M = basisCoordinateMatrix` of the Leech lattice is
an integer `24 × 24` matrix whose rows, divided by `√8`, are the vectors
`b₀, …, b₂₃ = basisVector 0, …, basisVector 23` of `ℝ^24`.  Its coordinates are those of the
Miracle Octad Generator, which realize the extended binary Golay code differently from TauCeti's
systematic code `TauCeti.BinaryGolay.code`.  This file proves that after the explicit coordinate
permutation `basisCoordPerm` these rows span exactly the Euclidean Leech lattice
`SphereCeti.Leech.lattice`: a vector `x` lies in the lattice if and only if its permuted copy
`coordPerm basisCoordPerm x` is an integer combination of the `bᵢ`.

The proof is a finite certificate on either side.

* Each permuted row `(coordPerm basisCoordPerm).symm bᵢ` is `a / √8` for an integer vector `a`
  satisfying the residue-class condition `IsLeechIntegralCoordinate TauCeti.BinaryGolay.code a`,
  checked by evaluation, so it lies in the lattice; hence the span of the `bᵢ` is contained in the
  permuted lattice.
* Conversely, the Gram matrix `M Mᵀ / 8` of the `bᵢ` has an integral inverse `N = 8 (M Mᵀ)⁻¹`,
  given explicitly; the identity `Mᵀ N M = 8` is checked by evaluation.  This gives the
  expansion `z = ∑ᵢ (∑ⱼ ⟪z, bⱼ⟫ Nⱼᵢ) bᵢ` for every `z ∈ ℝ^24`.  If `z` is a permuted lattice
  vector, every `⟪z, bⱼ⟫` is the Leech form of two lattice vectors and hence an integer, so the
  coefficients are integers.

The permutation `basisCoordPerm` sends TauCeti's coordinate `l` to the Conway–Sloane coordinate
`basisCoordPerm l`.  It carries the octads of `TauCeti.BinaryGolay.code` to the octads of the
Golay code of the Conway–Sloane coordinates; any permutation with this property would do.

## Main definitions and results

* `SphereCeti.Leech.coordPerm`: a permutation of the coordinates of `ℝ^24`, as a linear isometry.
* `SphereCeti.Leech.basisVector`: the `i`-th row of `basisCoordinateMatrix`, divided by `√8`.
* `SphereCeti.Leech.basisCoordPerm`: the coordinate permutation from TauCeti's Golay coordinates to
  Conway–Sloane's.
* `SphereCeti.Leech.coordPerm_symm_basisVector_mem_lattice`: each permuted basis vector lies in the
  Euclidean Leech lattice.
* `SphereCeti.Leech.mem_lattice_iff_coordPerm_mem_span`: `x` lies in the lattice if and only if
  `coordPerm basisCoordPerm x` lies in the `ℤ`-span of the basis vectors.
* `SphereCeti.Leech.exists_coordPerm_span_basisVectors`: the same statement with the permutation
  existentially quantified.

## Sources

The Leech lattice, the binary Golay code and the integrality of the Leech form are TauCeti's
(repository `TauCetiProject/TauCeti`, commit `83769e442d55cda9d85b3927a93b286831c595ff`, files
`TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/Basic.lean`,
`TauCeti/InformationTheory/Coding/Binary/Golay/Basic.lean` and
`TauCeti/LinearAlgebra/IntegralLattice/Basic.lean`).  The certificates are new.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer
  (1999), Chapter 4, §11, Figure 4.12 (the generator matrix), and Chapter 11 (the Miracle Octad
  Generator).
-/

public section

open scoped InnerProductSpace

namespace SphereCeti.Leech

/-! ### Coordinate permutations and the basis vectors -/

/-- A permutation `σ` of the coordinates of `ℝ^24`, as a linear isometry: the `j`-th coordinate of
`coordPerm σ x` is `x (σ.symm j)`. -/
noncomputable def coordPerm (σ : Equiv.Perm (Fin 24)) :
    EuclideanSpace ℝ (Fin 24) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 24) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

/-- The `j`-th coordinate of `coordPerm σ x` is the `σ.symm j`-th coordinate of `x`. -/
@[simp]
theorem coordPerm_apply (σ : Equiv.Perm (Fin 24)) (x : EuclideanSpace ℝ (Fin 24)) (j : Fin 24) :
    coordPerm σ x j = x (σ.symm j) :=
  (rfl)

example (x : EuclideanSpace ℝ (Fin 24)) (j : Fin 24) :
    coordPerm (Equiv.refl _) x j = x j := by
  simp

/-- The inverse of a coordinate permutation is the permutation by the inverse. -/
@[simp]
theorem coordPerm_symm (σ : Equiv.Perm (Fin 24)) : (coordPerm σ).symm = coordPerm σ.symm :=
  LinearIsometryEquiv.piLpCongrLeft_symm σ

example (σ : Equiv.Perm (Fin 24)) (x : EuclideanSpace ℝ (Fin 24)) (j : Fin 24) :
    (coordPerm σ).symm x j = x (σ j) := by
  simp

/-- The `i`-th published basis vector of the Leech lattice: the `i`-th row of
`basisCoordinateMatrix`, divided by `√8`, in Conway–Sloane's coordinates. -/
noncomputable def basisVector (i : Fin 24) : EuclideanSpace ℝ (Fin 24) :=
  WithLp.toLp 2 fun j => (basisCoordinateMatrix i j : ℝ) / Real.sqrt 8

/-- The `j`-th coordinate of `basisVector i` is `basisCoordinateMatrix i j / √8`. -/
@[simp]
theorem basisVector_apply (i j : Fin 24) :
    basisVector i j = (basisCoordinateMatrix i j : ℝ) / Real.sqrt 8 :=
  (rfl)

example : basisVector 23 0 = -3 / Real.sqrt 8 := by
  simp

/-- The coordinate permutation carrying TauCeti's Golay coordinates to Conway–Sloane's: the
TauCeti coordinate `l` becomes the Conway–Sloane coordinate `basisCoordPerm l`.  It maps
`TauCeti.BinaryGolay.code` onto the binary Golay code read off from `basisCoordinateMatrix`. -/
def basisCoordPerm : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 8, 15, 16, 9, 17, 18, 23, 10, 21, 14, 12, 19, 5, 20, 11, 13, 7, 22, 6]
  invFun := ![0, 1, 2, 3, 4, 17, 23, 21, 5, 8, 12, 19, 15, 20, 14, 6, 7, 9, 10, 16, 18, 13, 22, 11]
  left_inv := by decide
  right_inv := by decide

/-! ### The permuted rows lie in the Leech lattice -/

/-- Systematic membership test for TauCeti's Golay code: a word is a codeword exactly when it is
the systematic encoding of its first twelve coordinates. -/
private theorem mem_code_iff_append (x : Fin 24 → ZMod 2) :
    x ∈ TauCeti.BinaryGolay.code ↔
      Fin.append (fun i : Fin 12 => x (i.castAdd 12))
        (Matrix.vecMul (fun i : Fin 12 => x (i.castAdd 12)) TauCeti.BinaryGolay.block) = x := by
  rw [TauCeti.BinaryGolay.mem_code_iff]
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  rintro ⟨a, rfl⟩
  simp only [Fin.append_left]

/-- `residueWord` as an explicit function, for evaluation. -/
private theorem residueWord_eq (a : Fin 24 → ℤ) (r : ZMod 4) :
    residueWord a r = fun i => if (a i : ZMod 4) = r then 1 else 0 :=
  funext (residueWord_apply a r)

/-- `TauCeti.BinaryGolay.block` as an explicit function, for evaluation. -/
private theorem block_eq : TauCeti.BinaryGolay.block = fun i j =>
    if i = 0 then (if j = 0 then 0 else 1) else if j = 0 then 1 else
      if (i.val + j.val - 2) % 11 ∈ ({0, 1, 3, 4, 5, 9} : Finset ℕ) then 1 else 0 :=
  funext fun i => funext fun j => TauCeti.BinaryGolay.block_apply i j

/-- Every row of `basisCoordinateMatrix`, read in TauCeti's coordinates, satisfies the Leech
residue-class condition for TauCeti's Golay code. -/
private theorem isLeechIntegralCoordinate_row (i : Fin 24) :
    IsLeechIntegralCoordinate TauCeti.BinaryGolay.code
      (fun l => basisCoordinateMatrix i (basisCoordPerm l)) := by
  rw [isLeechIntegralCoordinate_iff]
  simp only [mem_code_iff_append, residueWord_eq, block_eq]
  revert i
  rw [basisCoordinateMatrix_def]
  decide +kernel

/-- The inverse coordinate permutation carries `basisVector i` to the embedded halved row
`a / 2` of TauCeti's coordinates, where `a l = basisCoordinateMatrix i (basisCoordPerm l)`. -/
theorem coordPerm_symm_basisVector (i : Fin 24) :
    (coordPerm basisCoordPerm).symm (basisVector i) =
      embedding (fun l => (basisCoordinateMatrix i (basisCoordPerm l) : ℚ) / 2) := by
  rw [embedding_div_two]
  ext l
  simp

/-- Each published basis vector, moved to TauCeti's coordinates, lies in the Euclidean Leech
lattice. -/
theorem coordPerm_symm_basisVector_mem_lattice (i : Fin 24) :
    (coordPerm basisCoordPerm).symm (basisVector i) ∈ lattice := by
  rw [coordPerm_symm_basisVector, mem_lattice_iff]
  exact ⟨_, (intCast_div_two_mem_leechLattice_carrier_iff _).mpr
    (isLeechIntegralCoordinate_row i), rfl⟩

/-! ### The inverse Gram certificate -/

/-- The integer matrix `8 (M Mᵀ)⁻¹`, where `M = basisCoordinateMatrix`: the inverse of the Gram
matrix `M Mᵀ / 8` of the basis vectors, which is integral because that Gram matrix is
unimodular. -/
private def gramCertificate : Matrix (Fin 24) (Fin 24) ℤ :=
![
  ![72, -20, -26, -20, -20, -12, -6, 3, -14, -9, -12, 12, -5, 6, 9, -9, -5, 3, 9, -6, 19, -9, -12, 11],
  ![-20, 8, 8, 6, 4, 4, 2, -3, 2, 3, 3, -5, 0, -2, -1, 4, 0, 0, -1, 2, -5, 3, 3, -4],
  ![-26, 8, 12, 8, 5, 4, 2, -2, 3, 4, 5, -7, 0, -1, -3, 5, 0, -1, -2, 4, -7, 4, 5, -6],
  ![-20, 6, 8, 8, 4, 4, 2, -3, 2, 2, 4, -5, 0, 0, -2, 3, 0, 1, -3, 3, -5, 2, 4, -4],
  ![-20, 4, 5, 4, 10, 3, 2, 1, 7, 1, 2, 1, 4, -3, -4, 0, 4, -2, -4, -1, -6, 2, 3, 0],
  ![-12, 4, 4, 4, 3, 4, 2, -3, 1, 1, 2, -2, 0, -1, -1, 2, 0, 1, -2, 1, -2, 1, 2, -2],
  ![-6, 2, 2, 2, 2, 2, 4, -4, 0, -1, 1, 0, 0, 1, -2, 1, 0, 2, -1, -1, 0, -1, 1, 0],
  ![3, -3, -2, -3, 1, -3, -4, 8, 3, 1, -1, 2, 2, -2, 0, -2, 2, -4, 0, 0, -2, 2, 0, 0],
  ![-14, 2, 3, 2, 7, 1, 0, 3, 8, 2, 2, 0, 4, -3, -3, -1, 4, -3, -3, -1, -4, 1, 1, 2],
  ![-9, 3, 4, 2, 1, 1, -1, 1, 2, 4, 2, -4, 0, -2, 0, 2, 0, -2, 0, 2, -2, 2, 1, -2],
  ![-12, 3, 5, 4, 2, 2, 1, -1, 2, 2, 4, -4, 0, 0, -2, 2, 0, 0, -2, 2, -2, 1, 2, -2],
  ![12, -5, -7, -5, 1, -2, 0, 2, 0, -4, -4, 8, 2, 0, 0, -4, 2, 0, 0, -4, 2, -2, -2, 4],
  ![-5, 0, 0, 0, 4, 0, 0, 2, 4, 0, 0, 2, 4, -2, -2, -2, 2, -1, -1, -1, -2, 0, 0, 2],
  ![6, -2, -1, 0, -3, -1, 1, -2, -3, -2, 0, 0, -2, 4, 0, 0, -1, 2, 0, 0, 2, -2, 0, 0],
  ![9, -1, -3, -2, -4, -1, -2, 0, -3, 0, -2, 0, -2, 0, 4, 0, -1, 0, 2, 0, 2, 0, -2, 0],
  ![-9, 4, 5, 3, 0, 2, 1, -2, -1, 2, 2, -4, -2, 0, 0, 4, -1, 0, 0, 2, -2, 2, 2, -4],
  ![-5, 0, 0, 0, 4, 0, 0, 2, 4, 0, 0, 2, 2, -1, -1, -1, 4, -2, -2, -2, -2, 0, 0, 2],
  ![3, 0, -1, 1, -2, 1, 2, -4, -3, -2, 0, 0, -1, 2, 0, 0, -2, 4, 0, 0, 2, -2, 0, 0],
  ![9, -1, -2, -3, -4, -2, -1, 0, -3, 0, -2, 0, -1, 0, 2, 0, -2, 0, 4, 0, 2, 0, -2, 0],
  ![-6, 2, 4, 3, -1, 1, -1, 0, -1, 2, 2, -4, -1, 0, 0, 2, -2, 0, 0, 4, -2, 2, 2, -4],
  ![19, -5, -7, -5, -6, -2, 0, -2, -4, -2, -2, 2, -2, 2, 2, -2, -2, 2, 2, -2, 8, -4, -4, 4],
  ![-9, 3, 4, 2, 2, 1, -1, 2, 1, 2, 1, -2, 0, -2, 0, 2, 0, -2, 0, 2, -4, 4, 2, -4],
  ![-12, 3, 5, 4, 3, 2, 1, 0, 1, 1, 2, -2, 0, 0, -2, 2, 0, 0, -2, 2, -4, 2, 4, -4],
  ![11, -4, -6, -4, 0, -2, 0, 0, 2, -2, -2, 4, 2, 0, 0, -4, 2, 0, 0, -4, 4, -4, -4, 8]]
/-- The certificate identity `Mᵀ N M = 8`, checked by evaluation. -/
private theorem transpose_mul_gramCertificate_mul :
    basisCoordinateMatrix.transpose * gramCertificate * basisCoordinateMatrix = 8 := by
  rw [basisCoordinateMatrix_def]
  decide +kernel

/-- Coordinate form of the expansion: if `Mᵀ N M = 8`, then `∑ᵢ (∑ⱼ ⟪z, Mⱼ / √8⟫ Nⱼᵢ) Mᵢ / √8 = z`
for every vector `z`. -/
private theorem sum_expansion_aux (M N : Fin 24 → Fin 24 → ℝ)
    (hc : ∀ m k, ∑ i, (∑ j, M j m * N j i) * M i k = if m = k then 8 else 0)
    (z : Fin 24 → ℝ) (k : Fin 24) :
    ∑ i, (∑ j, (∑ m, M j m / Real.sqrt 8 * z m) * N j i) * (M i k / Real.sqrt 8) = z k := by
  have hs : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hz : z k = ∑ m, z m * ((∑ i, (∑ j, M j m * N j i) * M i k) / 8) := by
    simp only [hc, ite_div, zero_div, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    norm_num
  rw [hz]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  -- Bring the summation over `m` outermost on the left, matching the right.
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  field_simp
  rw [hs]
  ring

/-- Expansion of an arbitrary vector of `ℝ^24` in the basis vectors, with coefficients given by
its inner products with the basis vectors and the certificate `gramCertificate`. -/
private theorem sum_inner_basisVector (z : EuclideanSpace ℝ (Fin 24)) :
    ∑ i, (∑ j, ⟪z, basisVector j⟫_ℝ * (gramCertificate j i : ℝ)) • basisVector i = z := by
  -- The certificate `Mᵀ N M = 8`, read entrywise in `ℝ`.
  have hc (m k : Fin 24) : ∑ i, (∑ j, (basisCoordinateMatrix j m : ℝ) * gramCertificate j i) *
      basisCoordinateMatrix i k = if m = k then 8 else 0 := by
    have h := congrFun (congrFun transpose_mul_gramCertificate_mul m) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.ofNat_apply] at h
    have h' := congrArg (Int.cast : ℤ → ℝ) h
    push_cast at h'
    rw [h']
  ext k
  simp [PiLp.inner_apply, -basisCoordinateMatrix_apply]
  exact sum_expansion_aux (fun i j => basisCoordinateMatrix i j) (fun i j => gramCertificate i j)
    hc z.ofLp k

/-! ### The span of the basis vectors -/

/-- A vector `x` of `ℝ^24` lies in the Euclidean Leech lattice if and only if its permuted copy
`coordPerm basisCoordPerm x` is an integer combination of the published basis vectors. -/
theorem mem_lattice_iff_coordPerm_mem_span (x : EuclideanSpace ℝ (Fin 24)) :
    x ∈ lattice ↔
      coordPerm basisCoordPerm x ∈ Submodule.span ℤ (Set.range basisVector) := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (mem_lattice_iff x).mp hx
    -- The inner products with the basis vectors are values of the integral Leech form.
    have hρ (j : Fin 24) :
        (fun l => (basisCoordinateMatrix j (basisCoordPerm l) : ℚ) / 2) ∈
          TauCeti.leechLattice.carrier :=
      (intCast_div_two_mem_leechLattice_carrier_iff _).mpr (isLeechIntegralCoordinate_row j)
    have hq (j : Fin 24) :
        ⟪coordPerm basisCoordPerm (embedding y), basisVector j⟫_ℝ =
          (TauCeti.leechLattice.integralForm ⟨y, hy⟩ ⟨_, hρ j⟩ : ℤ) := by
      rw [LinearIsometryEquiv.inner_map_eq_flip, coordPerm_symm_basisVector, inner_embedding,
        ← Rat.cast_intCast, TauCeti.IntegralLattice.integralForm_cast]
    rw [← sum_inner_basisVector (coordPerm basisCoordPerm (embedding y))]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hcoef : ∑ j, ⟪coordPerm basisCoordPerm (embedding y), basisVector j⟫_ℝ *
        (gramCertificate j i : ℝ) = ((∑ j, TauCeti.leechLattice.integralForm ⟨y, hy⟩ ⟨_, hρ j⟩ *
          gramCertificate j i : ℤ) : ℝ) := by
      push_cast
      simp only [hq]
    rw [hcoef, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro hx
    -- Every vector of the span is carried into the lattice by the inverse permutation.
    have key : ∀ z ∈ Submodule.span ℤ (Set.range basisVector),
        (coordPerm basisCoordPerm).symm z ∈ lattice := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact coordPerm_symm_basisVector_mem_lattice i
      | zero => rw [map_zero]; exact lattice.zero_mem
      | add u w _ _ hu hw => rw [map_add]; exact lattice.add_mem hu hw
      | smul n u _ hu => rw [map_zsmul]; exact lattice.smul_mem n hu
    simpa only [LinearIsometryEquiv.symm_apply_apply] using key _ hx

/-- After a coordinate permutation, the published rows span exactly the Euclidean Leech
lattice. -/
theorem exists_coordPerm_span_basisVectors :
    ∃ σ : Equiv.Perm (Fin 24), ∀ x : EuclideanSpace ℝ (Fin 24),
      x ∈ lattice ↔ coordPerm σ x ∈ Submodule.span ℤ (Set.range basisVector) :=
  ⟨basisCoordPerm, mem_lattice_iff_coordPerm_mem_span⟩

end SphereCeti.Leech
