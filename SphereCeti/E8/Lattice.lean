/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import SphereCeti.Lattice.IntegralPresentation
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Roots

/-!
# The Euclidean E8 lattice and its integral presentation

The E8 lattice `SphereCeti.E8.lattice` is the set of vectors `x ∈ ℝ^8` whose coordinates are
either all integers or all halves of odd integers, and whose coordinate sum is even.  Writing
`x = a / 2` with `a ∈ ℤ^8`, these are exactly the conditions that the coordinates of `a` all have
the same parity and that `∑ i, a i ≡ 0 [ZMOD 4]`; this integer form is the definition used here,
and `SphereCeti.E8.mem_lattice_iff_coordinates` recovers the coordinate-parity description.

The eight vectors

```text
b₀ = (2, 0, 0, 0, 0, 0, 0, 0),  bᵢ = eᵢ - eᵢ₋₁ (1 ≤ i ≤ 6),  b₇ = (1/2, …, 1/2)
```

form a `ℤ`-basis of the lattice: they lie in it, they are linearly independent, and every lattice
vector is an explicit integer combination of them.  Their Gram matrix `SphereCeti.E8.gram` is an
integer matrix with diagonal `(4, 2, …, 2)`, so the basis and its Gram matrix form an integral
presentation of the lattice.

The canonical algebraic E8 lattice is TauCeti's `TauCeti.IntegralLattice.typeE₈RootLattice`, the
Gram lattice of the Cartan matrix `C = CartanMatrix.E 8` in simple-root coordinates.  In terms of
the simple roots `α₁ = (e₀ + e₇) / 2 - (e₁ + ⋯ + e₆) / 2`, `α₂ = e₀ + e₁`, `α₃ = e₁ - e₀` and
`αₖ = eₖ₋₂ - eₖ₋₃` (`4 ≤ k ≤ 8`) of Bourbaki's Plate VII, each `bᵢ` has integer coordinates, the
rows of the matrix `V = SphereCeti.E8.simpleRootCoordinates`, and `V` is invertible over `ℤ`.  The
congruence `V * C * Vᵀ = gram` then gives an isometry from the presentation, in Gram coordinates,
to TauCeti's lattice.  Hence the presentation is even and unimodular, the lattice has covolume one,
and its `240` vectors of squared norm `2` are counted by TauCeti's enumeration of the E8 roots.
The minimum squared norm `2` follows from evenness; neither it nor the root count uses theta
series.

## Main definitions

* `SphereCeti.E8.lattice`: the E8 lattice in `EuclideanSpace ℝ (Fin 8)`.
* `SphereCeti.E8.basisVector`, `SphereCeti.E8.basis`: the vectors `bᵢ` and the `ℤ`-basis of the
  lattice they form.
* `SphereCeti.E8.gram`: the Gram matrix of the basis.
* `SphereCeti.E8.integralPresentation`: the integral presentation given by the basis and `gram`.
* `SphereCeti.E8.simpleRootCoordinates`: the coordinates of the `bᵢ` in the simple roots.
* `SphereCeti.E8.integralLatticeIsometry`: the isometry from the presentation in Gram coordinates
  to `TauCeti.IntegralLattice.typeE₈RootLattice`.

## Main statements

* `SphereCeti.E8.mem_lattice_iff_coordinates`: the coordinate-parity description of the lattice.
* `SphereCeti.E8.span_basisVector`: the lattice is the integer span of the `bᵢ`.
* `SphereCeti.E8.lattice_discrete`, `SphereCeti.E8.lattice_isZLattice`: it is a full lattice.
* `SphereCeti.E8.inner_basisVector`: the inner products of the `bᵢ` are the entries of `gram`.
* `SphereCeti.E8.integralLatticeIsometry_single`: the isometry sends the `i`-th standard basis
  vector to the `i`-th row of `simpleRootCoordinates`.
* `SphereCeti.E8.integralPresentation_even`, `SphereCeti.E8.integralPresentation_unimodular`: the
  presentation is even and unimodular.
* `SphereCeti.E8.covolume_lattice`: the lattice has covolume one.
* `SphereCeti.E8.hasMinNormSq`: nonzero lattice vectors have squared norm at least `2`, with
  equality attained.
* `SphereCeti.E8.representationNumber_lattice_two`: the lattice has `240` vectors of squared
  norm `2`.

## Sources

The lattice, its coordinate-parity description, the basis, its Gram matrix, and the spanning
argument are adapted from Sphere-Packing-Lean (repository
`thefundamentaltheor3m/Sphere-Packing-Lean`, commit `bad3de916074748eb88b7d1ee6dbf9494361ad17`,
file `SpherePacking/Basic/E8.lean`: `Submodule.E8`, `Submodule.mem_E8''`, `E8Matrix`, `E8.inn`,
`span_E8Matrix`, `E8Lattice` and `E8_ℤBasis`).  The integer coefficients in `span_basisVector` are those of that file's inverse
matrix `E8Inverse`.  The E8 root lattice, its evenness, unimodularity and root enumeration are
TauCeti's (repository `TauCetiProject/TauCeti`, commit `83769e442d55cda9d85b3927a93b286831c595ff`,
files `TauCeti/LinearAlgebra/IntegralLattice/RootLattice/TypeE/Basic.lean` and
`TauCeti/LinearAlgebra/IntegralLattice/RootLattice/TypeE/Roots.lean`); the isometry
`TauCeti.IntegralLattice.Isometry.ofGramMatrixEq` and the standard-coordinate form are from
`TauCeti/LinearAlgebra/IntegralLattice/Gram.lean` and
`TauCeti/LinearAlgebra/IntegralLattice/StandardCoordinates.lean` at the same commit.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer
  (1999), Chapter 4, §8.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Plate VII.
-/

public section

open Matrix

open scoped InnerProductSpace

namespace SphereCeti.E8

/-! ### The lattice -/

/-- The E8 lattice in `ℝ^8`: the vectors `a / 2` with `a ∈ ℤ^8` whose coordinates all have the
same parity and satisfy `∑ i, a i ≡ 0 [ZMOD 4]`.  Equivalently (`mem_lattice_iff_coordinates`),
the vectors whose coordinates are all integers or all halves of odd integers, with even
coordinate sum. -/
noncomputable def lattice : Submodule ℤ (EuclideanSpace ℝ (Fin 8)) where
  carrier := {x | ∃ a : Fin 8 → ℤ, (∀ i, x i = (a i : ℝ) / 2) ∧
    (∀ i, a i ≡ a 0 [ZMOD 2]) ∧ ∑ i, a i ≡ 0 [ZMOD 4]}
  add_mem' := by
    rintro x y ⟨a, hxa, hpa, hsa⟩ ⟨b, hyb, hpb, hsb⟩
    refine ⟨a + b, fun i => ?_, fun i => (hpa i).add (hpb i), ?_⟩
    · simp [hxa, hyb, add_div]
    · simpa [Finset.sum_add_distrib] using hsa.add hsb
  zero_mem' := ⟨0, fun i => by simp, fun i => rfl, by simp [Int.ModEq]⟩
  smul_mem' := by
    rintro c x ⟨a, hxa, hpa, hsa⟩
    refine ⟨c • a, fun i => ?_, fun i => (hpa i).mul_left c, ?_⟩
    · simp [hxa, mul_div_assoc]
    · simpa [Finset.mul_sum] using hsa.mul_left c

/-- A vector lies in the E8 lattice exactly when it is `a / 2` for an integer vector `a` whose
coordinates all have the same parity and whose coordinate sum is divisible by `4`. -/
theorem mem_lattice_iff (x : EuclideanSpace ℝ (Fin 8)) :
    x ∈ lattice ↔ ∃ a : Fin 8 → ℤ, (∀ i, x i = (a i : ℝ) / 2) ∧
      (∀ i, a i ≡ a 0 [ZMOD 2]) ∧ ∑ i, a i ≡ 0 [ZMOD 4] :=
  Iff.rfl

/-- **The coordinate-parity description of E8.**  A vector lies in the E8 lattice exactly when its
coordinates are all integers or all of the form `n + 1/2` with `n` an integer, and its coordinate
sum is even. -/
theorem mem_lattice_iff_coordinates (x : EuclideanSpace ℝ (Fin 8)) :
    x ∈ lattice ↔
      ((∀ i, ∃ n : ℤ, (n : ℝ) = x i) ∨ (∀ i, ∃ n : ℤ, (n : ℝ) + 2⁻¹ = x i)) ∧
        ∑ i, x i ≡ 0 [PMOD 2] := by
  rw [AddCommGroup.modEq_iff_zsmul', zero_sub, Fin.sum_univ_eight]
  constructor
  · rintro ⟨a, hxa, hpa, hsa⟩
    -- Write `a i = a 0 + 2 * t i` and `∑ i, a i = 4 * q`; the cases are the parities of `a 0`.
    choose t ht using fun i => (hpa i).symm.dvd
    obtain ⟨q, hq⟩ := hsa.symm.dvd
    rw [Fin.sum_univ_eight, sub_zero] at hq
    refine ⟨?_, -q, ?_⟩
    · rcases Int.even_or_odd' (a 0) with ⟨r, hr | hr⟩
      · refine Or.inl fun i => ⟨r + t i, ?_⟩
        have hai : a i = 2 * (r + t i) := by linarith [ht i]
        rw [hxa i, hai]
        push_cast
        ring
      · refine Or.inr fun i => ⟨r + t i, ?_⟩
        have hai : a i = 2 * (r + t i) + 1 := by linarith [ht i]
        rw [hxa i, hai]
        push_cast
        ring
    · have hq' : ((a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 : ℤ) : ℝ) = 4 * q := by
        rw [hq]; push_cast; ring
      simp only [hxa, zsmul_eq_mul]
      push_cast at hq' ⊢
      linarith
  · rintro ⟨hc | hc, m, hm⟩ <;> choose n hn using hc <;> simp only [← hn, zsmul_eq_mul] at hm
    · -- Integral coordinates `x i = n i`: take `a i = 2 * n i`.
      have hsum : n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 = -(2 * m) := by
        exact_mod_cast (by push_cast; linarith :
          ((n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 : ℤ) : ℝ) = ((-(2 * m) : ℤ) : ℝ))
      refine ⟨fun i => 2 * n i, fun i => by rw [← hn i]; push_cast; ring,
        fun i => by unfold Int.ModEq; beta_reduce; omega, ?_⟩
      rw [Fin.sum_univ_eight]
      unfold Int.ModEq
      omega
    · -- Half-integral coordinates `x i = n i + 1/2`: take `a i = 2 * n i + 1`.
      have hsum : n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 = -(2 * m) - 4 := by
        exact_mod_cast (by push_cast; linarith :
          ((n 0 + n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 : ℤ) : ℝ) = ((-(2 * m) - 4 : ℤ) : ℝ))
      refine ⟨fun i => 2 * n i + 1, fun i => by rw [← hn i]; push_cast; ring,
        fun i => by unfold Int.ModEq; beta_reduce; omega, ?_⟩
      rw [Fin.sum_univ_eight]
      unfold Int.ModEq
      omega

/-! ### The basis and its Gram matrix -/

/-- Twice the matrix whose rows are the basis vectors `b₀, …, b₇` of the E8 lattice: its rows are
`(4, 0, …, 0)`, `2 • (eᵢ - eᵢ₋₁)` for `1 ≤ i ≤ 6`, and `(1, …, 1)`.  Halving it gives
Sphere-Packing-Lean's `E8Matrix`; doubling makes the entries integers. -/
def doubledBasisMatrix : Matrix (Fin 8) (Fin 8) ℤ := !![
   4,  0,  0,  0,  0,  0,  0,  0;
  -2,  2,  0,  0,  0,  0,  0,  0;
   0, -2,  2,  0,  0,  0,  0,  0;
   0,  0, -2,  2,  0,  0,  0,  0;
   0,  0,  0, -2,  2,  0,  0,  0;
   0,  0,  0,  0, -2,  2,  0,  0;
   0,  0,  0,  0,  0, -2,  2,  0;
   1,  1,  1,  1,  1,  1,  1,  1]

/-- The Gram matrix of the basis `b₀, …, b₇` of the E8 lattice: its `(i, j)` entry is `⟪bᵢ, bⱼ⟫`
(`inner_basisVector`). -/
def gram : Matrix (Fin 8) (Fin 8) ℤ := !![
   4, -2,  0,  0,  0,  0,  0,  1;
  -2,  2, -1,  0,  0,  0,  0,  0;
   0, -1,  2, -1,  0,  0,  0,  0;
   0,  0, -1,  2, -1,  0,  0,  0;
   0,  0,  0, -1,  2, -1,  0,  0;
   0,  0,  0,  0, -1,  2, -1,  0;
   0,  0,  0,  0,  0, -1,  2,  0;
   1,  0,  0,  0,  0,  0,  0,  2]

/-- The `i`-th basis vector `bᵢ` of the E8 lattice: half the `i`-th row of
`doubledBasisMatrix`. -/
noncomputable def basisVector (i : Fin 8) : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 fun j => (doubledBasisMatrix i j : ℝ) / 2

/-- The `j`-th coordinate of `bᵢ` is half the `(i, j)` entry of `doubledBasisMatrix`. -/
@[simp]
theorem basisVector_apply (i j : Fin 8) :
    basisVector i j = (doubledBasisMatrix i j : ℝ) / 2 :=
  (rfl)

/-- Check that `simp` computes a coordinate of a basis vector. -/
example : basisVector 7 3 = 1 / 2 := by simp [doubledBasisMatrix]

/-- Each basis vector `bᵢ` lies in the E8 lattice. -/
theorem basisVector_mem (i : Fin 8) : basisVector i ∈ lattice := by
  refine ⟨doubledBasisMatrix i, fun j => rfl, ?_, ?_⟩
  · unfold Int.ModEq; revert i; decide
  · unfold Int.ModEq; revert i; decide

/-- The doubled basis matrix times its transpose is `4 • gram`, entrywise. -/
private theorem doubledBasisMatrix_mul_transpose :
    ∀ i j, ∑ k, doubledBasisMatrix i k * doubledBasisMatrix j k = 4 * gram i j := by
  decide

/-- The inner product `⟪bᵢ, bⱼ⟫` is the `(i, j)` entry of `gram`. -/
theorem inner_basisVector (i j : Fin 8) :
    ⟪basisVector i, basisVector j⟫_ℝ = gram i j := by
  have h' : (∑ k, (doubledBasisMatrix i k : ℝ) * doubledBasisMatrix j k) = 4 * gram i j := by
    exact_mod_cast doubledBasisMatrix_mul_transpose i j
  simp only [basisVector, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have hterm : ∀ k, (doubledBasisMatrix j k : ℝ) / 2 * ((doubledBasisMatrix i k : ℝ) / 2) =
      (doubledBasisMatrix i k : ℝ) * doubledBasisMatrix j k / 4 := fun k => by ring
  simp_rw [hterm, ← Finset.sum_div, h']
  ring

/-- The `k`-th coordinate of the integer combination `∑ i, cᵢ • bᵢ` is half the `k`-th entry of
the row vector `c` times `doubledBasisMatrix`. -/
theorem sum_smul_basisVector_apply (c : Fin 8 → ℤ) (k : Fin 8) :
    (∑ i, c i • basisVector i) k = ((∑ i, c i * doubledBasisMatrix i k : ℤ) : ℝ) / 2 := by
  simp [basisVector, Finset.sum_div, mul_div_assoc]

/-- The basis vectors `b₀, …, b₇` are linearly independent over `ℤ`. -/
theorem linearIndependent_basisVector : LinearIndependent ℤ basisVector := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hk : ∀ k, ∑ i, g i * doubledBasisMatrix i k = 0 := fun k => by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 8) => v k) hg
    simp only [sum_smul_basisVector_apply, PiLp.zero_apply] at h
    exact_mod_cast (div_eq_zero_iff.mp h).resolve_right two_ne_zero
  -- The coordinate equations form a triangular integer system with only the zero solution.
  have h0 := hk 0; have h1 := hk 1; have h2 := hk 2; have h3 := hk 3
  have h4 := hk 4; have h5 := hk 5; have h6 := hk 6; have h7 := hk 7
  simp [Fin.sum_univ_eight, doubledBasisMatrix] at h0 h1 h2 h3 h4 h5 h6 h7
  intro i
  fin_cases i <;> simp <;> omega

/-- The E8 lattice is the integer span of the basis vectors `b₀, …, b₇`. -/
theorem span_basisVector : Submodule.span ℤ (Set.range basisVector) = lattice := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx => ?_
  · rintro _ ⟨i, rfl⟩
    exact basisVector_mem i
  obtain ⟨a, hxa, hpa, hsa⟩ := hx
  -- With `a i = a 0 + 2 * t i` and `∑ i, a i = 4 * q`, the coefficients of `x = a / 2` are the
  -- entries of `x` times Sphere-Packing-Lean's `E8Inverse`, rewritten in `t` and `q`.
  choose t ht using fun i => (hpa i).symm.dvd
  obtain ⟨q, hq⟩ := hsa.symm.dvd
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨![q - 2 * a 7, t 1 + t 2 + t 3 + t 4 + t 5 + t 6 - 6 * t 7,
    t 2 + t 3 + t 4 + t 5 + t 6 - 5 * t 7, t 3 + t 4 + t 5 + t 6 - 4 * t 7,
    t 4 + t 5 + t 6 - 3 * t 7, t 5 + t 6 - 2 * t 7, t 6 - t 7, a 7], ?_⟩
  ext k
  rw [sum_smul_basisVector_apply, hxa]
  congr 2
  simp only [Fin.sum_univ_eight] at hq
  have h0 := ht 0; have h1 := ht 1; have h2 := ht 2; have h3 := ht 3
  have h4 := ht 4; have h5 := ht 5; have h6 := ht 6; have h7 := ht 7
  fin_cases k <;> simp [Fin.sum_univ_eight, doubledBasisMatrix] <;> omega

/-- The `ℤ`-basis `b₀, …, b₇` of the E8 lattice. -/
noncomputable def basis : Module.Basis (Fin 8) ℤ lattice :=
  (Module.Basis.span linearIndependent_basisVector).map (LinearEquiv.ofEq _ _ span_basisVector)

/-- The `i`-th vector of `basis` is `bᵢ`. -/
@[simp]
theorem coe_basis_apply (i : Fin 8) : (basis i : EuclideanSpace ℝ (Fin 8)) = basisVector i := by
  simp [basis, Module.Basis.span_apply]

/-- Check that `simp` computes the coordinates of the vectors of `basis`. -/
example : (basis 1 : EuclideanSpace ℝ (Fin 8)) 0 = -1 := by simp [doubledBasisMatrix]

/-- The E8 lattice is discrete. -/
instance lattice_discrete : DiscreteTopology lattice := by
  -- A lattice vector `a / 2` of norm less than `1 / 2` has all `|a i| < 1`, so it is zero.
  rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
  refine ⟨1 / 2, by norm_num, fun v hv => ?_⟩
  rw [dist_zero_right] at hv
  obtain ⟨a, hxa, -, -⟩ := v.2
  apply Subtype.ext
  ext i
  have h1 : |(v : EuclideanSpace ℝ (Fin 8)) i| < 1 / 2 :=
    lt_of_le_of_lt (PiLp.norm_apply_le (v : EuclideanSpace ℝ (Fin 8)) i) hv
  rw [hxa, abs_div, abs_two] at h1
  have h2 : |(a i : ℝ)| < 1 := by linarith
  have h3 : |a i| < 1 := by exact_mod_cast h2
  have h4 : a i = 0 := by rw [abs_lt] at h3; omega
  simp [hxa, h4]

/-- The E8 lattice is a full `ℤ`-lattice in `ℝ^8`. -/
instance lattice_isZLattice : IsZLattice ℝ lattice where
  span_top := by
    -- The lattice contains `2 • eᵢ` for every `i`, whose real multiples give the standard basis.
    set S := Submodule.span ℝ (lattice : Set (EuclideanSpace ℝ (Fin 8)))
    rw [eq_top_iff, ← (EuclideanSpace.basisFun (Fin 8) ℝ).toBasis.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : WithLp.toLp 2 (fun j => ((Pi.single i 4 : Fin 8 → ℤ) j : ℝ) / 2) ∈ lattice :=
      ⟨Pi.single i 4, fun j => rfl, by unfold Int.ModEq; revert i; decide, by
        rw [Finset.sum_pi_single']; simp⟩
    have heq : (EuclideanSpace.basisFun (Fin 8) ℝ).toBasis i =
        (1 / 2 : ℝ) • WithLp.toLp 2 (fun j => ((Pi.single i 4 : Fin 8 → ℤ) j : ℝ) / 2) := by
      ext j
      by_cases hj : j = i
      · subst hj; simp; norm_num
      · simp [hj]
    rw [heq]
    exact S.smul_mem _ (Submodule.subset_span hmem)

/-! ### The integral presentation -/

/-- The integral presentation of the E8 lattice given by the basis `b₀, …, b₇` and its Gram
matrix `gram`. -/
noncomputable def integralPresentation : EuclideanLattice.IntegralPresentation lattice :=
  EuclideanLattice.IntegralPresentation.ofBasis basis gram fun i j => by
    rw [coe_basis_apply, coe_basis_apply, inner_basisVector]

/-- The basis of `integralPresentation` is `b₀, …, b₇`. -/
@[simp]
theorem integralPresentation_basis_apply (i : Fin 8) :
    (integralPresentation.basis i : EuclideanSpace ℝ (Fin 8)) = basisVector i := by
  simp [integralPresentation]

/-- The Gram matrix of `integralPresentation` is `gram`. -/
@[simp]
theorem integralPresentation_gram : integralPresentation.gram = gram := by
  simp [integralPresentation]

/-- Check that `simp` evaluates the data of `integralPresentation`. -/
example : integralPresentation.gram 0 7 = 1 ∧
    (integralPresentation.basis 0 : EuclideanSpace ℝ (Fin 8)) = basisVector 0 := by
  simp [gram]

/-! ### Comparison with TauCeti's E8 root lattice -/

/-- The coordinates of the basis vectors `b₀, …, b₇` of the E8 lattice in the simple roots
`α₁, …, α₈` (Bourbaki's numbering) of the E8 root system: the `i`-th row lists the coefficients of
`bᵢ`.  In TauCeti's `typeE₈RootLattice` the simple roots are the standard basis vectors of
`ℚ^8`. -/
def simpleRootCoordinates : Matrix (Fin 8) (Fin 8) ℤ := !![
  0, 1, -1, 0, 0, 0, 0, 0;
  0, 0,  1, 0, 0, 0, 0, 0;
  0, 0,  0, 1, 0, 0, 0, 0;
  0, 0,  0, 0, 1, 0, 0, 0;
  0, 0,  0, 0, 0, 1, 0, 0;
  0, 0,  0, 0, 0, 0, 1, 0;
  0, 0,  0, 0, 0, 0, 0, 1;
  1, 3,  3, 5, 4, 3, 2, 1]

/-- The inverse of `simpleRootCoordinates` over `ℤ`. -/
private def simpleRootCoordinatesInv : Matrix (Fin 8) (Fin 8) ℤ := !![
  -3, -6, -5, -4, -3, -2, -1, 1;
   1,  1,  0,  0,  0,  0,  0, 0;
   0,  1,  0,  0,  0,  0,  0, 0;
   0,  0,  1,  0,  0,  0,  0, 0;
   0,  0,  0,  1,  0,  0,  0, 0;
   0,  0,  0,  0,  1,  0,  0, 0;
   0,  0,  0,  0,  0,  1,  0, 0;
   0,  0,  0,  0,  0,  0,  1, 0]

/-- `simpleRootCoordinatesInv` is a left inverse of `simpleRootCoordinates`. -/
private theorem inv_mul_simpleRootCoordinates :
    simpleRootCoordinatesInv * simpleRootCoordinates = 1 := by decide

/-- `simpleRootCoordinatesInv` is a right inverse of `simpleRootCoordinates`. -/
private theorem simpleRootCoordinates_mul_inv :
    simpleRootCoordinates * simpleRootCoordinatesInv = 1 := by decide

/-- The change of coordinates `simpleRootCoordinates` carries the E8 Cartan matrix to `gram`. -/
private theorem cartan_mul_eq :
    simpleRootCoordinates * CartanMatrix.E 8 * simpleRootCoordinatesᵀ = gram := by
  rw [CartanMatrix.E_eight_eq]
  decide

/-- Entrywise form of `cartan_mul_eq`. -/
private theorem cartan_eq (i j : Fin 8) :
    Matrix.vecMul (simpleRootCoordinates i) (CartanMatrix.E 8) ⬝ᵥ simpleRootCoordinates j =
      gram i j := by
  rw [← cartan_mul_eq]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

/-- Right multiplication of row vectors by `simpleRootCoordinates`, an automorphism of `ℤ^8`. -/
private noncomputable def coordinateEquiv : (Fin 8 → ℤ) ≃ₗ[ℤ] (Fin 8 → ℤ) :=
  LinearEquiv.ofLinearMap (Matrix.vecMulLinear simpleRootCoordinates)
    (Matrix.vecMulLinear simpleRootCoordinatesInv)
    (LinearMap.ext fun w => by
      simp [Matrix.vecMul_vecMul, inv_mul_simpleRootCoordinates])
    (LinearMap.ext fun w => by
      simp [Matrix.vecMul_vecMul, simpleRootCoordinates_mul_inv])

/-- The basis of the Gram lattice of the Cartan matrix whose `i`-th vector has simple-root
coordinates the `i`-th row of `simpleRootCoordinates`. -/
private noncomputable def cartanBasis :
    Module.Basis (Fin 8) ℤ (TauCeti.IntegralLattice.ofGramMatrix (Pi.basisFun ℚ (Fin 8))
      (CartanMatrix.E 8) (CartanMatrix.E_isSymm 8)) :=
  (Pi.basisFun ℤ (Fin 8)).map
    (coordinateEquiv.trans (TauCeti.IntegralLattice.ofGramMatrixBasisFunEquiv _ _))

/-- The `i`-th vector of `cartanBasis` is the `i`-th row of `simpleRootCoordinates`. -/
private theorem coe_cartanBasis (i : Fin 8) :
    (cartanBasis i : Fin 8 → ℚ) = fun j => (simpleRootCoordinates i j : ℚ) := by
  simp [cartanBasis, coordinateEquiv]

/-- The Gram matrix of `cartanBasis` is `gram`. -/
private theorem gramMatrix_cartanBasis :
    (TauCeti.IntegralLattice.ofGramMatrix (Pi.basisFun ℚ (Fin 8))
      (CartanMatrix.E 8) (CartanMatrix.E_isSymm 8)).gramMatrix cartanBasis = gram := by
  ext i j
  apply Int.cast_injective (α := ℚ)
  rw [TauCeti.IntegralLattice.intCast_gramMatrix_apply, coe_cartanBasis, coe_cartanBasis,
    TauCeti.IntegralLattice.form_ofGramMatrix_basisFun_intCast, cartan_eq]

/-- The isometry from the lattice of `integralPresentation` in Gram coordinates to TauCeti's E8
root lattice sending the `i`-th standard basis vector to the vector of simple-root coordinates
`simpleRootCoordinates i` (`integralLatticeIsometry_single`).  The two lattices are described in
different bases, so this is a Gram-preserving isometry, not an equality of coordinates. -/
noncomputable def integralLatticeIsometry :
    TauCeti.IntegralLattice.Isometry integralPresentation.toIntegralLattice
      TauCeti.IntegralLattice.typeE₈RootLattice :=
  ((TauCeti.IntegralLattice.Isometry.ofEq integralPresentation.toIntegralLattice_def).trans
    (TauCeti.IntegralLattice.Isometry.ofGramMatrixEq
      (TauCeti.IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin 8))
        integralPresentation.gram integralPresentation.gram_isSymm)
      cartanBasis
      ((TauCeti.IntegralLattice.gramMatrix_ofGramMatrix _ _ _).trans
        (integralPresentation_gram.trans gramMatrix_cartanBasis.symm)))).trans
    (TauCeti.IntegralLattice.Isometry.ofEq TauCeti.IntegralLattice.typeE₈RootLattice_def.symm)

/-- The isometry `integralLatticeIsometry` sends the `i`-th standard basis vector, the coordinate
vector of `bᵢ`, to the `i`-th row of `simpleRootCoordinates`. -/
@[simp]
theorem integralLatticeIsometry_single (i : Fin 8) :
    integralLatticeIsometry (Pi.single i 1) = fun j => (simpleRootCoordinates i j : ℚ) := by
  have h := TauCeti.IntegralLattice.Isometry.ofGramMatrixEq_apply_basis
    (TauCeti.IntegralLattice.ofGramMatrix.basis (Pi.basisFun ℚ (Fin 8))
      integralPresentation.gram integralPresentation.gram_isSymm)
    cartanBasis
    ((TauCeti.IntegralLattice.gramMatrix_ofGramMatrix _ _ _).trans
      (integralPresentation_gram.trans gramMatrix_cartanBasis.symm)) i
  simp only [TauCeti.IntegralLattice.ofGramMatrix.coe_basis, Pi.basisFun_apply] at h
  rw [integralLatticeIsometry, TauCeti.IntegralLattice.Isometry.trans_apply,
    TauCeti.IntegralLattice.Isometry.trans_apply, TauCeti.IntegralLattice.Isometry.ofEq_apply,
    TauCeti.IntegralLattice.Isometry.ofEq_apply, ← coe_cartanBasis]
  exact h

/-- Check that `simp` evaluates the isometry on a standard basis vector. -/
example : integralLatticeIsometry (Pi.single 7 1) 3 = 5 := by simp [simpleRootCoordinates]

/-- The integral presentation of the E8 lattice is even. -/
@[simp]
theorem integralPresentation_even : integralPresentation.IsEven :=
  integralLatticeIsometry.isEven_iff.mpr TauCeti.IntegralLattice.isEven_typeE₈RootLattice

/-- The integral presentation of the E8 lattice is unimodular.  It is not a `simp` lemma, since
`simp` unfolds unimodularity by `TauCeti.IntegralLattice.isUnimodular_def`; the unfolded form is
the `simp` lemma `integralPresentation_carrier_eq_dualCarrier`. -/
theorem integralPresentation_unimodular : integralPresentation.IsUnimodular :=
  integralLatticeIsometry.isUnimodular_iff.mpr
    TauCeti.IntegralLattice.isUnimodular_typeE₈RootLattice

/-- The lattice of the E8 presentation in Gram coordinates equals its dual lattice: the
unimodularity of the presentation in `simp` normal form. -/
@[simp]
theorem integralPresentation_carrier_eq_dualCarrier :
    integralPresentation.toIntegralLattice.carrier =
      integralPresentation.toIntegralLattice.dualCarrier :=
  integralPresentation.toIntegralLattice.isUnimodular_def.mp integralPresentation_unimodular

/-- Check that `simp` proves that the presentation is even and unimodular. -/
example : integralPresentation.IsEven ∧ integralPresentation.IsUnimodular := by simp

/-! ### Consequences -/

/-- The E8 lattice has covolume one. -/
theorem covolume_lattice : ZLattice.covolume lattice = 1 :=
  integralPresentation.isUnimodular_iff_covolume_eq_one.mp integralPresentation_unimodular

/-- A nonzero vector of the E8 lattice has squared norm at least `2`. -/
theorem two_le_norm_sq_of_mem_lattice {v : EuclideanSpace ℝ (Fin 8)} (hv : v ∈ lattice)
    (hv0 : v ≠ 0) : 2 ≤ ‖v‖ ^ 2 := by
  -- The lattice is even, so the squared norm is `2 * m` with `m` a positive integer.
  obtain ⟨m, hm⟩ :=
    ZLattice.isEven_iff.mp (integralPresentation.isEven_real integralPresentation_even) v hv
  have hpos : 0 < ‖v‖ ^ 2 := by positivity
  rw [hm] at hpos ⊢
  have hm0 : (0 : ℤ) < m := by exact_mod_cast (by linarith : (0 : ℝ) < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  linarith

/-- The basis vector `b₁ = e₁ - e₀` has squared norm `2`. -/
theorem norm_sq_basisVector_one : ‖basisVector 1‖ ^ 2 = 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_basisVector]
  simp [gram]

/-- **The E8 lattice has minimum squared norm `2`**: nonzero lattice vectors have squared norm at
least `2`, and some nonzero lattice vector has squared norm exactly `2`.  This is the roadmap
statement `EuclideanLattice.HasMinNormSq lattice 2` with its definition unfolded. -/
theorem hasMinNormSq :
    (∀ x : lattice, x ≠ 0 → 2 ≤ ‖(x : EuclideanSpace ℝ (Fin 8))‖ ^ 2) ∧
      ∃ x : lattice, x ≠ 0 ∧ ‖(x : EuclideanSpace ℝ (Fin 8))‖ ^ 2 = 2 := by
  refine ⟨fun x hx => two_le_norm_sq_of_mem_lattice x.2 fun h => hx (Subtype.ext h),
    ⟨basisVector 1, basisVector_mem 1⟩, fun h => ?_, norm_sq_basisVector_one⟩
  have h0 : basisVector 1 = 0 := congrArg Subtype.val h
  have h2 := norm_sq_basisVector_one
  rw [h0] at h2
  simp at h2

/-- **The E8 lattice has `240` vectors of squared norm `2`**: TauCeti's enumeration of the roots
of `typeE₈RootLattice`, transported through `integralLatticeIsometry`.  This is the roadmap
statement `Theta.rootCard lattice = 240`, whose definition is this representation number. -/
theorem representationNumber_lattice_two : ZLattice.representationNumber lattice 2 = 240 := by
  rw [ZLattice.representationNumber_def, ← Nat.card_coe_set_eq]
  -- Shells of `lattice` correspond to norm shells of the presentation in Gram coordinates.
  have h := Nat.card_congr (integralPresentation.shellEquiv 2)
  push_cast at h
  rw [h, Nat.card_coe_set_eq, ← TauCeti.IntegralLattice.representationNumber_def,
    integralLatticeIsometry.representationNumber_eq,
    TauCeti.IntegralLattice.representationNumber_typeE₈RootLattice_two]

end SphereCeti.E8
