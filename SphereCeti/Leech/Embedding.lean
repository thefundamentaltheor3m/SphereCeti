/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Basic

/-!
# The isometric embedding of the Leech coordinates into `ℝ^24`

TauCeti's Leech lattice `TauCeti.leechLattice` lives in `ℚ^24`, with points `a / 2` for integral
`a` and form half the dot product.  This file defines the additive map `x ↦ x / √2` into the
packing space `EuclideanSpace ℝ (Fin 24)` and proves that it carries that form to the inner
product, and the point `a / 2` to `a / √8`.

## Main definitions and results

* `SphereCeti.Leech.embedding`: the roadmap's `SphereCeti.Suggested.Leech.embedding`, with the
  same formula.
* `SphereCeti.Leech.inner_embedding` and `SphereCeti.Leech.embedding_div_two`: the roadmap targets
  of the same names.  The roadmap's `integralLattice` abbreviates `TauCeti.leechLattice`, which
  is written directly here.

This is an independent formalization; no proof text is adapted from another repository.
-/

public section

open scoped InnerProductSpace

namespace SphereCeti.Leech

/-- The isometric embedding `x ↦ x / √2` of TauCeti's rational Leech coordinates into the packing
space.  It carries the form of `TauCeti.leechLattice` to the inner product and `a / 2` to
`a / √8`.  It is an isometric embedding of the rational lattice, not a real-linear
equivalence. -/
@[expose]
noncomputable def embedding : (Fin 24 → ℚ) →+ EuclideanSpace ℝ (Fin 24) where
  toFun x := WithLp.toLp 2 fun i => (x i : ℝ) / Real.sqrt 2
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [add_div]

theorem embedding_apply (x : Fin 24 → ℚ) (i : Fin 24) :
    embedding x i = (x i : ℝ) / Real.sqrt 2 :=
  rfl

/-- The embedding carries the form of the canonical Leech lattice to the inner product. -/
theorem inner_embedding (x y : Fin 24 → ℚ) :
    ⟪embedding x, embedding y⟫_ℝ = (TauCeti.leechLattice.form x y : ℝ) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [TauCeti.leechLattice_form, TauCeti.ConstructionA.form_apply,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, embedding_apply, star_trivial, Rat.cast_div, Rat.cast_sum, Rat.cast_mul,
    Nat.cast_ofNat, Rat.cast_ofNat, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_mul_div_comm, h2, mul_comm]

/-- The point `a / 2` of TauCeti's coordinates is the point `a / √8` of the packing space. -/
theorem embedding_div_two (a : Fin 24 → ℤ) :
    embedding (fun i => (a i : ℚ) / 2) = WithLp.toLp 2 fun i => (a i : ℝ) / Real.sqrt 8 := by
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  ext i
  simp only [embedding_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, h8, div_div]

end SphereCeti.Leech
