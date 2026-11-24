/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Real
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Basic

/-!
# The isometric embedding of the Leech coordinates into `ℝ^24`

TauCeti's Leech lattice `TauCeti.leechLattice` lives in `ℚ^24`: its points are the vectors `a / 2`
with `a` integral, and its form is half the dot product, which is the binary Construction A form
`TauCeti.ConstructionA.form 2`.  Dividing every coordinate by `√2` carries this form to the
ordinary dot product.  This file packages that normalization as an additive map into the packing
space `EuclideanSpace ℝ (Fin 24)`.

## Main definitions and results

* `SphereCeti.Leech.embedding`: the map `x ↦ x / √2` from `ℚ^24` to `EuclideanSpace ℝ (Fin 24)`.
* `SphereCeti.Leech.embedding_apply`: its `i`-th coordinate is `(x i : ℝ) / √2`.
* `SphereCeti.Leech.embedding_injective`: the embedding is injective.
* `SphereCeti.Leech.inner_embedding`: the inner product of two embedded vectors is the Leech form
  of their preimages.
* `SphereCeti.Leech.norm_embedding_sq`: the squared norm of an embedded vector is the Leech norm
  of its preimage.
* `SphereCeti.Leech.embedding_div_two`: the point `a / 2` of `ℚ^24` is sent to `a / √8`.

## Source

The embedding is TauCeti's real Construction A normalization
`TauCeti.ConstructionA.realEmbedding 2` (repository `TauCetiProject/TauCeti`, commit
`83769e442d55cda9d85b3927a93b286831c595ff`, file
`TauCeti/LinearAlgebra/IntegralLattice/ConstructionA/Real.lean`), followed by the identification
of `Fin 24 → ℝ` with the Euclidean space; its injectivity and dot-product identity are taken from
the same file.  The Leech lattice itself is TauCeti's
`TauCeti/LinearAlgebra/IntegralLattice/Rank24/Leech/Basic.lean` at the same commit.
-/

public section

open scoped InnerProductSpace

namespace SphereCeti.Leech

/-- The isometric embedding `x ↦ x / √2` of TauCeti's rational Leech coordinates into the packing
space.  It carries the form of `TauCeti.leechLattice` to the inner product and `a / 2` to
`a / √8`.  It is an isometric embedding of the rational lattice, not a real-linear
equivalence. -/
noncomputable def embedding : (Fin 24 → ℚ) →+ EuclideanSpace ℝ (Fin 24) :=
  ((WithLp.linearEquiv 2 ℚ (Fin 24 → ℝ)).symm.toLinearMap.comp
    (TauCeti.ConstructionA.realEmbedding 2)).toAddMonoidHom

/-- The embedding is TauCeti's normalization `realEmbedding 2` read in Euclidean coordinates. -/
theorem embedding_eq_toLp_realEmbedding (x : Fin 24 → ℚ) :
    embedding x = WithLp.toLp 2 (TauCeti.ConstructionA.realEmbedding 2 x) :=
  (rfl)

/-- The `i`-th coordinate of `embedding x` is the rational coordinate `x i`, cast to `ℝ` and
divided by `√2`. -/
@[simp]
theorem embedding_apply (x : Fin 24 → ℚ) (i : Fin 24) :
    embedding x i = (x i : ℝ) / Real.sqrt 2 := by
  rw [embedding_eq_toLp_realEmbedding, PiLp.toLp_apply,
    TauCeti.ConstructionA.realEmbedding_apply, Nat.cast_ofNat]

example (i : Fin 24) : embedding 0 i = 0 := by simp

/-- The embedding is injective. -/
theorem embedding_injective : Function.Injective embedding := fun x y h =>
  TauCeti.ConstructionA.realEmbedding_injective 2 <| WithLp.toLp_injective 2 <| by
    rwa [embedding_eq_toLp_realEmbedding, embedding_eq_toLp_realEmbedding] at h

/-- The embedding carries the form of the canonical Leech lattice to the inner product. -/
theorem inner_embedding (x y : Fin 24 → ℚ) :
    ⟪embedding x, embedding y⟫_ℝ = (TauCeti.leechLattice.form x y : ℝ) := by
  rw [TauCeti.leechLattice_form, ← TauCeti.ConstructionA.dotProduct_realEmbedding,
    EuclideanSpace.inner_eq_star_dotProduct, embedding_eq_toLp_realEmbedding,
    embedding_eq_toLp_realEmbedding, star_trivial, dotProduct_comm]

/-- The squared norm of an embedded vector is the Leech norm of its preimage. -/
theorem norm_embedding_sq (y : Fin 24 → ℚ) :
    ‖embedding y‖ ^ 2 = (TauCeti.leechLattice.form y y : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_embedding]

/-- The point `a / 2` of TauCeti's coordinates is the point `a / √8` of the packing space. -/
theorem embedding_div_two (a : Fin 24 → ℤ) :
    embedding (fun i => (a i : ℚ) / 2) = WithLp.toLp 2 fun i => (a i : ℝ) / Real.sqrt 8 := by
  -- `√8 = √(2 ^ 2 * 2) = 2 * √2`, so dividing by `2` and then by `√2` is dividing by `√8`.
  have h8' : (8 : ℝ) = 2 ^ 2 * 2 := by norm_num
  have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [h8', Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  ext i
  simp only [embedding_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, h8, div_div]

end SphereCeti.Leech
