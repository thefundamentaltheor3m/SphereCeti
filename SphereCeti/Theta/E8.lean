/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Lattice.IntegralPresentation
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Eisenstein

/-!
# Theta series of rank-eight even unimodular lattices

TauCeti identifies the theta form of every rank-eight even unimodular lattice with the normalized
weight-four Eisenstein series.  This module transports that identity through a Euclidean lattice's
integral presentation.
-/

public section

open MatrixGroups UpperHalfPlane
open scoped ModularForm

namespace SphereCeti.Theta

/-- The theta series of a Euclidean lattice. -/
noncomputable abbrev latticeTheta {d : ℕ}
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) : UpperHalfPlane → ℂ :=
  ZLattice.thetaSeries Λ

/-- The normalized weight-four Eisenstein series. -/
noncomputable def E4 : ModularForm 𝒮ℒ 4 := ModularForm.E₄

/-- The theta series of a rank-eight even unimodular Euclidean lattice is `E₄`. -/
theorem theta_eq_E4_of_even_unimodular
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 8))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    latticeTheta Λ = fun τ => E4 τ := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 8 := finrank_euclideanSpace_fin
  have he := P.isEven_real heven
  rw [latticeTheta, ← ZLattice.coe_thetaForm he (P.isUnimodular_real hunimodular) (k := 4) hn,
    he.thetaForm_eq_E₄ _ hn]
  rfl

end SphereCeti.Theta
