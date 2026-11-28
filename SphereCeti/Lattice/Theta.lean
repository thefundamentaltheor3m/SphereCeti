/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Lattice.IntegralPresentation
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Eisenstein
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.RankTwentyFour

/-!
# Theta identities through integral presentations

The evenness and unimodularity of a Gram presentation transport to TauCeti's real lattice
predicates. Its theta identities then give the rank-eight identity and the rank-twenty-four
identity, including the rootless specialization, directly for the presented Euclidean lattice.

These are the three Layer 5 corollaries (MIGRATION G3). The statements use TauCeti's theta
series, Eisenstein series, discriminant and representation numbers directly. No second theta
series or root-count definition is introduced.

The proofs specialize the corresponding Layer 5 proofs in
`SphereCetiRoadmap/Suggested.lean` at `4ce30e4e79aa0e810e81ea38371b3fb41c2a5f6e`, now using
the admission-free presentation bridge. The underlying identities are from
`TauCetiProject/TauCeti@83769e442d55cda9d85b3927a93b286831c595ff`,
`TauCeti/NumberTheory/ModularForms/ThetaSeries/{Eisenstein,RankTwentyFour}.lean`.
-/

public section

namespace SphereCeti.EuclideanLattice.IntegralPresentation

/-- The theta series of an even unimodular rank-eight presentation is `E₄`. -/
theorem thetaSeries_eq_E4 {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 8))}
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (P : IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    ZLattice.thetaSeries Λ = fun τ ↦ ModularForm.E₄ τ := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 8)) = 8 := finrank_euclideanSpace_fin
  have he := P.isEven_real heven
  rw [← ZLattice.coe_thetaForm he (P.isUnimodular_real hunimodular) (k := 4) hn,
    he.thetaForm_eq_E₄ _ hn]

/-- In rank twenty-four the coefficient of `Δ` is the norm-two root count minus `720`. -/
theorem thetaSeries_rank24_eq_E4_cubed_add_mul_discriminant
    {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 24))}
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (P : IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    ZLattice.thetaSeries Λ = fun τ ↦
      (ModularForm.E₄ τ) ^ 3 +
        ((ZLattice.representationNumber Λ 2 : ℂ) - 720) * ModularForm.discriminant τ := by
  funext τ
  exact (P.isEven_real heven).thetaSeries_eq_E₄_cube_add_mul_discriminant
    (P.isUnimodular_real hunimodular) finrank_euclideanSpace_fin τ

/-- With no norm-two vectors, the rank-twenty-four theta series is `E₄³ - 720 Δ`. -/
theorem thetaSeries_rank24_rootless_eq_E4_cubed_sub_mul_discriminant
    {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 24))}
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (P : IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular)
    (hrootless : ZLattice.representationNumber Λ 2 = 0) :
    ZLattice.thetaSeries Λ = fun τ ↦
      (ModularForm.E₄ τ) ^ 3 - 720 * ModularForm.discriminant τ := by
  rw [P.thetaSeries_rank24_eq_E4_cubed_add_mul_discriminant heven hunimodular, hrootless]
  funext τ
  push_cast
  ring

example {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 8))}
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (P : IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) (τ : UpperHalfPlane) :
    ZLattice.thetaSeries Λ τ = ModularForm.E₄ τ :=
  congrFun (P.thetaSeries_eq_E4 heven hunimodular) τ

end SphereCeti.EuclideanLattice.IntegralPresentation
