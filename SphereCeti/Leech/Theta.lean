/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Lattice.Theta
public import SphereCeti.Leech.Presentation
public import SphereCeti.Leech.Shells

/-!
# The theta series of the Euclidean Leech lattice

The even unimodular presentation and the absence of norm-two vectors identify the theta
series of the actual Euclidean Leech lattice with `E₄³ - 720 Δ`. This is the concrete
Layer 5 Leech theta target (MIGRATION G3), using TauCeti's modular forms directly.

This independently written specialization follows the target in
`SphereCetiRoadmap/Suggested.lean` at `4ce30e4e79aa0e810e81ea38371b3fb41c2a5f6e`.
The general identity comes from `TauCetiProject/TauCeti` at
`83769e442d55cda9d85b3927a93b286831c595ff`,
`TauCeti/NumberTheory/ModularForms/ThetaSeries/RankTwentyFour.lean`.
-/

public section

namespace SphereCeti.Leech

/-- The Leech theta identity, with the rootless coefficient `-720`. -/
theorem theta_eq_E4_cubed_sub_720_Delta :
    ZLattice.thetaSeries lattice = fun τ ↦
      (ModularForm.E₄ τ) ^ 3 - 720 * ModularForm.discriminant τ :=
  integralPresentation.thetaSeries_rank24_rootless_eq_E4_cubed_sub_mul_discriminant
    integralPresentation_even integralPresentation_unimodular representationNumber_lattice_two

example (τ : UpperHalfPlane) :
    ZLattice.thetaSeries lattice τ =
      (ModularForm.E₄ τ) ^ 3 - 720 * ModularForm.discriminant τ :=
  congrFun theta_eq_E4_cubed_sub_720_Delta τ

end SphereCeti.Leech
