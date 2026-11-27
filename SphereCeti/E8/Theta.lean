/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.E8.Lattice
public import SphereCeti.Theta.E8

/-!
# The E8 theta series

The theta series of the Euclidean E8 lattice is the normalized weight-four Eisenstein series.
This is the rank-eight even unimodular identity specialized through E8's integral presentation.
-/

public section

namespace SphereCeti.E8

/-- The theta series of E8 is the normalized weight-four Eisenstein series `E₄`. -/
theorem theta_eq_E4 : Theta.latticeTheta lattice = fun τ => Theta.E4 τ :=
  Theta.theta_eq_E4_of_even_unimodular lattice integralPresentation integralPresentation_even
    integralPresentation_unimodular

end SphereCeti.E8
