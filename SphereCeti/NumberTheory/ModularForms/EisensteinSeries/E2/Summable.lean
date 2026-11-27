/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The `q`-expansion of `E₂`

## Main statements

* `EisensteinSeries.analyticAt_cuspFunction_E2`: the cusp function of `E₂` of width `1` is analytic
  at `0`.
* `EisensteinSeries.E2_qExpansion_coeff`: the `q`-coefficients of `E₂` are `1` and `-24 σ₁(m)` for
  `m ≥ 1`.
-/

public section

open UpperHalfPlane
open scoped ArithmeticFunction.sigma

namespace EisensteinSeries

/-- The cusp function of `E₂` of width `1` is analytic at `0`. -/
theorem analyticAt_cuspFunction_E2 : AnalyticAt ℂ (cuspFunction 1 E2) 0 :=
  analyticAt_cuspFunction_zero one_pos E2_periodic E2_mdifferentiable isBoundedAtImInfty_E2

/-- The `q`-coefficients of `E₂` are `1` and `-24 σ₁(m)` for `m ≥ 1`. -/
theorem E2_qExpansion_coeff (m : ℕ) :
    (qExpansion 1 E2).coeff m = if m = 0 then 1 else -24 * (σ 1 m : ℂ) :=
  (TauCeti.UpperHalfPlane.qExpansion_coeff_unique
    (c := fun m ↦ if m = 0 then 1 else -24 * (σ 1 m : ℂ)) one_pos analyticAt_cuspFunction_E2
    (fun τ ↦ by simpa only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
      using hasSum_qExpansion_E2 (z := τ)) m).symm

end EisensteinSeries
