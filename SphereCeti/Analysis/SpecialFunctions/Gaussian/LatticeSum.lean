/-
Copyright (c) 2026 Sphere-Packing-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sphere-Packing-Lean contributors, Bakhyt Momunov
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.LatticeSum

/-!
# Positivity of the complex Gaussian lattice series

The shifted Gaussian series is positive as a complex number whenever its real rate is positive.
The complex-to-real conversion follows `SpherePacking/ModularForms/JacobiTheta/Basic.lean` in
`thefundamentaltheor3m/Sphere-Packing-Lean@bad3de916074748eb88b7d1ee6dbf9494361ad17`
(Apache-2.0). Positivity is an application of TauCeti's Gaussian lattice-sum API.
-/

public section

open scoped ComplexOrder

namespace Complex

/-- A shifted Gaussian lattice series is a positive real complex number. -/
theorem tsum_exp_shifted_gaussian_pos (s t : ℝ) (ht : 0 < t) :
    0 < ∑' n : ℤ, exp (Real.pi * I * (n + (s : ℂ)) ^ 2 * (I * t)) := by
  have he (n : ℤ) : exp (Real.pi * I * (n + (s : ℂ)) ^ 2 * (I * t)) =
      (Real.exp (-Real.pi * ((n : ℝ) + s) ^ 2 * t) : ℝ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring_nf
    rw [I_sq]
    ring
  simp_rw [he]
  rw [← ofReal_tsum, zero_lt_real]
  have hw : 0 < 1 / (2 * Real.pi * t) := by positivity
  have hpos := Real.gaussianLatticeSum_pos (-s) (Real.sqrt_pos.mpr hw).ne'
  rw [Real.gaussianLatticeSum_def] at hpos
  convert hpos using 1
  apply tsum_congr
  intro n
  congr 1
  rw [sub_neg_eq_add, Real.sq_sqrt hw.le]
  field_simp

end Complex
