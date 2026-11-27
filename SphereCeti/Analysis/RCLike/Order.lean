/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Positivity of quotients of real or complex numbers

For the order in which a positive element is real and strictly positive, a quotient
of two positive elements is positive. The same interface applies to both `ℝ` and `ℂ`.
-/

public section

open scoped ComplexOrder

namespace RCLike

/-- The quotient of two positive elements is positive in the real order on `ℝ` or `ℂ`. -/
theorem div_pos_of_pos {K : Type*} [RCLike K] {a b : K} (ha : 0 < a) (hb : 0 < b) :
    0 < a / b := by
  rw [div_eq_mul_inv]
  exact mul_pos ha (RCLike.inv_pos_of_pos hb)

end RCLike
