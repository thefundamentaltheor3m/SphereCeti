/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A rescaled arithmetic-geometric mean inequality

For nonnegative `a`, `b` and a positive scale `t`, the sum `a / t + b t` is at least
`2 √a √b`. This balances reciprocal and linear terms, including exponential decay rates.
-/

public section

namespace Real

/-- A positive rescaling preserves the arithmetic-geometric mean lower bound. -/
theorem two_mul_sqrt_mul_sqrt_le_div_add_mul {a b t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) :
    2 * sqrt a * sqrt b ≤ a / t + b * t := by
  have hs : (sqrt b * t) ^ 2 = b * t ^ 2 := by
    rw [mul_pow, sq_sqrt hb]
  have h := sq_nonneg (sqrt a - sqrt b * t)
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith [sq_sqrt ha, div_mul_cancel₀ a ht.ne']

end Real
