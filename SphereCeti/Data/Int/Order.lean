/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.Linarith

/-!
# Consecutive-integer quadratic inequalities

The product of consecutive integers is nonnegative. This form is useful when bounding
Gaussian terms in the diagonal Jacobi theta series.
-/

public section

namespace Int

/-- The quadratic `n² + n` is nonnegative for every integer `n`. -/
theorem sq_add_self_nonneg (n : ℤ) : 0 ≤ n ^ 2 + n := by
  have h : 0 ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with hn | hn
    · exact mul_nonneg hn (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos hn.le (by omega)
  nlinarith

end Int
