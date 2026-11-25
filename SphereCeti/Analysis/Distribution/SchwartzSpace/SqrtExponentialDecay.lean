/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Schwartz functions from square-root exponential derivative bounds

Decay of the form `exp (-b √‖x‖)` dominates every polynomial weight. Thus a smooth function
whose iterated derivatives satisfy such cocompact bounds is Schwartz. Each derivative may
have its own positive rate, and the domain need not be finite dimensional.

These bounds arise for Laplace profiles with a cusp factor `exp (-a/t)`: balancing it against
`exp (-r t)` produces decay in `√r`. The statement assumes smoothness of the function, not of
the square-root majorant at the origin.
-/

public section

open Filter Topology Asymptotics
open scoped ContDiff SchwartzMap

namespace SchwartzMap

private lemma pow_mul_exp_neg_sqrt_le {b r : ℝ} (hb : 0 < b) (hr : 0 ≤ r) (k : ℕ) :
    r ^ k * Real.exp (-b * Real.sqrt r) ≤ ((2 * k).factorial : ℝ) / b ^ (2 * k) := by
  have hp := Real.pow_div_factorial_le_exp (x := b * Real.sqrt r)
    (mul_nonneg hb.le (Real.sqrt_nonneg r)) (2 * k)
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 * k).factorial)] at hp
  have hsq : (Real.sqrt r) ^ (2 * k) = r ^ k := by rw [pow_mul, Real.sq_sqrt hr]
  apply (le_div_iff₀ (pow_pos hb (2 * k))).mpr
  calc
    r ^ k * Real.exp (-b * Real.sqrt r) * b ^ (2 * k) =
        (b * Real.sqrt r) ^ (2 * k) * Real.exp (-b * Real.sqrt r) := by
      rw [mul_pow, hsq]
      ring
    _ ≤ Real.exp (b * Real.sqrt r) * (2 * k).factorial * Real.exp (-b * Real.sqrt r) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = (2 * k).factorial := by
      rw [mul_right_comm, ← Real.exp_add,
        show b * Real.sqrt r + -b * Real.sqrt r = 0 by ring]
      simp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Construct a Schwartz function from square-root exponential cocompact bounds on all
iterated derivatives. The positive rate may depend on the derivative order. -/
@[expose]
noncomputable def mkOfSqrtExponentialDecay (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ n : ℕ, ∃ b : ℝ, 0 < b ∧
      (iteratedFDeriv ℝ n f) =O[cocompact E] (fun x ↦ Real.exp (-b * Real.sqrt ‖x‖))) :
    𝓢(E, F) :=
  mkOfCocompact f smooth fun k n ↦ by
    obtain ⟨b, hb, hdecay⟩ := decay n
    obtain ⟨C, hC, hbound⟩ := hdecay.exists_nonneg
    refine ⟨C * (((2 * k).factorial : ℝ) / b ^ (2 * k)), ?_⟩
    filter_upwards [hbound.bound] with x hx
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at hx
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
          ‖x‖ ^ k * (C * Real.exp (-b * Real.sqrt ‖x‖)) :=
        mul_le_mul_of_nonneg_left hx (pow_nonneg (norm_nonneg x) k)
      _ = C * (‖x‖ ^ k * Real.exp (-b * Real.sqrt ‖x‖)) := by ring
      _ ≤ C * (((2 * k).factorial : ℝ) / b ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left (pow_mul_exp_neg_sqrt_le hb (norm_nonneg x) k) hC

/-- Evaluation of the Schwartz function constructed from square-root exponential bounds. -/
@[simp]
theorem mkOfSqrtExponentialDecay_apply (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ n : ℕ, ∃ b : ℝ, 0 < b ∧
      (iteratedFDeriv ℝ n f) =O[cocompact E] (fun x ↦ Real.exp (-b * Real.sqrt ‖x‖))) (x : E) :
    mkOfSqrtExponentialDecay f smooth decay x = f x := rfl

example {G : Type*} (h : F → G) (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ n : ℕ, ∃ b : ℝ, 0 < b ∧
      (iteratedFDeriv ℝ n f) =O[cocompact E] (fun x ↦ Real.exp (-b * Real.sqrt ‖x‖))) (x : E) :
    h (mkOfSqrtExponentialDecay f smooth decay x) = h (f x) := by simp

end SchwartzMap
