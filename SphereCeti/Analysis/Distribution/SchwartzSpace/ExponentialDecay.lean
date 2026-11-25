/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Analysis.Asymptotics.Basic

/-!
# Schwartz functions from exponential derivative bounds

A smooth function is Schwartz if every iterated derivative has exponential decay outside
compact sets. Each derivative may have its own positive decay rate. The construction works
on any real normed space, without a finite-dimensionality assumption.

The proof uses Mathlib's exponential-series bound to dominate all polynomial weights, then
`SchwartzMap.mkOfCocompact` to extend the resulting bounds across the compact exceptions.
-/

public section

open Filter Topology Asymptotics
open scoped ContDiff SchwartzMap

namespace SchwartzMap

private theorem pow_mul_exp_neg_le {b : ℝ} (hb : 0 < b) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ k * Real.exp (-b * r) ≤ (k.factorial : ℝ) / b ^ k := by
  have hk : 0 < (k.factorial : ℝ) := by positivity
  have hp : (b * r) ^ k ≤ (k.factorial : ℝ) * Real.exp (b * r) := by
    simpa only [mul_comm (Real.exp (b * r))] using
      (div_le_iff₀ hk).mp (Real.pow_div_factorial_le_exp (x := b * r) (mul_nonneg hb.le hr) k)
  apply (le_div_iff₀ (pow_pos hb k)).mpr
  calc
    r ^ k * Real.exp (-b * r) * b ^ k = (b * r) ^ k * Real.exp (-b * r) := by
      rw [mul_pow]
      ring
    _ ≤ (k.factorial : ℝ) * Real.exp (b * r) * Real.exp (-b * r) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
    _ = (k.factorial : ℝ) := by
      rw [mul_assoc, ← Real.exp_add, show b * r + -b * r = 0 by ring,
        Real.exp_zero, mul_one]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Construct a Schwartz function from exponential cocompact bounds on every derivative.
The positive exponential rate is allowed to depend on the derivative order. -/
@[expose]
noncomputable def mkOfExponentialDecay (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ n : ℕ, ∃ b : ℝ, 0 < b ∧
      (iteratedFDeriv ℝ n f) =O[cocompact E] (fun x => Real.exp (-b * ‖x‖))) : 𝓢(E, F) :=
  mkOfCocompact f smooth fun k n => by
    obtain ⟨b, hb, hdecay⟩ := decay n
    obtain ⟨C, hC, hbound⟩ := hdecay.exists_nonneg
    refine ⟨C * ((k.factorial : ℝ) / b ^ k), ?_⟩
    filter_upwards [hbound.bound] with x hx
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)] at hx
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ ‖x‖ ^ k * (C * Real.exp (-b * ‖x‖)) :=
        mul_le_mul_of_nonneg_left hx (pow_nonneg (norm_nonneg x) k)
      _ = C * (‖x‖ ^ k * Real.exp (-b * ‖x‖)) := by ring
      _ ≤ C * ((k.factorial : ℝ) / b ^ k) :=
        mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le hb k (norm_nonneg x)) hC

/-- Evaluation of a Schwartz function constructed from exponential derivative bounds. -/
@[simp]
theorem mkOfExponentialDecay_apply (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ n : ℕ, ∃ b : ℝ, 0 < b ∧
      (iteratedFDeriv ℝ n f) =O[cocompact E] (fun x => Real.exp (-b * ‖x‖))) (x : E) :
    mkOfExponentialDecay f smooth decay x = f x := rfl

-- The evaluation rule works inside another function without exposing decay witnesses.
example {G : Type*} (h : F → G) (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ n : ℕ, ∃ b : ℝ, 0 < b ∧
      (iteratedFDeriv ℝ n f) =O[cocompact E] (fun x => Real.exp (-b * ‖x‖))) (x : E) :
    h (mkOfExponentialDecay f smooth decay x) = h (f x) := by simp

end SchwartzMap
