/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Complex.Basic

/-!
# Exact local zero orders of radial profiles

A function `f : ℝ → ℂ` has an exact zero of order `m` at `a` when, near `a`, it factors as
`f x = (x - a) ^ m * g x` with a cofactor `g` that is continuous at `a` and does not vanish there.
Such a factorization records more than the vanishing of `f`: it gives a quantitative lower bound
`c * |x - a| ^ m ≤ ‖f x‖` near `a`, with an explicit positive constant `c`.  Zeros of the profiles
of the E8 and Leech auxiliary functions are described in this way, so that the bounds remain
available for quantitative stability estimates.

## Main definitions

* `SphereCeti.MagicFunction.HasExactZeroOrder f a m`: `f` has an exact zero of order `m` at `a`.

## Main statements

* `SphereCeti.MagicFunction.HasExactZeroOrder.quantitativeLowerBound`: near an exact zero of
  order `m`, `‖f x‖` is bounded below by a positive multiple of `|x - a| ^ m`.
-/

public section

open Filter
open scoped Topology

namespace SphereCeti.MagicFunction

/-- The function `f` has an exact zero of order `m` at `a`: near `a` it factors as
`(x - a) ^ m * g x` with a cofactor `g` continuous at `a` and nonzero there. -/
def HasExactZeroOrder (f : ℝ → ℂ) (a : ℝ) (m : ℕ) : Prop :=
  ∃ g : ℝ → ℂ, ContinuousAt g a ∧ g a ≠ 0 ∧ ∀ᶠ x in 𝓝 a, f x = (x - a) ^ m * g x

/-- Near an exact zero of order `m`, `‖f x‖` is at least a positive multiple of `|x - a| ^ m`. -/
theorem HasExactZeroOrder.quantitativeLowerBound {f : ℝ → ℂ} {a : ℝ} {m : ℕ}
    (h : HasExactZeroOrder f a m) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in 𝓝 a, c * |x - a| ^ m ≤ ‖f x‖ := by
  obtain ⟨g, hg, hga, hfg⟩ := h
  have hpos : 0 < ‖g a‖ := norm_pos_iff.mpr hga
  refine ⟨‖g a‖ / 2, half_pos hpos, ?_⟩
  -- The cofactor stays away from zero near `a`.
  have hnear : ∀ᶠ x in 𝓝 a, ‖g a‖ / 2 < ‖g x‖ :=
    hg.norm.eventually (lt_mem_nhds (half_lt_self hpos))
  filter_upwards [hfg, hnear] with x hx hgx
  simp only [hx, ← Complex.ofReal_sub, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [pow_nonneg (abs_nonneg (x - a)) m]

end SphereCeti.MagicFunction
