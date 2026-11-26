/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Exact zero orders of functions of a real variable

A function `f : ℝ → ℂ` has an exact zero of order `m` at `a` when, near `a`, it factors as
`f x = (x - a) ^ m * g x` with a cofactor `g` that is continuous at `a` and does not vanish there.
This is the real-variable form of the local factorization that defines TauCeti's zero
multiplicities `TauCeti.IsZeroMultiplicity` of functions on `ℂ`.  Such a factorization records
more than the vanishing of `f`: it gives a quantitative lower bound `c * |x - a| ^ m ≤ ‖f x‖` near
`a`, with an explicit positive constant `c`.  The zeros of the radial profiles of the E8 and Leech
auxiliary functions are described in this way, so that the bounds remain available for
quantitative stability estimates.

## Main definitions

* `SphereCeti.HasExactZeroOrder f a m`: `f` has an exact zero of order `m` at `a`.

## Main statements

* `SphereCeti.hasExactZeroOrder_iff`: the defining factorization with a continuous nonvanishing
  cofactor.
* `SphereCeti.HasExactZeroOrder.quantitativeLowerBound`: near an exact zero of order `m`, `‖f x‖`
  is bounded below by a positive multiple of `|x - a| ^ m`.
* `SphereCeti.hasExactZeroOrder_one_of_hasDerivAt`: a zero with nonzero derivative has exact
  order one.
* `SphereCeti.HasExactZeroOrder.mul`, `SphereCeti.HasExactZeroOrder.pow`: orders add under
  products and multiply under powers.
* `SphereCeti.HasExactZeroOrder.mul_continuousAt`: a continuous factor nonzero at the basepoint
  preserves the exact order.
## Provenance

The product-factorization proof `HasExactZeroOrder.mul` is adapted from
`TauCeti.IsZeroMultiplicity.mul` in `TauCetiProject/TauCeti` at commit
`83769e442d55cda9d85b3927a93b286831c595ff`, file
`TauCeti/Analysis/Complex/ZeroMultiplicity.lean` (Apache-2.0, Tau Ceti contributors).
The source has complex domain; here the base variable is real and the cofactors are complex.
-/

public section

open Filter
open scoped Topology

namespace SphereCeti

/-- The function `f` has an exact zero of order `m` at `a`: near `a` it factors as
`(x - a) ^ m * g x` with a cofactor `g` continuous at `a` and nonzero there. -/
def HasExactZeroOrder (f : ℝ → ℂ) (a : ℝ) (m : ℕ) : Prop :=
  ∃ g : ℝ → ℂ, ContinuousAt g a ∧ g a ≠ 0 ∧ ∀ᶠ x in 𝓝 a, f x = (x - a) ^ m * g x

variable {f : ℝ → ℂ} {a : ℝ} {m : ℕ}

/-- The function `f` has an exact zero of order `m` at `a` if and only if near `a` it factors as
`(x - a) ^ m * g x` with a cofactor `g` continuous at `a` and nonzero there. -/
theorem hasExactZeroOrder_iff :
    HasExactZeroOrder f a m ↔
      ∃ g : ℝ → ℂ, ContinuousAt g a ∧ g a ≠ 0 ∧ ∀ᶠ x in 𝓝 a, f x = (x - a) ^ m * g x :=
  Iff.rfl

/-- A function continuous and nonzero at `a` has exact order zero there. -/
theorem hasExactZeroOrder_zero (hf : ContinuousAt f a) (hfa : f a ≠ 0) :
    HasExactZeroOrder f a 0 := by
  refine ⟨f, hf, hfa, .of_forall fun x ↦ ?_⟩
  simp

/-- A zero with nonzero derivative has exact order one. -/
theorem hasExactZeroOrder_one_of_hasDerivAt {f' : ℂ}
    (hf : HasDerivAt f f' a) (hfa : f a = 0) (hf' : f' ≠ 0) :
    HasExactZeroOrder f a 1 := by
  -- The divided difference is continuous at the basepoint with value `f'`.
  refine ⟨dslope f a, continuousAt_dslope_same.mpr hf.differentiableAt, ?_, ?_⟩
  · simpa only [dslope_same, hf.deriv] using hf'
  · refine .of_forall fun x ↦ ?_
    simpa only [pow_one, Complex.ofReal_sub, Complex.real_smul] using
      (sub_smul_dslope_of_zero hfa x).symm

/-- Exact zero orders add under products. -/
theorem HasExactZeroOrder.mul {g : ℝ → ℂ} {n : ℕ}
    (hf : HasExactZeroOrder f a m) (hg : HasExactZeroOrder g a n) :
    HasExactZeroOrder (fun x ↦ f x * g x) a (m + n) := by
  obtain ⟨u, hu, hua, hfu⟩ := hf
  obtain ⟨v, hv, hva, hgv⟩ := hg
  refine ⟨fun x ↦ u x * v x, hu.mul hv, mul_ne_zero hua hva, ?_⟩
  filter_upwards [hfu, hgv] with x hfx hgx
  rw [hfx, hgx, pow_add]
  ring

/-- Raising a function to the `k`-th power multiplies its exact zero order by `k`. -/
theorem HasExactZeroOrder.pow (hf : HasExactZeroOrder f a m) (k : ℕ) :
    HasExactZeroOrder (fun x ↦ f x ^ k) a (m * k) := by
  obtain ⟨u, hu, hua, hfu⟩ := hf
  refine ⟨fun x ↦ u x ^ k, hu.pow k, pow_ne_zero _ hua, ?_⟩
  filter_upwards [hfu] with x hx
  simp only [hx, mul_pow, pow_mul]

/-- Multiplying by a function continuous and nonzero at `a` preserves the exact zero order. -/
theorem HasExactZeroOrder.mul_continuousAt {g : ℝ → ℂ}
    (hf : HasExactZeroOrder f a m) (hg : ContinuousAt g a) (hga : g a ≠ 0) :
    HasExactZeroOrder (fun x ↦ f x * g x) a m := by
  simpa using hf.mul (hasExactZeroOrder_zero hg hga)

/-- Near an exact zero of order `m`, `‖f x‖` is at least a positive multiple of `|x - a| ^ m`. -/
theorem HasExactZeroOrder.quantitativeLowerBound (h : HasExactZeroOrder f a m) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in 𝓝 a, c * |x - a| ^ m ≤ ‖f x‖ := by
  obtain ⟨g, hg, hga, hfg⟩ := hasExactZeroOrder_iff.mp h
  have hpos : 0 < ‖g a‖ := norm_pos_iff.mpr hga
  refine ⟨‖g a‖ / 2, half_pos hpos, ?_⟩
  -- The cofactor stays away from zero near `a`.
  have hnear : ∀ᶠ x in 𝓝 a, ‖g a‖ / 2 < ‖g x‖ :=
    hg.norm.eventually (lt_mem_nhds (half_lt_self hpos))
  filter_upwards [hfg, hnear] with x hx hgx
  simp only [hx, ← Complex.ofReal_sub, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  nlinarith [pow_nonneg (abs_nonneg (x - a)) m]

end SphereCeti
