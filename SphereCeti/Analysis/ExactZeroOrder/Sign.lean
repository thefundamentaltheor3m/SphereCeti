/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.ExactZeroOrder
public import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic

/-!
# The parity of a zero of a nonnegative profile

A complex-valued function of a real variable which is locally real and nonnegative
can only have an even exact zero order. The continuous nonvanishing cofactor has
nonnegative right limit; an odd order would also force its left limit to be nonpositive.

The proof is independent of analytic or differentiability hypotheses.
-/

public section

open Filter
open scoped Topology ComplexOrder

namespace SphereCeti

/-- A locally nonnegative real-valued profile has even exact zero order.
The scoped complex order records both reality and nonnegativity. -/
theorem HasExactZeroOrder.even_of_nonneg {f : ℝ → ℂ} {a : ℝ} {m : ℕ}
    (h : HasExactZeroOrder f a m) (hf : ∀ᶠ x in 𝓝 a, 0 ≤ f x) : Even m := by
  by_contra hm
  have hodd : Odd m := (Nat.even_or_odd m).resolve_left hm
  obtain ⟨g, hg, hga, hfg⟩ := hasExactZeroOrder_iff.mp h
  have hright : ∀ᶠ x in 𝓝[>] a, 0 ≤ g x := by
    filter_upwards [hfg.filter_mono nhdsWithin_le_nhds,
      hf.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hfx hxa
    have hr : 0 < (x - a) ^ m := pow_pos (sub_pos.mpr hxa) m
    have he : f x = ((x - a) ^ m : ℝ) • g x := by
      simpa only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_sub] using hx
    have hp : 0 ≤ (((x - a) ^ m)⁻¹ : ℝ) • f x :=
      smul_nonneg (inv_nonneg.mpr hr.le) hfx
    rwa [he, inv_smul_smul₀ hr.ne'] at hp
  have hleft : ∀ᶠ x in 𝓝[<] a, g x ≤ 0 := by
    filter_upwards [hfg.filter_mono nhdsWithin_le_nhds,
      hf.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx hfx hxa
    have hr : 0 < -((x - a) ^ m) := neg_pos.mpr (hodd.pow_neg_iff.mpr (sub_neg.mpr hxa))
    have he : f x = (-((x - a) ^ m) : ℝ) • (-g x) := by
      simpa only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_pow,
        Complex.ofReal_sub, neg_mul_neg] using hx
    have hp : 0 ≤ ((-((x - a) ^ m))⁻¹ : ℝ) • f x :=
      smul_nonneg (inv_nonneg.mpr hr.le) hfx
    rw [he, inv_smul_smul₀ hr.ne'] at hp
    exact neg_nonneg.mp hp
  have hge : 0 ≤ g a := isClosed_Ici.mem_of_tendsto
    (hg.tendsto.mono_left nhdsWithin_le_nhds) hright
  have hle : g a ≤ 0 := isClosed_Iic.mem_of_tendsto
    (hg.tendsto.mono_left nhdsWithin_le_nhds) hleft
  exact hga (le_antisymm hle hge)

-- A simple zero is incompatible with a nonnegative neighborhood on both sides.
example {f : ℝ → ℂ} {a : ℝ} (h : HasExactZeroOrder f a 1)
    (hf : ∀ᶠ x in 𝓝 a, 0 ≤ f x) : False := by
  have he := h.even_of_nonneg hf
  norm_num at he

end SphereCeti
