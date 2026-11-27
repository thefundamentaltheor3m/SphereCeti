/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Asymptotic estimates for differences of powers

A bound for `f - c` at a finite limit gives the same asymptotic rate for every
`fⁿ - cⁿ`. This controls errors of polynomial expressions without specializing
the filter, comparison function or limiting value.
-/

public section

open Filter Asymptotics
open scoped Topology

namespace Asymptotics

/-- At a finite limit, taking a natural power preserves a big-O error bound. -/
theorem IsBigO.pow_sub_pow_of_tendsto {α R : Type*} [NormedCommRing R] {l : Filter α} {f : α → R} {g : α → ℝ}
    {c : R} (hO : (fun x ↦ f x - c) =O[l] g) (hf : Tendsto f l (𝓝 c)) (n : ℕ) :
    (fun x ↦ f x ^ n - c ^ n) =O[l] g := by
  induction n with
  | zero => simpa only [pow_zero, sub_self] using (isBigO_zero g l : (fun _ ↦ (0 : R)) =O[l] g)
  | succ n ih =>
    have hm : (fun x ↦ (f x ^ n - c ^ n) * f x) =O[l] g :=
      (ih.mul (hf.isBigO_one ℝ)).congr_right fun x ↦ mul_one (g x)
    refine (hm.add (hO.const_mul_left (c ^ n))).congr_left fun x ↦ ?_
    rw [pow_succ, pow_succ]
    ring

end Asymptotics
