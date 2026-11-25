/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# `q`-expansions of functions with analytic cusp functions

The functions `f : ℍ → ℂ` whose cusp function of width `h` is analytic at `0` form a subring of
`ℍ → ℂ`, and on it `qExpansion h` is a ring homomorphism to `ℂ⟦X⟧`.

## Main definitions

* `TauCeti.UpperHalfPlane.analyticCuspSubring h`: the functions `f : ℍ → ℂ` whose cusp function
  of width `h` is analytic at `0`.
* `TauCeti.UpperHalfPlane.qExpansionRingHom h`: `qExpansion h` as a ring homomorphism on
  `analyticCuspSubring h`.

## Main statements

* `TauCeti.UpperHalfPlane.analyticAt_cuspFunction_mul`,
  `TauCeti.UpperHalfPlane.analyticAt_cuspFunction_add`,
  `TauCeti.UpperHalfPlane.analyticAt_cuspFunction_neg`,
  `TauCeti.UpperHalfPlane.analyticAt_cuspFunction_const`: analyticity of the cusp function at `0`
  passes to products, sums and negations, and holds for constant functions.
* `TauCeti.UpperHalfPlane.mem_analyticCuspSubring`,
  `TauCeti.UpperHalfPlane.qExpansionRingHom_apply`: the defining characterizations.
-/

public noncomputable section

open UpperHalfPlane

namespace TauCeti

variable {h : ℝ} {f g : ℍ → ℂ}

/-- The cusp function of a product is analytic at `0` when both cusp functions are. -/
theorem UpperHalfPlane.analyticAt_cuspFunction_mul (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0) : AnalyticAt ℂ (cuspFunction h (f * g)) 0 := by
  rw [_root_.UpperHalfPlane.cuspFunction_mul hf.continuousAt hg.continuousAt]
  exact hf.mul hg

/-- The cusp function of a sum is analytic at `0` when both cusp functions are. -/
theorem UpperHalfPlane.analyticAt_cuspFunction_add (hf : AnalyticAt ℂ (cuspFunction h f) 0)
    (hg : AnalyticAt ℂ (cuspFunction h g) 0) : AnalyticAt ℂ (cuspFunction h (f + g)) 0 := by
  rw [_root_.UpperHalfPlane.cuspFunction_add hf.continuousAt hg.continuousAt]
  exact hf.add hg

/-- The cusp function of a negation is analytic at `0` when the cusp function is. -/
theorem UpperHalfPlane.analyticAt_cuspFunction_neg (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    AnalyticAt ℂ (cuspFunction h (-f)) 0 := by
  rw [_root_.UpperHalfPlane.cuspFunction_neg hf.continuousAt]
  exact hf.neg

/-- The cusp function of a constant function is analytic at `0`. -/
theorem UpperHalfPlane.analyticAt_cuspFunction_const (c : ℂ) :
    AnalyticAt ℂ (cuspFunction h fun _ : ℍ ↦ c) 0 := by
  rw [UpperHalfPlane.cuspFunction_const]
  exact analyticAt_const

variable (h) in
/-- The functions `f : ℍ → ℂ` whose cusp function of width `h` is analytic at `0`. -/
def UpperHalfPlane.analyticCuspSubring : Subring (ℍ → ℂ) where
  carrier := {f | AnalyticAt ℂ (cuspFunction h f) 0}
  mul_mem' := UpperHalfPlane.analyticAt_cuspFunction_mul
  one_mem' := UpperHalfPlane.analyticAt_cuspFunction_const 1
  add_mem' := UpperHalfPlane.analyticAt_cuspFunction_add
  zero_mem' := UpperHalfPlane.analyticAt_cuspFunction_const 0
  neg_mem' := UpperHalfPlane.analyticAt_cuspFunction_neg

/-- A function lies in `analyticCuspSubring h` exactly when its cusp function of width `h` is
analytic at `0`. -/
@[simp]
theorem UpperHalfPlane.mem_analyticCuspSubring :
    f ∈ UpperHalfPlane.analyticCuspSubring h ↔ AnalyticAt ℂ (cuspFunction h f) 0 :=
  Iff.rfl

variable (h) in
/-- `qExpansion h` as a ring homomorphism on the functions whose cusp function of width `h` is
analytic at `0`. -/
def UpperHalfPlane.qExpansionRingHom :
    UpperHalfPlane.analyticCuspSubring h →+* PowerSeries ℂ where
  toFun f := qExpansion h f
  map_one' := _root_.UpperHalfPlane.qExpansion_one h
  map_mul' f g := _root_.UpperHalfPlane.qExpansion_mul f.2 g.2
  map_zero' := _root_.UpperHalfPlane.qExpansion_zero h
  map_add' f g := _root_.UpperHalfPlane.qExpansion_add f.2 g.2

/-- `qExpansionRingHom h f` is the `q`-expansion of `f`. -/
@[simp]
theorem UpperHalfPlane.qExpansionRingHom_apply (f : UpperHalfPlane.analyticCuspSubring h) :
    UpperHalfPlane.qExpansionRingHom h f = qExpansion h f :=
  (rfl)

end TauCeti
