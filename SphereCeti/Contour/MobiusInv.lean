/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The inversion `z ↦ -1/z`

The modular matrix `S = !![0, -1; 1, 0]` acts on `ℂ` by the Möbius transformation
`z ↦ -1/z = -z⁻¹`.  Comparing contour integrals over a path and over its image under this map
requires the chain rule, so this file defines the map on all of `ℂ` (with the junk value `0` at
`z = 0`) and computes its complex derivative: at every `z ≠ 0`, the derivative is `(z ^ 2)⁻¹`.

That the map sends the upper half-plane to itself is already `TauCeti.im_neg_one_div_pos`, which
this module imports publicly so that it reaches every consumer; together with `mobiusInv_apply`
it gives `0 < (mobiusInv z).im` whenever `0 < z.im`, as the example below records.

## Main definitions

* `SphereCeti.Contour.mobiusInv`: the map `z ↦ -z⁻¹` on `ℂ`.

## Main statements

* `SphereCeti.Contour.mobiusInv_apply`: the evaluation formula `mobiusInv z = -z⁻¹`.
* `SphereCeti.Contour.hasDerivAt_mobiusInv`: `mobiusInv` has derivative `(z ^ 2)⁻¹` at every
  nonzero `z`.

## Provenance

The definition and the statements follow the `gauss2` branch of Sphere-Packing-Lean at commit
`01f23eccf963c50250c9e48dd103e8cc88c36f85`, file
`SpherePacking/Contour/MobiusInv/WedgeSetContour.lean` (see `PROVENANCE.md`, section 4).  The
proofs in this file were written independently of that source; no proof text is copied from it.
-/

public section

namespace SphereCeti.Contour

/-- The inversion `z ↦ -1/z`, the Möbius transformation of the modular matrix `S`. -/
noncomputable def mobiusInv : ℂ → ℂ := fun z => -z⁻¹

/-- `mobiusInv z` evaluates to `-z⁻¹`. -/
@[simp]
theorem mobiusInv_apply (z : ℂ) : mobiusInv z = -z⁻¹ := (rfl)

/-- The inversion is an involution, by `simp` via `mobiusInv_apply`. -/
example (z : ℂ) : mobiusInv (mobiusInv z) = z := by simp

/-- The derivative of `z ↦ -z⁻¹` at a nonzero point `z` is `(z ^ 2)⁻¹`. -/
theorem hasDerivAt_mobiusInv {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt mobiusInv ((z ^ 2)⁻¹) z := by
  -- Negate Mathlib's derivative `-(z ^ 2)⁻¹` of `w ↦ w⁻¹`; the function `fun w => -w⁻¹` is
  -- `mobiusInv` by definition.
  have h := (hasDerivAt_inv hz).neg
  rw [neg_neg] at h
  exact h

/-- The inversion maps the upper half-plane to itself: this is `TauCeti.im_neg_one_div_pos`
rewritten through `mobiusInv_apply`. -/
example {z : ℂ} (hz : 0 < z.im) : 0 < (mobiusInv z).im := by
  simpa [div_eq_mul_inv] using TauCeti.im_neg_one_div_pos hz

end SphereCeti.Contour
