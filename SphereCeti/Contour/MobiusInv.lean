/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Complex.Basic

/-!
# The inversion `z ↦ -1/z`

The finite branch of the Layer 8 contour deformation compares contour legs under the Möbius
transformation of the modular matrix `S`, namely `z ↦ -z⁻¹`.  This file defines that map on `ℂ`
and proves its derivative and that it preserves the upper half-plane.

## Main definitions and results

* `SphereCeti.Contour.mobiusInv`: the inversion, with the defining formula of the roadmap's
  `SphereCeti.Suggested.Contour.mobiusInv`.
* `SphereCeti.Contour.mobiusInv_apply`, `SphereCeti.Contour.hasDerivAt_mobiusInv`, and
  `SphereCeti.Contour.mobiusInv_im_pos`: the roadmap targets of the same names, with the same
  statements.

## Provenance

The definitions and statements are the roadmap's Layer 8 targets, which are based on the `gauss2`
branch of Sphere-Packing-Lean at commit `01f23eccf963c50250c9e48dd103e8cc88c36f85`, file
`SpherePacking/Contour/MobiusInv/WedgeSetContour.lean` (see `PROVENANCE.md`, section 4).  The
proofs in this file were written independently of that source; no proof text is copied from it.
-/

public section

namespace SphereCeti.Contour

/-- The inversion `z ↦ -1/z`, the Möbius transformation of the modular matrix `S`. -/
@[expose]
noncomputable def mobiusInv : ℂ → ℂ := fun z => -z⁻¹

/-- Unfolding rule for `mobiusInv`.  It rewrites `mobiusInv z` to the closed form `-z⁻¹`, which
contains no further occurrence of `mobiusInv`, so it cannot loop. -/
@[simp]
theorem mobiusInv_apply (z : ℂ) : mobiusInv z = -z⁻¹ := rfl

example (z : ℂ) : mobiusInv (mobiusInv z) = z := by simp

/-- The derivative of `z ↦ -z⁻¹` at a nonzero point is `(z ^ 2)⁻¹`. -/
theorem hasDerivAt_mobiusInv {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt mobiusInv ((z ^ 2)⁻¹) z := by
  have h := (hasDerivAt_inv hz).neg
  rw [neg_neg] at h
  exact h

/-- The inversion `z ↦ -z⁻¹` maps the upper half-plane to itself. -/
theorem mobiusInv_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (mobiusInv z).im := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [mobiusInv_apply, Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_pos hz (Complex.normSq_pos.mpr hz0)

end SphereCeti.Contour
