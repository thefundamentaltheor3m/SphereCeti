/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Images of translates under affine maps

For any map `T` from an additive commutative group to a type with a commutative addition,
`x ↦ T (x - v) + w` carries the translate `v +ᵥ S` of a set onto the translate `w +ᵥ T '' S` of its
image.  Applied to a linear isometry carrying one lattice onto another, this carries a coset of the
first lattice onto a coset of the second.

## Main statements

* `Set.image_sub_add_vadd_eq`: `(fun x ↦ T (x - v) + w) '' (v +ᵥ S) = w +ᵥ T '' S`.
-/

public section

open scoped Pointwise

/-- For any map `T` from an additive commutative group to a type with a commutative addition,
`x ↦ T (x - v) + w` carries the translate `v +ᵥ S` onto the translate `w +ᵥ T '' S`. -/
theorem Set.image_sub_add_vadd_eq {G H : Type*} [AddCommGroup G] [AddCommMagma H] (T : G → H)
    (v : G) (w : H) (S : Set G) :
    (fun x ↦ T (x - v) + w) '' (v +ᵥ S) = w +ᵥ T '' S := by
  rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ ↦ ?_
  simp [vadd_eq_add, add_comm]
