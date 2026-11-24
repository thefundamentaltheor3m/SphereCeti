/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The kernels of the `+1` eigencomponent of the E8 magic function

Viazovska's function `φ₀ = (E₂ E₄ - E₆)² / Δ` on the upper half-plane, extended by `0` to `ℂ`, is
`1`-periodic.  The `+1` eigencomponent of the E8 magic function is a six-piece contour integral of
four kernels built from `φ₀`:
`φ₀(-1/(z+1)) (z+1)²` on the left legs, `φ₀(-1/(z-1)) (z-1)²` on the right legs,
`-2 φ₀(-1/z) z²` on the central leg and `2 φ₀(z)` on the vertical ray.

These kernels satisfy the signed transformation laws under `z ↦ -1/z` in dimension `8`, for every
`z ∈ ℂ`: `(i/z)⁴ g_L(z) = z⁻² g_R(-1/z)` and `(i/z)⁴ g_C(z) = -z⁻² g_Ray(-1/z)`.

## Main definitions

* `SphereCeti.E8.phi0`: `φ₀ = (E₂ E₄ - E₆)² / Δ` on the upper half-plane.
* `SphereCeti.E8.phi0Ext`: `φ₀` extended by `0` to `ℂ`.
* `SphereCeti.E8.plusKernelLeft`, `plusKernelRight`, `plusKernelCentral`, `plusKernelRay`: the four
  kernels of the `+1` eigencomponent.

## Main statements

* `SphereCeti.E8.phi0_def`, `SphereCeti.E8.phi0Ext_of_im_pos`, `SphereCeti.E8.phi0Ext_of_im_nonpos`,
  `SphereCeti.E8.plusKernelLeft_def` and its siblings: the defining formulas.
* `SphereCeti.E8.phi0Ext_add_one`: `φ₀` is `1`-periodic.
* `SphereCeti.E8.differentiableOn_phi0Ext`: `φ₀` is holomorphic on the upper half-plane.
* `SphereCeti.E8.plusKernel_law_leftRight`, `SphereCeti.E8.plusKernel_law_centralRay`: the signed
  transformation laws of the kernels.

## References

* M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991–1015, Section 4.
* The definitions follow Sphere-Packing-Lean (`thefundamentaltheor3m/Sphere-Packing-Lean`).
-/

public section

open Complex ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace SphereCeti.E8

/-- Viazovska's function `φ₀ = (E₂ E₄ - E₆)² / Δ` on the upper half-plane. -/
noncomputable def phi0 (z : ℍ) : ℂ :=
  (E2 z * E₄ z - E₆ z) ^ 2 / CuspForm.discriminant z

/-- `φ₀(z) = (E₂(z) E₄(z) - E₆(z))² / Δ(z)`. -/
theorem phi0_def (z : ℍ) : phi0 z = (E2 z * E₄ z - E₆ z) ^ 2 / CuspForm.discriminant z :=
  (rfl)

/-- `φ₀` extended by `0` from the upper half-plane to `ℂ`. -/
noncomputable def phi0Ext (z : ℂ) : ℂ :=
  if hz : 0 < z.im then phi0 ⟨z, hz⟩ else 0

/-- On the upper half-plane, `phi0Ext` is `φ₀`. -/
theorem phi0Ext_of_im_pos {z : ℂ} (hz : 0 < z.im) : phi0Ext z = phi0 ⟨z, hz⟩ := by
  simp [phi0Ext, hz]

/-- Off the upper half-plane, `phi0Ext` vanishes. -/
theorem phi0Ext_of_im_nonpos {z : ℂ} (hz : z.im ≤ 0) : phi0Ext z = 0 := by
  simp [phi0Ext, hz.not_gt]

/-- A function on the upper half-plane whose composition with `ofComplex` is `1`-periodic takes the
same value at `z + 1` and at `z`. -/
private lemma apply_add_one {f : ℍ → ℂ} (hf : Function.Periodic (f ∘ ofComplex) 1) {z : ℂ}
    (hz : 0 < z.im) (hz' : 0 < (z + 1).im) : f ⟨z + 1, hz'⟩ = f ⟨z, hz⟩ := by
  have h := hf z
  simp only [Function.comp_apply] at h
  rwa [ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos hz] at h

/-- `φ₀` is `1`-periodic. -/
theorem phi0Ext_add_one (z : ℂ) : phi0Ext (z + 1) = phi0Ext z := by
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa using hz
    rw [phi0Ext_of_im_pos hz', phi0Ext_of_im_pos hz, phi0, phi0,
      apply_add_one E2_periodic hz hz',
      apply_add_one (SlashInvariantFormClass.periodic_comp_ofComplex (f := E₄)
        one_mem_strictPeriods_SL) hz hz',
      apply_add_one (SlashInvariantFormClass.periodic_comp_ofComplex (f := E₆)
        one_mem_strictPeriods_SL) hz hz',
      apply_add_one (SlashInvariantFormClass.periodic_comp_ofComplex
        (f := CuspForm.discriminant) one_mem_strictPeriods_SL) hz hz']
  · have hz' : (z + 1).im ≤ 0 := by simpa using hz
    rw [phi0Ext_of_im_nonpos hz', phi0Ext_of_im_nonpos (not_lt.mp hz)]

/-- `φ₀` is holomorphic on the upper half-plane. -/
theorem differentiableOn_phi0Ext : DifferentiableOn ℂ phi0Ext {z : ℂ | 0 < z.im} := by
  have hE2 := UpperHalfPlane.mdifferentiable_iff.mp E2_mdifferentiable
  have hE4 := UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo E₄)
  have hE6 := UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo E₆)
  have hΔ := UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo CuspForm.discriminant)
  refine ((((hE2.mul hE4).sub hE6).pow 2).div hΔ fun z _ ↦ discriminant_ne_zero _).congr
    fun z (hz : 0 < z.im) ↦ ?_
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz, Pi.div_apply, Pi.pow_apply,
    Pi.sub_apply, Pi.mul_apply]
  rw [phi0Ext_of_im_pos hz, phi0]

/-- The left-leg kernel `φ₀(-1/(z+1)) (z+1)²` of the `+1` eigencomponent. -/
noncomputable def plusKernelLeft (z : ℂ) : ℂ := phi0Ext (-1 / (z + 1)) * (z + 1) ^ 2

/-- The right-leg kernel `φ₀(-1/(z-1)) (z-1)²` of the `+1` eigencomponent. -/
noncomputable def plusKernelRight (z : ℂ) : ℂ := phi0Ext (-1 / (z - 1)) * (z - 1) ^ 2

/-- The central-leg kernel `-2 φ₀(-1/z) z²` of the `+1` eigencomponent. -/
noncomputable def plusKernelCentral (z : ℂ) : ℂ := -2 * (phi0Ext (-1 / z) * z ^ 2)

/-- The vertical-ray kernel `2 φ₀(z)` of the `+1` eigencomponent. -/
noncomputable def plusKernelRay (z : ℂ) : ℂ := 2 * phi0Ext z

/-- The left-leg kernel is `φ₀(-1/(z+1)) (z+1)²`. -/
theorem plusKernelLeft_def (z : ℂ) : plusKernelLeft z = phi0Ext (-1 / (z + 1)) * (z + 1) ^ 2 :=
  (rfl)

/-- The right-leg kernel is `φ₀(-1/(z-1)) (z-1)²`. -/
theorem plusKernelRight_def (z : ℂ) :
    plusKernelRight z = phi0Ext (-1 / (z - 1)) * (z - 1) ^ 2 :=
  (rfl)

/-- The central-leg kernel is `-2 φ₀(-1/z) z²`. -/
theorem plusKernelCentral_def (z : ℂ) : plusKernelCentral z = -2 * (phi0Ext (-1 / z) * z ^ 2) :=
  (rfl)

/-- The vertical-ray kernel is `2 φ₀(z)`. -/
theorem plusKernelRay_def (z : ℂ) : plusKernelRay z = 2 * phi0Ext z :=
  (rfl)

/-- The left/right transformation law of the `+1` kernels: `(i/z)⁴ g_L(z) = z⁻² g_R(-1/z)`. -/
theorem plusKernel_law_leftRight (z : ℂ) :
    (I / z) ^ 4 * plusKernelLeft z = (z ^ 2)⁻¹ * plusKernelRight (-z⁻¹) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  rcases eq_or_ne (z + 1) 0 with hz1 | hz1
  · rw [eq_neg_of_add_eq_zero_left hz1]
    simp [plusKernelLeft, plusKernelRight]
  -- `-1/(-1/z - 1) = -1/(z+1) + 1`, so periodicity identifies the two values of `φ₀`.
  have hw : -z⁻¹ - 1 = -(z + 1) / z := by
    field_simp
    ring
  have harg : -1 / (-z⁻¹ - 1) = -1 / (z + 1) + 1 := by
    rw [hw]
    field_simp
    ring
  have hsq : (-z⁻¹ - 1) ^ 2 = (z + 1) ^ 2 / z ^ 2 := by
    rw [hw, div_pow, neg_sq]
  rw [plusKernelLeft, plusKernelRight, harg, phi0Ext_add_one, hsq, div_pow, I_pow_four]
  field_simp

/-- The central/ray transformation law of the `+1` kernels: `(i/z)⁴ g_C(z) = -z⁻² g_Ray(-1/z)`. -/
theorem plusKernel_law_centralRay (z : ℂ) :
    (I / z) ^ 4 * plusKernelCentral z = -(z ^ 2)⁻¹ * plusKernelRay (-z⁻¹) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  rw [plusKernelCentral, plusKernelRay, div_pow, I_pow_four, neg_div, one_div]
  field_simp

end SphereCeti.E8
