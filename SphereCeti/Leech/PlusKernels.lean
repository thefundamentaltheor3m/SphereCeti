/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The kernels of the `+1` eigencomponent of the Leech magic function

The weakly holomorphic quasimodular form
`φ = (25 E₄⁴ - 49 E₆² E₄ + 48 E₆ E₄² E₂ + (25 E₆² - 49 E₄³) E₂²) / Δ²`
of Cohn–Kumar–Miller–Radchenko–Viazovska, on the upper half-plane and extended by `0` to `ℂ`, is
`1`-periodic.  The `+1` eigencomponent of the Leech magic function is a six-piece contour integral
of four kernels built from `φ`: `φ(-1/(z+1)) (z+1)¹⁰` on the left legs, `φ(-1/(z-1)) (z-1)¹⁰` on
the right legs, `-2 φ(-1/z) z¹⁰` on the central leg and `2 φ(z)` on the vertical ray.

These kernels satisfy the signed transformation laws under `z ↦ -1/z` in dimension `24`, for every
`z ∈ ℂ`: `(i/z)¹² g_L(z) = z⁻² g_R(-1/z)` and `(i/z)¹² g_C(z) = -z⁻² g_Ray(-1/z)`.

## Main definitions

* `SphereCeti.Leech.varphi`: the quasimodular form `φ` on the upper half-plane.
* `SphereCeti.Leech.varphiExt`: `φ` extended by `0` to `ℂ`.
* `SphereCeti.Leech.plusKernelLeft`, `plusKernelRight`, `plusKernelCentral`, `plusKernelRay`: the
  four kernels of the `+1` eigencomponent.

## Main statements

* `SphereCeti.Leech.varphiExt_add_one`: `φ` is `1`-periodic.
* `SphereCeti.Leech.plusKernel_law_leftRight`, `SphereCeti.Leech.plusKernel_law_centralRay`: the
  signed transformation laws of the kernels.

## References

* H. Cohn, A. Kumar, S. D. Miller, D. Radchenko and M. Viazovska, *The sphere packing problem in
  dimension 24*, Annals of Mathematics 185 (2017), 1017–1033, Section 2.
-/

public section

open Complex ModularForm EisensteinSeries
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace SphereCeti.Leech

/-- The quasimodular form
`φ = (25 E₄⁴ - 49 E₆² E₄ + 48 E₆ E₄² E₂ + (25 E₆² - 49 E₄³) E₂²) / Δ²` on the upper half-plane. -/
noncomputable def varphi (z : ℍ) : ℂ :=
  (25 * E₄ z ^ 4 - 49 * E₆ z ^ 2 * E₄ z + 48 * E₆ z * E₄ z ^ 2 * E2 z +
    (25 * E₆ z ^ 2 - 49 * E₄ z ^ 3) * E2 z ^ 2) / CuspForm.discriminant z ^ 2

/-- `φ` extended by `0` from the upper half-plane to `ℂ`. -/
noncomputable def varphiExt (z : ℂ) : ℂ :=
  if hz : 0 < z.im then varphi ⟨z, hz⟩ else 0

/-- On the upper half-plane, `varphiExt` is `φ`. -/
theorem varphiExt_of_im_pos {z : ℂ} (hz : 0 < z.im) : varphiExt z = varphi ⟨z, hz⟩ := by
  simp [varphiExt, hz]

/-- Off the upper half-plane, `varphiExt` vanishes. -/
theorem varphiExt_of_im_nonpos {z : ℂ} (hz : z.im ≤ 0) : varphiExt z = 0 := by
  simp [varphiExt, hz.not_gt]

/-- A function on the upper half-plane whose composition with `ofComplex` is `1`-periodic takes the
same value at `z + 1` and at `z`. -/
private lemma apply_add_one {f : ℍ → ℂ} (hf : Function.Periodic (f ∘ ofComplex) 1) {z : ℂ}
    (hz : 0 < z.im) (hz' : 0 < (z + 1).im) : f ⟨z + 1, hz'⟩ = f ⟨z, hz⟩ := by
  have h := hf z
  simp only [Function.comp_apply] at h
  rwa [ofComplex_apply_of_im_pos hz', ofComplex_apply_of_im_pos hz] at h

/-- `φ` is `1`-periodic. -/
theorem varphiExt_add_one (z : ℂ) : varphiExt (z + 1) = varphiExt z := by
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa using hz
    rw [varphiExt_of_im_pos hz', varphiExt_of_im_pos hz, varphi, varphi,
      apply_add_one E2_periodic hz hz',
      apply_add_one (SlashInvariantFormClass.periodic_comp_ofComplex (f := E₄)
        one_mem_strictPeriods_SL) hz hz',
      apply_add_one (SlashInvariantFormClass.periodic_comp_ofComplex (f := E₆)
        one_mem_strictPeriods_SL) hz hz',
      apply_add_one (SlashInvariantFormClass.periodic_comp_ofComplex
        (f := CuspForm.discriminant) one_mem_strictPeriods_SL) hz hz']
  · have hz' : (z + 1).im ≤ 0 := by simpa using hz
    rw [varphiExt_of_im_nonpos hz', varphiExt_of_im_nonpos (not_lt.mp hz)]

/-- The left-leg kernel `φ(-1/(z+1)) (z+1)¹⁰` of the `+1` eigencomponent. -/
noncomputable def plusKernelLeft (z : ℂ) : ℂ := varphiExt (-1 / (z + 1)) * (z + 1) ^ 10

/-- The right-leg kernel `φ(-1/(z-1)) (z-1)¹⁰` of the `+1` eigencomponent. -/
noncomputable def plusKernelRight (z : ℂ) : ℂ := varphiExt (-1 / (z - 1)) * (z - 1) ^ 10

/-- The central-leg kernel `-2 φ(-1/z) z¹⁰` of the `+1` eigencomponent. -/
noncomputable def plusKernelCentral (z : ℂ) : ℂ := -2 * (varphiExt (-1 / z) * z ^ 10)

/-- The vertical-ray kernel `2 φ(z)` of the `+1` eigencomponent. -/
noncomputable def plusKernelRay (z : ℂ) : ℂ := 2 * varphiExt z

/-- The left/right transformation law of the `+1` kernels: `(i/z)¹² g_L(z) = z⁻² g_R(-1/z)`. -/
theorem plusKernel_law_leftRight (z : ℂ) :
    (I / z) ^ 12 * plusKernelLeft z = (z ^ 2)⁻¹ * plusKernelRight (-z⁻¹) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  rcases eq_or_ne (z + 1) 0 with hz1 | hz1
  · rw [eq_neg_of_add_eq_zero_left hz1]
    simp [plusKernelLeft, plusKernelRight]
  -- `-1/(-1/z - 1) = -1/(z+1) + 1`, so periodicity identifies the two values of `φ`.
  have hw : -z⁻¹ - 1 = -(z + 1) / z := by
    field_simp
    ring
  have harg : -1 / (-z⁻¹ - 1) = -1 / (z + 1) + 1 := by
    rw [hw]
    field_simp
    ring
  have hpow : (-z⁻¹ - 1) ^ 10 = (z + 1) ^ 10 / z ^ 10 := by
    rw [hw, div_pow, Even.neg_pow (by decide)]
  have hI : I ^ 12 = 1 := by
    rw [show 12 = 4 * 3 by norm_num, pow_mul, I_pow_four, one_pow]
  rw [plusKernelLeft, plusKernelRight, harg, varphiExt_add_one, hpow, div_pow, hI]
  field_simp

/-- The central/ray transformation law of the `+1` kernels: `(i/z)¹² g_C(z) = -z⁻² g_Ray(-1/z)`. -/
theorem plusKernel_law_centralRay (z : ℂ) :
    (I / z) ^ 12 * plusKernelCentral z = -(z ^ 2)⁻¹ * plusKernelRay (-z⁻¹) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hI : I ^ 12 = 1 := by
    rw [show 12 = 4 * 3 by norm_num, pow_mul, I_pow_four, one_pow]
  rw [plusKernelCentral, plusKernelRay, div_pow, hI, neg_div, one_div]
  field_simp

end SphereCeti.Leech
