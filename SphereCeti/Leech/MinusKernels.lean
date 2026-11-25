/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.SlashActions
import Mathlib.NumberTheory.ModularForms.Identities
import SphereCeti.NumberTheory.ModularForms.JacobiTheta.JacobiIdentity
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# The kernels of the `-1` eigencomponent of the Leech magic function

From the fourth powers `H₂ = Θ₂⁴`, `H₃ = Θ₃⁴`, `H₄ = Θ₄⁴` of the Jacobi thetanullwerte and the
discriminant `Δ`, Cohn, Kumar, Miller, Radchenko and Viazovska build the function
`ψ_I = (7 H₄⁵ H₂² + 7 H₄⁶ H₂ + 2 H₄⁷) / Δ²` on the upper half-plane, and from it
`ψ_S = ψ_I ∣[-10] S` and `ψ_T = ψ_I ∣[-10] T`. Explicitly,

* `ψ_S = -(7 H₂⁵ H₄² + 7 H₂⁶ H₄ + 2 H₂⁷) / Δ²`,
* `ψ_T = (7 H₃⁵ H₂² - 7 H₃⁶ H₂ + 2 H₃⁷) / Δ²`,

so that `ψ_I = ψ_T + ψ_S`, and in weight `-10` they satisfy `ψ_T ∣ T = ψ_I`, `ψ_S ∣ S = ψ_I`,
`ψ_S ∣ (S T) = ψ_T`, `ψ_T ∣ S = -ψ_T` and `ψ_S ∣ T = -ψ_S`. All three are holomorphic on the upper
half-plane.

The `-1` eigencomponent of the Leech magic function is a six-piece contour integral of four kernels
built from these functions, extended by `0` to `ℂ`: `ψ_T(z)` on the left legs and on the right
legs, `-2 ψ_I(z)` on the central leg and `-2 ψ_S(z)` on the vertical ray. They satisfy the signed
transformation laws under `z ↦ -1/z` in dimension `24`, for every `z ∈ ℂ`:
`(i/z)¹² g_L(z) = -z⁻² g_R(-1/z)` and `(i/z)¹² g_C(z) = z⁻² g_Ray(-1/z)`.

## Main definitions

* `SphereCeti.Leech.psiI`, `SphereCeti.Leech.psiS`, `SphereCeti.Leech.psiT`: `ψ_I`, `ψ_S` and
  `ψ_T`.
* `SphereCeti.Leech.psiIExt`, `SphereCeti.Leech.psiSExt`, `SphereCeti.Leech.psiTExt`: their
  extensions by `0` to `ℂ`.
* `SphereCeti.Leech.minusKernelLeft`, `minusKernelRight`, `minusKernelCentral`, `minusKernelRay`:
  the four kernels of the `-1` eigencomponent.

## Main statements

* `SphereCeti.Leech.psiI_def`, `SphereCeti.Leech.psiS_def`, `SphereCeti.Leech.psiT_def`,
  `SphereCeti.Leech.psiIExt_of_im_pos`, `SphereCeti.Leech.psiIExt_of_im_nonpos`,
  `SphereCeti.Leech.minusKernelLeft_def` and their siblings: the defining formulas.
* `SphereCeti.Leech.psiS_eq`, `SphereCeti.Leech.psiT_eq`, `SphereCeti.Leech.psiI_eq_psiT_add_psiS`:
  the explicit formulas.
* `SphereCeti.Leech.psiT_slash_T`, `SphereCeti.Leech.psiS_slash_S`,
  `SphereCeti.Leech.psiS_slash_ST`, `SphereCeti.Leech.psiT_slash_S`,
  `SphereCeti.Leech.psiS_slash_T`: the slash relations.
* `SphereCeti.Leech.mdifferentiable_psiI`, `SphereCeti.Leech.differentiableOn_psiIExt`,
  `SphereCeti.Leech.continuousOn_psiIExt` and their siblings for `ψ_S` and `ψ_T`: holomorphy and
  continuity on the upper half-plane.
* `SphereCeti.Leech.minusKernel_law_leftRight`, `SphereCeti.Leech.minusKernel_law_centralRay`:
  the signed transformation laws of the kernels.

## References

* H. Cohn, A. Kumar, S. D. Miller, D. Radchenko and M. Viazovska, *The sphere packing problem in
  dimension 24*, Annals of Mathematics 185 (2017), 1017–1033, Section 3: `ψ_I` is (3.1), `ψ_S` is
  (3.2), `ψ_T` is the formula following it, and the contour presentation of the `-1`
  eigenfunction `b` is in the proof of Lemma 3.1.
-/

public section

open Complex ModularForm ModularGroup TauCeti.ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups Manifold

namespace SphereCeti.Leech

/-! ### The functions `ψ_I`, `ψ_S` and `ψ_T` -/

/-- The function `ψ_I = (7 H₄⁵ H₂² + 7 H₄⁶ H₂ + 2 H₄⁷) / Δ²` on the upper half-plane. -/
noncomputable def psiI : ℍ → ℂ :=
  ((7 : ℂ) • (H₄ ^ 5 * H₂ ^ 2) + (7 : ℂ) • (H₄ ^ 6 * H₂) + (2 : ℂ) • H₄ ^ 7) /
    ⇑CuspForm.discriminant ^ 2

/-- `ψ_I = (7 H₄⁵ H₂² + 7 H₄⁶ H₂ + 2 H₄⁷) / Δ²`. -/
theorem psiI_def : psiI =
    ((7 : ℂ) • (H₄ ^ 5 * H₂ ^ 2) + (7 : ℂ) • (H₄ ^ 6 * H₂) + (2 : ℂ) • H₄ ^ 7) /
      ⇑CuspForm.discriminant ^ 2 :=
  (rfl)

/-- The function `ψ_S = ψ_I ∣[-10] S` on the upper half-plane. -/
noncomputable def psiS : ℍ → ℂ := psiI ∣[(-10 : ℤ)] S

/-- `ψ_S = ψ_I ∣[-10] S`. -/
theorem psiS_def : psiS = psiI ∣[(-10 : ℤ)] S :=
  (rfl)

/-- The function `ψ_T = ψ_I ∣[-10] T` on the upper half-plane. -/
noncomputable def psiT : ℍ → ℂ := psiI ∣[(-10 : ℤ)] T

/-- `ψ_T = ψ_I ∣[-10] T`. -/
theorem psiT_def : psiT = psiI ∣[(-10 : ℤ)] T :=
  (rfl)

/-- The weight `-10` slash action on `ψ_I` acts on `H₂`, `H₄` in weight `2` and on `Δ` in
weight `12`. -/
private theorem psiI_slash (A : SL(2, ℤ)) :
    psiI ∣[(-10 : ℤ)] A =
      ((7 : ℂ) • ((H₄ ∣[(2 : ℤ)] A) ^ 5 * (H₂ ∣[(2 : ℤ)] A) ^ 2) +
        (7 : ℂ) • ((H₄ ∣[(2 : ℤ)] A) ^ 6 * H₂ ∣[(2 : ℤ)] A) +
        (2 : ℂ) • (H₄ ∣[(2 : ℤ)] A) ^ 7) / (⇑CuspForm.discriminant ∣[(12 : ℤ)] A) ^ 2 := by
  have hΔ := pow_slash_SL2 2 12 A ⇑CuspForm.discriminant
  have h₂ := pow_slash_SL2 2 2 A H₂
  have h₅ := pow_slash_SL2 5 2 A H₄
  have h₆ := pow_slash_SL2 6 2 A H₄
  have h₇ := pow_slash_SL2 7 2 A H₄
  have m₁ := mul_slash_SL2 10 4 A (H₄ ^ 5) (H₂ ^ 2)
  have m₂ := mul_slash_SL2 12 2 A (H₄ ^ 6) H₂
  have hdiv := div_slash_SL2 14 24 A
    ((7 : ℂ) • (H₄ ^ 5 * H₂ ^ 2) + (7 : ℂ) • (H₄ ^ 6 * H₂) + (2 : ℂ) • H₄ ^ 7)
    (⇑CuspForm.discriminant ^ 2)
  rw [(by norm_num : ((2 : ℕ) : ℤ) * 12 = 24)] at hΔ
  rw [(by norm_num : ((2 : ℕ) : ℤ) * 2 = 4)] at h₂
  rw [(by norm_num : ((5 : ℕ) : ℤ) * 2 = 10)] at h₅
  rw [(by norm_num : ((6 : ℕ) : ℤ) * 2 = 12)] at h₆
  rw [(by norm_num : ((7 : ℕ) : ℤ) * 2 = 14)] at h₇
  rw [(by norm_num : (10 : ℤ) + 4 = 14)] at m₁
  rw [(by norm_num : (12 : ℤ) + 2 = 14)] at m₂
  rw [(by norm_num : (14 : ℤ) - 24 = -10)] at hdiv
  rw [psiI_def, hdiv, SlashAction.add_slash, SlashAction.add_slash, SL_smul_slash, SL_smul_slash,
    SL_smul_slash, m₁, m₂, h₅, h₂, h₆, h₇, hΔ]

/-! ### Explicit formulas -/

/-- `ψ_S = -(7 H₂⁵ H₄² + 7 H₂⁶ H₄ + 2 H₂⁷) / Δ²`. -/
theorem psiS_eq : psiS =
    -(((7 : ℂ) • (H₂ ^ 5 * H₄ ^ 2) + (7 : ℂ) • (H₂ ^ 6 * H₄) + (2 : ℂ) • H₂ ^ 7) /
      ⇑CuspForm.discriminant ^ 2) := by
  rw [psiS_def, psiI_slash, H₄_slash_S, H₂_slash_S, CuspForm.coe_discriminant,
    discriminant_S_invariant]
  ext z
  simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
    smul_eq_mul]
  ring

/-- `ψ_T = (7 H₃⁵ H₂² - 7 H₃⁶ H₂ + 2 H₃⁷) / Δ²`. -/
theorem psiT_eq : psiT =
    ((7 : ℂ) • (H₃ ^ 5 * H₂ ^ 2) - (7 : ℂ) • (H₃ ^ 6 * H₂) + (2 : ℂ) • H₃ ^ 7) /
      ⇑CuspForm.discriminant ^ 2 := by
  rw [psiT_def, psiI_slash, H₄_slash_T, H₂_slash_T, CuspForm.coe_discriminant,
    discriminant_T_invariant]
  ext z
  simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply,
    Pi.neg_apply, smul_eq_mul]
  ring

/-! ### Slash relations -/

/-- `ψ_T ∣[-10] T = ψ_I`. -/
theorem psiT_slash_T : psiT ∣[(-10 : ℤ)] T = psiI := by
  rw [psiT_def, ← SlashAction.slash_mul, psiI_slash]
  simp only [SlashAction.slash_mul, H₂_slash_T, H₃_slash_T, H₄_slash_T, SlashAction.neg_slash,
    CuspForm.coe_discriminant, discriminant_T_invariant]
  rw [psiI_def]
  ext z
  simp only [Pi.div_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply,
    smul_eq_mul, CuspForm.coe_discriminant]
  ring

/-- `ψ_S ∣[-10] S = ψ_I`. -/
theorem psiS_slash_S : psiS ∣[(-10 : ℤ)] S = psiI := by
  rw [psiS_def, SL_slash_S_slash_S]
  norm_num

/-- `ψ_S ∣[-10] (S T) = ψ_T`. -/
theorem psiS_slash_ST : psiS ∣[(-10 : ℤ)] (S * T) = psiT := by
  rw [SlashAction.slash_mul, psiS_slash_S, psiT_def]

/-- `ψ_I = ψ_T + ψ_S`. -/
theorem psiI_eq_psiT_add_psiS : psiI = psiT + psiS := by
  rw [psiT_eq, psiS_eq, psiI_def]
  ext z
  -- Jacobi's identity `H₂ + H₄ = H₃` at `z`
  have h := congrFun jacobi_identity z
  simp only [Pi.add_apply] at h
  simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply,
    Pi.neg_apply, smul_eq_mul]
  rw [← h]
  ring

/-- `ψ_T ∣[-10] S = -ψ_T`. -/
theorem psiT_slash_S : psiT ∣[(-10 : ℤ)] S = -psiT := by
  rw [eq_sub_of_add_eq psiI_eq_psiT_add_psiS.symm, SlashAction.sub_slash, psiS_slash_S,
    ← psiS_def, neg_sub]

/-- `ψ_S ∣[-10] T = -ψ_S`. -/
theorem psiS_slash_T : psiS ∣[(-10 : ℤ)] T = -psiS := by
  rw [eq_sub_of_add_eq' psiI_eq_psiT_add_psiS.symm, SlashAction.sub_slash, psiT_slash_T,
    ← psiT_def, neg_sub]

/-! ### Extensions by zero -/

/-- `ψ_I` extended by `0` from the upper half-plane to `ℂ`. -/
noncomputable def psiIExt (z : ℂ) : ℂ :=
  if hz : 0 < z.im then psiI ⟨z, hz⟩ else 0

/-- `ψ_S` extended by `0` from the upper half-plane to `ℂ`. -/
noncomputable def psiSExt (z : ℂ) : ℂ :=
  if hz : 0 < z.im then psiS ⟨z, hz⟩ else 0

/-- `ψ_T` extended by `0` from the upper half-plane to `ℂ`. -/
noncomputable def psiTExt (z : ℂ) : ℂ :=
  if hz : 0 < z.im then psiT ⟨z, hz⟩ else 0

/-- On the upper half-plane, `psiIExt` is `ψ_I`. -/
@[simp]
theorem psiIExt_of_im_pos {z : ℂ} (hz : 0 < z.im) : psiIExt z = psiI ⟨z, hz⟩ := by
  simp [psiIExt, hz]

/-- Off the upper half-plane, `psiIExt` vanishes. -/
@[simp]
theorem psiIExt_of_im_nonpos {z : ℂ} (hz : z.im ≤ 0) : psiIExt z = 0 := by
  simp [psiIExt, hz.not_gt]

/-- On the upper half-plane, `psiSExt` is `ψ_S`. -/
@[simp]
theorem psiSExt_of_im_pos {z : ℂ} (hz : 0 < z.im) : psiSExt z = psiS ⟨z, hz⟩ := by
  simp [psiSExt, hz]

/-- Off the upper half-plane, `psiSExt` vanishes. -/
@[simp]
theorem psiSExt_of_im_nonpos {z : ℂ} (hz : z.im ≤ 0) : psiSExt z = 0 := by
  simp [psiSExt, hz.not_gt]

/-- On the upper half-plane, `psiTExt` is `ψ_T`. -/
@[simp]
theorem psiTExt_of_im_pos {z : ℂ} (hz : 0 < z.im) : psiTExt z = psiT ⟨z, hz⟩ := by
  simp [psiTExt, hz]

/-- Off the upper half-plane, `psiTExt` vanishes. -/
@[simp]
theorem psiTExt_of_im_nonpos {z : ℂ} (hz : z.im ≤ 0) : psiTExt z = 0 := by
  simp [psiTExt, hz.not_gt]

/-! ### Holomorphy -/

/-- `ψ_I` is holomorphic on the upper half-plane. -/
theorem mdifferentiable_psiI : MDiff psiI := by
  rw [psiI_def]
  refine MDifferentiable.div ?_ ((ModularFormClass.holo CuspForm.discriminant).pow 2)
    fun z ↦ pow_ne_zero 2 (discriminant_ne_zero z)
  exact ((((mdifferentiable_H₄.pow 5).mul (mdifferentiable_H₂.pow 2)).const_smul 7).add
    (((mdifferentiable_H₄.pow 6).mul mdifferentiable_H₂).const_smul 7)).add
      ((mdifferentiable_H₄.pow 7).const_smul 2)

/-- `ψ_S` is holomorphic on the upper half-plane. -/
theorem mdifferentiable_psiS : MDiff psiS := by
  rw [psiS_def, ModularForm.SL_slash]
  exact mdifferentiable_psiI.slash _ _

/-- `ψ_T` is holomorphic on the upper half-plane. -/
theorem mdifferentiable_psiT : MDiff psiT := by
  rw [psiT_def, ModularForm.SL_slash]
  exact mdifferentiable_psiI.slash _ _

/-- `ψ_I` is holomorphic on the upper half-plane, as a function on `ℂ`. -/
theorem differentiableOn_psiIExt : DifferentiableOn ℂ psiIExt {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_psiI).congr fun z (hz : 0 < z.im) ↦ by
    rw [psiIExt_of_im_pos hz, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- `ψ_S` is holomorphic on the upper half-plane, as a function on `ℂ`. -/
theorem differentiableOn_psiSExt : DifferentiableOn ℂ psiSExt {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_psiS).congr fun z (hz : 0 < z.im) ↦ by
    rw [psiSExt_of_im_pos hz, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- `ψ_T` is holomorphic on the upper half-plane, as a function on `ℂ`. -/
theorem differentiableOn_psiTExt : DifferentiableOn ℂ psiTExt {z : ℂ | 0 < z.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_psiT).congr fun z (hz : 0 < z.im) ↦ by
    rw [psiTExt_of_im_pos hz, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-- `ψ_I` is continuous on the upper half-plane, as a function on `ℂ`. -/
theorem continuousOn_psiIExt : ContinuousOn psiIExt {z : ℂ | 0 < z.im} :=
  differentiableOn_psiIExt.continuousOn

/-- `ψ_S` is continuous on the upper half-plane, as a function on `ℂ`. -/
theorem continuousOn_psiSExt : ContinuousOn psiSExt {z : ℂ | 0 < z.im} :=
  differentiableOn_psiSExt.continuousOn

/-- `ψ_T` is continuous on the upper half-plane, as a function on `ℂ`. -/
theorem continuousOn_psiTExt : ContinuousOn psiTExt {z : ℂ | 0 < z.im} :=
  differentiableOn_psiTExt.continuousOn

/-! ### The kernels -/

/-- The left-leg kernel `ψ_T(z)` of the `-1` eigencomponent. -/
noncomputable def minusKernelLeft (z : ℂ) : ℂ := psiTExt z

/-- The right-leg kernel `ψ_T(z)` of the `-1` eigencomponent. -/
noncomputable def minusKernelRight (z : ℂ) : ℂ := psiTExt z

/-- The central-leg kernel `-2 ψ_I(z)` of the `-1` eigencomponent. -/
noncomputable def minusKernelCentral (z : ℂ) : ℂ := -2 * psiIExt z

/-- The vertical-ray kernel `-2 ψ_S(z)` of the `-1` eigencomponent. -/
noncomputable def minusKernelRay (z : ℂ) : ℂ := -2 * psiSExt z

/-- The left-leg kernel is `ψ_T(z)`. -/
theorem minusKernelLeft_def (z : ℂ) : minusKernelLeft z = psiTExt z :=
  (rfl)

/-- The right-leg kernel is `ψ_T(z)`. -/
theorem minusKernelRight_def (z : ℂ) : minusKernelRight z = psiTExt z :=
  (rfl)

/-- The central-leg kernel is `-2 ψ_I(z)`. -/
theorem minusKernelCentral_def (z : ℂ) : minusKernelCentral z = -2 * psiIExt z :=
  (rfl)

/-- The vertical-ray kernel is `-2 ψ_S(z)`. -/
theorem minusKernelRay_def (z : ℂ) : minusKernelRay z = -2 * psiSExt z :=
  (rfl)

example {z : ℂ} (hz : 0 < z.im) : minusKernelLeft z = psiT ⟨z, hz⟩ := by
  simp [minusKernelLeft_def, hz]

example {z : ℂ} (hz : z.im ≤ 0) : minusKernelCentral z + minusKernelRay z = 0 := by
  simp [minusKernelCentral_def, minusKernelRay_def, hz]

/-! ### The transformation laws -/

/-- The left/right transformation law of the `-1` kernels: `(i/z)¹² g_L(z) = -z⁻² g_R(-1/z)`. -/
theorem minusKernel_law_leftRight (z : ℂ) :
    (I / z) ^ 12 * minusKernelLeft z = -(z ^ 2)⁻¹ * minusKernelRight (-z⁻¹) := by
  rcases le_or_gt z.im 0 with hz | hz
  · have hz' : (-z⁻¹).im ≤ 0 := by
      rw [neg_im, inv_im, neg_div, neg_neg]
      exact div_nonpos_of_nonpos_of_nonneg hz (normSq_nonneg z)
    rw [minusKernelLeft_def, minusKernelRight_def, psiTExt_of_im_nonpos hz,
      psiTExt_of_im_nonpos hz', mul_zero, mul_zero]
  · have hz0 : z ≠ 0 := fun h0 ↦ by simp [h0] at hz
    have hz' : 0 < (-z⁻¹).im := by
      rw [neg_im, inv_im, neg_div, neg_neg]
      exact div_pos hz (normSq_pos.mpr hz0)
    -- `ψ_T ∣[-10] S = -ψ_T` at `z` reads `ψ_T(-1/z) z¹⁰ = -ψ_T(z)`
    have h := congrFun psiT_slash_S ⟨z, hz⟩
    simp only [SlashInvariantForm.slash_S_apply, Pi.neg_apply, inv_neg, neg_neg, zpow_ofNat] at h
    rw [minusKernelLeft_def, minusKernelRight_def, psiTExt_of_im_pos hz, psiTExt_of_im_pos hz']
    generalize psiT ⟨-z⁻¹, hz'⟩ = a at h ⊢
    generalize psiT ⟨z, hz⟩ = b at h ⊢
    rw [div_pow, (by norm_num [pow_mul, I_pow_four] : I ^ 12 = 1)]
    field_simp
    linear_combination h

/-- The central/ray transformation law of the `-1` kernels: `(i/z)¹² g_C(z) = z⁻² g_Ray(-1/z)`. -/
theorem minusKernel_law_centralRay (z : ℂ) :
    (I / z) ^ 12 * minusKernelCentral z = (z ^ 2)⁻¹ * minusKernelRay (-z⁻¹) := by
  rcases le_or_gt z.im 0 with hz | hz
  · have hz' : (-z⁻¹).im ≤ 0 := by
      rw [neg_im, inv_im, neg_div, neg_neg]
      exact div_nonpos_of_nonpos_of_nonneg hz (normSq_nonneg z)
    rw [minusKernelCentral_def, minusKernelRay_def, psiIExt_of_im_nonpos hz,
      psiSExt_of_im_nonpos hz', mul_zero, mul_zero, mul_zero]
  · have hz0 : z ≠ 0 := fun h0 ↦ by simp [h0] at hz
    have hz' : 0 < (-z⁻¹).im := by
      rw [neg_im, inv_im, neg_div, neg_neg]
      exact div_pos hz (normSq_pos.mpr hz0)
    -- `ψ_S ∣[-10] S = ψ_I` at `z` reads `ψ_S(-1/z) z¹⁰ = ψ_I(z)`
    have h := congrFun psiS_slash_S ⟨z, hz⟩
    simp only [SlashInvariantForm.slash_S_apply, inv_neg, neg_neg, zpow_ofNat] at h
    rw [minusKernelCentral_def, minusKernelRay_def, psiIExt_of_im_pos hz,
      psiSExt_of_im_pos hz']
    generalize psiS ⟨-z⁻¹, hz'⟩ = a at h ⊢
    generalize psiI ⟨z, hz⟩ = b at h ⊢
    rw [div_pow, (by norm_num [pow_mul, I_pow_four] : I ^ 12 = 1)]
    field_simp
    linear_combination h

end SphereCeti.Leech
