/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.SlashActions
import Mathlib.NumberTheory.ModularForms.Identities
import TauCeti.NumberTheory.ModularForms.Basic

/-!
# The kernels of the `-1` eigencomponent of the E8 magic function

From the fourth powers `H₂ = Θ₂⁴`, `H₃ = Θ₃⁴`, `H₄ = Θ₄⁴` of the Jacobi thetanullwerte, Viazovska
builds the function `h = 128 (H₃ + H₄) / H₂²` and the three functions `ψ_I = h - h ∣[-2] (S T)`,
`ψ_T = ψ_I ∣[-2] T` and `ψ_S = ψ_I ∣[-2] S` on the upper half-plane. Explicitly,

* `ψ_I = 128 ((H₃ + H₄) / H₂² + (H₄ - H₂) / H₃²)`,
* `ψ_T = 128 ((H₃ + H₄) / H₂² + (H₂ + H₃) / H₄²)`,
* `ψ_S = 128 ((H₄ - H₂) / H₃² - (H₂ + H₃) / H₄²)`,

so that `ψ_I = ψ_T + ψ_S`, and in weight `-2` they satisfy `ψ_T ∣ T = ψ_I`, `ψ_S ∣ S = ψ_I`,
`ψ_S ∣ (S T) = ψ_T`, `ψ_T ∣ S = -ψ_T` and `ψ_S ∣ T = -ψ_S`.

The `-1` eigencomponent of the E8 magic function is a six-piece contour integral of four kernels
built from these functions, extended by `0` to `ℂ`: `ψ_T(z)` on the left legs and on the right
legs, `-2 ψ_I(z)` on the central leg and `-2 ψ_S(z)` on the vertical ray. They satisfy the signed
transformation laws under `z ↦ -1/z` in dimension `8`, for every `z ∈ ℂ`:
`(i/z)⁴ g_L(z) = -z⁻² g_R(-1/z)` and `(i/z)⁴ g_C(z) = z⁻² g_Ray(-1/z)`.

## Main definitions

* `SphereCeti.E8.hTheta`: Viazovska's `h = 128 (H₃ + H₄) / H₂²`.
* `SphereCeti.E8.psiI`, `SphereCeti.E8.psiT`, `SphereCeti.E8.psiS`: `ψ_I`, `ψ_T` and `ψ_S`.
* `SphereCeti.E8.psiIExt`, `SphereCeti.E8.psiTExt`, `SphereCeti.E8.psiSExt`: their extensions by
  `0` to `ℂ`.
* `SphereCeti.E8.minusKernelLeft`, `minusKernelRight`, `minusKernelCentral`, `minusKernelRay`: the
  four kernels of the `-1` eigencomponent.

## Main statements

* `SphereCeti.E8.hTheta_def`, `SphereCeti.E8.psiI_def`, `SphereCeti.E8.psiIExt_of_im_pos`,
  `SphereCeti.E8.psiIExt_of_im_nonpos`, `SphereCeti.E8.minusKernelLeft_def` and their siblings:
  the defining formulas.
* `SphereCeti.E8.psiI_eq`, `SphereCeti.E8.psiT_eq`, `SphereCeti.E8.psiS_eq`,
  `SphereCeti.E8.psiI_eq_psiT_add_psiS`: the explicit formulas.
* `SphereCeti.E8.psiT_slash_T`, `SphereCeti.E8.psiS_slash_S`, `SphereCeti.E8.psiS_slash_ST`,
  `SphereCeti.E8.psiT_slash_S`, `SphereCeti.E8.psiS_slash_T`: the slash relations.
* `SphereCeti.E8.minusKernel_law_leftRight`, `SphereCeti.E8.minusKernel_law_centralRay`: the
  signed transformation laws of the kernels.

## References

* M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991–1015, Section 4: `h` is (42), `ψ_I`, `ψ_T`, `ψ_S` are (43)–(45), and the `-1` eigenfunction
  `b` is (52).
* The definitions are adapted from Sphere-Packing-Lean
  (`thefundamentaltheor3m/Sphere-Packing-Lean`) at commit
  `01f23eccf963c50250c9e48dd103e8cc88c36f85`, file `SpherePacking/MagicFunction/b/PsiBounds.lean`:
  `hTheta`, `psiI`, `psiT`, `psiS` and their extensions are `h`, `ψI`, `ψT`, `ψS`, `ψI'`, `ψT'`,
  `ψS'` there, and the four kernels are the functions integrated against `exp (π i x z) dz` in
  `J₁'`–`J₆'`, the central and ray kernels with the factor `-2` of `J₅'` and `J₆'`. The proofs in
  this file were written independently of that source; no proof text is copied from it.
-/

public section

open Complex ModularForm ModularGroup TauCeti.ModularForm
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace SphereCeti.E8

/-! ### Viazovska's functions `h`, `ψ_I`, `ψ_T` and `ψ_S` -/

/-- Viazovska's function `h = 128 (H₃ + H₄) / H₂²` on the upper half-plane. -/
noncomputable def hTheta : ℍ → ℂ := (128 : ℂ) • ((H₃ + H₄) / H₂ ^ 2)

/-- `h = 128 (H₃ + H₄) / H₂²`. -/
theorem hTheta_def : hTheta = (128 : ℂ) • ((H₃ + H₄) / H₂ ^ 2) :=
  (rfl)

/-- Viazovska's function `ψ_I = h - h ∣[-2] (S T)` on the upper half-plane. -/
noncomputable def psiI : ℍ → ℂ := hTheta - hTheta ∣[(-2 : ℤ)] (S * T)

/-- `ψ_I = h - h ∣[-2] (S T)`. -/
theorem psiI_def : psiI = hTheta - hTheta ∣[(-2 : ℤ)] (S * T) :=
  (rfl)

/-- Viazovska's function `ψ_T = ψ_I ∣[-2] T` on the upper half-plane. -/
noncomputable def psiT : ℍ → ℂ := psiI ∣[(-2 : ℤ)] T

/-- `ψ_T = ψ_I ∣[-2] T`. -/
theorem psiT_def : psiT = psiI ∣[(-2 : ℤ)] T :=
  (rfl)

/-- Viazovska's function `ψ_S = ψ_I ∣[-2] S` on the upper half-plane. -/
noncomputable def psiS : ℍ → ℂ := psiI ∣[(-2 : ℤ)] S

/-- `ψ_S = ψ_I ∣[-2] S`. -/
theorem psiS_def : psiS = psiI ∣[(-2 : ℤ)] S :=
  (rfl)

/-- The weight `-2` slash action on `h = 128 (H₃ + H₄) / H₂²` acts on `H₂`, `H₃`, `H₄` in
weight `2`. -/
private theorem hTheta_slash (A : SL(2, ℤ)) :
    hTheta ∣[(-2 : ℤ)] A =
      (128 : ℂ) • ((H₃ ∣[(2 : ℤ)] A + H₄ ∣[(2 : ℤ)] A) / (H₂ ∣[(2 : ℤ)] A) ^ 2) := by
  have hpow := pow_slash_SL2 2 2 A H₂
  have hdiv := div_slash_SL2 2 4 A (H₃ + H₄) (H₂ ^ 2)
  rw [(by norm_num : ((2 : ℕ) : ℤ) * 2 = 4)] at hpow
  rw [(by norm_num : (2 : ℤ) - 4 = -2), hpow, SlashAction.add_slash] at hdiv
  rw [hTheta_def, SL_smul_slash, hdiv]

/-- Unfolds `ψ_I`, `ψ_T`, `ψ_S` into slashes of `h`, evaluates them through `hTheta_slash` and the
slash actions on `H₂`, `H₃`, `H₄`, and closes the resulting identity pointwise. -/
local macro "psi_slash" : tactic =>
  `(tactic| (
    simp only [psiS_def, psiT_def, psiI_def, SlashAction.sub_slash, ← SlashAction.slash_mul]
    simp only [hTheta_slash]
    simp only [hTheta_def, SlashAction.slash_mul, H₂_slash_S, H₃_slash_S, H₄_slash_S, H₂_slash_T,
      H₃_slash_T, H₄_slash_T, SlashAction.neg_slash]
    ext z
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply,
      Pi.neg_apply, smul_eq_mul]
    ring))

/-! ### Explicit formulas -/

/-- `ψ_I = 128 ((H₃ + H₄) / H₂² + (H₄ - H₂) / H₃²)`. -/
theorem psiI_eq : psiI = (128 : ℂ) • ((H₃ + H₄) / H₂ ^ 2 + (H₄ - H₂) / H₃ ^ 2) := by
  psi_slash

/-- `ψ_T = 128 ((H₃ + H₄) / H₂² + (H₂ + H₃) / H₄²)`. -/
theorem psiT_eq : psiT = (128 : ℂ) • ((H₃ + H₄) / H₂ ^ 2 + (H₂ + H₃) / H₄ ^ 2) := by
  psi_slash

/-- `ψ_S = 128 ((H₄ - H₂) / H₃² - (H₂ + H₃) / H₄²)`. -/
theorem psiS_eq : psiS = (128 : ℂ) • ((H₄ - H₂) / H₃ ^ 2 - (H₂ + H₃) / H₄ ^ 2) := by
  psi_slash

/-- `ψ_I = ψ_T + ψ_S`. -/
theorem psiI_eq_psiT_add_psiS : psiI = psiT + psiS := by
  rw [psiI_eq, psiT_eq, psiS_eq]
  ext z
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.div_apply, Pi.pow_apply, smul_eq_mul]
  ring

/-! ### Slash relations -/

/-- `ψ_T ∣[-2] T = ψ_I`. -/
theorem psiT_slash_T : psiT ∣[(-2 : ℤ)] T = psiI := by
  psi_slash

/-- `ψ_S ∣[-2] S = ψ_I`. -/
theorem psiS_slash_S : psiS ∣[(-2 : ℤ)] S = psiI := by
  rw [psiS_def, SL_slash_S_slash_S]
  norm_num

/-- `ψ_S ∣[-2] (S T) = ψ_T`. -/
theorem psiS_slash_ST : psiS ∣[(-2 : ℤ)] (S * T) = psiT := by
  rw [SlashAction.slash_mul, psiS_slash_S, psiT_def]

/-- `ψ_T ∣[-2] S = -ψ_T`. -/
theorem psiT_slash_S : psiT ∣[(-2 : ℤ)] S = -psiT := by
  rw [eq_sub_of_add_eq psiI_eq_psiT_add_psiS.symm, SlashAction.sub_slash, psiS_slash_S,
    ← psiS_def, neg_sub]

/-- `ψ_S ∣[-2] T = -ψ_S`. -/
theorem psiS_slash_T : psiS ∣[(-2 : ℤ)] T = -psiS := by
  rw [eq_sub_of_add_eq' psiI_eq_psiT_add_psiS.symm, SlashAction.sub_slash, psiT_slash_T,
    ← psiT_def, neg_sub]

/-! ### Extensions by zero -/

/-- `ψ_I` extended by `0` from the upper half-plane to `ℂ`. -/
noncomputable def psiIExt (z : ℂ) : ℂ :=
  if hz : 0 < z.im then psiI ⟨z, hz⟩ else 0

/-- `ψ_T` extended by `0` from the upper half-plane to `ℂ`. -/
noncomputable def psiTExt (z : ℂ) : ℂ :=
  if hz : 0 < z.im then psiT ⟨z, hz⟩ else 0

/-- `ψ_S` extended by `0` from the upper half-plane to `ℂ`. -/
noncomputable def psiSExt (z : ℂ) : ℂ :=
  if hz : 0 < z.im then psiS ⟨z, hz⟩ else 0

/-- On the upper half-plane, `psiIExt` is `ψ_I`. -/
@[simp]
theorem psiIExt_of_im_pos {z : ℂ} (hz : 0 < z.im) : psiIExt z = psiI ⟨z, hz⟩ := by
  simp [psiIExt, hz]

/-- Off the upper half-plane, `psiIExt` vanishes. -/
@[simp]
theorem psiIExt_of_im_nonpos {z : ℂ} (hz : z.im ≤ 0) : psiIExt z = 0 := by
  simp [psiIExt, hz.not_gt]

/-- On the upper half-plane, `psiTExt` is `ψ_T`. -/
@[simp]
theorem psiTExt_of_im_pos {z : ℂ} (hz : 0 < z.im) : psiTExt z = psiT ⟨z, hz⟩ := by
  simp [psiTExt, hz]

/-- Off the upper half-plane, `psiTExt` vanishes. -/
@[simp]
theorem psiTExt_of_im_nonpos {z : ℂ} (hz : z.im ≤ 0) : psiTExt z = 0 := by
  simp [psiTExt, hz.not_gt]

/-- On the upper half-plane, `psiSExt` is `ψ_S`. -/
@[simp]
theorem psiSExt_of_im_pos {z : ℂ} (hz : 0 < z.im) : psiSExt z = psiS ⟨z, hz⟩ := by
  simp [psiSExt, hz]

/-- Off the upper half-plane, `psiSExt` vanishes. -/
@[simp]
theorem psiSExt_of_im_nonpos {z : ℂ} (hz : z.im ≤ 0) : psiSExt z = 0 := by
  simp [psiSExt, hz.not_gt]

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

/-- The left/right transformation law of the `-1` kernels: `(i/z)⁴ g_L(z) = -z⁻² g_R(-1/z)`. -/
theorem minusKernel_law_leftRight (z : ℂ) :
    (I / z) ^ 4 * minusKernelLeft z = -(z ^ 2)⁻¹ * minusKernelRight (-z⁻¹) := by
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
    -- `ψ_T ∣[-2] S = -ψ_T` at `z` reads `ψ_T(-1/z) z² = -ψ_T(z)`
    have h := congrFun psiT_slash_S ⟨z, hz⟩
    simp only [SlashInvariantForm.slash_S_apply, Pi.neg_apply, inv_neg, neg_neg, zpow_ofNat] at h
    rw [minusKernelLeft_def, minusKernelRight_def, psiTExt_of_im_pos hz, psiTExt_of_im_pos hz']
    generalize psiT ⟨-z⁻¹, hz'⟩ = a at h ⊢
    generalize psiT ⟨z, hz⟩ = b at h ⊢
    rw [div_pow, I_pow_four]
    field_simp
    linear_combination h

/-- The central/ray transformation law of the `-1` kernels: `(i/z)⁴ g_C(z) = z⁻² g_Ray(-1/z)`. -/
theorem minusKernel_law_centralRay (z : ℂ) :
    (I / z) ^ 4 * minusKernelCentral z = (z ^ 2)⁻¹ * minusKernelRay (-z⁻¹) := by
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
    -- `ψ_S ∣[-2] S = ψ_I` at `z` reads `ψ_S(-1/z) z² = ψ_I(z)`
    have h := congrFun psiS_slash_S ⟨z, hz⟩
    simp only [SlashInvariantForm.slash_S_apply, inv_neg, neg_neg, zpow_ofNat] at h
    rw [minusKernelCentral_def, minusKernelRay_def, psiIExt_of_im_pos hz,
      psiSExt_of_im_pos hz']
    generalize psiS ⟨-z⁻¹, hz'⟩ = a at h ⊢
    generalize psiI ⟨z, hz⟩ = b at h ⊢
    rw [div_pow, I_pow_four]
    field_simp
    linear_combination h

end SphereCeti.E8
