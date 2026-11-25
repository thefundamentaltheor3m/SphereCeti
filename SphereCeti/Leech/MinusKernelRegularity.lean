/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.KernelContinuity
public import SphereCeti.Contour.KernelIntegrability
public import SphereCeti.Leech.MinusKernels
public import SphereCeti.NumberTheory.ModularForms.JacobiTheta.Estimates
import Mathlib.NumberTheory.ModularForms.Identities
import Mathlib.NumberTheory.ModularForms.Petersson
import TauCeti.NumberTheory.ModularForms.Cusps.Basic

/-!
# Regularity of the `-1` Leech kernels

The kernels of the `-1` eigencomponent of the Leech magic function are all built from `ψ_S`. With
`ψ_I`, `ψ_T`, `ψ_S` extended by `0` to `ℂ`, for every `z ∈ ℂ`, `ψ_I(z) = ψ_S(-1/z) z¹⁰` and
`ψ_T(z) = ψ_I(z + 1) = ψ_I(z - 1)`. So the left, right and central kernels are
`ψ_S(-1/(z+1)) (z+1)¹⁰`, `ψ_S(-1/(z-1)) (z-1)¹⁰` and `-2 ψ_S(-1/z) z¹⁰`, and the ray kernel is
`-2 ψ_S(z)`. Moreover `ψ_S = O(exp(-π Im τ))` at `i∞`.

Let `E` be a finite-dimensional real inner product space. The kernels satisfy the absolute
integrability of `g(z(t)) exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` along the two left legs
`-1 → -1 + i → i`, the two right legs `1 → 1 + i → i` and the central leg `0 → i` of the magic
contour, and `t ↦ ψ_S(it)` is integrable on `(1, ∞)`. For every `r`, the transported left kernel
`(i/z)¹² g_L(z) exp(πir (-1/z))` is continuous on the left legs, and the right kernel times
`exp(πirz)` is holomorphic on the wedge `{0 < Im z, |Re z - 1| < Im z}` and continuous on its
closure.

## Main statements

* `SphereCeti.Leech.psiIExt_eq_psiSExt`, `SphereCeti.Leech.psiTExt_eq_psiIExt_add_one`,
  `SphereCeti.Leech.psiTExt_eq_psiIExt_sub_one`: `ψ_I(z) = ψ_S(-1/z) z¹⁰` and
  `ψ_T(z) = ψ_I(z + 1) = ψ_I(z - 1)`.
* `SphereCeti.Leech.minusKernelLeft_eq_psiSExt`, `SphereCeti.Leech.minusKernelRight_eq_psiSExt`,
  `SphereCeti.Leech.minusKernelCentral_eq_psiSExt`: the kernels through `ψ_S`.
* `SphereCeti.Leech.isBigO_psiS`: `ψ_S = O(exp(-π Im τ))` at `i∞`.
* `SphereCeti.Leech.integrableOn_psiSExt_mul_I`: `t ↦ ψ_S(it)` is integrable on `(1, ∞)`.
* `SphereCeti.Leech.integrable_minusKernelLeft`, `SphereCeti.Leech.integrable_minusKernelRight`,
  `SphereCeti.Leech.integrable_minusKernelCentral`: absolute integrability of the left-leg,
  right-leg and central-leg kernels.
* `SphereCeti.Leech.tendsto_psiSExt_neg_one_div_mul_pow`: `ψ_S(-1/w) w¹⁰ → 0` as `w → 0` in the
  cone `|Re w| ≤ Im w`.
* `SphereCeti.Leech.continuousOn_minusKernelLeft_transport`: the transported left kernel is
  continuous on the left legs.
* `SphereCeti.Leech.diffContOnCl_minusKernelRight_mul_cexp`: the right kernel times `exp(πirz)` is
  holomorphic on the wedge and continuous on its closure.

## References

* H. Cohn, A. Kumar, S. D. Miller, D. Radchenko and M. Viazovska, *The sphere packing problem in
  dimension 24*, Annals of Mathematics 185 (2017), 1017–1033, Section 3: the expansion (3.2) of
  `ψ_S` begins with `q^{1/2} = exp(π i τ)`.
-/

public section

open Complex Filter Asymptotics MeasureTheory Set Topology ModularForm ModularGroup
  TauCeti.ModularForm
open UpperHalfPlane hiding I
open scoped Real

namespace SphereCeti.Leech

/-! ### The kernels through `ψ_S` -/

/-- `ψ_I(z) = ψ_S(-1/z) z¹⁰` for every `z ∈ ℂ`, for the extensions by `0`. -/
theorem psiIExt_eq_psiSExt (z : ℂ) : psiIExt z = psiSExt (-1 / z) * z ^ 10 := by
  rw [neg_div, one_div]
  rcases le_or_gt z.im 0 with hz | hz
  · have hz' : (-z⁻¹).im ≤ 0 := by
      rw [neg_im, inv_im, neg_div, neg_neg]
      exact div_nonpos_of_nonpos_of_nonneg hz (normSq_nonneg z)
    rw [psiIExt_of_im_nonpos hz, psiSExt_of_im_nonpos hz', zero_mul]
  · have hz0 : z ≠ 0 := fun h0 ↦ by simp [h0] at hz
    have hz' : 0 < (-z⁻¹).im := by
      rw [neg_im, inv_im, neg_div, neg_neg]
      exact div_pos hz (normSq_pos.mpr hz0)
    -- `ψ_S ∣[-10] S = ψ_I` at `z` reads `ψ_S(-1/z) z¹⁰ = ψ_I(z)`
    have h := congrFun psiS_slash_S ⟨z, hz⟩
    simp only [SlashInvariantForm.slash_S_apply, inv_neg, neg_neg, zpow_ofNat] at h
    rw [psiIExt_of_im_pos hz, psiSExt_of_im_pos hz', ← h]

/-- `ψ_T(z) = ψ_I(z + 1)` for every `z ∈ ℂ`, for the extensions by `0`. -/
theorem psiTExt_eq_psiIExt_add_one (z : ℂ) : psiTExt z = psiIExt (z + 1) := by
  rcases le_or_gt z.im 0 with hz | hz
  · rw [psiTExt_of_im_nonpos hz, psiIExt_of_im_nonpos (by simpa using hz)]
  · have hz' : 0 < (z + 1).im := by simpa using hz
    rw [psiTExt_of_im_pos hz, psiIExt_of_im_pos hz', psiT_def, ← zpow_one T,
      slash_T_zpow_apply]
    congr 1
    ext
    simp [add_comm]

/-- `ψ_T(z) = ψ_I(z - 1)` for every `z ∈ ℂ`, for the extensions by `0`. -/
theorem psiTExt_eq_psiIExt_sub_one (z : ℂ) : psiTExt z = psiIExt (z - 1) := by
  rcases le_or_gt z.im 0 with hz | hz
  · rw [psiTExt_of_im_nonpos hz, psiIExt_of_im_nonpos (by simpa using hz)]
  · have hz' : 0 < (z - 1).im := by simpa using hz
    -- `ψ_T ∣[-10] T = ψ_I` at `z - 1` reads `ψ_T(z) = ψ_I(z - 1)`
    have h := congrFun psiT_slash_T ⟨z - 1, hz'⟩
    rw [← zpow_one T, slash_T_zpow_apply] at h
    rw [psiTExt_of_im_pos hz, psiIExt_of_im_pos hz', ← h]
    congr 1
    ext
    simp

/-- The left-leg kernel is `ψ_S(-1/(z+1)) (z+1)¹⁰`. -/
theorem minusKernelLeft_eq_psiSExt (z : ℂ) :
    minusKernelLeft z = psiSExt (-1 / (z + 1)) * (z + 1) ^ 10 := by
  rw [minusKernelLeft_def, psiTExt_eq_psiIExt_add_one, psiIExt_eq_psiSExt]

/-- The right-leg kernel is `ψ_S(-1/(z-1)) (z-1)¹⁰`. -/
theorem minusKernelRight_eq_psiSExt (z : ℂ) :
    minusKernelRight z = psiSExt (-1 / (z - 1)) * (z - 1) ^ 10 := by
  rw [minusKernelRight_def, psiTExt_eq_psiIExt_sub_one, psiIExt_eq_psiSExt]

/-- The central-leg kernel is `-2 ψ_S(-1/z) z¹⁰`. -/
theorem minusKernelCentral_eq_psiSExt (z : ℂ) :
    minusKernelCentral z = -2 * (psiSExt (-1 / z) * z ^ 10) := by
  rw [minusKernelCentral_def, psiIExt_eq_psiSExt]

/-! ### Decay of `ψ_S` at `i∞` -/

/-- `ψ_S = O(exp(-π Im τ))` at `i∞`. -/
theorem isBigO_psiS : psiS =O[atImInfty] fun τ ↦ Real.exp (-π * τ.im) := by
  -- `ψ_S = -H₂⁵ (7 H₄² + 7 H₂ H₄ + 2 H₂²) / Δ²`, where `H₂ = O(exp(-π Im τ))`, `H₂` and `H₄` are
  -- bounded, and `Δ⁻² = O(exp(4π Im τ))`
  have hden : (fun τ : ℍ ↦ (CuspForm.discriminant τ)⁻¹) =O[atImInfty]
      fun τ ↦ (Real.exp (-2 * π * τ.im))⁻¹ :=
    exp_isBigO_discriminant.inv_rev (Eventually.of_forall fun τ h ↦
      absurd h (Real.exp_pos _).ne')
  have h₂ : H₂ =O[atImInfty] fun _ ↦ (1 : ℝ) := isBoundedAtImInfty_H₂
  have h₄ : H₄ =O[atImInfty] fun _ ↦ (1 : ℝ) := isBoundedAtImInfty_H₄
  have h₄₄ : (fun τ ↦ H₄ τ ^ 2) =O[atImInfty] fun _ ↦ (1 : ℝ) := by simpa using h₄.pow 2
  have h₂₂ : (fun τ ↦ H₂ τ ^ 2) =O[atImInfty] fun _ ↦ (1 : ℝ) := by simpa using h₂.pow 2
  have h₂₄ : (fun τ ↦ H₂ τ * H₄ τ) =O[atImInfty] fun _ ↦ (1 : ℝ) := by simpa using h₂.mul h₄
  have hB : (fun τ ↦ 7 * H₄ τ ^ 2 + 7 * (H₂ τ * H₄ τ) + 2 * H₂ τ ^ 2) =O[atImInfty]
      fun _ ↦ (1 : ℝ) :=
    ((h₄₄.const_mul_left 7).add (h₂₄.const_mul_left 7)).add (h₂₂.const_mul_left 2)
  refine ((((isBigO_H₂_atImInfty.pow 5).mul hB).mul (hden.pow 2)).neg_left.congr_left fun τ ↦ ?_)
    |>.congr_right fun τ ↦ ?_
  · rw [psiS_eq]
    simp only [Pi.neg_apply, Pi.div_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply,
      Pi.pow_apply, smul_eq_mul]
    ring
  · rw [mul_one, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring

/-- `ψ_S = O(exp(-π Im τ))` at `i∞`, for `ψ_S` extended by `0` to `ℂ`. -/
private lemma isBigO_psiSExt :
    (fun τ : ℍ ↦ psiSExt τ) =O[atImInfty] fun τ ↦ Real.exp (-π * τ.im) :=
  isBigO_psiS.congr_left fun τ ↦ (psiSExt_of_im_pos τ.im_pos).symm

/-- `ψ_S` is bounded at `i∞`, for `ψ_S` extended by `0` to `ℂ`. -/
private lemma isBoundedAtImInfty_psiSExt : IsBoundedAtImInfty fun τ : ℍ ↦ psiSExt τ :=
  (IsZeroAtImInfty.of_exp_decay ⟨π, Real.pi_pos, isBigO_psiSExt⟩).isBoundedAtImInfty

/-! ### Integrability -/

/-- `ψ_S` on the imaginary axis, `t ↦ ψ_S(it)`, is integrable on `(1, ∞)`. -/
theorem integrableOn_psiSExt_mul_I : IntegrableOn (fun t : ℝ ↦ psiSExt (t * I)) (Ioi 1) :=
  UpperHalfPlane.integrableOn_mul_I_Ioi_of_isBigO one_pos Real.pi_pos continuousOn_psiSExt
    isBigO_psiSExt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The left-leg kernel `ψ_T(z)` satisfies the absolute integrability of
`g(z(t)) exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` along both left legs `-1 → -1 + i` and
`-1 + i → i`. -/
theorem integrable_minusKernelLeft :
    ∀ p ∈ ({(-1, -1 + I), (-1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖minusKernelLeft (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  simpa only [minusKernelLeft_eq_psiSExt] using
    Contour.integrable_leftLegs_of_isBigO Real.pi_pos continuousOn_psiSExt isBigO_psiSExt 10

/-- The right-leg kernel `ψ_T(z)` satisfies the absolute integrability of
`g(z(t)) exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` along both right legs `1 → 1 + i` and
`1 + i → i`. -/
theorem integrable_minusKernelRight :
    ∀ p ∈ ({(1, 1 + I), (1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖minusKernelRight (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  simpa only [minusKernelRight_eq_psiSExt] using
    Contour.integrable_rightLegs_of_isBigO Real.pi_pos continuousOn_psiSExt isBigO_psiSExt 10

/-- The central-leg kernel `-2 ψ_I(z)` satisfies the absolute integrability of
`g(it) exp(-π ‖x‖² t)` on `E × (0, 1]`. -/
theorem integrable_minusKernelCentral :
    Integrable (fun q : E × ℝ ↦ ‖minusKernelCentral (q.2 * I)‖ * Real.exp (-π * ‖q.1‖ ^ 2 * q.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  refine ((Contour.integrable_centralLeg_of_isBigO Real.pi_pos continuousOn_psiSExt
    isBigO_psiSExt 10).const_mul 2).congr (ae_of_all _ fun q ↦ ?_)
  simp only [minusKernelCentral_eq_psiSExt, norm_mul, norm_neg, Complex.norm_two]
  ring

/-! ### Continuity at the cusps of the contour -/

/-- `ψ_S(-1/w) w¹⁰ → 0` as `w → 0` within the cone `|Re w| ≤ Im w`. -/
theorem tendsto_psiSExt_neg_one_div_mul_pow :
    Tendsto (fun w : ℂ ↦ psiSExt (-1 / w) * w ^ 10) (𝓝[{w : ℂ | |w.re| ≤ w.im}] 0) (𝓝 0) :=
  isBoundedAtImInfty_psiSExt.tendsto_neg_one_div_mul_pow (by norm_num)

/-- The transported left kernel `(i/z)¹² g_L(z) exp(πir (-1/z))` is continuous on the left legs
`-1 → -1 + i → i`, for every `r`. -/
theorem continuousOn_minusKernelLeft_transport (r : ℝ) :
    ContinuousOn (fun z : ℂ ↦ (I / z) ^ 12 * minusKernelLeft z * cexp (π * I * r * (-z⁻¹)))
      (segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I) :=
  Contour.continuousOn_I_div_pow_mul_mul_cexp
    ((Contour.continuousOn_neg_one_div_add_one_mul_pow continuousOn_psiSExt
      isBoundedAtImInfty_psiSExt (by norm_num)).congr fun z _ ↦ minusKernelLeft_eq_psiSExt z)
    12 _

/-- The transported right kernel `g_R(z) exp(πirz)` is holomorphic on the wedge
`{0 < Im z, |Re z - 1| < Im z}` and continuous on its closure, for every `r`. -/
theorem diffContOnCl_minusKernelRight_mul_cexp (r : ℝ) :
    DiffContOnCl ℂ (fun z : ℂ ↦ minusKernelRight z * cexp (π * I * r * z))
      {z : ℂ | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im} := by
  have h := Contour.diffContOnCl_neg_one_div_sub_one_mul_pow (k := 10) differentiableOn_psiSExt
    isBoundedAtImInfty_psiSExt (by norm_num)
  simp only [minusKernelRight_eq_psiSExt]
  exact ⟨h.differentiableOn.mul (by fun_prop), h.continuousOn.mul (by fun_prop)⟩

end SphereCeti.Leech
