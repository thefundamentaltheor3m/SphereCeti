/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import SphereCeti.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
public import SphereCeti.NumberTheory.ModularForms.QExpansion.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
public import TauCeti.NumberTheory.ModularForms.LevelOne.QExpansion
public import TauCeti.NumberTheory.ModularForms.QExpansion.BigO

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

* `SphereCeti.Leech.varphi_def`, `SphereCeti.Leech.varphiExt_of_im_pos`,
  `SphereCeti.Leech.varphiExt_of_im_nonpos`, `SphereCeti.Leech.plusKernelLeft_def` and its
  siblings: the defining formulas.
* `SphereCeti.Leech.varphiExt_add_one`: `φ` is `1`-periodic.
* `SphereCeti.Leech.differentiableOn_varphiExt`, `SphereCeti.Leech.continuousOn_varphiExt`: `φ` is
  holomorphic, hence continuous, on the upper half-plane.
* `SphereCeti.Leech.isBigO_varphi`: `φ = O(exp(-2π Im τ))` at `i∞`.
* `SphereCeti.Leech.plusKernel_law_leftRight`, `SphereCeti.Leech.plusKernel_law_centralRay`: the
  signed transformation laws of the kernels.

## References

* H. Cohn, A. Kumar, S. D. Miller, D. Radchenko and M. Viazovska, *The sphere packing problem in
  dimension 24*, Annals of Mathematics 185 (2017), 1017–1033, Section 2.
-/

public section

open Complex ModularForm EisensteinSeries Filter Asymptotics
open UpperHalfPlane hiding I
open scoped MatrixGroups Real

namespace SphereCeti.Leech

/-- The quasimodular form
`φ = (25 E₄⁴ - 49 E₆² E₄ + 48 E₆ E₄² E₂ + (25 E₆² - 49 E₄³) E₂²) / Δ²` on the upper half-plane. -/
noncomputable def varphi (z : ℍ) : ℂ :=
  (25 * E₄ z ^ 4 - 49 * E₆ z ^ 2 * E₄ z + 48 * E₆ z * E₄ z ^ 2 * E2 z +
    (25 * E₆ z ^ 2 - 49 * E₄ z ^ 3) * E2 z ^ 2) / CuspForm.discriminant z ^ 2

/-- The defining formula of `φ`. -/
theorem varphi_def (z : ℍ) : varphi z =
    (25 * E₄ z ^ 4 - 49 * E₆ z ^ 2 * E₄ z + 48 * E₆ z * E₄ z ^ 2 * E2 z +
      (25 * E₆ z ^ 2 - 49 * E₄ z ^ 3) * E2 z ^ 2) / CuspForm.discriminant z ^ 2 :=
  (rfl)

/-- `φ` extended by `0` from the upper half-plane to `ℂ`. -/
noncomputable def varphiExt (z : ℂ) : ℂ :=
  if hz : 0 < z.im then varphi ⟨z, hz⟩ else 0

/-- On the upper half-plane, `varphiExt` is `φ`. -/
@[simp]
theorem varphiExt_of_im_pos {z : ℂ} (hz : 0 < z.im) : varphiExt z = varphi ⟨z, hz⟩ := by
  simp [varphiExt, hz]

/-- Off the upper half-plane, `varphiExt` vanishes. -/
@[simp]
theorem varphiExt_of_im_nonpos {z : ℂ} (hz : z.im ≤ 0) : varphiExt z = 0 := by
  simp [varphiExt, hz.not_gt]

/-- `φ` is `1`-periodic. -/
theorem varphiExt_add_one (z : ℂ) : varphiExt (z + 1) = varphiExt z := by
  by_cases hz : 0 < z.im
  · have hz' : 0 < (z + 1).im := by simpa using hz
    have hτ : (⟨z + 1, hz'⟩ : ℍ) = (1 : ℝ) +ᵥ ⟨z, hz⟩ := UpperHalfPlane.ext (by simp [add_comm])
    have h {f : ℍ → ℂ} (hf : Function.Periodic (f ∘ ofComplex) 1) : f ⟨z + 1, hz'⟩ = f ⟨z, hz⟩ :=
      hτ ▸ TauCeti.UpperHalfPlane.periodic_comp_ofComplex_iff.mp hf _
    rw [varphiExt_of_im_pos hz', varphiExt_of_im_pos hz, varphi, varphi, h E2_periodic,
      h (SlashInvariantFormClass.periodic_comp_ofComplex (f := E₄) one_mem_strictPeriods_SL),
      h (SlashInvariantFormClass.periodic_comp_ofComplex (f := E₆) one_mem_strictPeriods_SL),
      h (SlashInvariantFormClass.periodic_comp_ofComplex (f := CuspForm.discriminant)
        one_mem_strictPeriods_SL)]
  · have hz' : (z + 1).im ≤ 0 := by simpa using hz
    rw [varphiExt_of_im_nonpos hz', varphiExt_of_im_nonpos (not_lt.mp hz)]

/-- `φ` is holomorphic on the upper half-plane. -/
theorem differentiableOn_varphiExt : DifferentiableOn ℂ varphiExt {z : ℂ | 0 < z.im} := by
  have hE2 := UpperHalfPlane.mdifferentiable_iff.mp E2_mdifferentiable
  have hE4 := UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo E₄)
  have hE6 := UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo E₆)
  have hΔ := UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo CuspForm.discriminant)
  have hnum : DifferentiableOn ℂ (fun z : ℂ ↦
      25 * E₄ (ofComplex z) ^ 4 - 49 * E₆ (ofComplex z) ^ 2 * E₄ (ofComplex z) +
        48 * E₆ (ofComplex z) * E₄ (ofComplex z) ^ 2 * E2 (ofComplex z) +
        (25 * E₆ (ofComplex z) ^ 2 - 49 * E₄ (ofComplex z) ^ 3) * E2 (ofComplex z) ^ 2)
      {z : ℂ | 0 < z.im} := by
    have h4 : DifferentiableOn ℂ (fun z : ℂ ↦ E₄ (ofComplex z)) {z : ℂ | 0 < z.im} := hE4
    have h6 : DifferentiableOn ℂ (fun z : ℂ ↦ E₆ (ofComplex z)) {z : ℂ | 0 < z.im} := hE6
    have h2 : DifferentiableOn ℂ (fun z : ℂ ↦ E2 (ofComplex z)) {z : ℂ | 0 < z.im} := hE2
    fun_prop (disch := assumption)
  refine (hnum.div (hΔ.pow 2) fun z _ ↦ pow_ne_zero 2 (discriminant_ne_zero _)).congr
    fun z (hz : 0 < z.im) ↦ ?_
  simp only [Pi.div_apply, Pi.pow_apply, Function.comp_apply, ofComplex_apply_of_im_pos hz]
  rw [varphiExt_of_im_pos hz, varphi]

/-! ### Decay of `φ` at `i∞` -/

/-- The numerator of `φ`. -/
private noncomputable def numer (z : ℍ) : ℂ :=
  25 * E₄ z ^ 4 - 49 * E₆ z ^ 2 * E₄ z + 48 * E₆ z * E₄ z ^ 2 * E2 z +
    (25 * E₆ z ^ 2 - 49 * E₄ z ^ 3) * E2 z ^ 2

/-- `E₂`, `E₄` and `E₆` as functions with analytic cusp function. -/
private noncomputable def e2 : TauCeti.UpperHalfPlane.analyticCuspSubring 1 :=
  ⟨E2, TauCeti.UpperHalfPlane.mem_analyticCuspSubring.mpr analyticAt_cuspFunction_E2⟩

private noncomputable def e4 : TauCeti.UpperHalfPlane.analyticCuspSubring 1 :=
  ⟨E₄, TauCeti.UpperHalfPlane.mem_analyticCuspSubring.mpr
    (ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL)⟩

private noncomputable def e6 : TauCeti.UpperHalfPlane.analyticCuspSubring 1 :=
  ⟨E₆, TauCeti.UpperHalfPlane.mem_analyticCuspSubring.mpr
    (ModularFormClass.analyticAt_cuspFunction_zero E₆ one_pos one_mem_strictPeriods_SL)⟩

/-- The numerator of `φ`, as a function with analytic cusp function. -/
private noncomputable def numerS : TauCeti.UpperHalfPlane.analyticCuspSubring 1 :=
  25 * e4 ^ 4 - 49 * e6 ^ 2 * e4 + 48 * e6 * e4 ^ 2 * e2 + (25 * e6 ^ 2 - 49 * e4 ^ 3) * e2 ^ 2

private lemma coe_numerS : (numerS : ℍ → ℂ) = numer := by
  funext z
  rfl

/-- The first three `q`-coefficients of the numerator of `φ` vanish. -/
private lemma numer_qExpansion_coeff_eq_zero {n : ℕ} (hn : n < 3) :
    (qExpansion 1 numer).coeff n = 0 := by
  have hQ : qExpansion 1 numer = 25 * qExpansion 1 E₄ ^ 4 -
      49 * qExpansion 1 E₆ ^ 2 * qExpansion 1 E₄ +
      48 * qExpansion 1 E₆ * qExpansion 1 E₄ ^ 2 * qExpansion 1 E2 +
      (25 * qExpansion 1 E₆ ^ 2 - 49 * qExpansion 1 E₄ ^ 3) * qExpansion 1 E2 ^ 2 := by
    rw [← coe_numerS, ← TauCeti.UpperHalfPlane.qExpansionRingHom_apply]
    simp only [numerS, map_add, map_sub, map_mul, map_pow, map_ofNat,
      TauCeti.UpperHalfPlane.qExpansionRingHom_apply, e2, e4, e6]
  have h20 : (qExpansion 1 E2).coeff 0 = 1 := by simp [E2_qExpansion_coeff]
  have h21 : (qExpansion 1 E2).coeff 1 = -24 := by simp [E2_qExpansion_coeff]
  have h22 : (qExpansion 1 E2).coeff 2 = -72 := by
    rw [E2_qExpansion_coeff]
    norm_num [ArithmeticFunction.sigma_apply, Nat.prime_two.divisors]
  have h40 : (qExpansion 1 E₄).coeff 0 = 1 :=
    E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
  have h60 : (qExpansion 1 E₆).coeff 0 = 1 :=
    E_qExpansion_coeff_zero (k := 6) (by norm_num) ⟨3, rfl⟩
  have h41 := E₄_qExpansion_coeff_one
  have h61 := E₆_qExpansion_coeff_one
  have h42 := TauCeti.ModularForm.E₄_qExpansion_coeff_two
  have h62 := TauCeti.ModularForm.E₆_qExpansion_coeff_two
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h20 h40 h60
  rw [hQ]
  interval_cases n <;>
    norm_num [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, map_ofNat,
      h20, h21, h22, h40, h60, h41, h61, h42, h62]

/-- The numerator of `φ` is `1`-periodic. -/
private lemma periodic_numer : Function.Periodic (numer ∘ ofComplex) 1 := fun z ↦ by
  have h2 := E2_periodic z
  have h4 := SlashInvariantFormClass.periodic_comp_ofComplex (f := E₄) one_mem_strictPeriods_SL z
  have h6 := SlashInvariantFormClass.periodic_comp_ofComplex (f := E₆) one_mem_strictPeriods_SL z
  simp only [Function.comp_apply, ofReal_one] at h2 h4 h6 ⊢
  simp only [numer, h2, h4, h6]

/-- The numerator of `φ` is `O(exp(-6π Im τ))` at `i∞`. -/
private lemma isBigO_numer : numer =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im) ^ 3 := by
  have hana : AnalyticAt ℂ (cuspFunction 1 numer) 0 :=
    coe_numerS ▸ TauCeti.UpperHalfPlane.mem_analyticCuspSubring.mp numerS.2
  have hO := (TauCeti.UpperHalfPlane.cuspFunction_isBigO_pow_iff_qExpansion_coeff_eq_zero hana
    (N := 3)).2 fun n hn ↦ numer_qExpansion_coeff_eq_zero hn
  refine ((hO.comp_tendsto (qParam_tendsto_atImInfty one_pos)).congr_left fun τ ↦ ?_).congr_right
    fun τ ↦ ?_
  · exact UpperHalfPlane.eq_cuspFunction τ one_ne_zero periodic_numer
  · simp [Function.Periodic.norm_qParam]

/-- `φ` is `O(exp(-2π Im τ))` at `i∞`. -/
theorem isBigO_varphi : varphi =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im) := by
  -- The numerator is `O(exp(-6π Im τ))` and `Δ⁻² = O(exp(4π Im τ))`.
  have hden : (fun τ : ℍ ↦ (CuspForm.discriminant τ)⁻¹) =O[atImInfty]
      fun τ ↦ (Real.exp (-2 * π * τ.im))⁻¹ :=
    exp_isBigO_discriminant.inv_rev (Eventually.of_forall fun τ h ↦
      absurd h (Real.exp_pos _).ne')
  refine ((isBigO_numer.mul (hden.pow 2)).congr_left fun τ ↦ ?_).congr_right fun τ ↦ ?_
  · rw [varphi_def, div_eq_mul_inv, inv_pow]
    rfl
  · have := (Real.exp_pos (-2 * π * τ.im)).ne'
    field_simp

/-- `φ` is continuous on the upper half-plane. -/
theorem continuousOn_varphiExt : ContinuousOn varphiExt {z : ℂ | 0 < z.im} :=
  differentiableOn_varphiExt.continuousOn

/-- The left-leg kernel `φ(-1/(z+1)) (z+1)¹⁰` of the `+1` eigencomponent. -/
noncomputable def plusKernelLeft (z : ℂ) : ℂ := varphiExt (-1 / (z + 1)) * (z + 1) ^ 10

/-- The right-leg kernel `φ(-1/(z-1)) (z-1)¹⁰` of the `+1` eigencomponent. -/
noncomputable def plusKernelRight (z : ℂ) : ℂ := varphiExt (-1 / (z - 1)) * (z - 1) ^ 10

/-- The central-leg kernel `-2 φ(-1/z) z¹⁰` of the `+1` eigencomponent. -/
noncomputable def plusKernelCentral (z : ℂ) : ℂ := -2 * (varphiExt (-1 / z) * z ^ 10)

/-- The vertical-ray kernel `2 φ(z)` of the `+1` eigencomponent. -/
noncomputable def plusKernelRay (z : ℂ) : ℂ := 2 * varphiExt z

/-- The left-leg kernel is `φ(-1/(z+1)) (z+1)¹⁰`. -/
theorem plusKernelLeft_def (z : ℂ) :
    plusKernelLeft z = varphiExt (-1 / (z + 1)) * (z + 1) ^ 10 :=
  (rfl)

/-- The right-leg kernel is `φ(-1/(z-1)) (z-1)¹⁰`. -/
theorem plusKernelRight_def (z : ℂ) :
    plusKernelRight z = varphiExt (-1 / (z - 1)) * (z - 1) ^ 10 :=
  (rfl)

/-- The central-leg kernel is `-2 φ(-1/z) z¹⁰`. -/
theorem plusKernelCentral_def (z : ℂ) :
    plusKernelCentral z = -2 * (varphiExt (-1 / z) * z ^ 10) :=
  (rfl)

/-- The vertical-ray kernel is `2 φ(z)`. -/
theorem plusKernelRay_def (z : ℂ) : plusKernelRay z = 2 * varphiExt z :=
  (rfl)

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
  have hI : I ^ 12 = 1 := by norm_num
  rw [plusKernelLeft, plusKernelRight, harg, varphiExt_add_one, hpow, div_pow, hI]
  field_simp

/-- The central/ray transformation law of the `+1` kernels: `(i/z)¹² g_C(z) = -z⁻² g_Ray(-1/z)`. -/
theorem plusKernel_law_centralRay (z : ℂ) :
    (I / z) ^ 12 * plusKernelCentral z = -(z ^ 2)⁻¹ * plusKernelRay (-z⁻¹) := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hI : I ^ 12 = 1 := by norm_num
  rw [plusKernelCentral, plusKernelRay, div_pow, hI, neg_div, one_div]
  field_simp

end SphereCeti.Leech
