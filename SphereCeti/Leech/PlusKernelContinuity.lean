/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.NumberTheory.ModularForms.Petersson
public import SphereCeti.Contour.KernelContinuity
public import SphereCeti.Leech.PlusKernels

/-!
# Continuity of the `+1` Leech kernels at the cusps of the contour

The kernels of the `+1` eigencomponent of the Leech magic function involve `φ(-1/w) w¹⁰` with
`w = z ± 1` or `w = z`, which is `0` at `w = 0`.  As `w → 0` in the closed cone
`{w | |Re w| ≤ Im w}`, `φ(-1/w) w¹⁰ → 0`.  The transported left kernel
`(i/z)¹² g_L(z) exp(πir (-1/z))` is continuous on the left legs `-1 → -1 + i → i`, and the right
kernel times `exp(πirz)` is holomorphic on the wedge `{0 < Im z, |Re z - 1| < Im z}` and
continuous on its closure, for every `r`.

## Main statements

* `SphereCeti.Leech.tendsto_varphiExt_neg_one_div_mul_pow`: `φ(-1/w) w¹⁰ → 0` as `w → 0` in the
  cone.
* `SphereCeti.Leech.continuousOn_plusKernelLeft_transport`: the transported left kernel is
  continuous on the left legs.
* `SphereCeti.Leech.diffContOnCl_plusKernelRight_mul_cexp`: the right kernel times `exp(πirz)` is
  holomorphic on the wedge `{0 < Im z, |Re z - 1| < Im z}` and continuous on its closure.
-/

public section

open Complex Filter Topology
open UpperHalfPlane hiding I
open scoped Real

namespace SphereCeti.Leech

/-- `φ` is bounded at `i∞`. -/
private lemma isBoundedAtImInfty_varphiExt : IsBoundedAtImInfty fun τ : ℍ ↦ varphiExt τ :=
  (IsZeroAtImInfty.of_exp_decay ⟨2 * π, Real.two_pi_pos,
    (isBigO_varphi.congr_left fun τ ↦ (varphiExt_of_im_pos τ.im_pos).symm).congr_right
      fun τ ↦ by ring_nf⟩).isBoundedAtImInfty

/-- `φ(-1/w) w¹⁰ → 0` as `w → 0` within the cone `|Re w| ≤ Im w`. -/
theorem tendsto_varphiExt_neg_one_div_mul_pow :
    Tendsto (fun w : ℂ ↦ varphiExt (-1 / w) * w ^ 10) (𝓝[{w : ℂ | |w.re| ≤ w.im}] 0) (𝓝 0) :=
  isBoundedAtImInfty_varphiExt.tendsto_neg_one_div_mul_pow (by norm_num)

/-- The transported left kernel `(i/z)¹² g_L(z) exp(πir (-1/z))` is continuous on the left legs
`-1 → -1 + i → i`, for every `r`. -/
theorem continuousOn_plusKernelLeft_transport (r : ℝ) :
    ContinuousOn (fun z : ℂ ↦ (I / z) ^ 12 * plusKernelLeft z * cexp (π * I * r * (-z⁻¹)))
      (segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I) :=
  Contour.continuousOn_I_div_pow_mul_mul_cexp
    ((Contour.continuousOn_neg_one_div_add_one_mul_pow continuousOn_varphiExt
      isBoundedAtImInfty_varphiExt (by norm_num)).congr fun z _ ↦ plusKernelLeft_def z) 12 _

/-- The transported right kernel `g_R(z) exp(πirz)` is holomorphic on the wedge
`{0 < Im z, |Re z - 1| < Im z}` and continuous on its closure, for every `r`. -/
theorem diffContOnCl_plusKernelRight_mul_cexp (r : ℝ) :
    DiffContOnCl ℂ (fun z : ℂ ↦ plusKernelRight z * cexp (π * I * r * z))
      {z : ℂ | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im} := by
  have h := Contour.diffContOnCl_neg_one_div_sub_one_mul_pow (k := 10) differentiableOn_varphiExt
    isBoundedAtImInfty_varphiExt (by norm_num)
  simp only [plusKernelRight_def]
  exact ⟨h.differentiableOn.mul (by fun_prop), h.continuousOn.mul (by fun_prop)⟩

end SphereCeti.Leech
