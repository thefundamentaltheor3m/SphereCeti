/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.SpecialFunctions.Exp
public import SphereCeti.Analysis.Complex.UpperHalfPlane.Cone

/-!
# Kernels `F(-1/(z ± 1)) (z ± 1)ᵏ` at the corners of the magic contour

Let `F : ℂ → ℂ` be bounded at `i∞` and `k ≠ 0`.  If `F` is continuous on the upper half-plane, the
left kernel `z ↦ F(-1/(z+1)) (z+1)ᵏ` is continuous on the left legs `-1 → -1 + i → i` of the magic
contour, corner `-1` included.  If `F` is holomorphic on the upper half-plane, the right kernel
`z ↦ F(-1/(z-1)) (z-1)ᵏ` is holomorphic on the wedge `{z | 0 < Im z, |Re z - 1| < Im z}` and
continuous on its closure, corner `1` included.  For every kernel `g` continuous on the left legs
and all `m : ℕ`, `c : ℂ`, the transported kernel `z ↦ (i/z)ᵐ g(z) exp(c · (-1/z))` is continuous
on the left legs.

## Main statements

* `SphereCeti.Contour.continuousOn_neg_one_div_add_one_mul_pow`: the left kernel is continuous on
  the left legs.
* `SphereCeti.Contour.continuousOn_I_div_pow_mul_mul_cexp`: the transported kernel is continuous on
  the left legs.
* `SphereCeti.Contour.diffContOnCl_neg_one_div_sub_one_mul_pow`: the right kernel is holomorphic
  on the wedge and continuous on its closure.
-/

public section

open Complex Set
open UpperHalfPlane hiding I

namespace SphereCeti.Contour

/-- The left legs `-1 → -1 + i → i`, shifted by `1`, lie in the cone `|Re w| ≤ Im w`. -/
private lemma add_one_mem_cone {z : ℂ}
    (hz : z ∈ segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I) : |(z + 1).re| ≤ (z + 1).im := by
  rw [segment_eq_image', segment_eq_image'] at hz
  rcases hz with ⟨t, ⟨ht0, -⟩, rfl⟩ | ⟨t, ⟨ht0, ht1⟩, rfl⟩
  · simpa using ht0
  · simp [abs_of_nonneg ht0, ht1]

/-- The left legs `-1 → -1 + i → i` avoid `0`. -/
private lemma ne_zero_of_mem_leftLegs {z : ℂ}
    (hz : z ∈ segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I) : z ≠ 0 := by
  rintro rfl
  exact absurd (add_one_mem_cone hz) (by norm_num)

/-- The closure of the wedge `{0 < Im z, |Re z - 1| < Im z}`, shifted by `-1`, lies in the cone
`|Re w| ≤ Im w`. -/
private lemma sub_one_mem_cone_of_mem_closure {z : ℂ}
    (hz : z ∈ closure {z : ℂ | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im}) :
    |(z - 1).re| ≤ (z - 1).im := by
  refine closure_minimal (t := {w : ℂ | |(w - 1).re| ≤ (w - 1).im}) (fun w hw ↦ ?_)
    (isClosed_le (by fun_prop) (by fun_prop)) hz
  simp only [mem_ofPred_eq, sub_re, one_re, sub_im, one_im, sub_zero] at hw ⊢
  exact abs_le.mpr ⟨by linarith [hw.2.2], hw.2.1.le⟩

/-- If `F` is continuous on the upper half-plane and bounded at `i∞`, and `k ≠ 0`, then
`z ↦ F(-1/(z+1)) (z+1)ᵏ` is continuous on the left legs `-1 → -1 + i → i`. -/
theorem continuousOn_neg_one_div_add_one_mul_pow {F : ℂ → ℂ} {k : ℕ}
    (hF : ContinuousOn F {z : ℂ | 0 < z.im}) (hb : IsBoundedAtImInfty fun τ : ℍ ↦ F τ)
    (hk : k ≠ 0) :
    ContinuousOn (fun z : ℂ ↦ F (-1 / (z + 1)) * (z + 1) ^ k)
      (segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I) :=
  (hb.continuousOn_neg_one_div_mul_pow hF hk).comp (continuous_add_const 1).continuousOn
    fun _ hz ↦ add_one_mem_cone hz

/-- If `g` is continuous on the left legs `-1 → -1 + i → i`, then so is
`z ↦ (i/z)ᵐ g(z) exp(c · (-1/z))`, for every `m` and `c`. -/
theorem continuousOn_I_div_pow_mul_mul_cexp {g : ℂ → ℂ}
    (hg : ContinuousOn g (segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I)) (m : ℕ) (c : ℂ) :
    ContinuousOn (fun z : ℂ ↦ (I / z) ^ m * g z * cexp (c * (-z⁻¹)))
      (segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I) := by
  have h0 : ∀ z ∈ segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I, z ≠ 0 :=
    fun _ hz ↦ ne_zero_of_mem_leftLegs hz
  fun_prop (disch := assumption)

/-- If `F` is holomorphic on the upper half-plane and bounded at `i∞`, and `k ≠ 0`, then
`z ↦ F(-1/(z-1)) (z-1)ᵏ` is holomorphic on the wedge `{0 < Im z, |Re z - 1| < Im z}` and
continuous on its closure. -/
theorem diffContOnCl_neg_one_div_sub_one_mul_pow {F : ℂ → ℂ} {k : ℕ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im}) (hb : IsBoundedAtImInfty fun τ : ℍ ↦ F τ)
    (hk : k ≠ 0) :
    DiffContOnCl ℂ (fun z : ℂ ↦ F (-1 / (z - 1)) * (z - 1) ^ k)
      {z : ℂ | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im} :=
  ⟨(differentiableOn_neg_one_div_mul_pow hF k).comp (differentiableOn_id.sub_const 1)
      fun z hz ↦ by simpa using hz.1,
    (hb.continuousOn_neg_one_div_mul_pow hF.continuousOn hk).comp
      (continuous_sub_right 1).continuousOn fun _ hz ↦ sub_one_mem_cone_of_mem_closure hz⟩

end SphereCeti.Contour
