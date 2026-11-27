/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The inversion `w ↦ -1/w` near the vertex of a cone

As `w → 0` in the closed cone `{w : ℂ | |Re w| ≤ Im w}` with `w ≠ 0`, the point `-1/w` tends to
`i∞`.  For `F : ℂ → ℂ` bounded at `i∞` and `k ≠ 0`, the function `w ↦ F(-1/w) wᵏ` tends to `0`
as `w → 0` in the cone, and it is continuous on the cone if `F` is continuous on the upper
half-plane.  If `F` is holomorphic on the upper half-plane, then so is `w ↦ F(-1/w) wᵏ`, for every
`k`.

## Main statements

* `UpperHalfPlane.tendsto_im_neg_one_div_atTop`: `Im(-1/w) → ∞` as `w → 0` in the cone, `w ≠ 0`.
* `UpperHalfPlane.IsBoundedAtImInfty.tendsto_neg_one_div_mul_pow`: `F(-1/w) wᵏ → 0` as `w → 0` in
  the cone.
* `UpperHalfPlane.IsBoundedAtImInfty.continuousOn_neg_one_div_mul_pow`: `w ↦ F(-1/w) wᵏ` is
  continuous on the cone.
* `UpperHalfPlane.differentiableOn_neg_one_div_mul_pow`: `w ↦ F(-1/w) wᵏ` is holomorphic on the
  upper half-plane.
-/

public section

open Complex Filter Topology

namespace UpperHalfPlane

/-- A nonzero point of the cone `|Re w| ≤ Im w` lies in the upper half-plane. -/
private lemma im_pos_of_abs_re_le {w : ℂ} (hw : |w.re| ≤ w.im) (hw0 : w ≠ 0) : 0 < w.im := by
  refine ((abs_nonneg _).trans hw).lt_of_ne fun h ↦ hw0 (Complex.ext ?_ h.symm)
  rw [← h] at hw
  exact abs_nonpos_iff.mp hw

/-- For `w ≠ 0` in the cone `|Re w| ≤ Im w`, `Im(-1/w) ≥ ‖1/w‖ / 2`. -/
private lemma norm_inv_div_two_le_im_neg_one_div {w : ℂ} (hw : |w.re| ≤ w.im) (hw0 : w ≠ 0) :
    ‖w⁻¹‖ / 2 ≤ (-1 / w).im := by
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hsq : ‖w‖ ^ 2 ≤ 2 * w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_abs w.re, sq_le_sq' (neg_le_of_abs_le hw) (le_of_abs_le hw)]
  have hle : ‖w‖ ≤ 2 * w.im := by nlinarith [(abs_nonneg w.re).trans hw]
  calc ‖w⁻¹‖ / 2 = ‖w‖ / 2 / ‖w‖ ^ 2 := by
        rw [norm_inv]
        field_simp
    _ ≤ w.im / ‖w‖ ^ 2 := by gcongr; linarith
    _ = (-1 / w).im := by
        rw [neg_div, one_div, neg_im, inv_im, neg_div, neg_neg, Complex.normSq_eq_norm_sq]

/-- `Im(-1/w) → ∞` as `w → 0` within the cone `|Re w| ≤ Im w`, `w ≠ 0`. -/
theorem tendsto_im_neg_one_div_atTop :
    Tendsto (fun w : ℂ ↦ (-1 / w).im) (𝓝[{w : ℂ | |w.re| ≤ w.im} \ {0}] 0) atTop :=
  tendsto_atTop_mono' _ (eventually_nhdsWithin_of_forall fun _ hw ↦
      norm_inv_div_two_le_im_neg_one_div hw.1 hw.2)
    ((tendsto_norm_inv_nhdsNE_zero_atTop.atTop_div_const two_pos).mono_left
      (nhdsWithin_mono _ fun _ hw ↦ hw.2))

/-- If `F` is bounded at `i∞` and `k ≠ 0`, then `F(-1/w) wᵏ → 0` as `w → 0` within the cone
`|Re w| ≤ Im w`. -/
theorem IsBoundedAtImInfty.tendsto_neg_one_div_mul_pow {F : ℂ → ℂ} {k : ℕ}
    (hb : IsBoundedAtImInfty fun τ : ℍ ↦ F τ) (hk : k ≠ 0) :
    Tendsto (fun w : ℂ ↦ F (-1 / w) * w ^ k) (𝓝[{w : ℂ | |w.re| ≤ w.im}] 0) (𝓝 0) := by
  obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.mp hb
  -- Off the vertex, `F(-1/w)` stays bounded while `wᵏ → 0`.
  have hbdd : ∀ᶠ w in 𝓝[{w : ℂ | |w.re| ≤ w.im} \ {0}] 0, ‖F (-1 / w)‖ ≤ M := by
    filter_upwards [tendsto_im_neg_one_div_atTop.eventually_ge_atTop (max A 1)] with w hw
    exact hMA ⟨-1 / w, one_pos.trans_le ((le_max_right A 1).trans hw)⟩
      ((le_max_left A 1).trans hw)
  have hpow : Tendsto (fun w : ℂ ↦ w ^ k) (𝓝[{w : ℂ | |w.re| ≤ w.im} \ {0}] 0) (𝓝 0) :=
    ((continuous_pow k).tendsto' 0 0 (zero_pow hk)).mono_left nhdsWithin_le_nhds
  have hlim := isBoundedUnder_le_mul_tendsto_zero (f := fun w ↦ F (-1 / w))
    (isBoundedUnder_of_eventually_le hbdd) hpow
  -- At the vertex the function vanishes.
  have h0 : F (-1 / 0) * (0 : ℂ) ^ k = 0 := by simp [zero_pow hk]
  have h : ContinuousWithinAt (fun w : ℂ ↦ F (-1 / w) * w ^ k) {w : ℂ | |w.re| ≤ w.im} 0 :=
    continuousWithinAt_sdiff_self.mp (by simpa only [ContinuousWithinAt, h0] using hlim)
  simpa only [ContinuousWithinAt, h0] using h

/-- If `F` is continuous on the upper half-plane and bounded at `i∞`, and `k ≠ 0`, then
`w ↦ F(-1/w) wᵏ` is continuous on the cone `|Re w| ≤ Im w`. -/
theorem IsBoundedAtImInfty.continuousOn_neg_one_div_mul_pow {F : ℂ → ℂ} {k : ℕ}
    (hb : IsBoundedAtImInfty fun τ : ℍ ↦ F τ) (hF : ContinuousOn F {z : ℂ | 0 < z.im})
    (hk : k ≠ 0) :
    ContinuousOn (fun w : ℂ ↦ F (-1 / w) * w ^ k) {w : ℂ | |w.re| ≤ w.im} := by
  intro w hw
  rcases eq_or_ne w 0 with rfl | hw0
  · simpa only [ContinuousWithinAt, div_zero, zero_pow hk, mul_zero] using
      hb.tendsto_neg_one_div_mul_pow hk
  · have hpos := TauCeti.im_neg_one_div_pos (im_pos_of_abs_re_le hw hw0)
    exact (((hF.continuousAt (isOpen_upperHalfPlaneSet.mem_nhds hpos)).comp
      (f := fun w : ℂ ↦ -1 / w) (by fun_prop (disch := exact hw0))).mul
      (continuous_pow k).continuousAt).continuousWithinAt

/-- If `F` is holomorphic on the upper half-plane, then so is `w ↦ F(-1/w) wᵏ`. -/
theorem differentiableOn_neg_one_div_mul_pow {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im}) (k : ℕ) :
    DifferentiableOn ℂ (fun w : ℂ ↦ F (-1 / w) * w ^ k) {w : ℂ | 0 < w.im} := by
  intro w (hw : 0 < w.im)
  have hw0 : w ≠ 0 := fun h ↦ hw.ne' (by simp [h])
  have hpos := TauCeti.im_neg_one_div_pos hw
  exact (((hF.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hpos)).comp
    (f := fun w : ℂ ↦ -1 / w) w (by fun_prop (disch := exact hw0))).mul
    (differentiableAt_pow k)).differentiableWithinAt

end UpperHalfPlane
