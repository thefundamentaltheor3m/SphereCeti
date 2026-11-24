/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.E8.PlusKernels

/-!
# Continuity of the `+1` E8 kernels at the cusps of the contour

The kernels of the `+1` eigencomponent of the E8 magic function involve `φ₀(-1/w) w²` with
`w = z ± 1` or `w = z`, which is defined by `0` at `w = 0`.  In the closed cone
`{w | |Re w| ≤ Im w}` the point `-1/w` tends to `i∞` as `w → 0`, where `φ₀` decays, so
`φ₀(-1/w) w² → 0`.  The left legs `-1 → -1 + i → i` of the magic contour lie in `-1` plus this
cone, so the transported left kernel `(i/z)⁴ g_L(z) exp(πir (-1/z))` is continuous on them, for
every `r`.

## Main statements

* `SphereCeti.E8.tendsto_phi0Ext_neg_one_div_mul_sq`: `φ₀(-1/w) w² → 0` as `w → 0` in the cone.
* `SphereCeti.E8.continuousOn_plusKernelLeft_transport`: the transported left kernel is continuous
  on the left legs.
-/

public section

open Complex Filter Topology Asymptotics
open UpperHalfPlane hiding I
open scoped Real

namespace SphereCeti.E8

/-- For `w` in the cone `|Re w| ≤ Im w`, `w ≠ 0`, the point `-1/w` has imaginary part at least
`1 / (2 ‖w‖)`. -/
private lemma one_div_two_mul_norm_le_im_neg_one_div {w : ℂ} (hw : |w.re| ≤ w.im) (hw0 : w ≠ 0) :
    1 / (2 * ‖w‖) ≤ (-1 / w).im := by
  have him : 0 < w.im := by
    rcases (abs_nonneg w.re).trans hw |>.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hw0
      have hre : w.re = 0 := abs_eq_zero.mp (le_antisymm (h ▸ hw) (abs_nonneg _))
      exact Complex.ext hre h.symm
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hsq : ‖w‖ ^ 2 ≤ 2 * w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [sq_abs w.re, sq_le_sq' (neg_le_of_abs_le hw) (le_of_abs_le hw)]
  have hdiv : (-1 / w).im = w.im / ‖w‖ ^ 2 := by
    rw [div_im, Complex.normSq_eq_norm_sq]
    simp only [neg_im, one_im, neg_zero, zero_mul, zero_div, neg_re, one_re, neg_mul, one_mul,
      zero_sub, neg_div, neg_neg]
  rw [hdiv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Complex.im_le_norm w]

/-- `φ₀(-1/w) w² → 0` as `w → 0` within the cone `|Re w| ≤ Im w`. -/
theorem tendsto_phi0Ext_neg_one_div_mul_sq :
    Tendsto (fun w : ℂ ↦ phi0Ext (-1 / w) * w ^ 2) (𝓝[{w : ℂ | |w.re| ≤ w.im}] 0) (𝓝 0) := by
  -- `φ₀` is bounded by `max C 0` where `Im ≥ A`.
  obtain ⟨C, hC⟩ := isBigO_phi0.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC
  set M := max A 1
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right A 1)
  have hb : Tendsto (fun w : ℂ ↦ max C 0 * ‖w‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun w : ℂ ↦ max C 0 * ‖w‖ ^ 2 := by fun_prop
    simpa using hc.tendsto 0
  refine squeeze_zero_norm' ?_ (tendsto_nhdsWithin_of_tendsto_nhds hb)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  refine ⟨1 / (2 * M), by positivity, fun w hwdist hw ↦ ?_⟩
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  rw [dist_zero_right] at hwdist
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hIm := one_div_two_mul_norm_le_im_neg_one_div hw hw0
  have hlarge : M < (-1 / w).im := by
    refine lt_of_lt_of_le ?_ hIm
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hwdist
    linarith
  have hpos : 0 < (-1 / w).im := hM.trans hlarge
  have hφ := hA ⟨-1 / w, hpos⟩ ((le_max_left A 1).trans hlarge.le)
  simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hφ
  rw [norm_mul, norm_pow, phi0Ext_of_im_pos hpos]
  have hexp : Real.exp (-2 * π * (⟨-1 / w, hpos⟩ : ℍ).im) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 < (⟨-1 / w, hpos⟩ : ℍ).im := hpos
    nlinarith [Real.pi_pos]
  have hφ' : ‖phi0 ⟨-1 / w, hpos⟩‖ ≤ max C 0 :=
    hφ.trans ((mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le).trans
      (by nlinarith [le_max_right C 0, Real.exp_pos (-2 * π * (⟨-1 / w, hpos⟩ : ℍ).im)]))
  exact mul_le_mul_of_nonneg_right hφ' (by positivity)

/-- The closed cone `|Re w| ≤ Im w` is convex. -/
private lemma convex_cone : Convex ℝ {w : ℂ | |w.re| ≤ w.im} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul]
  calc |a * x.re + b * y.re| ≤ |a * x.re| + |b * y.re| := abs_add_le _ _
    _ = a * |x.re| + b * |y.re| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * x.im + b * y.im := by gcongr

/-- The left legs, shifted by `1`, lie in the cone `|Re w| ≤ Im w`. -/
private lemma add_one_mem_cone {z : ℂ}
    (hz : z ∈ segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I) :
    z + 1 ∈ {w : ℂ | |w.re| ≤ w.im} := by
  have hmem : ∀ {a b : ℂ}, a + 1 ∈ {w : ℂ | |w.re| ≤ w.im} → b + 1 ∈ {w : ℂ | |w.re| ≤ w.im} →
      z ∈ segment ℝ a b → z + 1 ∈ {w : ℂ | |w.re| ≤ w.im} := by
    intro a b ha hb hz
    have h : 1 + z ∈ segment ℝ (1 + a) (1 + b) := (mem_segment_translate ℝ 1).mpr hz
    rw [add_comm 1 z, add_comm 1 a, add_comm 1 b] at h
    exact convex_cone.segment_subset ha hb h
  rcases hz with hz | hz
  · exact hmem (by simp) (by simp) hz
  · exact hmem (by simp) (by simp) hz

/-- The transported left kernel `(i/z)⁴ g_L(z) exp(πir (-1/z))` is continuous on the left legs
`-1 → -1 + i → i`, for every `r`. -/
theorem continuousOn_plusKernelLeft_transport (r : ℝ) :
    ContinuousOn (fun z : ℂ ↦ (I / z) ^ 4 * plusKernelLeft z * cexp (π * I * r * (-z⁻¹)))
      (segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I) := by
  intro z hz
  have hcone := add_one_mem_cone hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at hcone
  have hsplit : (fun z : ℂ ↦ (I / z) ^ 4 * plusKernelLeft z * cexp (π * I * r * (-z⁻¹))) =
      fun z ↦ ((I / z) ^ 4 * cexp (π * I * r * (-z⁻¹))) *
        (phi0Ext (-1 / (z + 1)) * (z + 1) ^ 2) := by
    funext z
    rw [plusKernelLeft_def]
    ring
  rw [hsplit]
  have hA : ContinuousAt (fun z : ℂ ↦ (I / z) ^ 4 * cexp (π * I * r * (-z⁻¹))) z := by
    fun_prop (disch := exact hz0)
  rcases eq_or_ne z (-1) with rfl | hz1
  · -- At `-1` the kernel factor tends to `0`.
    have hB : Tendsto (fun z : ℂ ↦ phi0Ext (-1 / (z + 1)) * (z + 1) ^ 2)
        (𝓝[segment ℝ (-1) (-1 + I) ∪ segment ℝ (-1 + I) I] (-1)) (𝓝 0) := by
      refine tendsto_phi0Ext_neg_one_div_mul_sq.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
      · have h : Tendsto (fun z : ℂ ↦ z + 1) (𝓝 (-1)) (𝓝 0) := by
          have hc : Continuous fun z : ℂ ↦ z + 1 := by fun_prop
          simpa using hc.tendsto (-1 : ℂ)
        exact h.mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun z hz ↦ add_one_mem_cone hz
    have h := (hA.tendsto.mono_left nhdsWithin_le_nhds).mul hB
    simpa [ContinuousWithinAt] using h
  · -- Elsewhere `-1/(z+1)` lies in the upper half-plane, where `φ₀` is continuous.
    have hz1' : z + 1 ≠ 0 := fun h ↦ hz1 (eq_neg_of_add_eq_zero_left h)
    have hpos : 0 < (-1 / (z + 1)).im :=
      lt_of_lt_of_le (by positivity) (one_div_two_mul_norm_le_im_neg_one_div hcone hz1')
    have hφ : ContinuousAt (fun z : ℂ ↦ phi0Ext (-1 / (z + 1))) z :=
      (continuousOn_phi0Ext.continuousAt ((isOpen_lt continuous_const
        Complex.continuous_im).mem_nhds hpos)).comp (f := fun z : ℂ ↦ -1 / (z + 1))
        (by fun_prop (disch := exact hz1'))
    exact (hA.mul (hφ.mul (by fun_prop))).continuousWithinAt

end SphereCeti.E8
