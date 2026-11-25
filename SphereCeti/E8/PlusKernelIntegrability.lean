/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.KernelIntegrability
public import SphereCeti.E8.PlusKernels

/-!
# Absolute integrability of the `+1` E8 kernels

Let `E` be a finite-dimensional real inner product space.  The kernels of the `+1` eigencomponent
of the E8 magic function satisfy the absolute integrability of `g(z(t)) exp(-π ‖x‖² Im z(t))` on
`E × (0, 1]` along the two left legs `-1 → -1 + i → i`, the two right legs `1 → 1 + i → i` and the
central leg `0 → i` of the magic contour.

## Main statements

* `SphereCeti.E8.integrable_plusKernelLeft`, `SphereCeti.E8.integrable_plusKernelRight`: absolute
  integrability of the left-leg and right-leg kernels along both legs of each pair.
* `SphereCeti.E8.integrable_plusKernelCentral`: absolute integrability of the central-leg kernel.
-/

public section

open Complex MeasureTheory Set
open UpperHalfPlane (atImInfty)
open scoped Real UpperHalfPlane

namespace SphereCeti.E8

/-- `φ₀ = O(exp(-2π Im τ))` at `i∞`, for `φ₀` extended by `0` to `ℂ`. -/
private lemma isBigO_phi0Ext :
    (fun τ : ℍ ↦ phi0Ext τ) =O[atImInfty] fun τ ↦ Real.exp (-(2 * π) * τ.im) :=
  (isBigO_phi0.congr_left fun τ ↦ (phi0Ext_of_im_pos τ.im_pos).symm).congr_right
    fun τ ↦ by ring_nf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The left-leg kernel `φ₀(-1/(z+1)) (z+1)²` satisfies the absolute integrability of
`g(z(t)) exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` along both left legs `-1 → -1 + i` and
`-1 + i → i`. -/
theorem integrable_plusKernelLeft :
    ∀ p ∈ ({(-1, -1 + I), (-1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖plusKernelLeft (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  simpa only [plusKernelLeft_def] using
    Contour.integrable_leftLegs_of_isBigO Real.two_pi_pos continuousOn_phi0Ext isBigO_phi0Ext 2

/-- The right-leg kernel `φ₀(-1/(z-1)) (z-1)²` satisfies the absolute integrability of
`g(z(t)) exp(-π ‖x‖² Im z(t))` on `E × (0, 1]` along both right legs `1 → 1 + i` and
`1 + i → i`. -/
theorem integrable_plusKernelRight :
    ∀ p ∈ ({(1, 1 + I), (1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖plusKernelRight (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  simpa only [plusKernelRight_def] using
    Contour.integrable_rightLegs_of_isBigO Real.two_pi_pos continuousOn_phi0Ext isBigO_phi0Ext 2

/-- The central-leg kernel `-2 φ₀(-1/z) z²` satisfies the absolute integrability of
`g(it) exp(-π ‖x‖² t)` on `E × (0, 1]`. -/
theorem integrable_plusKernelCentral :
    Integrable (fun q : E × ℝ ↦ ‖plusKernelCentral (q.2 * I)‖ * Real.exp (-π * ‖q.1‖ ^ 2 * q.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  refine ((Contour.integrable_centralLeg_of_isBigO Real.two_pi_pos continuousOn_phi0Ext
    isBigO_phi0Ext 2).const_mul 2).congr (ae_of_all _ fun q ↦ ?_)
  simp only [plusKernelCentral_def, norm_mul, norm_neg, Complex.norm_two]
  ring

end SphereCeti.E8
