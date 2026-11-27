/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.SixPiece
public import SphereCeti.E8.PlusKernels

import SphereCeti.Contour.Eigenfunction
import SphereCeti.Contour.PieceRegularity
import SphereCeti.E8.PlusKernelContinuity
import SphereCeti.E8.PlusKernelIntegrability

/-!
# The `+1` eigencomponent of the E8 magic function is a Fourier eigenfunction

The `+1` eigencomponent of the E8 magic function is the six-piece contour component of the
kernels `g_L(z) = φ₀(-1/(z+1)) (z+1)²`, `g_R(z) = φ₀(-1/(z-1)) (z-1)²`, `g_C(z) = -2 φ₀(-1/z) z²`
and `g_Ray(z) = 2 φ₀(z)`: at `x`, the sum of the contour integrals of `g(z) exp(πi ‖x‖² z)` along
the left legs, the right legs, the central leg and the vertical ray, each with its own kernel.

The four pieces of the component are integrable on every finite-dimensional real inner product
space, the left-leg and central-leg pieces are continuous on every seminormed group, and the
one-form `g_R(z) exp(πirz) dz` is closed on the wedge for every `r ∈ ℝ`.  On a real inner product
space of dimension `8`, the component is its own Fourier transform: it is a Fourier eigenfunction
with eigenvalue `1`.

## Main statements

* `SphereCeti.E8.integrableOn_norm_plusKernelRay_mul_I`: `t ↦ ‖g_Ray(it)‖` is integrable on
  `(1, ∞)`.
* `SphereCeti.E8.integrable_leftLegs_plusKernelLeft`,
  `SphereCeti.E8.integrable_rightLegs_plusKernelRight`,
  `SphereCeti.E8.integrable_centralLeg_plusKernelCentral`,
  `SphereCeti.E8.integrable_verticalRay_plusKernelRay`: integrability of the four pieces.
* `SphereCeti.E8.continuous_leftLegs_plusKernelLeft`,
  `SphereCeti.E8.continuous_centralLeg_plusKernelCentral`: continuity of the left-leg and
  central-leg pieces.
* `SphereCeti.E8.closedOneFormOn_expKernel_plusKernelRight`: closedness of
  `g_R(z) exp(πirz) dz` on the wedge.
* `SphereCeti.E8.fourier_sixPiece_plus`: in dimension `8`, the six-piece component of the `+1`
  kernels is its own Fourier transform.

## References

* M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991–1015, Section 4.
-/

public section

open Complex MeasureTheory Set
open scoped Real FourierTransform

namespace SphereCeti.E8

open Contour

section Continuity

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The left-leg piece `x ↦ leftLegs (expKernel g_L ‖x‖²)` of the `+1` kernels is continuous. -/
theorem continuous_leftLegs_plusKernelLeft :
    Continuous fun x : E ↦ leftLegs (expKernel plusKernelLeft (‖x‖ ^ 2)) :=
  -- `‖g_L(z(t))‖` is integrable on `(0, 1]` along each left leg: it is a slice of the product
  -- integrability on `ℝ × (0, 1]`.
  continuous_leftLegs_expKernel fun p hp ↦
    integrableOn_norm_of_integrable_prod (integrable_plusKernelLeft (E := ℝ) p hp)

/-- The central-leg piece `x ↦ centralLeg (expKernel g_C ‖x‖²)` of the `+1` kernels is
continuous. -/
theorem continuous_centralLeg_plusKernelCentral :
    Continuous fun x : E ↦ centralLeg (expKernel plusKernelCentral (‖x‖ ^ 2)) := by
  -- `‖g_C(it)‖` is integrable on `(0, 1]`: it is a slice of the product integrability on
  -- `ℝ × (0, 1]`.
  refine continuous_centralLeg_expKernel ?_
  simpa only [zero_add, sub_zero] using integrableOn_norm_of_integrable_prod (E := ℝ) (a := 0)
    (b := I) (g := plusKernelCentral) (by
      simpa only [zero_add, sub_zero, mul_I_im, ofReal_re] using
        integrable_plusKernelCentral (E := ℝ))

end Continuity

/-- For every `r`, the one-form `g_R(z) exp(πirz) dz` of the right kernel is closed on the
wedge. -/
theorem closedOneFormOn_expKernel_plusKernelRight (r : ℝ) :
    ClosedOneFormOn (scalarOneForm (expKernel plusKernelRight r)) wedgeSet := by
  have hk : expKernel plusKernelRight r = fun z ↦ plusKernelRight z * cexp (π * I * r * z) :=
    funext (expKernel_apply _ _)
  have hw : {z : ℂ | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im} = wedgeSet :=
    Set.ext fun _ ↦ mem_wedgeSet.symm
  rw [hk, ← hw]
  exact ClosedOneFormOn.of_diffContOnCl (diffContOnCl_plusKernelRight_mul_cexp r)

/-- The norm `t ↦ ‖g_Ray(it)‖` of the ray kernel on the imaginary axis is integrable on
`(1, ∞)`. -/
theorem integrableOn_norm_plusKernelRay_mul_I :
    IntegrableOn (fun t : ℝ ↦ ‖plusKernelRay (t * I)‖) (Ioi 1) := by
  refine IntegrableOn.congr_fun (integrableOn_phi0Ext_mul_I.norm.const_mul 2) (fun t _ ↦ ?_)
    measurableSet_Ioi
  rw [plusKernelRay_def, norm_mul, Complex.norm_two]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The left-leg piece `x ↦ leftLegs (expKernel g_L ‖x‖²)` of the `+1` kernels is integrable. -/
theorem integrable_leftLegs_plusKernelLeft :
    Integrable fun x : E ↦ leftLegs (expKernel plusKernelLeft (‖x‖ ^ 2)) :=
  integrable_leftLegs_expKernel integrable_plusKernelLeft

/-- The right-leg piece `x ↦ rightLegs (expKernel g_R ‖x‖²)` of the `+1` kernels is
integrable. -/
theorem integrable_rightLegs_plusKernelRight :
    Integrable fun x : E ↦ rightLegs (expKernel plusKernelRight (‖x‖ ^ 2)) :=
  integrable_rightLegs_expKernel integrable_plusKernelRight

/-- The central-leg piece `x ↦ centralLeg (expKernel g_C ‖x‖²)` of the `+1` kernels is
integrable. -/
theorem integrable_centralLeg_plusKernelCentral :
    Integrable fun x : E ↦ centralLeg (expKernel plusKernelCentral (‖x‖ ^ 2)) :=
  integrable_centralLeg_expKernel integrable_plusKernelCentral

/-- The vertical-ray piece `x ↦ verticalRay (expKernel g_Ray ‖x‖²)` of the `+1` kernels is
integrable. -/
theorem integrable_verticalRay_plusKernelRay :
    Integrable fun x : E ↦ verticalRay (expKernel plusKernelRay (‖x‖ ^ 2)) :=
  integrable_verticalRay_expKernel integrableOn_norm_plusKernelRay_mul_I

/-- **The `+1` eigencomponent of the E8 magic function is a Fourier eigenfunction.**  On a real
inner product space `E` of dimension `8`, the six-piece contour component of the `+1` kernels
`g_L, g_R, g_C, g_Ray` is its own Fourier transform. -/
theorem fourier_sixPiece_plus (hE : Module.finrank ℝ E = 8) :
    𝓕 (sixPieceComponent (E := E) plusKernelLeft plusKernelRight plusKernelCentral
        plusKernelRay) =
      sixPieceComponent plusKernelLeft plusKernelRight plusKernelCentral plusKernelRay := by
  simpa only [one_mul] using fourier_sixPieceComponent_of_laws (k := 4) (s := 1)
    (hE.trans (by norm_num)) (one_pow 2) integrable_plusKernelLeft integrable_plusKernelRight
    integrable_plusKernelCentral integrableOn_norm_plusKernelRay_mul_I
    (fun z _ ↦ by rw [plusKernel_law_leftRight, one_mul])
    (fun r _ ↦ closedOneFormOn_expKernel_plusKernelRight r)
    fun t _ ↦ by rw [plusKernel_law_centralRay, neg_one_mul]

end SphereCeti.E8
