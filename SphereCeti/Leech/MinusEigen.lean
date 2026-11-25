/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.SixPiece
public import SphereCeti.Leech.MinusKernels

import SphereCeti.Contour.Eigenfunction
import SphereCeti.Contour.PieceRegularity
import SphereCeti.Leech.MinusKernelRegularity

/-!
# The `-1` eigencomponent of the Leech magic function is a Fourier eigenfunction

The `-1` eigencomponent of the Leech magic function is the six-piece contour component of the
kernels `g_L(z) = ψ_T(z)`, `g_R(z) = ψ_T(z)`, `g_C(z) = -2 ψ_I(z)` and `g_Ray(z) = -2 ψ_S(z)`: at
`x`, the sum of the contour integrals of `g(z) exp(πi ‖x‖² z)` along the left legs, the right
legs, the central leg and the vertical ray, each with its own kernel.

The four pieces of the component are integrable on every finite-dimensional real inner product
space, the left-leg and central-leg pieces are continuous on every seminormed group, and the
one-form `g_R(z) exp(πirz) dz` is closed on the wedge for every `r ∈ ℝ`.  On a real inner product
space of dimension `24`, the Fourier transform of the component is minus the component: it is a
Fourier eigenfunction with eigenvalue `-1`.

## Main statements

* `SphereCeti.Leech.integrableOn_norm_minusKernelRay_mul_I`: `t ↦ ‖g_Ray(it)‖` is integrable on
  `(1, ∞)`.
* `SphereCeti.Leech.integrable_leftLegs_minusKernelLeft`,
  `SphereCeti.Leech.integrable_rightLegs_minusKernelRight`,
  `SphereCeti.Leech.integrable_centralLeg_minusKernelCentral`,
  `SphereCeti.Leech.integrable_verticalRay_minusKernelRay`: integrability of the four pieces.
* `SphereCeti.Leech.continuous_leftLegs_minusKernelLeft`,
  `SphereCeti.Leech.continuous_centralLeg_minusKernelCentral`: continuity of the left-leg and
  central-leg pieces.
* `SphereCeti.Leech.closedOneFormOn_expKernel_minusKernelRight`: closedness of
  `g_R(z) exp(πirz) dz` on the wedge.
* `SphereCeti.Leech.fourier_sixPiece_minus`: in dimension `24`, the Fourier transform of the
  six-piece component of the `-1` kernels is minus the component.

## References

* H. Cohn, A. Kumar, S. D. Miller, D. Radchenko and M. Viazovska, *The sphere packing problem in
  dimension 24*, Annals of Mathematics 185 (2017), 1017–1033, Section 3.
-/

public section

open Complex MeasureTheory Set
open scoped Real FourierTransform

namespace SphereCeti.Leech

open Contour

section Continuity

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The left-leg piece `x ↦ leftLegs (expKernel g_L ‖x‖²)` of the `-1` kernels is continuous. -/
theorem continuous_leftLegs_minusKernelLeft :
    Continuous fun x : E ↦ leftLegs (expKernel minusKernelLeft (‖x‖ ^ 2)) :=
  -- `‖g_L(z(t))‖` is integrable on `(0, 1]` along each left leg: it is a slice of the product
  -- integrability on `ℝ × (0, 1]`.
  continuous_leftLegs_expKernel fun p hp ↦
    integrableOn_norm_of_integrable_prod (integrable_minusKernelLeft (E := ℝ) p hp)

/-- The central-leg piece `x ↦ centralLeg (expKernel g_C ‖x‖²)` of the `-1` kernels is
continuous. -/
theorem continuous_centralLeg_minusKernelCentral :
    Continuous fun x : E ↦ centralLeg (expKernel minusKernelCentral (‖x‖ ^ 2)) := by
  -- `‖g_C(it)‖` is integrable on `(0, 1]`: it is a slice of the product integrability on
  -- `ℝ × (0, 1]`.
  refine continuous_centralLeg_expKernel ?_
  simpa only [zero_add, sub_zero] using integrableOn_norm_of_integrable_prod (E := ℝ) (a := 0)
    (b := I) (g := minusKernelCentral) (by
      simpa only [zero_add, sub_zero, mul_I_im, ofReal_re] using
        integrable_minusKernelCentral (E := ℝ))

end Continuity

/-- For every `r`, the one-form `g_R(z) exp(πirz) dz` of the right kernel is closed on the
wedge. -/
theorem closedOneFormOn_expKernel_minusKernelRight (r : ℝ) :
    ClosedOneFormOn (scalarOneForm (expKernel minusKernelRight r)) wedgeSet := by
  have hk : expKernel minusKernelRight r = fun z ↦ minusKernelRight z * cexp (π * I * r * z) :=
    funext (expKernel_apply _ _)
  have hw : {z : ℂ | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im} = wedgeSet :=
    Set.ext fun _ ↦ mem_wedgeSet.symm
  rw [hk, ← hw]
  exact ClosedOneFormOn.of_diffContOnCl (diffContOnCl_minusKernelRight_mul_cexp r)

/-- The norm `t ↦ ‖g_Ray(it)‖` of the ray kernel on the imaginary axis is integrable on
`(1, ∞)`. -/
theorem integrableOn_norm_minusKernelRay_mul_I :
    IntegrableOn (fun t : ℝ ↦ ‖minusKernelRay (t * I)‖) (Ioi 1) := by
  refine IntegrableOn.congr_fun (integrableOn_psiSExt_mul_I.norm.const_mul 2) (fun t _ ↦ ?_)
    measurableSet_Ioi
  rw [minusKernelRay_def, norm_mul, norm_neg, Complex.norm_two]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The left-leg piece `x ↦ leftLegs (expKernel g_L ‖x‖²)` of the `-1` kernels is integrable. -/
theorem integrable_leftLegs_minusKernelLeft :
    Integrable fun x : E ↦ leftLegs (expKernel minusKernelLeft (‖x‖ ^ 2)) :=
  integrable_leftLegs_expKernel integrable_minusKernelLeft

/-- The right-leg piece `x ↦ rightLegs (expKernel g_R ‖x‖²)` of the `-1` kernels is
integrable. -/
theorem integrable_rightLegs_minusKernelRight :
    Integrable fun x : E ↦ rightLegs (expKernel minusKernelRight (‖x‖ ^ 2)) :=
  integrable_rightLegs_expKernel integrable_minusKernelRight

/-- The central-leg piece `x ↦ centralLeg (expKernel g_C ‖x‖²)` of the `-1` kernels is
integrable. -/
theorem integrable_centralLeg_minusKernelCentral :
    Integrable fun x : E ↦ centralLeg (expKernel minusKernelCentral (‖x‖ ^ 2)) :=
  integrable_centralLeg_expKernel integrable_minusKernelCentral

/-- The vertical-ray piece `x ↦ verticalRay (expKernel g_Ray ‖x‖²)` of the `-1` kernels is
integrable. -/
theorem integrable_verticalRay_minusKernelRay :
    Integrable fun x : E ↦ verticalRay (expKernel minusKernelRay (‖x‖ ^ 2)) :=
  integrable_verticalRay_expKernel integrableOn_norm_minusKernelRay_mul_I

/-- **The `-1` eigencomponent of the Leech magic function is a Fourier eigenfunction.**  On a
real inner product space `E` of dimension `24`, the Fourier transform of the six-piece contour
component of the `-1` kernels `g_L, g_R, g_C, g_Ray` is minus the component. -/
theorem fourier_sixPiece_minus (hE : Module.finrank ℝ E = 24) :
    𝓕 (sixPieceComponent (E := E) minusKernelLeft minusKernelRight minusKernelCentral
        minusKernelRay) =
      fun ξ ↦ -sixPieceComponent minusKernelLeft minusKernelRight minusKernelCentral
        minusKernelRay ξ := by
  simpa only [neg_one_mul] using fourier_sixPieceComponent_of_laws (k := 12) (s := -1)
    (hE.trans (by norm_num)) (by norm_num) integrable_minusKernelLeft
    integrable_minusKernelRight integrable_minusKernelCentral
    integrableOn_norm_minusKernelRay_mul_I
    (fun z _ ↦ by rw [minusKernel_law_leftRight, neg_one_mul])
    (fun r _ ↦ closedOneFormOn_expKernel_minusKernelRight r)
    fun t _ ↦ by rw [minusKernel_law_centralRay, neg_neg, one_mul]

end SphereCeti.Leech
