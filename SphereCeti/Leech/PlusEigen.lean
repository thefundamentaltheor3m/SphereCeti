/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.SixPiece
public import SphereCeti.Leech.PlusKernels

import SphereCeti.Contour.Components
import SphereCeti.Contour.PieceRegularity
import SphereCeti.Leech.PlusKernelContinuity
import SphereCeti.Leech.PlusKernelIntegrability

/-!
# The `+1` eigencomponent of the Leech magic function is a Fourier eigenfunction

The `+1` eigencomponent of the Leech magic function is the six-piece contour component of the
kernels `g_L(z) = φ(-1/(z+1)) (z+1)¹⁰`, `g_R(z) = φ(-1/(z-1)) (z-1)¹⁰`,
`g_C(z) = -2 φ(-1/z) z¹⁰` and `g_Ray(z) = 2 φ(z)`: at `x`, the sum of the contour integrals of
`g(z) exp(πi ‖x‖² z)` along the left legs, the right legs, the central leg and the vertical ray,
each with its own kernel.

The four pieces of the component are integrable on every finite-dimensional real inner product
space, the left-leg and central-leg pieces are continuous on every seminormed group, and the
one-form `g_R(z) exp(πirz) dz` is closed on the wedge for every `r ∈ ℝ`.  On a real inner product
space of dimension `24`, the component is its own Fourier transform: it is a Fourier
eigenfunction with eigenvalue `1`.

## Main statements

* `SphereCeti.Leech.integrable_leftLegs_plusKernelLeft`,
  `SphereCeti.Leech.integrable_rightLegs_plusKernelRight`,
  `SphereCeti.Leech.integrable_centralLeg_plusKernelCentral`,
  `SphereCeti.Leech.integrable_verticalRay_plusKernelRay`: integrability of the four pieces.
* `SphereCeti.Leech.continuous_leftLegs_plusKernelLeft`,
  `SphereCeti.Leech.continuous_centralLeg_plusKernelCentral`: continuity of the left-leg and
  central-leg pieces.
* `SphereCeti.Leech.closedOneFormOn_expKernel_plusKernelRight`: closedness of
  `g_R(z) exp(πirz) dz` on the wedge.
* `SphereCeti.Leech.fourier_sixPiece_plus`: in dimension `24`, the six-piece component of the
  `+1` kernels is its own Fourier transform.

## References

* H. Cohn, A. Kumar, S. D. Miller, D. Radchenko and M. Viazovska, *The sphere packing problem in
  dimension 24*, Annals of Mathematics 185 (2017), 1017–1033, Section 2.
-/

public section

open Complex MeasureTheory Set
open scoped Real FourierTransform

namespace SphereCeti.Leech

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
    Integrable fun x : E ↦ verticalRay (expKernel plusKernelRay (‖x‖ ^ 2)) := by
  refine integrable_verticalRay_expKernel ?_
  refine IntegrableOn.congr_fun (integrableOn_varphiExt_mul_I.norm.const_mul 2) (fun t _ ↦ ?_)
    measurableSet_Ioi
  rw [plusKernelRay_def, norm_mul, Complex.norm_two]

/-- **The `+1` eigencomponent of the Leech magic function is a Fourier eigenfunction.**  On a
real inner product space `E` of dimension `24`, the six-piece contour component of the `+1`
kernels `g_L, g_R, g_C, g_Ray` is its own Fourier transform. -/
theorem fourier_sixPiece_plus (hE : Module.finrank ℝ E = 24) :
    𝓕 (sixPieceComponent (E := E) plusKernelLeft plusKernelRight plusKernelCentral
        plusKernelRay) =
      sixPieceComponent plusKernelLeft plusKernelRight plusKernelCentral plusKernelRay := by
  have hk : Module.finrank ℝ E = 2 * 12 := hE.trans (by norm_num)
  have hL := integrable_leftLegs_plusKernelLeft (E := E)
  have hR := integrable_rightLegs_plusKernelRight (E := E)
  have hC := integrable_centralLeg_plusKernelCentral (E := E)
  have hRay := integrable_verticalRay_plusKernelRay (E := E)
  -- The Fourier transform carries the left legs to the right legs and the central leg to the
  -- vertical ray, with eigenvalue `1`.
  have hLR : 𝓕 (fun x : E ↦ leftLegs (expKernel plusKernelLeft (‖x‖ ^ 2))) =
      fun ξ ↦ rightLegs (expKernel plusKernelRight (‖ξ‖ ^ 2)) := by
    simpa only [one_mul] using fourier_leftLegs_expKernel (s := 1) hk integrable_plusKernelLeft
      (fun z _ ↦ by rw [plusKernel_law_leftRight, one_mul])
      fun r _ ↦ closedOneFormOn_expKernel_plusKernelRight r
  have hCRay : 𝓕 (fun x : E ↦ centralLeg (expKernel plusKernelCentral (‖x‖ ^ 2))) =
      fun ξ ↦ verticalRay (expKernel plusKernelRay (‖ξ‖ ^ 2)) := by
    simpa only [one_mul] using fourier_centralLeg_expKernel (s := 1) hk
      integrable_plusKernelCentral fun t _ ↦ by rw [plusKernel_law_centralRay, neg_one_mul]
  -- Fourier inversion reverses both identities, since the left-leg and central-leg pieces are
  -- continuous and even.
  have hRL := hL.fourier_reverse hR continuous_leftLegs_plusKernelLeft
    (fun x ↦ by simp only [norm_neg]) (one_pow 2) (by rw [hLR, one_smul])
  have hRayC := hC.fourier_reverse hRay continuous_centralLeg_plusKernelCentral
    (fun x ↦ by simp only [norm_neg]) (one_pow 2) (by rw [hCRay, one_smul])
  rw [one_smul] at hRL hRayC
  simpa only [one_mul] using fourier_sixPieceComponent (s := 1) hL hR hC hRay
    (by simpa only [one_mul] using hLR) (by simpa only [one_mul] using hRL)
    (by simpa only [one_mul] using hCRay) (by simpa only [one_mul] using hRayC)

end SphereCeti.Leech
