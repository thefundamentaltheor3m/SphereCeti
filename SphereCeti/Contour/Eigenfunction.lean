/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.SixPiece

import SphereCeti.Contour.Components
import SphereCeti.Contour.PieceRegularity
import SphereCeti.Contour.SegmentContinuity

/-!
# Six-piece contour components that are Fourier eigenfunctions

Let `E` be a real inner product space of dimension `2k`, and let `s ∈ ℂ` with `s ^ 2 = 1`.  Let
`g_L, g_R, g_C, g_Ray : ℂ → ℂ` be kernels such that:

* `(i/z)^k g_L(z) = s z⁻² g_R(-1/z)` for every `z` in the upper half-plane, and the one-form
  `expKernel g_R r dz` is closed on the wedge for every `r ≥ 0`;
* `(i/z)^k g_C(z) = -s z⁻² g_Ray(-1/z)` for every `z = it` with `t > 0`;
* `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` is integrable on `E × (0, 1]` along both left legs for
  `g = g_L`, along both right legs for `g = g_R` and along the central leg for `g = g_C`, and
  `‖g_Ray(it)‖` is integrable on `(1, ∞)`.

Then the six-piece component of `g_L, g_R, g_C, g_Ray` is a Fourier eigenfunction with eigenvalue
`s`.  The `+1` and `-1` eigencomponents of the E8 and Leech magic functions have this form, with
`s = 1` and `s = -1`.

## Main statements

* `SphereCeti.Contour.fourier_sixPieceComponent_of_laws`: the six-piece component of kernels
  satisfying the transformation laws, the closedness and the integrability above is a Fourier
  eigenfunction with eigenvalue `s`.

## References

* M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991–1015, Section 4.
-/

public section

open Complex MeasureTheory Set
open scoped Real FourierTransform

namespace SphereCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Six-piece Fourier eigenfunctions from the transformation laws.**  Let `E` be a real inner
product space of dimension `2k`, and let `s ^ 2 = 1`.  Let `(i/z)^k g_L(z) = s z⁻² g_R(-1/z)` for
every `z` in the upper half-plane, with `expKernel g_R r dz` closed on the wedge for every `r ≥ 0`,
and let `(i/z)^k g_C(z) = -s z⁻² g_Ray(-1/z)` for every `z = it` with `t > 0`.  Let
`‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` be integrable on `E × (0, 1]` along both left legs for `g = g_L`,
along both right legs for `g = g_R` and along the central leg for `g = g_C`, and let `‖g_Ray(it)‖`
be integrable on `(1, ∞)`.  Then the Fourier transform of the six-piece component of
`g_L, g_R, g_C, g_Ray` is `s` times the component. -/
theorem fourier_sixPieceComponent_of_laws {k : ℕ} (hk : Module.finrank ℝ E = 2 * k) {s : ℂ}
    (hs : s ^ 2 = 1) {gL gR gC gRay : ℂ → ℂ}
    (hintL : ∀ p ∈ ({(-1, -1 + I), (-1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖gL (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))))
    (hintR : ∀ p ∈ ({(1, 1 + I), (1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖gR (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))))
    (hintC : Integrable (fun q : E × ℝ ↦ ‖gC (q.2 * I)‖ * Real.exp (-π * ‖q.1‖ ^ 2 * q.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))))
    (hintRay : IntegrableOn (fun t : ℝ ↦ ‖gRay (t * I)‖) (Ioi 1))
    (hlawLR : ∀ z : ℂ, 0 < z.im → (I / z) ^ k * gL z = s * (z ^ 2)⁻¹ * gR (-z⁻¹))
    (hclosed : ∀ r : ℝ, 0 ≤ r → ClosedOneFormOn (scalarOneForm (expKernel gR r)) wedgeSet)
    (hlawCRay : ∀ t : ℝ, 0 < t →
      (I / (t * I)) ^ k * gC (t * I) = -s * ((t * I) ^ 2)⁻¹ * gRay (-(t * I)⁻¹)) :
    𝓕 (sixPieceComponent (E := E) gL gR gC gRay) =
      fun ξ ↦ s * sixPieceComponent gL gR gC gRay ξ := by
  have hL := integrable_leftLegs_expKernel hintL
  have hR := integrable_rightLegs_expKernel hintR
  have hC := integrable_centralLeg_expKernel hintC
  have hRay := integrable_verticalRay_expKernel (E := E) hintRay
  -- The left-leg and central-leg pieces are continuous: the norms of `g_L` and `g_C` along their
  -- segments are integrable on `(0, 1]`, as slices of the product integrability.
  have hLc : Continuous fun x : E ↦ leftLegs (expKernel gL (‖x‖ ^ 2)) :=
    continuous_leftLegs_expKernel fun p hp ↦ integrableOn_norm_of_integrable_prod (hintL p hp)
  have hCc : Continuous fun x : E ↦ centralLeg (expKernel gC (‖x‖ ^ 2)) := by
    refine continuous_centralLeg_expKernel ?_
    simpa only [zero_add, sub_zero] using integrableOn_norm_of_integrable_prod (E := E)
      (a := 0) (b := I) (g := gC)
      (by simpa only [zero_add, sub_zero, mul_I_im, ofReal_re] using hintC)
  -- The left-to-right and central-to-ray identities, and their reverses by Fourier inversion,
  -- since the left-leg and central-leg pieces are continuous and even.
  have hsmul (G : E → ℂ) : (fun ξ ↦ s * G ξ) = s • G :=
    funext fun ξ ↦ by rw [Pi.smul_apply, smul_eq_mul]
  have hLR := fourier_leftLegs_expKernel hk hintL hlawLR hclosed
  have hCRay := fourier_centralLeg_expKernel hk hintC hlawCRay
  have hRL := hL.fourier_reverse hR hLc (fun x ↦ by simp only [norm_neg]) hs
    (hLR.trans (hsmul _))
  have hRayC := hC.fourier_reverse hRay hCc (fun x ↦ by simp only [norm_neg]) hs
    (hCRay.trans (hsmul _))
  exact fourier_sixPieceComponent hL hR hC hRay hLR (hRL.trans (hsmul _).symm) hCRay
    (hRayC.trans (hsmul _).symm)

end SphereCeti.Contour
