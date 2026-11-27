/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Analysis.Fourier.Exchange
public import SphereCeti.Contour.Legs

/-!
# The six-piece magic contour component

The magic contour of the E8 and Leech eigencomponents consists of the left legs
`-1 → -1 + i → i`, the right legs `1 → 1 + i → i`, the central leg `0 → i` and the vertical ray
from `i` to `i∞`.  For kernels `g_L, g_R, g_C, g_Ray : ℂ → ℂ`, the six-piece component at
`x ∈ E` integrates `g(z) exp(πi ‖x‖² z)` over these pieces, each with its own kernel.

When each piece is integrable on `E` and the Fourier transform exchanges the left legs with the
right legs and the central leg with the vertical ray, up to a common scalar `s`, the six-piece
component is an eigenfunction of the Fourier transform with eigenvalue `s`.

## Main definitions

* `SphereCeti.Contour.expKernel g r`: the kernel `z ↦ g z * exp(π i r z)`.
* `SphereCeti.Contour.centralLeg Ψ`: the contour integral of `Ψ` along `[0, i]`.
* `SphereCeti.Contour.verticalRay Ψ`: the integral `i ∫_{(1, ∞)} Ψ(t i) dt` along the vertical ray
  from `i` to `i∞`.
* `SphereCeti.Contour.sixPieceComponent gL gR gC gRay`: the six-piece component, a function on a
  real inner product space `E`.

## Main statements

* `SphereCeti.Contour.fourier_sixPieceComponent`: the six-piece assembly.
-/

public section

open Complex MeasureTheory
open scoped Real FourierTransform

namespace SphereCeti.Contour

/-- The exponential kernel `z ↦ g z * exp(π i r z)` of a contour component at the radial parameter
`r`. -/
noncomputable def expKernel (g : ℂ → ℂ) (r : ℝ) : ℂ → ℂ :=
  fun z ↦ g z * cexp (π * I * r * z)

/-- The exponential kernel is `z ↦ g z * exp(π i r z)`. -/
@[simp]
theorem expKernel_apply (g : ℂ → ℂ) (r : ℝ) (z : ℂ) :
    expKernel g r z = g z * cexp (π * I * r * z) :=
  (rfl)

/-- The central leg of the magic contour: the contour integral of `Ψ` along `[0, i]`. -/
noncomputable def centralLeg (Ψ : ℂ → ℂ) : ℂ :=
  ∫ᶜ z in Path.segment 0 I, scalarOneForm Ψ z

/-- The central leg is the contour integral of `Ψ` along `[0, i]`. -/
theorem centralLeg_def (Ψ : ℂ → ℂ) : centralLeg Ψ = ∫ᶜ z in Path.segment 0 I, scalarOneForm Ψ z :=
  (rfl)

/-- The vertical ray of the magic contour: `i ∫_{(1, ∞)} Ψ(t i) dt`, the integral of `Ψ` along the
ray from `i` to `i∞`. -/
noncomputable def verticalRay (Ψ : ℂ → ℂ) : ℂ :=
  I * ∫ t in Set.Ioi (1 : ℝ), Ψ (t * I)

/-- The vertical ray is `i ∫_{(1, ∞)} Ψ(t i) dt`. -/
theorem verticalRay_def (Ψ : ℂ → ℂ) : verticalRay Ψ = I * ∫ t in Set.Ioi (1 : ℝ), Ψ (t * I) :=
  (rfl)

section Component

variable {E : Type*} [Norm E]

/-- The six-piece magic contour component at `x ∈ E`: the left legs, right legs, central leg and
vertical ray, with kernels `gL`, `gR`, `gC`, `gRay`, at the radial parameter `‖x‖²`. -/
noncomputable def sixPieceComponent (gL gR gC gRay : ℂ → ℂ) (x : E) : ℂ :=
  leftLegs (expKernel gL (‖x‖ ^ 2)) + rightLegs (expKernel gR (‖x‖ ^ 2))
    + centralLeg (expKernel gC (‖x‖ ^ 2)) + verticalRay (expKernel gRay (‖x‖ ^ 2))

/-- The six-piece component is the sum of its four pieces at `‖x‖²`. -/
theorem sixPieceComponent_def (gL gR gC gRay : ℂ → ℂ) (x : E) :
    sixPieceComponent gL gR gC gRay x =
      leftLegs (expKernel gL (‖x‖ ^ 2)) + rightLegs (expKernel gR (‖x‖ ^ 2))
        + centralLeg (expKernel gC (‖x‖ ^ 2)) + verticalRay (expKernel gRay (‖x‖ ^ 2)) :=
  (rfl)

end Component

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Six-piece assembly.** If the four pieces of the six-piece component are integrable on `E`,
and the Fourier transform carries the left legs to `s` times the right legs, the right legs to `s`
times the left legs, the central leg to `s` times the vertical ray and the vertical ray to `s`
times the central leg, then the six-piece component is an eigenfunction of the Fourier transform
with eigenvalue `s`. -/
theorem fourier_sixPieceComponent {s : ℂ} {gL gR gC gRay : ℂ → ℂ}
    (hintL : Integrable fun x : E ↦ leftLegs (expKernel gL (‖x‖ ^ 2)))
    (hintR : Integrable fun x : E ↦ rightLegs (expKernel gR (‖x‖ ^ 2)))
    (hintC : Integrable fun x : E ↦ centralLeg (expKernel gC (‖x‖ ^ 2)))
    (hintRay : Integrable fun x : E ↦ verticalRay (expKernel gRay (‖x‖ ^ 2)))
    (hLR : 𝓕 (fun x : E ↦ leftLegs (expKernel gL (‖x‖ ^ 2)))
      = fun ξ ↦ s * rightLegs (expKernel gR (‖ξ‖ ^ 2)))
    (hRL : 𝓕 (fun x : E ↦ rightLegs (expKernel gR (‖x‖ ^ 2)))
      = fun ξ ↦ s * leftLegs (expKernel gL (‖ξ‖ ^ 2)))
    (hCRay : 𝓕 (fun x : E ↦ centralLeg (expKernel gC (‖x‖ ^ 2)))
      = fun ξ ↦ s * verticalRay (expKernel gRay (‖ξ‖ ^ 2)))
    (hRayC : 𝓕 (fun x : E ↦ verticalRay (expKernel gRay (‖x‖ ^ 2)))
      = fun ξ ↦ s * centralLeg (expKernel gC (‖ξ‖ ^ 2))) :
    𝓕 (sixPieceComponent (E := E) gL gR gC gRay)
      = fun ξ ↦ s * sixPieceComponent gL gR gC gRay ξ := by
  have h := hintL.fourier_add_add_add_eq_smul_add hintR hintC hintRay hLR hRL hCRay hRayC
  exact h.trans (funext fun ξ ↦ smul_eq_mul _ _)

end SphereCeti.Contour
