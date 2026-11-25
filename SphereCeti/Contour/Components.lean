/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.SixPiece

import SphereCeti.Contour.CentralComponent

/-!
# The magic contour components and their Fourier transforms

For a kernel `g : ℂ → ℂ` and `r ∈ ℝ`, the components of the magic contour integrate the
exponential kernel `expKernel g r : z ↦ g(z) exp(πi r z)` along the left legs `-1 → -1 + i → i`,
the right legs `1 → 1 + i → i`, the central leg `0 → i` and the vertical ray from `i` to `i∞`.
Each of the four pieces is an explicit integral: along a segment `[a, b]` with
`z(t) = a + t (b - a)`, the contour integral is `∫₀¹ g(z(t)) exp(πi r z(t)) (b - a) dt`, and the
vertical ray is `i ∫_{(1, ∞)} g(it) exp(πi r (it)) dt`.

Let `E` be a real inner product space of dimension `2k`, let `s ∈ ℂ` and let `g'` be a second
kernel.  This file computes the Fourier transforms of the left-leg and central-leg components
`x ↦ leftLegs (expKernel g ‖x‖²)` and `x ↦ centralLeg (expKernel g ‖x‖²)`.

* Left legs.  Let `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` be integrable on `E × (0, 1]` along both left
  legs `z(t) = a + t (b - a)`, `(a, b) = (-1, -1 + i)` and `(a, b) = (-1 + i, i)`, let
  `(i/z)^k g(z) = s z⁻² g'(-1/z)` for every `z` in the upper half-plane, and let the one-form
  `expKernel g' r dz` be closed on the wedge for every `r ≥ 0`.  Then the Fourier transform of
  `x ↦ leftLegs (expKernel g ‖x‖²)` is `ξ ↦ s * rightLegs (expKernel g' ‖ξ‖²)`.
* Central leg.  Let `‖g(it)‖ exp(-π ‖x‖² t)` be integrable on `E × (0, 1]`, and let
  `(i/z)^k g(z) = -s z⁻² g'(-1/z)` for every `z = it` with `t > 0`.  Then the Fourier transform of
  `x ↦ centralLeg (expKernel g ‖x‖²)` is `ξ ↦ s * verticalRay (expKernel g' ‖ξ‖²)`.

Both identities hold for every `k`, including `k = 0`.  They are the left-to-right and
central-to-ray identities that the six-piece assembly `SphereCeti.Contour.fourier_sixPieceComponent`
takes as hypotheses.

## Main statements

* `SphereCeti.Contour.leftLegs_expKernel_eq`, `SphereCeti.Contour.rightLegs_expKernel_eq`,
  `SphereCeti.Contour.centralLeg_expKernel_eq`, `SphereCeti.Contour.verticalRay_expKernel_eq`:
  the four pieces of `expKernel g r` as explicit integrals.
* `SphereCeti.Contour.fourier_leftLegs_expKernel`: the Fourier transform of the left-leg
  component.
* `SphereCeti.Contour.fourier_centralLeg_expKernel`: the Fourier transform of the central-leg
  component.

## References

* M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991–1015.
-/

public section

open Complex MeasureTheory Set
open scoped Real FourierTransform

namespace SphereCeti.Contour

/-- The left legs of `expKernel g r` are the sum of the integrals
`∫₀¹ g(z(t)) exp(πi r z(t)) (b - a) dt` along the segments `z(t) = a + t (b - a)` with
`(a, b) = (-1, -1 + i)` and `(a, b) = (-1 + i, i)`. -/
theorem leftLegs_expKernel_eq (g : ℂ → ℂ) (r : ℝ) :
    leftLegs (expKernel g r) =
      (∫ t in (0 : ℝ)..1, g (-1 + t * ((-1 + I) - -1)) *
          cexp (π * I * r * (-1 + t * ((-1 + I) - -1))) * ((-1 + I) - -1)) +
        ∫ t in (0 : ℝ)..1, g ((-1 + I) + t * (I - (-1 + I))) *
          cexp (π * I * r * ((-1 + I) + t * (I - (-1 + I)))) * (I - (-1 + I)) := by
  simp only [leftLegs_def, curveIntegral_segment_scalarOneForm, expKernel_apply]

/-- The right legs of `expKernel g r` are the sum of the integrals
`∫₀¹ g(z(t)) exp(πi r z(t)) (b - a) dt` along the segments `z(t) = a + t (b - a)` with
`(a, b) = (1, 1 + i)` and `(a, b) = (1 + i, i)`. -/
theorem rightLegs_expKernel_eq (g : ℂ → ℂ) (r : ℝ) :
    rightLegs (expKernel g r) =
      (∫ t in (0 : ℝ)..1, g (1 + t * ((1 + I) - 1)) *
          cexp (π * I * r * (1 + t * ((1 + I) - 1))) * ((1 + I) - 1)) +
        ∫ t in (0 : ℝ)..1, g ((1 + I) + t * (I - (1 + I))) *
          cexp (π * I * r * ((1 + I) + t * (I - (1 + I)))) * (I - (1 + I)) := by
  simp only [rightLegs_def, curveIntegral_segment_scalarOneForm, expKernel_apply]

/-- The central leg of `expKernel g r` is `∫₀¹ g(it) exp(πi r (it)) i dt`. -/
theorem centralLeg_expKernel_eq (g : ℂ → ℂ) (r : ℝ) :
    centralLeg (expKernel g r) =
      ∫ t in (0 : ℝ)..1, g (t * I) * cexp (π * I * r * (t * I)) * I := by
  simp only [centralLeg_def, curveIntegral_segment_scalarOneForm, expKernel_apply, zero_add,
    sub_zero]

/-- The vertical ray of `expKernel g r` is `i ∫_{(1, ∞)} g(it) exp(πi r (it)) dt`. -/
theorem verticalRay_expKernel_eq (g : ℂ → ℂ) (r : ℝ) :
    verticalRay (expKernel g r) =
      I * ∫ t in Ioi (1 : ℝ), g (t * I) * cexp (π * I * r * (t * I)) := by
  simp only [verticalRay_def, expKernel_apply]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The Fourier transform of the left-leg component.**  Let `E` be a real inner product space of
dimension `2k` and let `s ∈ ℂ`.  Let `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` be integrable on
`E × (0, 1]` along both left legs `z(t) = a + t (b - a)`, `(a, b) = (-1, -1 + i)` and
`(a, b) = (-1 + i, i)`.  Let the kernels `g` and `g'` satisfy the signed inversion law
`(i/z)^k g(z) = s z⁻² g'(-1/z)` for every `z` in the upper half-plane, and let the one-form
`expKernel g' r dz` be closed on the wedge for every `r ≥ 0`.  Then the Fourier transform of
`x ↦ leftLegs (expKernel g ‖x‖²)` is `ξ ↦ s * rightLegs (expKernel g' ‖ξ‖²)`. -/
theorem fourier_leftLegs_expKernel {k : ℕ} (hk : Module.finrank ℝ E = 2 * k) {s : ℂ}
    {g g' : ℂ → ℂ}
    (hint : ∀ p ∈ ({(-1, -1 + I), (-1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖g (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))))
    (hlaw : ∀ z : ℂ, 0 < z.im → (I / z) ^ k * g z = s * (z ^ 2)⁻¹ * g' (-z⁻¹))
    (hclosed : ∀ r : ℝ, 0 ≤ r → ClosedOneFormOn (scalarOneForm (expKernel g' r)) wedgeSet) :
    𝓕 (fun x : E ↦ leftLegs (expKernel g (‖x‖ ^ 2))) =
      fun ξ ↦ s * rightLegs (expKernel g' (‖ξ‖ ^ 2)) := by
  funext ξ
  -- The Fourier transform of the two Gaussian segment integrals along the left legs.
  simp only [leftLegs_expKernel_eq]
  rw [fourier_add_segment_gaussian_integral (a := -1) (b := -1 + I) (c := I) hk
    (fun t ht ↦ by simpa using ht.1) (fun t _ ↦ by simp) (hint (-1, -1 + I) (mem_insert _ _))
    (hint (-1 + I, I) (mem_insert_of_mem _ (mem_singleton _)))]
  -- The result is the left legs of `z ↦ (i/z)^k g(z) exp(πi ‖ξ‖² (-1/z))`, which the signed
  -- inversion law relates to the right legs of `expKernel g' ‖ξ‖²`.
  rw [← perm_leftLegs_eq_smul_rightLegs
      (Ψ := fun z ↦ (I / z) ^ k * g z * cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * (-1 / z)))
      (fun z hz ↦ by rw [expKernel_apply, hlaw z hz, neg_div, one_div]; ring)
      (hclosed _ (by positivity)),
    leftLegs_def, curveIntegral_segment_scalarOneForm, curveIntegral_segment_scalarOneForm]

/-- **The Fourier transform of the central-leg component.**  Let `E` be a real inner product space
of dimension `2k` and let `s ∈ ℂ`.  Let `‖g(it)‖ exp(-π ‖x‖² t)` be integrable on `E × (0, 1]`,
and let the kernels `g` and `g'` satisfy the signed inversion law `(i/z)^k g(z) = -s z⁻² g'(-1/z)`
for every `z = it` with `t > 0`.  Then the Fourier transform of `x ↦ centralLeg (expKernel g ‖x‖²)`
is `ξ ↦ s * verticalRay (expKernel g' ‖ξ‖²)`. -/
theorem fourier_centralLeg_expKernel {k : ℕ} (hk : Module.finrank ℝ E = 2 * k) {s : ℂ}
    {g g' : ℂ → ℂ}
    (hint : Integrable (fun q : E × ℝ ↦ ‖g (q.2 * I)‖ * Real.exp (-π * ‖q.1‖ ^ 2 * q.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))))
    (hlaw : ∀ t : ℝ, 0 < t →
      (I / (t * I)) ^ k * g (t * I) = -s * ((t * I) ^ 2)⁻¹ * g' (-(t * I)⁻¹)) :
    𝓕 (fun x : E ↦ centralLeg (expKernel g (‖x‖ ^ 2))) =
      fun ξ ↦ s * verticalRay (expKernel g' (‖ξ‖ ^ 2)) := by
  simp only [centralLeg_expKernel_eq, verticalRay_expKernel_eq]
  exact fourier_centralComponent hk s hint hlaw

end SphereCeti.Contour
