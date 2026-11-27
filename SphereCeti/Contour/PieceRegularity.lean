/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.SixPiece

import SphereCeti.Contour.Components
import SphereCeti.Contour.Segment
import SphereCeti.Contour.SegmentContinuity
import SphereCeti.Contour.VerticalRay

/-!
# Integrability and continuity of the magic contour pieces

For a kernel `g : ℂ → ℂ`, the four pieces of the six-piece contour component of `g` are the
functions `x ↦ leftLegs (expKernel g ‖x‖²)`, `x ↦ rightLegs (expKernel g ‖x‖²)`,
`x ↦ centralLeg (expKernel g ‖x‖²)` and `x ↦ verticalRay (expKernel g ‖x‖²)`.

* Integrability, on a finite-dimensional real inner product space `E`.  The left-leg piece is
  integrable when `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` is integrable on `E × (0, 1]` along both left
  legs `z(t) = a + t (b - a)`, `(a, b) = (-1, -1 + i)` and `(a, b) = (-1 + i, i)`; likewise for
  the right-leg piece along `(a, b) = (1, 1 + i)` and `(a, b) = (1 + i, i)`, and for the
  central-leg piece along `z(t) = it`.  The vertical-ray piece is integrable when `‖g(it)‖` is
  integrable on `(1, ∞)`.
* Continuity, on a seminormed group `E`.  The left-leg piece is continuous when `‖g(z(t))‖` is
  integrable on `(0, 1]` along both left legs, and the central-leg piece is continuous when
  `‖g(it)‖` is integrable on `(0, 1]`.

The integrability statements are the integrability hypotheses of the six-piece assembly
`SphereCeti.Contour.fourier_sixPieceComponent`.  Continuity of the left-leg and central-leg pieces
is what Fourier inversion (`MeasureTheory.Integrable.fourier_reverse`) needs to reverse the
left-to-right and central-to-ray identities.

## Main statements

* `SphereCeti.Contour.integrable_leftLegs_expKernel`,
  `SphereCeti.Contour.integrable_rightLegs_expKernel`,
  `SphereCeti.Contour.integrable_centralLeg_expKernel`,
  `SphereCeti.Contour.integrable_verticalRay_expKernel`: integrability of the four pieces.
* `SphereCeti.Contour.continuous_leftLegs_expKernel`,
  `SphereCeti.Contour.continuous_centralLeg_expKernel`: continuity of the left-leg and central-leg
  pieces.
-/

public section

open Complex MeasureTheory Set
open scoped Real

namespace SphereCeti.Contour

section Continuity

variable {E : Type*} [SeminormedAddCommGroup E] {g : ℂ → ℂ}

/-- If `‖g(z(t))‖` is integrable on `(0, 1]` along both left legs `z(t) = a + t (b - a)`,
`(a, b) = (-1, -1 + i)` and `(a, b) = (-1 + i, i)`, then `x ↦ leftLegs (expKernel g ‖x‖²)` is
continuous. -/
theorem continuous_leftLegs_expKernel
    (hg : ∀ p ∈ ({(-1, -1 + I), (-1 + I, I)} : Set (ℂ × ℂ)),
      IntegrableOn (fun t : ℝ ↦ ‖g (p.1 + t * (p.2 - p.1))‖) (Ioc 0 1)) :
    Continuous fun x : E ↦ leftLegs (expKernel g (‖x‖ ^ 2)) := by
  simp only [leftLegs_expKernel_eq]
  exact (continuous_segment_gaussian_integral (a := -1) (b := -1 + I)
    (fun t ht ↦ by simpa using ht.1.le) (hg (-1, -1 + I) (mem_insert _ _))).add
    (continuous_segment_gaussian_integral (a := -1 + I) (b := I) (fun t _ ↦ by simp)
      (hg (-1 + I, I) (mem_insert_of_mem _ (mem_singleton _))))

/-- If `‖g(it)‖` is integrable on `(0, 1]`, then `x ↦ centralLeg (expKernel g ‖x‖²)` is
continuous. -/
theorem continuous_centralLeg_expKernel (hg : IntegrableOn (fun t : ℝ ↦ ‖g (t * I)‖) (Ioc 0 1)) :
    Continuous fun x : E ↦ centralLeg (expKernel g (‖x‖ ^ 2)) := by
  simp only [centralLeg_expKernel_eq]
  simpa using continuous_segment_gaussian_integral (E := E) (a := 0) (b := I) (g := g)
    (fun t ht ↦ by simpa using ht.1.le) (by simpa using hg)

end Continuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {g : ℂ → ℂ}

/-- If `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` is integrable on `E × (0, 1]` along both left legs
`z(t) = a + t (b - a)`, `(a, b) = (-1, -1 + i)` and `(a, b) = (-1 + i, i)`, then
`x ↦ leftLegs (expKernel g ‖x‖²)` is integrable on `E`. -/
theorem integrable_leftLegs_expKernel
    (hint : ∀ p ∈ ({(-1, -1 + I), (-1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖g (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) :
    Integrable fun x : E ↦ leftLegs (expKernel g (‖x‖ ^ 2)) := by
  simp only [leftLegs_expKernel_eq]
  exact (integrable_segment_gaussian_integral (a := -1) (b := -1 + I)
    (hint (-1, -1 + I) (mem_insert _ _))).fun_add
    (integrable_segment_gaussian_integral (a := -1 + I) (b := I)
      (hint (-1 + I, I) (mem_insert_of_mem _ (mem_singleton _))))

/-- If `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` is integrable on `E × (0, 1]` along both right legs
`z(t) = a + t (b - a)`, `(a, b) = (1, 1 + i)` and `(a, b) = (1 + i, i)`, then
`x ↦ rightLegs (expKernel g ‖x‖²)` is integrable on `E`. -/
theorem integrable_rightLegs_expKernel
    (hint : ∀ p ∈ ({(1, 1 + I), (1 + I, I)} : Set (ℂ × ℂ)),
      Integrable (fun q : E × ℝ ↦ ‖g (p.1 + q.2 * (p.2 - p.1))‖ *
        Real.exp (-π * ‖q.1‖ ^ 2 * (p.1 + q.2 * (p.2 - p.1)).im))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) :
    Integrable fun x : E ↦ rightLegs (expKernel g (‖x‖ ^ 2)) := by
  simp only [rightLegs_expKernel_eq]
  exact (integrable_segment_gaussian_integral (a := 1) (b := 1 + I)
    (hint (1, 1 + I) (mem_insert _ _))).fun_add
    (integrable_segment_gaussian_integral (a := 1 + I) (b := I)
      (hint (1 + I, I) (mem_insert_of_mem _ (mem_singleton _))))

/-- If `‖g(it)‖ exp(-π ‖x‖² t)` is integrable on `E × (0, 1]`, then
`x ↦ centralLeg (expKernel g ‖x‖²)` is integrable on `E`. -/
theorem integrable_centralLeg_expKernel
    (hint : Integrable (fun q : E × ℝ ↦ ‖g (q.2 * I)‖ * Real.exp (-π * ‖q.1‖ ^ 2 * q.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) :
    Integrable fun x : E ↦ centralLeg (expKernel g (‖x‖ ^ 2)) := by
  simp only [centralLeg_expKernel_eq]
  simpa using integrable_segment_gaussian_integral (E := E) (a := 0) (b := I) (g := g)
    (by simpa using hint)

/-- If `‖g(it)‖` is integrable on `(1, ∞)`, then `x ↦ verticalRay (expKernel g ‖x‖²)` is
integrable on `E`. -/
theorem integrable_verticalRay_expKernel (hg : IntegrableOn (fun t : ℝ ↦ ‖g (t * I)‖) (Ioi 1)) :
    Integrable fun x : E ↦ verticalRay (expKernel g (‖x‖ ^ 2)) := by
  simp only [verticalRay_expKernel_eq]
  exact (integrable_ray_gaussian_integral hg).const_mul I

end SphereCeti.Contour
