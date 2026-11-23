/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Contour deformation for half-infinite rectangles

This file proves the unbounded branch of the Layer 8 contour deformation: the integral of a
function along a horizontal edge `[x₁, x₂] + i y` can be replaced by the integrals along the two
vertical half-lines above its endpoints.

The hypotheses are those of Mathlib's bounded rectangle theorem
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`, on the closed
half-infinite strip, with explicit integrability of `f` on both half-lines.  The top edge is
controlled only by convergence of the top-edge integrals to zero.  This is weaker than the uniform
decay assumed by Mathlib's unbounded-rectangle theorem, so it is kept as a separate statement.

## Main results

* `SphereCeti.Contour.horizontal_add_vertical_eq_vertical_of_tendsto_top`: the roadmap target
  `SphereCeti.Suggested.Contour.horizontal_add_vertical_eq_vertical_of_tendsto_top`, with the same
  hypotheses and conclusion.

## Proof

For every height `m ≥ y`, the bounded rectangle theorem on `[x₁, x₂] × [y, m]` gives a vanishing
boundary integral.  As `m → ∞`, the top edge tends to zero by hypothesis and the vertical edges
tend to their half-line integrals by `MeasureTheory.intervalIntegral_tendsto_integral_Ioi`.  The
limit of an eventually-zero function is zero.

This is an independent formalization; no proof text is adapted from another repository.  The
corresponding Sphere-Packing-Lean file is `ForMathlib/CauchyGoursat/OpenRectangular.lean`
(see `UPSTREAM.md`, entry A12, which records Mathlib as the intended destination).
-/

public section

open Complex MeasureTheory Set Filter
open scoped Interval Topology

namespace SphereCeti.Contour

/-- Deformation of a horizontal edge into the two vertical half-lines above its endpoints, off a
countable exceptional set, matching the generality of Mathlib's bounded rectangle theorem.  The
half-line integrability hypotheses are explicit, and the top edge is controlled by convergence of
the top-edge integrals to zero. -/
theorem horizontal_add_vertical_eq_vertical_of_tendsto_top
    {f : ℂ → ℂ} {x₁ x₂ y : ℝ} {s : Set ℂ} (hs : s.Countable)
    (hcont : ContinuousOn f {z : ℂ | z.re ∈ Set.uIcc x₁ x₂ ∧ y ≤ z.im})
    (hdiff : ∀ z ∈ {z : ℂ | z.re ∈ Set.Ioo (min x₁ x₂) (max x₁ x₂) ∧ y < z.im} \ s,
      DifferentiableAt ℂ f z)
    (hint₁ : IntegrableOn (fun t : ℝ => f (x₁ + t * Complex.I)) (Set.Ioi y))
    (hint₂ : IntegrableOn (fun t : ℝ => f (x₂ + t * Complex.I)) (Set.Ioi y))
    (htop : Tendsto (fun m : ℝ => ∫ x in x₁..x₂, f (x + m * Complex.I)) atTop (𝓝 0)) :
    (∫ x in x₁..x₂, f (x + y * Complex.I))
        + Complex.I * ∫ t in Set.Ioi y, f (x₂ + t * Complex.I)
      = Complex.I * ∫ t in Set.Ioi y, f (x₁ + t * Complex.I) := by
  set B := ∫ x in x₁..x₂, f (x + y * Complex.I)
  set R := ∫ t in Set.Ioi y, f (x₂ + t * Complex.I)
  set L := ∫ t in Set.Ioi y, f (x₁ + t * Complex.I)
  -- The boundary of every bounded rectangle `[x₁, x₂] × [y, m]` with `y ≤ m` integrates to zero.
  have hrect : ∀ m : ℝ, y ≤ m →
      B - (∫ x in x₁..x₂, f (x + m * Complex.I))
          + Complex.I * (∫ t in y..m, f (x₂ + t * Complex.I))
          - Complex.I * (∫ t in y..m, f (x₁ + t * Complex.I)) = 0 := by
    intro m hm
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f
      ⟨x₁, y⟩ ⟨x₂, m⟩ s hs ?_ ?_
    · simpa [B, smul_eq_mul] using h
    · refine hcont.mono fun z hz => ?_
      rw [mem_reProdIm, uIcc_of_le hm] at hz
      exact ⟨hz.1, hz.2.1⟩
    · intro z hz
      refine hdiff z ⟨?_, hz.2⟩
      have hz' := hz.1
      rw [mem_reProdIm, min_eq_left hm, max_eq_right hm] at hz'
      exact ⟨hz'.1, hz'.2.1⟩
  -- Passing to the limit `m → ∞`.
  have hlim : Tendsto (fun m : ℝ => B - (∫ x in x₁..x₂, f (x + m * Complex.I))
        + Complex.I * (∫ t in y..m, f (x₂ + t * Complex.I))
        - Complex.I * (∫ t in y..m, f (x₁ + t * Complex.I))) atTop
      (𝓝 (B - 0 + Complex.I * R - Complex.I * L)) :=
    (((tendsto_const_nhds.sub htop).add
      ((intervalIntegral_tendsto_integral_Ioi y hint₂ tendsto_id).const_mul _)).sub
      ((intervalIntegral_tendsto_integral_Ioi y hint₁ tendsto_id).const_mul _))
  have hzero : B - 0 + Complex.I * R - Complex.I * L = 0 :=
    tendsto_nhds_unique hlim
      (tendsto_const_nhds.congr' ((eventually_ge_atTop y).mono fun m hm => (hrect m hm).symm))
  linear_combination hzero

end SphereCeti.Contour
