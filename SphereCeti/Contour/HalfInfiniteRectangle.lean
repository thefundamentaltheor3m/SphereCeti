/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Contour deformation for half-infinite rectangles

A function that is holomorphic, off a countable set, on the half-infinite strip above the segment
`[x₁, x₂] + i y` has its integral along that segment equal to the difference of its integrals along
the two vertical half-lines above the endpoints, provided the half-line integrals converge and the
integrals along the horizontal top edges `[x₁, x₂] + i m` tend to zero as `m → ∞`.

This is the unbounded branch of the roadmap's contour layer (`MIGRATION.md`, PR J6;
`UPSTREAM.md`, A12).  The proof applies Mathlib's Cauchy–Goursat theorem for a bounded rectangle,
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`, to the rectangles
with corners `x₁ + i y` and `x₂ + i m`, and lets `m → ∞`.

Mathlib's unbounded-rectangle theorems, in `Mathlib.Analysis.Complex.CauchyIntegral`, assume that
`f` tends to zero uniformly through the strip.  The theorem here assumes only that the top-edge
integrals tend to zero.

## Main results

- `SphereCeti.Contour.horizontal_add_vertical_eq_vertical_of_tendsto_top`: the deformation
  identity.  It proves the target of the same name in the `SphereCeti.Suggested.Contour`
  namespace of `SphereCetiRoadmap/Suggested.lean`, with the same hypotheses and conclusion.
-/

public section

open MeasureTheory Set Filter Complex
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
  -- The boundary integral of the rectangle with corners `x₁ + i y` and `x₂ + i m`.
  set boundary : ℝ → ℂ := fun m =>
    (∫ x in x₁..x₂, f (x + y * I)) - (∫ x in x₁..x₂, f (x + m * I))
      + I • (∫ t in y..m, f (x₂ + t * I)) - I • (∫ t in y..m, f (x₁ + t * I)) with hboundary
  -- It vanishes for every `m ≥ y`, by the bounded Cauchy–Goursat theorem.
  have hzero : boundary =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_ge_atTop y] with m hm
    have key := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f
      (x₁ + y * I) (x₂ + m * I) s hs ?_ ?_
    · simpa [hboundary] using key
    · refine hcont.mono fun z hz => ?_
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add, uIcc_of_le hm, mem_reProdIm] at hz
      exact ⟨hz.1, hz.2.1⟩
    · intro z hz
      refine hdiff z ⟨?_, hz.2⟩
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add, min_eq_left hm, max_eq_right hm] at hz
      exact ⟨hz.1.1, hz.1.2.1⟩
  -- As `m → ∞` it tends to the difference of the two sides of the claimed identity.
  have hlim : Tendsto boundary atTop
      (𝓝 ((∫ x in x₁..x₂, f (x + y * I)) - 0 + I • (∫ t in Ioi y, f (x₂ + t * I))
        - I • (∫ t in Ioi y, f (x₁ + t * I)))) :=
    (((tendsto_const_nhds.sub htop).add
      ((intervalIntegral_tendsto_integral_Ioi y hint₂ tendsto_id).const_smul I)).sub
      ((intervalIntegral_tendsto_integral_Ioi y hint₁ tendsto_id).const_smul I))
  have h := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hzero.symm)
  simp only [sub_zero, smul_eq_mul] at h
  exact sub_eq_zero.mp h

end SphereCeti.Contour
