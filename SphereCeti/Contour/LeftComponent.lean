/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.CentralComponent
public import TauCeti.Analysis.Fourier.Continuous

/-!
# The Fourier transform of the left legs of the magic contour

Let `E` be a real inner product space of dimension `2k`.  For a segment `z(t) = a + t (b - a)`,
`0 < t ≤ 1`, and a kernel `g : ℂ → ℂ`, the Gaussian segment integral is the function
`x ↦ ∫₀¹ g(z(t)) exp(πi ‖x‖² z(t)) (b - a) dt` on `E`.  If `g(z(t)) exp(-π ‖x‖² Im z(t))` is
absolutely integrable on `E × (0, 1]`, this function is integrable on `E`.

For a path of two segments `a → b → c` in the upper half-plane, with this integrability along
both segments, the Fourier transform of the sum of the two Gaussian segment integrals is the sum of
the transported segment integrals
`ξ ↦ ∫₀¹ (i / z(t))^k g(z(t)) exp(πi ‖ξ‖² (-1 / z(t))) (b - a) dt`.  The left legs
`-1 → -1 + i → i` of the magic contour are such a path.

## Main statements

* `SphereCeti.Contour.integrable_segment_gaussian_integral`: a Gaussian segment integral is
  integrable under absolute integrability of the kernel along the segment.
* `SphereCeti.Contour.fourier_add_segment_gaussian_integral`: the Fourier transform of the sum of
  the Gaussian segment integrals along a path of two segments in the upper half-plane.

## References

* M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991–1015.
-/

public section

open Complex MeasureTheory Set
open scoped Real FourierTransform

namespace SphereCeti.Contour

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A Gaussian segment integral `x ↦ ∫₀¹ g(z(t)) exp(πi ‖x‖² z(t)) (b - a) dt` along the segment
`z(t) = a + t (b - a)` is integrable on `E` when `g(z(t)) exp(-π ‖x‖² Im z(t))` is absolutely
integrable on `E × (0, 1]`. -/
theorem integrable_segment_gaussian_integral {a b : ℂ} {g : ℂ → ℂ}
    (hint : Integrable (fun q : E × ℝ ↦
      ‖g (a + q.2 * (b - a))‖ * Real.exp (-π * ‖q.1‖ ^ 2 * (a + q.2 * (b - a)).im))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) :
    Integrable (fun x : E ↦ ∫ t in (0 : ℝ)..1,
      g (a + t * (b - a)) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a)) := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  by_cases hmeas : AEStronglyMeasurable (fun t : ℝ ↦ g (a + t * (b - a)))
    (volume.restrict (Ioc (0 : ℝ) 1))
  · -- The integrand is absolutely integrable on `E × (0, 1]`, so its partial integral is.
    refine Integrable.integral_prod_left (f := fun q : E × ℝ ↦ g (a + q.2 * (b - a)) *
      cexp (π * I * (‖q.1‖ ^ 2 : ℝ) * (a + q.2 * (b - a))) * (b - a)) ?_
    refine (hint.mul_const ‖b - a‖).mono' ?_ (ae_of_all _ fun q ↦ le_of_eq ?_)
    · have h1 : AEStronglyMeasurable (fun q : E × ℝ ↦ g (a + q.2 * (b - a)))
          (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := hmeas.comp_snd
      have h3 : Continuous fun q : E × ℝ ↦
          cexp (π * I * (‖q.1‖ ^ 2 : ℝ) * (a + q.2 * (b - a))) := by
        fun_prop
      exact (h1.mul h3.aestronglyMeasurable).mul aestronglyMeasurable_const
    · obtain ⟨x, t⟩ := q
      simp only [norm_mul, Complex.norm_exp]
      congr 2
      generalize ‖x‖ ^ 2 = r
      simp [mul_re, mul_im]
  · -- Without measurability of the kernel along the segment, the function vanishes.
    rcases eq_or_ne b a with rfl | hba
    · simp
    convert (integrable_zero E ℂ volume) using 1
    funext x
    refine integral_non_aestronglyMeasurable fun h ↦ hmeas ?_
    refine (aestronglyMeasurable_fun_smul_iff₀ (c := fun t : ℝ ↦
      cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a))
      (Measurable.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun t ↦ mul_ne_zero (exp_ne_zero _) (sub_ne_zero.mpr hba))).mp ?_
    exact h.congr (ae_of_all _ fun t ↦ by simp only [smul_eq_mul]; ring)

/-- **The Fourier transform along a path of two segments.**  Let `E` have dimension `2k`, and let
the segments `a → b` and `b → c` lie in the upper half-plane for `0 < t ≤ 1`.  If the kernel `g`
is absolutely integrable along both segments in the sense of
`SphereCeti.Contour.fourier_segment_gaussian_integral`, then the Fourier transform of the sum of
the two Gaussian segment integrals is the sum of the two transported segment integrals. -/
theorem fourier_add_segment_gaussian_integral {k : ℕ} (hk : Module.finrank ℝ E = 2 * k)
    {a b c : ℂ} (hab : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < (a + t * (b - a)).im)
    (hbc : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < (b + t * (c - b)).im) {g : ℂ → ℂ}
    (hint₁ : Integrable (fun q : E × ℝ ↦
      ‖g (a + q.2 * (b - a))‖ * Real.exp (-π * ‖q.1‖ ^ 2 * (a + q.2 * (b - a)).im))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))))
    (hint₂ : Integrable (fun q : E × ℝ ↦
      ‖g (b + q.2 * (c - b))‖ * Real.exp (-π * ‖q.1‖ ^ 2 * (b + q.2 * (c - b)).im))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) (ξ : E) :
    𝓕 (fun x : E ↦ (∫ t in (0 : ℝ)..1,
        g (a + t * (b - a)) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a)) +
        ∫ t in (0 : ℝ)..1,
          g (b + t * (c - b)) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (b + t * (c - b))) * (c - b)) ξ =
      (∫ t in (0 : ℝ)..1, (I / (a + t * (b - a))) ^ k * g (a + t * (b - a)) *
        cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * (-1 / (a + t * (b - a)))) * (b - a)) +
      ∫ t in (0 : ℝ)..1, (I / (b + t * (c - b))) ^ k * g (b + t * (c - b)) *
        cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * (-1 / (b + t * (c - b)))) * (c - b) := by
  have h := congrFun ((integrable_segment_gaussian_integral hint₁).fourier_add
    (integrable_segment_gaussian_integral hint₂)) ξ
  rw [Pi.add_apply, fourier_segment_gaussian_integral hk hab hint₁,
    fourier_segment_gaussian_integral hk hbc hint₂] at h
  exact h

end SphereCeti.Contour
