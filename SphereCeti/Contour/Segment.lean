/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Analysis.Fourier.Continuous
public import TauCeti.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian segment integrals

Let `E` be a finite-dimensional real inner product space.  For a segment `z(t) = a + t (b - a)`,
`0 < t ≤ 1`, and a kernel `g : ℂ → ℂ`, the Gaussian segment integral is the function
`x ↦ ∫₀¹ g(z(t)) exp(πi ‖x‖² z(t)) (b - a) dt` on `E`.  The central leg `0 → i`, the left legs
`-1 → -1 + i → i` and the right legs `1 → 1 + i → i` of the magic contour are segments of this
kind.

Suppose that `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` is integrable on `E × (0, 1]`.  Then the Gaussian
segment integral is integrable on `E`.  If moreover `E` has dimension `2k` and `z(t)` lies in the
upper half-plane for `0 < t ≤ 1`, its Fourier transform is the transported segment integral
`ξ ↦ ∫₀¹ (i / z(t))^k g(z(t)) exp(πi ‖ξ‖² (-1 / z(t))) (b - a) dt`, for every `k`, including
`k = 0`.  Along a path of two such segments `a → b → c`, the Fourier transform of the sum of the two
Gaussian segment integrals is the sum of the two transported segment integrals.

## Main statements

* `SphereCeti.Contour.integrable_segment_gaussian_integral`: integrability of a Gaussian segment
  integral on `E`.
* `SphereCeti.Contour.fourier_segment_gaussian_integral`: the Fourier transform of a Gaussian
  segment integral.
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

/-- If `g` is a.e. strongly measurable along the segment `z(t) = a + t (b - a)`, `0 < t ≤ 1`, and
`‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` is integrable on `E × (0, 1]`, then the integrand
`g(z(t)) exp(πi ‖x‖² z(t)) (b - a)` of the Gaussian segment integral is integrable on
`E × (0, 1]`. -/
private lemma integrable_segment_gaussian_integrand {a b : ℂ} {g : ℂ → ℂ}
    (hmeas : AEStronglyMeasurable (fun t : ℝ ↦ g (a + t * (b - a)))
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hint : Integrable (fun q : E × ℝ ↦
      ‖g (a + q.2 * (b - a))‖ * Real.exp (-π * ‖q.1‖ ^ 2 * (a + q.2 * (b - a)).im))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) :
    Integrable (fun q : E × ℝ ↦
      g (a + q.2 * (b - a)) * cexp (π * I * (‖q.1‖ ^ 2 : ℝ) * (a + q.2 * (b - a))) * (b - a))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  refine (hint.mul_const ‖b - a‖).mono' ?_ (ae_of_all _ fun q ↦ le_of_eq ?_)
  · have hexp : Continuous fun q : E × ℝ ↦
        cexp (π * I * (‖q.1‖ ^ 2 : ℝ) * (a + q.2 * (b - a))) := by
      fun_prop
    exact (hmeas.comp_snd.mul hexp.aestronglyMeasurable).mul aestronglyMeasurable_const
  · obtain ⟨x, t⟩ := q
    simp only [norm_mul, Complex.norm_exp]
    congr 2
    generalize ‖x‖ ^ 2 = r
    simp [mul_re, mul_im]

/-- If `g` is not a.e. strongly measurable along the segment `z(t) = a + t (b - a)`, `0 < t ≤ 1`,
with `b ≠ a`, then `∫_{(0, 1]} g(z(t)) exp(πi r z(t)) (b - a) dt = 0` for every real `r`. -/
private lemma setIntegral_segment_gaussian_eq_zero {a b : ℂ} (hba : b ≠ a) {g : ℂ → ℂ}
    (hmeas : ¬ AEStronglyMeasurable (fun t : ℝ ↦ g (a + t * (b - a)))
      (volume.restrict (Ioc (0 : ℝ) 1))) (r : ℝ) :
    ∫ t in Ioc (0 : ℝ) 1, g (a + t * (b - a)) * cexp (π * I * r * (a + t * (b - a))) * (b - a) =
      0 := by
  refine integral_non_aestronglyMeasurable fun h ↦ hmeas ?_
  refine (aestronglyMeasurable_fun_smul_iff₀ (c := fun t : ℝ ↦
    cexp (π * I * r * (a + t * (b - a))) * (b - a))
    (Measurable.aestronglyMeasurable (by fun_prop))
    (ae_of_all _ fun t ↦ mul_ne_zero (exp_ne_zero _) (sub_ne_zero.mpr hba))).mp ?_
  exact h.congr (ae_of_all _ fun t ↦ by simp only [smul_eq_mul]; ring)

/-- A Gaussian segment integral `x ↦ ∫₀¹ g(z(t)) exp(πi ‖x‖² z(t)) (b - a) dt` along the segment
`z(t) = a + t (b - a)` is integrable on `E` when `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` is integrable on
`E × (0, 1]`. -/
theorem integrable_segment_gaussian_integral {a b : ℂ} {g : ℂ → ℂ}
    (hint : Integrable (fun q : E × ℝ ↦
      ‖g (a + q.2 * (b - a))‖ * Real.exp (-π * ‖q.1‖ ^ 2 * (a + q.2 * (b - a)).im))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) :
    Integrable (fun x : E ↦ ∫ t in (0 : ℝ)..1,
      g (a + t * (b - a)) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a)) := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  by_cases hmeas : AEStronglyMeasurable (fun t : ℝ ↦ g (a + t * (b - a)))
    (volume.restrict (Ioc (0 : ℝ) 1))
  · exact (integrable_segment_gaussian_integrand hmeas hint).integral_prod_left
  · rcases eq_or_ne b a with rfl | hba
    · simp
    simp_rw [setIntegral_segment_gaussian_eq_zero hba hmeas]
    exact integrable_zero E ℂ volume

/-- **The Fourier transform of a Gaussian segment integral.**  Let `E` be a real inner product
space of dimension `2k`, and let the segment `z(t) = a + t (b - a)`, `0 < t ≤ 1`, lie in the upper
half-plane.  If `‖g(z(t))‖ exp(-π ‖x‖² Im z(t))` is integrable on `E × (0, 1]`, then the Fourier
transform of `x ↦ ∫₀¹ g(z(t)) exp(πi ‖x‖² z(t)) (b - a) dt` is
`ξ ↦ ∫₀¹ (i / z(t))^k g(z(t)) exp(πi ‖ξ‖² (-1 / z(t))) (b - a) dt`. -/
theorem fourier_segment_gaussian_integral {k : ℕ} (hk : Module.finrank ℝ E = 2 * k) {a b : ℂ}
    (hab : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < (a + t * (b - a)).im) {g : ℂ → ℂ}
    (hint : Integrable (fun q : E × ℝ ↦
      ‖g (a + q.2 * (b - a))‖ * Real.exp (-π * ‖q.1‖ ^ 2 * (a + q.2 * (b - a)).im))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) (ξ : E) :
    𝓕 (fun x : E ↦ ∫ t in (0 : ℝ)..1,
        g (a + t * (b - a)) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a)) ξ =
      ∫ t in (0 : ℝ)..1, (I / (a + t * (b - a))) ^ k * g (a + t * (b - a)) *
        cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * (-1 / (a + t * (b - a)))) * (b - a) := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  rcases eq_or_ne b a with rfl | hba
  · simp [Real.fourier_eq]
  have hz0 (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : a + t * (b - a) ≠ 0 := fun h ↦
    (hab t ht).ne' (by rw [h, zero_im])
  by_cases hmeas : AEStronglyMeasurable (fun t : ℝ ↦ g (a + t * (b - a)))
    (volume.restrict (Ioc (0 : ℝ) 1))
  · -- Exchange the Fourier integral with the segment integral.
    have hF : Integrable (Function.uncurry fun (x : E) (t : ℝ) ↦ (𝐞 (-inner ℝ x ξ) : ℂ) *
        (g (a + t * (b - a)) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a)))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
      (integrable_segment_gaussian_integrand hmeas hint).bdd_mul
        (by fun_prop : Continuous fun q : E × ℝ ↦ (𝐞 (-inner ℝ q.1 ξ) : ℂ)).aestronglyMeasurable
        (ae_of_all _ fun q ↦ (Circle.norm_coe _).le)
    rw [Real.fourier_eq]
    simp_rw [Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    rw [integral_integral_swap hF]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    -- The inner integral is the Fourier transform of a Gaussian with parameter `z(t)`.
    have hG := TauCeti.fourier_cexp_pi_mul_I_mul_norm_sq_mul_of_finrank_eq hk (hab t ht) ξ
    rw [Real.fourier_eq] at hG
    simp_rw [Circle.smul_def, smul_eq_mul] at hG
    have hpow : ((-I) ^ k * (a + t * (b - a)) ^ k)⁻¹ = (I / (a + t * (b - a))) ^ k := by
      rw [← mul_pow, ← inv_pow, mul_inv, inv_neg, inv_I, neg_neg, div_eq_mul_inv]
    rw [hpow] at hG
    calc ∫ x : E, (𝐞 (-inner ℝ x ξ) : ℂ) *
          (g (a + t * (b - a)) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a))
        = g (a + t * (b - a)) * (b - a) * ∫ x : E, (𝐞 (-inner ℝ x ξ) : ℂ) *
            cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) := by
          rw [← integral_const_mul]
          congr 1 with x
          ring
      _ = _ := by
          rw [hG]
          ring
  · -- Without measurability of the kernel along the segment, both sides vanish.
    have hA : (fun x : E ↦ ∫ t in Ioc (0 : ℝ) 1, g (a + t * (b - a)) *
        cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a)) = 0 :=
      funext fun x ↦ setIntegral_segment_gaussian_eq_zero hba hmeas _
    have hB : ∫ t in Ioc (0 : ℝ) 1, (I / (a + t * (b - a))) ^ k * g (a + t * (b - a)) *
        cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * (-1 / (a + t * (b - a)))) * (b - a) = 0 := by
      refine integral_non_aestronglyMeasurable fun h ↦ hmeas ?_
      have hc0 : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 1)), (I / (a + t * (b - a))) ^ k *
          cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * (-1 / (a + t * (b - a)))) * (b - a) ≠ 0 := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (div_ne_zero I_ne_zero (hz0 t ht)))
          (exp_ne_zero _)) (sub_ne_zero.mpr hba)
      refine (aestronglyMeasurable_fun_smul_iff₀ (c := fun t : ℝ ↦ (I / (a + t * (b - a))) ^ k *
        cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * (-1 / (a + t * (b - a)))) * (b - a))
        (Measurable.aestronglyMeasurable (by fun_prop)) hc0).mp ?_
      exact h.congr (ae_of_all _ fun t ↦ by simp only [smul_eq_mul]; ring)
    rw [hA, hB, Real.fourier_eq]
    simp

/-- **The Fourier transform along a path of two segments.**  Let `E` have dimension `2k`, and let
the segments `a → b` and `b → c` lie in the upper half-plane for `0 < t ≤ 1`.  If the kernel `g`
satisfies the integrability hypothesis of `SphereCeti.Contour.fourier_segment_gaussian_integral`
along both segments, then the Fourier transform of the sum of the two Gaussian segment integrals
is the sum of the two transported segment integrals. -/
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
