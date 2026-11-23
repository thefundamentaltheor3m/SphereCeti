/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The central-pair Fourier identity

Let `E` be a real inner product space of dimension `2k`.  For a kernel `g : ℂ → ℂ`, the central
leg of the magic contour carries the radial function
`x ↦ ∫₀¹ g(it) exp(πi ‖x‖² (it)) i dt`, the integral of `g(z) exp(πi ‖x‖² z) dz` along the segment
from `0` to `i`.  If `g` is related to a second kernel `g'` on the imaginary axis by the signed
inversion law `(i/z)^k g(z) = -s z⁻² g'(-1/z)`, then the Fourier transform of this function is
`s` times the radial function `ξ ↦ i ∫_{1}^{∞} g'(it) exp(πi ‖ξ‖² (it)) dt` of the vertical ray from
`i` to `i∞`.

The identity rests on the Fourier transform of a Gaussian segment integral along any segment
`z(t) = a + t (b - a)` in the upper half-plane: the transform of
`x ↦ ∫₀¹ g(z(t)) exp(πi ‖x‖² z(t)) (b - a) dt` is
`ξ ↦ ∫₀¹ (i / z(t))^k g(z(t)) exp(πi ‖ξ‖² (-1 / z(t))) (b - a) dt`.  The left legs of the magic
contour are segments of this kind as well.

The identity needs no integrability of `g'` along the ray and holds for every `s ∈ ℂ` and every
`k`, including `k = 0`.  The integrability hypothesis is on `g` alone: `‖g(it)‖ exp(-π ‖x‖² t)` is
integrable on `E × (0, 1]`.  The inversion `z ↦ -1/z` maps the segment `0 → i` onto the ray
traversed from `i∞` down to `i`, opposite to the orientation of the vertical ray, so the law
carries the sign `-s` while the identity produces `s`.

## Main statements

* `SphereCeti.Contour.fourier_segment_gaussian_integral`: the Fourier transform of a Gaussian
  segment integral.
* `SphereCeti.Contour.fourier_centralComponent`: the central-pair Fourier identity.

## References

* M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991–1015.
-/

public section

open Complex MeasureTheory Set
open scoped Real FourierTransform

namespace SphereCeti.Contour

/-- If `φ * c` is almost everywhere strongly measurable for a measurable `c` that is almost
everywhere nonzero, then so is `φ`. -/
private lemma aestronglyMeasurable_of_mul_right {μ : Measure ℝ} {φ c : ℝ → ℂ} (hc : Measurable c)
    (hc0 : ∀ᵐ t ∂μ, c t ≠ 0) (h : AEStronglyMeasurable (fun t ↦ φ t * c t) μ) :
    AEStronglyMeasurable φ μ :=
  (h.mul hc.inv.aestronglyMeasurable).congr (hc0.mono fun t ht ↦ mul_inv_cancel_right₀ ht (φ t))

/-- The substitution `u = 1/t` carries an integral over the ray `(1, ∞)` onto one over `(0, 1]`. -/
private lemma integral_Ioi_one_eq_integral_Ioc (h : ℝ → ℂ) :
    ∫ u in Ioi (1 : ℝ), h u = ∫ t in Ioc (0 : ℝ) 1, ((t : ℂ) ^ 2)⁻¹ * h t⁻¹ := by
  have himage : (fun u : ℝ ↦ u⁻¹) '' Ioi 1 = Ioo 0 1 := by
    rw [Set.image_inv_eq_inv, Set.inv_Ioi₀ one_pos, inv_one]
  have hderiv : ∀ u ∈ Ioi (1 : ℝ), HasDerivWithinAt (fun u : ℝ ↦ u⁻¹) (-(u ^ 2)⁻¹) (Ioi 1) u :=
    fun u hu ↦ (hasDerivAt_inv (by linarith [mem_Ioi.mp hu] : u ≠ 0)).hasDerivWithinAt
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv
    inv_injective.injOn fun t : ℝ ↦ ((t : ℂ) ^ 2)⁻¹ * h t⁻¹
  rw [himage, ← integral_Ioc_eq_integral_Ioo] at hcov
  rw [hcov]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith [mem_Ioi.mp hu])
  rw [abs_neg, abs_of_pos (inv_pos.mpr (pow_pos (by linarith [mem_Ioi.mp hu]) 2)), inv_inv,
    Complex.real_smul]
  push_cast
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The Fourier transform of a Gaussian segment integral.**  Let `E` be a real inner product
space of dimension `2k`, and let the segment `z(t) = a + t (b - a)`, `0 < t ≤ 1`, lie in the upper
half-plane.  If `g(z(t)) exp(-π ‖x‖² Im z(t))` is absolutely integrable on `E × (0, 1]`, then the
Fourier transform of `x ↦ ∫₀¹ g(z(t)) exp(πi ‖x‖² z(t)) (b - a) dt` is
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
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
      refine (hint.mul_const ‖b - a‖).mono' ?_ (ae_of_all _ fun q ↦ le_of_eq ?_)
      · have h1 : AEStronglyMeasurable (fun q : E × ℝ ↦ g (a + q.2 * (b - a)))
            (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := hmeas.comp_snd
        have h2 : Continuous fun q : E × ℝ ↦ (𝐞 (-inner ℝ q.1 ξ) : ℂ) := by fun_prop
        have h3 : Continuous fun q : E × ℝ ↦
            cexp (π * I * (‖q.1‖ ^ 2 : ℝ) * (a + q.2 * (b - a))) := by
          fun_prop
        exact h2.aestronglyMeasurable.mul
          ((h1.mul h3.aestronglyMeasurable).mul aestronglyMeasurable_const)
      · obtain ⟨x, t⟩ := q
        simp only [Function.uncurry_apply_pair, norm_mul, Circle.norm_coe, one_mul,
          Complex.norm_exp]
        congr 3
        generalize ‖x‖ ^ 2 = r
        simp [mul_re, mul_im]
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
        cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a)) = 0 := by
      funext x
      refine integral_non_aestronglyMeasurable fun h ↦ hmeas ?_
      refine aestronglyMeasurable_of_mul_right (c := fun t : ℝ ↦
        cexp (π * I * (‖x‖ ^ 2 : ℝ) * (a + t * (b - a))) * (b - a)) (by fun_prop)
        (ae_of_all _ fun t ↦ mul_ne_zero (exp_ne_zero _) (sub_ne_zero.mpr hba)) ?_
      simpa only [mul_assoc] using h
    have hB : ∫ t in Ioc (0 : ℝ) 1, (I / (a + t * (b - a))) ^ k * g (a + t * (b - a)) *
        cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * (-1 / (a + t * (b - a)))) * (b - a) = 0 := by
      refine integral_non_aestronglyMeasurable fun h ↦ hmeas ?_
      refine aestronglyMeasurable_of_mul_right (c := fun t : ℝ ↦ (I / (a + t * (b - a))) ^ k *
        cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * (-1 / (a + t * (b - a)))) * (b - a)) (by fun_prop) ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (div_ne_zero I_ne_zero (hz0 t ht)))
          (exp_ne_zero _)) (sub_ne_zero.mpr hba)
      · exact h.congr (ae_of_all _ fun t ↦ by ring)
    rw [hA, hB, Real.fourier_eq]
    simp

/-- **The central-pair Fourier identity.**  Let `E` be a real inner product space of dimension
`2k`, and let kernels `g` and `g'` satisfy the signed inversion law
`(i/z)^k g(z) = -s z⁻² g'(-1/z)` on the positive imaginary axis, with `g(it) exp(-π‖x‖² t)`
absolutely integrable on `E × (0, 1]`.  Then the Fourier transform of the function
`x ↦ ∫₀¹ g(it) exp(πi‖x‖² (it)) i dt` of the central leg is `s` times the function
`ξ ↦ i ∫_{(1, ∞)} g'(it) exp(πi‖ξ‖² (it)) dt` of the vertical ray. -/
theorem fourier_centralComponent {k : ℕ} (hk : Module.finrank ℝ E = 2 * k) (s : ℂ)
    {g g' : ℂ → ℂ}
    (hint : Integrable (fun q : E × ℝ ↦ ‖g (q.2 * I)‖ * Real.exp (-π * ‖q.1‖ ^ 2 * q.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))))
    (hlaw : ∀ t : ℝ, 0 < t →
      (I / (t * I)) ^ k * g (t * I) = -s * ((t * I) ^ 2)⁻¹ * g' (-(t * I)⁻¹)) :
    𝓕 (fun x : E ↦ ∫ t in (0 : ℝ)..1, g (t * I) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (t * I)) * I) =
      fun ξ ↦ s * (I * ∫ t in Ioi (1 : ℝ),
        g' (t * I) * cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * (t * I))) := by
  -- The central leg is the segment from `0` to `i`.  On it the inversion law turns the transformed
  -- kernel at `z = it` into `s t⁻² g'(i/t)`, and the substitution `u = 1/t` carries the resulting
  -- integral over `(0, 1]` onto the ray `(1, ∞)`.
  funext ξ
  have hseg := fourier_segment_gaussian_integral hk (a := 0) (b := I) (g := g)
    (fun t ht ↦ by simpa using ht.1) (by simpa using hint) ξ
  simp only [zero_add, sub_zero] at hseg
  rw [hseg, intervalIntegral.integral_of_le zero_le_one, integral_Ioi_one_eq_integral_Ioc,
    ← integral_const_mul I, ← integral_const_mul s]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
  have h1 : -((t : ℂ) * I)⁻¹ = ((t⁻¹ : ℝ) : ℂ) * I := by
    rw [ofReal_inv, mul_inv, inv_I]
    ring
  have h2 : -1 / ((t : ℂ) * I) = ((t⁻¹ : ℝ) : ℂ) * I := by
    rw [neg_div, one_div, h1]
  have h3 : ((t : ℂ) * I) ^ 2 = -(t : ℂ) ^ 2 := by
    rw [mul_pow, I_sq]
    ring
  rw [hlaw t ht.1, h1, h2, h3, inv_neg]
  ring

end SphereCeti.Contour
