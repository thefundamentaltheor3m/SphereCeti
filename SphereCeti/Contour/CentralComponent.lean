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

The identity needs no integrability of `g'` along the ray and holds for every `s ∈ ℂ` and every
`k`, including `k = 0`.  The integrability hypothesis is on `g` alone: `‖g(it)‖ exp(-π ‖x‖² t)` is
integrable on `E × (0, 1]`.  The inversion `z ↦ -1/z` maps the segment `0 → i` onto the ray
traversed from `i∞` down to `i`, opposite to the orientation of the vertical ray, so the law
carries the sign `-s` while the identity produces `s`.

## Main statements

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

/-- The Fourier transform of the radial function of the central leg is an integral over `(0, 1]`
of the kernel against the transformed Gaussians. -/
private lemma fourier_centralLeg {k : ℕ} (hk : Module.finrank ℝ E = 2 * k) {g : ℂ → ℂ}
    (hint : Integrable (fun q : E × ℝ ↦ ‖g (q.2 * I)‖ * Real.exp (-π * ‖q.1‖ ^ 2 * q.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1)))) (ξ : E) :
    𝓕 (fun x : E ↦ ∫ t in (0 : ℝ)..1, g (t * I) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (t * I)) * I) ξ =
      I * ∫ t in Ioc (0 : ℝ) 1,
        ((t : ℂ) ^ k)⁻¹ * g (t * I) * cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * ((t : ℂ)⁻¹ * I)) := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  by_cases hmeas : AEStronglyMeasurable (fun t : ℝ ↦ g (t * I)) (volume.restrict (Ioc (0 : ℝ) 1))
  · -- Exchange the Fourier integral with the segment integral.
    have hF : Integrable (Function.uncurry fun (x : E) (t : ℝ) ↦ (𝐞 (-inner ℝ x ξ) : ℂ) *
        (g (t * I) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (t * I)) * I))
        (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
      refine hint.mono' ?_ (ae_of_all _ fun q ↦ le_of_eq ?_)
      · have h1 : AEStronglyMeasurable (fun q : E × ℝ ↦ g (q.2 * I))
            (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := hmeas.comp_snd
        have h2 : Continuous fun q : E × ℝ ↦ (𝐞 (-inner ℝ q.1 ξ) : ℂ) := by fun_prop
        have h3 : Continuous fun q : E × ℝ ↦ cexp (π * I * (‖q.1‖ ^ 2 : ℝ) * (q.2 * I)) := by
          fun_prop
        exact h2.aestronglyMeasurable.mul
          ((h1.mul h3.aestronglyMeasurable).mul aestronglyMeasurable_const)
      · obtain ⟨x, t⟩ := q
        simp only [Function.uncurry_apply_pair, norm_mul, Circle.norm_coe, norm_I, one_mul,
          mul_one, Complex.norm_exp]
        congr 2
        generalize ‖x‖ ^ 2 = r
        simp [mul_re, mul_im]
    rw [Real.fourier_eq]
    simp_rw [Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    rw [integral_integral_swap hF]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    -- The inner integral is the Fourier transform of a Gaussian with parameter `t i`.
    have hG := TauCeti.fourier_cexp_pi_mul_I_mul_norm_sq_mul_of_finrank_eq hk
      (τ := (t : ℂ) * I) (by simpa using ht.1) ξ
    rw [Real.fourier_eq] at hG
    simp_rw [Circle.smul_def, smul_eq_mul] at hG
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have hpow : (-I) ^ k * ((t : ℂ) * I) ^ k = (t : ℂ) ^ k := by
      rw [← mul_pow]
      congr 1
      linear_combination (-(t : ℂ)) * I_sq
    have hinv : -1 / ((t : ℂ) * I) = (t : ℂ)⁻¹ * I := by
      field_simp
      linear_combination -I_sq
    rw [hpow, hinv] at hG
    calc ∫ x : E, (𝐞 (-inner ℝ x ξ) : ℂ) *
          (g (t * I) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (t * I)) * I)
        = g (t * I) * I * ∫ x : E, (𝐞 (-inner ℝ x ξ) : ℂ) *
            cexp (π * I * (‖x‖ ^ 2 : ℝ) * (t * I)) := by
          rw [← integral_const_mul]
          congr 1 with x
          ring
      _ = _ := by
          rw [hG]
          ring
  · -- Without measurability of the kernel on the axis, both sides vanish.
    have hA : (fun x : E ↦ ∫ t in Ioc (0 : ℝ) 1,
        g (t * I) * cexp (π * I * (‖x‖ ^ 2 : ℝ) * (t * I)) * I) = 0 := by
      funext x
      refine integral_non_aestronglyMeasurable fun h ↦ hmeas ?_
      refine aestronglyMeasurable_of_mul_right
        (c := fun t : ℝ ↦ cexp (π * I * (‖x‖ ^ 2 : ℝ) * (t * I)) * I) (by fun_prop)
        (ae_of_all _ fun t ↦ mul_ne_zero (exp_ne_zero _) I_ne_zero) ?_
      simpa only [mul_assoc] using h
    have hB : ∫ t in Ioc (0 : ℝ) 1,
        ((t : ℂ) ^ k)⁻¹ * g (t * I) * cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * ((t : ℂ)⁻¹ * I)) = 0 := by
      refine integral_non_aestronglyMeasurable fun h ↦ hmeas ?_
      refine aestronglyMeasurable_of_mul_right (c := fun t : ℝ ↦
        ((t : ℂ) ^ k)⁻¹ * cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * ((t : ℂ)⁻¹ * I))) (by fun_prop) ?_ ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr ht.1.ne')))
          (exp_ne_zero _)
      · exact h.congr (ae_of_all _ fun t ↦ by ring)
    rw [hA, hB, mul_zero, Real.fourier_eq]
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
  -- The Fourier transform turns each Gaussian `x ↦ exp(πi‖x‖² (it))` into
  -- `ξ ↦ t⁻ᵏ exp(πi‖ξ‖² (i/t))` (`fourier_centralLeg`).  The inversion law rewrites
  -- `t⁻ᵏ g(it)` as `s t⁻² g'(i/t)`, and the substitution `u = 1/t` carries the resulting integral
  -- over `(0, 1]` onto the ray `(1, ∞)`.
  funext ξ
  rw [fourier_centralLeg hk hint ξ, integral_Ioi_one_eq_integral_Ioc, mul_left_comm,
    ← integral_const_mul s]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
  -- On the imaginary axis the inversion law reads `t⁻ᵏ g(it) = s t⁻² g'(i/t)`.
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
  have hlaw' : ((t : ℂ) ^ k)⁻¹ * g (t * I) = s * (((t : ℂ) ^ 2)⁻¹ * g' ((t : ℂ)⁻¹ * I)) := by
    have h := hlaw t ht.1
    have h1 : I / ((t : ℂ) * I) = (t : ℂ)⁻¹ := by
      rw [mul_comm, ← div_div, div_self I_ne_zero, one_div]
    have h2 : ((t : ℂ) * I) ^ 2 = -(t : ℂ) ^ 2 := by
      rw [mul_pow, I_sq]
      ring
    have h3 : -((t : ℂ) * I)⁻¹ = (t : ℂ)⁻¹ * I := by
      rw [mul_inv, inv_I]
      ring
    rw [h1, h2, h3, inv_pow, inv_neg] at h
    rw [h]
    ring
  rw [ofReal_inv]
  linear_combination cexp (π * I * (‖ξ‖ ^ 2 : ℝ) * ((t : ℂ)⁻¹ * I)) * hlaw'

end SphereCeti.Contour
