/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.Segment

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
