/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import SphereCeti.Analysis.Distribution.SchwartzSpace.Dilation
public import SphereCeti.Analysis.Distribution.SchwartzSpace.FourierPositivity

/-!
# Cohn–Elkies certificates

A Cohn–Elkies certificate in dimension `d` with radius `r > 0` is a Schwartz function
`f : ℝ^d → ℂ` such that `f` and its Fourier transform `f̂` are real-valued, `f(x) ≤ 0` whenever
`‖x‖ ≥ r`, `f̂ ≥ 0` everywhere, and `f̂(0) > 0`.  The linear programming bound of Cohn and Elkies
bounds the density of every sphere packing with center separation `r` by
`f(0) / f̂(0) · vol B(0, r / 2)`.  The Fourier transform is Mathlib's, with kernel
`exp(-2πi⟪x, ξ⟫)`.  No radiality is required.

The value `f(0)` of a certificate, and hence its density bound, is positive, by the general
positivity `SchwartzMap.re_apply_zero_pos_of_fourier_nonneg`.

Certificates transport along linear isometries `A` of `ℝ^d`, as `f ∘ A`, and along dilations by
`c > 0`, as `x ↦ f (c⁻¹ • x)` with radius `c * r`.  The Fourier transform of the dilation is
`y ↦ c ^ d • f̂ (c • y)`, so both transports leave the density bound unchanged.

## Main definitions

* `SphereCeti.CohnElkies.Certificate d r`: a Cohn–Elkies certificate in dimension `d` with radius
  `r`.
* `SphereCeti.CohnElkies.Certificate.bound`: the density bound `f(0) / f̂(0) · vol B(0, r / 2)`.
* `SphereCeti.CohnElkies.Certificate.compLinearIsometryEquiv`,
  `SphereCeti.CohnElkies.Certificate.dilate`: the transports along a linear isometry and a
  dilation.

## Main statements

* `SphereCeti.CohnElkies.Certificate.bound_def`: the defining formula of the density bound.
* `SphereCeti.CohnElkies.Certificate.f_zero_pos`: the value of a certificate at `0` is positive.
* `SphereCeti.CohnElkies.Certificate.bound_pos`: the density bound of a certificate is positive.
* `SphereCeti.CohnElkies.Certificate.bound_compLinearIsometryEquiv`,
  `SphereCeti.CohnElkies.Certificate.bound_dilate`: the transports keep the density bound.

## References

* H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714.
-/

public section

open MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap

namespace SphereCeti.CohnElkies

/-- A Cohn–Elkies certificate in dimension `d` with radius `r`: a Schwartz function whose values
and Fourier transform are real, which is nonpositive outside the ball of radius `r`, and whose
Fourier transform is nonnegative and positive at the origin. -/
structure Certificate (d : ℕ) (r : ℝ) where
  /-- The radius is positive. -/
  radius_pos : 0 < r
  /-- The auxiliary Schwartz function. -/
  f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)
  /-- The function is real-valued. -/
  real_f : ∀ x, (f x).im = 0
  /-- Its Fourier transform is real-valued. -/
  real_fourier : ∀ x, (𝓕 f x).im = 0
  /-- The function is nonpositive at distance at least `r` from the origin. -/
  nonpos_of_radius_le_norm : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0
  /-- Its Fourier transform is nonnegative. -/
  fourier_nonneg : ∀ x, 0 ≤ (𝓕 f x).re
  /-- Its Fourier transform is positive at the origin. -/
  fourier_zero_pos : 0 < (𝓕 f 0).re

namespace Certificate

variable {d : ℕ} {r : ℝ}

/-- The density bound `f(0) / f̂(0) · vol B(0, r / 2)` supplied by a certificate. -/
noncomputable def bound (C : Certificate d r) : ℝ≥0∞ :=
  ENNReal.ofReal ((C.f 0).re / (𝓕 C.f 0).re) *
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r / 2))

/-- The defining formula of the density bound of a certificate. -/
theorem bound_def (C : Certificate d r) :
    C.bound = ENNReal.ofReal ((C.f 0).re / (𝓕 C.f 0).re) *
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r / 2)) :=
  (rfl)

/-- The value of a certificate at the origin has positive real part. -/
theorem f_zero_pos (C : Certificate d r) : 0 < (C.f 0).re :=
  C.f.re_apply_zero_pos_of_fourier_nonneg C.fourier_nonneg C.fourier_zero_pos

/-- The density bound of a certificate is positive. -/
theorem bound_pos (C : Certificate d r) : 0 < C.bound := by
  rw [bound_def]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (div_pos C.f_zero_pos C.fourier_zero_pos)).ne'
    (measure_ball_pos volume _ (half_pos C.radius_pos)).ne'

/-! ### Transport along linear isometries and dilations -/

/-- The transport of a certificate along a linear isometry `A` of `ℝ^d`: the function `f ∘ A`,
again a certificate of radius `r`. -/
noncomputable def compLinearIsometryEquiv (C : Certificate d r)
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) : Certificate d r where
  radius_pos := C.radius_pos
  f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv C.f
  real_f x := C.real_f (A x)
  real_fourier x := by
    simpa [SchwartzMap.fourier_coe, Real.fourier_comp_linearIsometry] using C.real_fourier (A x)
  nonpos_of_radius_le_norm x hx := C.nonpos_of_radius_le_norm (A x) (by rwa [A.norm_map])
  fourier_nonneg x := by
    simpa [SchwartzMap.fourier_coe, Real.fourier_comp_linearIsometry] using C.fourier_nonneg (A x)
  fourier_zero_pos := by
    simpa [SchwartzMap.fourier_coe, Real.fourier_comp_linearIsometry] using C.fourier_zero_pos

/-- The transported certificate is `f ∘ A`. -/
@[simp]
theorem compLinearIsometryEquiv_f_apply (C : Certificate d r)
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    (C.compLinearIsometryEquiv A).f x = C.f (A x) :=
  (rfl)

/-- The Fourier transform of the transported certificate is `f̂ ∘ A`. -/
@[simp]
theorem fourier_compLinearIsometryEquiv_f_apply (C : Certificate d r)
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    𝓕 (C.compLinearIsometryEquiv A).f x = 𝓕 C.f (A x) := by
  have h : ⇑(C.compLinearIsometryEquiv A).f = C.f ∘ A :=
    funext (C.compLinearIsometryEquiv_f_apply A)
  rw [SchwartzMap.fourier_coe, h, Real.fourier_comp_linearIsometry, SchwartzMap.fourier_coe]

/-- Transport along a linear isometry does not change the density bound. -/
@[simp]
theorem bound_compLinearIsometryEquiv (C : Certificate d r)
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    (C.compLinearIsometryEquiv A).bound = C.bound := by
  rw [bound_def, bound_def, compLinearIsometryEquiv_f_apply,
    fourier_compLinearIsometryEquiv_f_apply, map_zero]

/-- The dilation of a certificate by `c > 0`: the function `x ↦ f (c⁻¹ • x)`, a certificate of
radius `c * r`. -/
noncomputable def dilate (C : Certificate d r) {c : ℝ} (hc : 0 < c) : Certificate d (c * r) where
  radius_pos := mul_pos hc C.radius_pos
  f := SchwartzMap.dilate hc.ne' C.f
  real_f x := by
    rw [SchwartzMap.dilate_apply]
    exact C.real_f (c⁻¹ • x)
  real_fourier x := by
    rw [SchwartzMap.fourier_dilate_apply, Complex.smul_im, C.real_fourier, smul_zero]
  nonpos_of_radius_le_norm x hx := by
    rw [SchwartzMap.dilate_apply]
    refine C.nonpos_of_radius_le_norm (c⁻¹ • x) ?_
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), le_inv_mul_iff₀ hc]
    exact hx
  fourier_nonneg x := by
    rw [SchwartzMap.fourier_dilate_apply, Complex.smul_re, smul_eq_mul]
    exact mul_nonneg (by positivity) (C.fourier_nonneg (c • x))
  fourier_zero_pos := by
    rw [SchwartzMap.fourier_dilate_apply, Complex.smul_re, smul_zero, smul_eq_mul]
    exact mul_pos (by positivity) C.fourier_zero_pos

/-- The function of the dilated certificate is the dilation of `f`. -/
theorem dilate_f (C : Certificate d r) {c : ℝ} (hc : 0 < c) :
    (C.dilate hc).f = SchwartzMap.dilate hc.ne' C.f :=
  (rfl)

/-- The dilated certificate is `x ↦ f (c⁻¹ • x)`. -/
@[simp]
theorem dilate_f_apply (C : Certificate d r) {c : ℝ} (hc : 0 < c) (x : EuclideanSpace ℝ (Fin d)) :
    (C.dilate hc).f x = C.f (c⁻¹ • x) := by
  rw [dilate_f, SchwartzMap.dilate_apply]

/-- The Fourier transform of the dilated certificate is `y ↦ c ^ d • f̂ (c • y)`. -/
@[simp]
theorem fourier_dilate_f_apply (C : Certificate d r) {c : ℝ} (hc : 0 < c)
    (y : EuclideanSpace ℝ (Fin d)) : 𝓕 (C.dilate hc).f y = (c : ℂ) ^ d * 𝓕 C.f (c • y) := by
  rw [dilate_f, SchwartzMap.fourier_dilate_apply]
  simp [abs_of_pos hc]

/-- Dilation does not change the density bound. -/
@[simp]
theorem bound_dilate (C : Certificate d r) {c : ℝ} (hc : 0 < c) :
    (C.dilate hc).bound = C.bound := by
  have ha := C.f_zero_pos
  have hb := C.fourier_zero_pos
  -- `f(0)` is unchanged, while `f̂(0)` and the volume of the ball both gain the factor `c ^ d`.
  have hF : (𝓕 (C.dilate hc).f 0).re = c ^ d * (𝓕 C.f 0).re := by
    rw [fourier_dilate_f_apply, smul_zero, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have hball : volume (ball (0 : EuclideanSpace ℝ (Fin d)) (c * r / 2)) =
      ENNReal.ofReal (c ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r / 2)) := by
    simpa only [mul_div_assoc, finrank_euclideanSpace_fin] using
      Measure.addHaar_ball_mul_of_pos volume (0 : EuclideanSpace ℝ (Fin d)) hc (r / 2)
  -- The factors `c ^ d` cancel in `ℝ`, and the cancellation lifts through `ENNReal.ofReal`.
  have hcancel : (C.f 0).re / (c ^ d * (𝓕 C.f 0).re) * c ^ d = (C.f 0).re / (𝓕 C.f 0).re := by
    field_simp
  have hscalar : ENNReal.ofReal ((C.f 0).re / (c ^ d * (𝓕 C.f 0).re)) * ENNReal.ofReal (c ^ d) =
      ENNReal.ofReal ((C.f 0).re / (𝓕 C.f 0).re) := by
    rw [← ENNReal.ofReal_mul (by positivity), hcancel]
  calc (C.dilate hc).bound
      = ENNReal.ofReal ((C.f 0).re / (c ^ d * (𝓕 C.f 0).re)) *
          (ENNReal.ofReal (c ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r / 2))) := by
        rw [bound_def, dilate_f_apply, smul_zero, hF, hball]
    _ = C.bound := by rw [← mul_assoc, hscalar, bound_def]

/-- Check that `simp` computes the function, the Fourier transform and the bound of a transported,
dilated certificate. -/
example (C : Certificate d r) (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    {c : ℝ} (hc : 0 < c) (x : EuclideanSpace ℝ (Fin d)) :
    ((C.compLinearIsometryEquiv A).dilate hc).f x = C.f (A (c⁻¹ • x)) ∧
      𝓕 ((C.compLinearIsometryEquiv A).dilate hc).f x = c ^ d * 𝓕 C.f (A (c • x)) ∧
      ((C.compLinearIsometryEquiv A).dilate hc).bound = C.bound := by
  simp

end Certificate

end SphereCeti.CohnElkies
