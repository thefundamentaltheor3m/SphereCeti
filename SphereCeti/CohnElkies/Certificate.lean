/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import SphereCeti.Analysis.Distribution.SchwartzSpace.FourierPositivity
public import TauCeti.Analysis.Fourier.ChangeOfVariables

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
`y ↦ c ^ d • f̂ (c • y)`, so both transports leave the density bound unchanged, as does
multiplication by `t > 0`.  In dimension `d > 0`, dilating until `f̂(0) = f(0)` and then dividing by
`f(0)` gives a normalized certificate, with `f(0) = f̂(0) = 1`, and the same density bound.

## Main definitions

* `SphereCeti.CohnElkies.Certificate d r`: a Cohn–Elkies certificate in dimension `d` with radius
  `r`.
* `SphereCeti.CohnElkies.Certificate.bound`: the density bound `f(0) / f̂(0) · vol B(0, r / 2)`.
* `SphereCeti.CohnElkies.Certificate.compLinearIsometryEquiv`,
  `SphereCeti.CohnElkies.Certificate.dilate`: the transports along a linear isometry and a
  dilation.
* `SphereCeti.CohnElkies.Certificate.smul`: the multiple of a certificate by `t > 0`.
* `SphereCeti.CohnElkies.Certificate.IsNormalized`: a certificate with `f(0) = f̂(0) = 1`.

## Main statements

* `SphereCeti.CohnElkies.Certificate.bound_def`: the defining formula of the density bound.
* `SphereCeti.CohnElkies.Certificate.f_zero_pos`: the value of a certificate at `0` is positive.
* `SphereCeti.CohnElkies.Certificate.bound_pos`: the density bound of a certificate is positive.
* `SphereCeti.CohnElkies.Certificate.bound_compLinearIsometryEquiv`,
  `SphereCeti.CohnElkies.Certificate.bound_dilate`, `SphereCeti.CohnElkies.Certificate.bound_smul`:
  the transports and positive multiples keep the density bound.
* `SphereCeti.CohnElkies.Certificate.exists_isNormalized`: in dimension `d > 0`, every certificate
  gives a normalized certificate with the same density bound.

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

/-- Transport along a linear isometry does not change the density bound. -/
@[simp]
theorem bound_compLinearIsometryEquiv (C : Certificate d r)
    (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    (C.compLinearIsometryEquiv A).bound = C.bound := by
  simp only [bound_def, compLinearIsometryEquiv_f_apply, map_zero]
  congr 3
  simp [compLinearIsometryEquiv, SchwartzMap.fourier_coe, Real.fourier_comp_linearIsometry]

/-- The dilation `x ↦ f (c⁻¹ • x)` of a Schwartz function by `c > 0`. -/
private noncomputable def dilateFun (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) {c : ℝ} (hc : 0 < c) :
    𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin d)) c⁻¹
      (inv_ne_zero hc.ne')).toContinuousLinearEquiv f

private theorem dilateFun_apply (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) {c : ℝ} (hc : 0 < c)
    (x : EuclideanSpace ℝ (Fin d)) : dilateFun f hc x = f (c⁻¹ • x) :=
  (rfl)

/-- The Fourier transform of the dilation `x ↦ f (c⁻¹ • x)` is `y ↦ c ^ d • 𝓕 f (c • y)`. -/
private theorem fourier_dilateFun (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) {c : ℝ} (hc : 0 < c)
    (y : EuclideanSpace ℝ (Fin d)) : 𝓕 (dilateFun f hc) y = (c ^ d : ℝ) • 𝓕 f (c • y) := by
  have h : ((dilateFun f hc : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) : EuclideanSpace ℝ (Fin d) → ℂ) =
      fun x ↦ f (c⁻¹ • x) :=
    funext (dilateFun_apply f hc)
  rw [SchwartzMap.fourier_coe, h, TauCeti.fourier_comp_smul, finrank_euclideanSpace_fin, inv_inv,
    inv_pow, abs_inv, inv_inv, abs_of_pos (pow_pos hc d), SchwartzMap.fourier_coe]

/-- The dilation of a certificate by `c > 0`: the function `x ↦ f (c⁻¹ • x)`, a certificate of
radius `c * r`. -/
noncomputable def dilate (C : Certificate d r) {c : ℝ} (hc : 0 < c) : Certificate d (c * r) where
  radius_pos := mul_pos hc C.radius_pos
  f := dilateFun C.f hc
  real_f x := C.real_f (c⁻¹ • x)
  real_fourier x := by
    rw [fourier_dilateFun, Complex.smul_im, C.real_fourier, smul_zero]
  nonpos_of_radius_le_norm x hx := by
    refine C.nonpos_of_radius_le_norm (c⁻¹ • x) ?_
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), le_inv_mul_iff₀ hc]
    exact hx
  fourier_nonneg x := by
    rw [fourier_dilateFun, Complex.smul_re]
    exact mul_nonneg (pow_nonneg hc.le d) (C.fourier_nonneg (c • x))
  fourier_zero_pos := by
    rw [fourier_dilateFun, Complex.smul_re, smul_zero]
    exact mul_pos (pow_pos hc d) C.fourier_zero_pos

/-- The dilated certificate is `x ↦ f (c⁻¹ • x)`. -/
@[simp]
theorem dilate_f_apply (C : Certificate d r) {c : ℝ} (hc : 0 < c) (x : EuclideanSpace ℝ (Fin d)) :
    (C.dilate hc).f x = C.f (c⁻¹ • x) :=
  (rfl)

/-- Dilation does not change the density bound: `f(0)` is unchanged, while `f̂(0)` and the volume
of the ball of radius `c * r / 2` are both multiplied by `c ^ d`. -/
@[simp]
theorem bound_dilate (C : Certificate d r) {c : ℝ} (hc : 0 < c) :
    (C.dilate hc).bound = C.bound := by
  have hF : (𝓕 (C.dilate hc).f 0).re = c ^ d * (𝓕 C.f 0).re := by
    change (𝓕 (dilateFun C.f hc) 0).re = _
    rw [fourier_dilateFun, Complex.smul_re, smul_zero, smul_eq_mul]
  have hball : volume (ball (0 : EuclideanSpace ℝ (Fin d)) (c * r / 2)) =
      ENNReal.ofReal (c ^ d) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r / 2)) := by
    have h := smul_ball hc.ne' (0 : EuclideanSpace ℝ (Fin d)) (r / 2)
    rw [smul_zero, Real.norm_of_nonneg hc.le] at h
    rw [mul_div_assoc, ← h, Measure.addHaar_smul, finrank_euclideanSpace_fin,
      abs_of_pos (pow_pos hc d)]
  rw [bound_def, bound_def, dilate_f_apply, smul_zero, hF, hball, ← mul_assoc,
    ← ENNReal.ofReal_mul (div_nonneg C.f_zero_pos.le (mul_pos (pow_pos hc d)
      C.fourier_zero_pos).le)]
  congr 2
  field_simp

/-! ### Normalization -/

/-- A certificate is normalized when `f(0) = 1` and `f̂(0) = 1`, the normalization of the magic
functions. -/
def IsNormalized (C : Certificate d r) : Prop :=
  C.f 0 = 1 ∧ 𝓕 C.f 0 = 1

/-- A certificate is normalized exactly when `f(0) = 1` and `f̂(0) = 1`. -/
theorem isNormalized_iff (C : Certificate d r) : C.IsNormalized ↔ C.f 0 = 1 ∧ 𝓕 C.f 0 = 1 :=
  Iff.rfl

/-- The multiple `t • f` of a certificate by `t > 0`, again a certificate of radius `r`. -/
noncomputable def smul (C : Certificate d r) {t : ℝ} (ht : 0 < t) : Certificate d r where
  radius_pos := C.radius_pos
  f := (t : ℂ) • C.f
  real_f x := by simp [C.real_f x]
  real_fourier x := by
    rw [FourierSMul.fourier_smul, smul_apply, smul_eq_mul, Complex.im_ofReal_mul, C.real_fourier,
      mul_zero]
  nonpos_of_radius_le_norm x hx := by
    simpa [Complex.re_ofReal_mul] using mul_nonpos_of_nonneg_of_nonpos ht.le
      (C.nonpos_of_radius_le_norm x hx)
  fourier_nonneg x := by
    rw [FourierSMul.fourier_smul, smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_nonneg ht.le (C.fourier_nonneg x)
  fourier_zero_pos := by
    rw [FourierSMul.fourier_smul, smul_apply, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_pos ht C.fourier_zero_pos

/-- The multiple of a certificate by `t` is `x ↦ t • f x`. -/
@[simp]
theorem smul_f_apply (C : Certificate d r) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)) :
    (C.smul ht).f x = t * C.f x :=
  (rfl)

/-- The Fourier transform of the multiple of a certificate by `t` is `t • f̂`. -/
@[simp]
theorem fourier_smul_f_apply (C : Certificate d r) {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin d)) : 𝓕 (C.smul ht).f x = t * 𝓕 C.f x := by
  change 𝓕 ((t : ℂ) • C.f) x = _
  rw [FourierSMul.fourier_smul, smul_apply, smul_eq_mul]

/-- Multiplying a certificate by `t > 0` does not change the density bound. -/
@[simp]
theorem bound_smul (C : Certificate d r) {t : ℝ} (ht : 0 < t) : (C.smul ht).bound = C.bound := by
  rw [bound_def, bound_def, smul_f_apply, fourier_smul_f_apply, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, mul_div_mul_left _ _ ht.ne']

/-- **Normalization.**  In dimension `d > 0`, every certificate gives a normalized certificate,
of another radius, with the same density bound: dilate until `f̂(0) = f(0)`, then divide by
`f(0)`. -/
theorem exists_isNormalized (C : Certificate d r) (hd : 0 < d) :
    ∃ (r' : ℝ) (C' : Certificate d r'), C'.IsNormalized ∧ C'.bound = C.bound := by
  set a := (C.f 0).re
  set b := (𝓕 C.f 0).re
  have ha : 0 < a := C.f_zero_pos
  have hb : 0 < b := C.fourier_zero_pos
  -- The dilation by `c = (a / b) ^ (1 / d)` makes `f̂(0) = c ^ d * b = a`.
  set c := (a / b) ^ (1 / d : ℝ)
  have hc : 0 < c := Real.rpow_pos_of_pos (div_pos ha hb) _
  have hcd : c ^ d * b = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos ha hb).le, one_div_mul_cancel
      (Nat.cast_ne_zero.mpr hd.ne'), Real.rpow_one, div_mul_cancel₀ _ hb.ne']
  -- Real values at the origin are their real parts.
  have hreal (z : ℂ) (hz : z.im = 0) : z = z.re := Complex.ext rfl (by simpa using hz)
  refine ⟨c * r, (C.dilate hc).smul (inv_pos.mpr ha), ⟨?_, ?_⟩, by simp⟩
  · rw [smul_f_apply, dilate_f_apply, smul_zero, hreal _ (C.real_f 0)]
    push_cast
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne')
  · rw [fourier_smul_f_apply]
    change ((a⁻¹ : ℝ) : ℂ) * 𝓕 (dilateFun C.f hc) 0 = 1
    rw [fourier_dilateFun, smul_zero, hreal _ (C.real_fourier 0), Complex.real_smul]
    push_cast
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, hcd]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne')

/-- Check that `simp` computes the function and the bound of a transported, dilated certificate. -/
example (C : Certificate d r) (A : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    {c : ℝ} (hc : 0 < c) (x : EuclideanSpace ℝ (Fin d)) :
    ((C.compLinearIsometryEquiv A).dilate hc).f x = C.f (A (c⁻¹ • x)) ∧
      ((C.compLinearIsometryEquiv A).dilate hc).bound = C.bound := by
  simp

/-- Check that `simp` computes the values and the bound of a positive multiple of a certificate. -/
example (C : Certificate d r) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin d)) :
    (C.smul ht).f x = t * C.f x ∧ 𝓕 (C.smul ht).f x = t * 𝓕 C.f x ∧
      (C.smul ht).bound = C.bound := by
  simp

end Certificate

end SphereCeti.CohnElkies
