/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
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

## Main definitions

* `SphereCeti.CohnElkies.Certificate d r`: a Cohn–Elkies certificate in dimension `d` with radius
  `r`.
* `SphereCeti.CohnElkies.Certificate.bound`: the density bound `f(0) / f̂(0) · vol B(0, r / 2)`.

## Main statements

* `SphereCeti.CohnElkies.Certificate.bound_def`: the defining formula of the density bound.
* `SphereCeti.CohnElkies.Certificate.f_zero_pos`: the value of a certificate at `0` is positive.
* `SphereCeti.CohnElkies.Certificate.bound_pos`: the density bound of a certificate is positive.

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

end Certificate

end SphereCeti.CohnElkies
