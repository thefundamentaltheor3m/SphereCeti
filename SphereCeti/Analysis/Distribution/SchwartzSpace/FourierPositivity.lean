/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Positivity at the origin from a nonnegative Fourier transform

A Schwartz function `f` on a finite-dimensional real inner product space whose Fourier transform
has nonnegative real part, positive at some point, has positive real part at the origin.  This is
the positivity of `f(0)` for a Cohn–Elkies certificate, and is stated in the form intended for
Mathlib's Schwartz Fourier API (`UPSTREAM.md`, item A18).

## Main statements

* `SchwartzMap.re_apply_zero_pos_of_fourier_nonneg`: if `0 ≤ Re 𝓕 f` everywhere and
  `0 < Re 𝓕 f(ξ₀)` for some `ξ₀`, then `0 < Re f(0)`.
-/

public section

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace SchwartzMap

/-- A Schwartz function whose Fourier transform has nonnegative real part, positive at some point,
has positive real part at the origin. -/
theorem re_apply_zero_pos_of_fourier_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : 𝓢(E, ℂ)) (hnonneg : ∀ ξ, 0 ≤ (𝓕 f ξ).re) {ξ₀ : E} (hpos : 0 < (𝓕 f ξ₀).re) :
    0 < (f 0).re := by
  -- By Fourier inversion `f 0` is the integral of `𝓕 f`, whose real part is continuous,
  -- nonnegative, and positive at `ξ₀`.
  have h0 : f 0 = ∫ ξ, 𝓕 f ξ :=
    calc f 0 = (𝓕⁻ (𝓕 f) : 𝓢(E, ℂ)) 0 := by
          rw [FourierPair.fourierInv_fourier_eq]
      _ = ∫ ξ, 𝓕 f ξ := by
          rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
          simp
  have hint : Integrable ⇑(𝓕 f : 𝓢(E, ℂ)) := (𝓕 f).integrable
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [h0, ← hre]
  exact integral_pos_of_integrable_nonneg_ne_zero (x := ξ₀)
    (Complex.continuous_re.comp (𝓕 f).continuous) hint.re hnonneg hpos.ne'

end SchwartzMap
