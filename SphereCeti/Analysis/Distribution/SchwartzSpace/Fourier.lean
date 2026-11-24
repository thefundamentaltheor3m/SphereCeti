/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import SphereCeti.Analysis.Fourier.FourierTransform

/-!
# The Fourier transform applied twice to a Schwartz function

For a Schwartz function `f` on a finite-dimensional real inner product space, Fourier inversion
gives `𝓕 (𝓕 f) x = f (-x)`.  Hence the Fourier transform is an involution on even Schwartz
functions, and in particular on radial ones, and it maps radial Schwartz functions to radial
Schwartz functions.

## Main statements

* `SchwartzMap.isRadial_fourier`: the Fourier transform of a radial Schwartz function is radial.
* `SchwartzMap.fourier_fourier_apply`: `𝓕 (𝓕 f) x = f (-x)`.
* `SchwartzMap.fourier_fourier_of_even`: `𝓕 (𝓕 f) = f` for even `f`.
* `SchwartzMap.fourier_fourier_of_isRadial`: `𝓕 (𝓕 f) = f` for radial `f`.
-/

public section

open scoped FourierTransform SchwartzMap

namespace SchwartzMap

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Fourier transform of a radial Schwartz function is radial. -/
theorem isRadial_fourier {f : 𝓢(V, E)} (hf : (⇑f).IsRadial) :
    (⇑(𝓕 f : 𝓢(V, E))).IsRadial := by
  rw [fourier_coe]
  exact hf.fourier

variable [CompleteSpace E]

/-- Applying the Fourier transform twice to a Schwartz function reflects it:
`𝓕 (𝓕 f) x = f (-x)`. -/
theorem fourier_fourier_apply (f : 𝓢(V, E)) (x : V) : 𝓕 (𝓕 f) x = f (-x) := by
  have h : (𝓕⁻ (𝓕 f) : 𝓢(V, E)) = f := FourierPair.fourierInv_fourier_eq f
  conv_rhs => rw [← h]
  rw [fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg, fourier_coe]

/-- The Fourier transform is an involution on even Schwartz functions. -/
theorem fourier_fourier_of_even (f : 𝓢(V, E)) (hf : Function.Even ⇑f) : 𝓕 (𝓕 f) = f := by
  ext x
  rw [fourier_fourier_apply, hf]

/-- The Fourier transform is an involution on radial Schwartz functions. -/
theorem fourier_fourier_of_isRadial (f : 𝓢(V, E)) (hf : (⇑f).IsRadial) : 𝓕 (𝓕 f) = f :=
  f.fourier_fourier_of_even hf.even

end SchwartzMap
