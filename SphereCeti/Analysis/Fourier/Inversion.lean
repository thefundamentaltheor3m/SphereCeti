/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Fourier.Inversion
public import SphereCeti.Analysis.Fourier.FourierTransform

/-!
# The Fourier transform applied twice

Let `f` be an integrable function on a finite-dimensional real inner product space whose Fourier
transform `𝓕 f` is integrable.  Then `𝓕 (𝓕 f) x = f (-x)` at every `x` such that `f` is continuous
at `-x`.  Hence, for a continuous such `f`, applying the Fourier transform twice gives back `f` when
`f` is even, in particular when `f` is radial.

## Main statements

* `MeasureTheory.Integrable.fourier_fourier_apply`: `𝓕 (𝓕 f) x = f (-x)`.
* `Continuous.fourier_fourier_eq_of_even`: `𝓕 (𝓕 f) = f` for an even `f`.
* `Continuous.fourier_fourier_eq_of_isRadial`: `𝓕 (𝓕 f) = f` for a radial `f`.
-/

public section

open MeasureTheory
open scoped FourierTransform

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : V → E}

/-- Applying the Fourier transform twice to an integrable function `f` with integrable Fourier
transform reflects it: `𝓕 (𝓕 f) x = f (-x)` whenever `f` is continuous at `-x`. -/
theorem MeasureTheory.Integrable.fourier_fourier_apply (hf : Integrable f)
    (h'f : Integrable (𝓕 f)) {x : V} (hv : ContinuousAt f (-x)) : 𝓕 (𝓕 f) x = f (-x) := by
  rw [← hf.fourierInv_fourier_eq h'f hv, Real.fourierInv_eq_fourier_neg, neg_neg]

/-- Applying the Fourier transform twice to a continuous even integrable function `f` with
integrable Fourier transform gives back `f`. -/
theorem Continuous.fourier_fourier_eq_of_even (h : Continuous f) (hf : Integrable f)
    (h'f : Integrable (𝓕 f)) (heven : f.Even) : 𝓕 (𝓕 f) = f :=
  funext fun x ↦ (hf.fourier_fourier_apply h'f h.continuousAt).trans (heven x)

/-- Applying the Fourier transform twice to a continuous radial integrable function `f` with
integrable Fourier transform gives back `f`. -/
theorem Continuous.fourier_fourier_eq_of_isRadial (h : Continuous f) (hf : Integrable f)
    (h'f : Integrable (𝓕 f)) (hrad : f.IsRadial) : 𝓕 (𝓕 f) = f :=
  h.fourier_fourier_eq_of_even hf h'f hrad.even
