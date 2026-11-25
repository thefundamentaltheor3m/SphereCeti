/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The Fourier transform of radial and even functions

A function on a finite-dimensional real inner product space is radial (`Function.IsRadial`) when
its value at `x` depends only on `‖x‖`, equivalently when it is invariant under every linear
isometry (`Function.isRadial_iff_comp_linearIsometryEquiv`).  The Fourier transform and the inverse
Fourier transform of a radial function are radial.  The inverse Fourier transform of an even
function is its Fourier transform.

## Main statements

* `Function.Even.fourierInv_eq_fourier`: `𝓕⁻ f = 𝓕 f` for an even function `f`.
* `Function.IsRadial.fourier`: the Fourier transform of a radial function is radial.
* `Function.IsRadial.fourierInv`: the inverse Fourier transform of a radial function is radial.
-/

public section

open scoped FourierTransform

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The inverse Fourier transform of an even function is its Fourier transform. -/
theorem Function.Even.fourierInv_eq_fourier (hf : f.Even) : 𝓕⁻ f = 𝓕 f := by
  rw [Real.fourierInv_eq_fourier_comp_neg, funext hf]

namespace Function.IsRadial

/-- The Fourier transform of a radial function is radial. -/
theorem fourier (hf : f.IsRadial) : (𝓕 f).IsRadial := by
  rw [Function.isRadial_iff_comp_linearIsometryEquiv] at hf ⊢
  intro g
  funext w
  rw [Function.comp_apply, ← Real.fourier_comp_linearIsometry, hf g]

/-- The inverse Fourier transform of a radial function is radial. -/
theorem fourierInv (hf : f.IsRadial) : (𝓕⁻ f).IsRadial :=
  hf.even.fourierInv_eq_fourier ▸ hf.fourier

end Function.IsRadial
