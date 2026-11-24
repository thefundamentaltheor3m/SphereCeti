/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The Fourier transform of a radial function

A function on a finite-dimensional real inner product space is radial (`Function.IsRadial`) when
its value at `x` depends only on `‖x‖`, equivalently when it is invariant under every linear
isometry (`Function.isRadial_iff_comp_linearIsometryEquiv`).  The Fourier transform commutes with
linear isometries (`Real.fourier_comp_linearIsometry`), so the Fourier transform and the inverse
Fourier transform of a radial function are radial.

## Main statements

* `Function.IsRadial.fourier`: the Fourier transform of a radial function is radial.
* `Function.IsRadial.fourierInv`: the inverse Fourier transform of a radial function is radial.
-/

public section

open scoped FourierTransform

namespace Function.IsRadial

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of a radial function is radial. -/
theorem fourier (hf : f.IsRadial) : (𝓕 f).IsRadial := by
  rw [Function.isRadial_iff_comp_linearIsometryEquiv] at hf ⊢
  intro g
  funext w
  rw [Function.comp_apply, ← Real.fourier_comp_linearIsometry, hf g]

/-- The inverse Fourier transform of a radial function is radial. -/
theorem fourierInv (hf : f.IsRadial) : (𝓕⁻ f).IsRadial := by
  rw [Function.isRadial_iff_comp_linearIsometryEquiv] at hf ⊢
  intro g
  funext w
  rw [Function.comp_apply, ← Real.fourierInv_comp_linearIsometry, hf g]

end Function.IsRadial
