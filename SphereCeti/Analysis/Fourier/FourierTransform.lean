/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import TauCeti.Analysis.Bochner.Fourier.Nonneg

/-!
# The Fourier transform of radial, even and real functions

A function on a finite-dimensional real inner product space is radial (`Function.IsRadial`) when
its value at `x` depends only on `‖x‖`, equivalently when it is invariant under every linear
isometry (`Function.isRadial_iff_comp_linearIsometryEquiv`).  The Fourier transform and the inverse
Fourier transform of a radial function are radial.  The inverse Fourier transform of an even
function is its Fourier transform, and both are even.

The Fourier transform of a real-valued even function `f : V → ℂ` is real-valued.  For integrable
`f` this is a special case of `TauCeti.fourier_im_eq_zero_of_map_neg_eq_conj`, about
conjugate-symmetric functions; `Function.Even.im_fourier_eq_zero` assumes no integrability, and for
a nonintegrable `f` the transform `𝓕 f` is zero.

## Main statements

* `Function.Even.fourierInv_eq_fourier`: `𝓕⁻ f = 𝓕 f` for an even function `f`.
* `Function.IsRadial.fourier`: the Fourier transform of a radial function is radial.
* `Function.IsRadial.fourierInv`: the inverse Fourier transform of a radial function is radial.
* `Function.Even.fourier`, `Function.Even.fourierInv`: the Fourier transform and the inverse Fourier
  transform of an even function are even.
* `Function.Even.im_fourier_eq_zero`: the Fourier transform of a real-valued even function is
  real-valued.
-/

public section

open MeasureTheory
open scoped FourierTransform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

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

namespace Function.Even

/-- The Fourier transform of an even function is even. -/
theorem fourier (hf : f.Even) : (𝓕 f).Even := fun ξ ↦ by
  rw [← Real.fourierInv_eq_fourier_neg, hf.fourierInv_eq_fourier]

/-- The inverse Fourier transform of an even function is even. -/
theorem fourierInv (hf : f.Even) : (𝓕⁻ f).Even :=
  hf.fourierInv_eq_fourier ▸ hf.fourier

end Function.Even

end

namespace Function.Even

variable {f : V → ℂ}

/-- The Fourier transform of a real-valued even function is real-valued.  No integrability is
assumed: for a nonintegrable `f`, `𝓕 f` is zero. -/
theorem im_fourier_eq_zero (hf : f.Even) (hre : ∀ x, (f x).im = 0) (ξ : V) :
    (𝓕 f ξ).im = 0 := by
  by_cases hint : Integrable f
  · exact TauCeti.fourier_im_eq_zero_of_map_neg_eq_conj f
      (fun x ↦ (hf x).trans (Complex.conj_eq_iff_im.mpr (hre x)).symm) hint ξ
  · rw [Real.fourier_eq, integral_undef (mt (Real.fourierIntegral_convergent_iff ξ).mp hint),
      Complex.zero_im]

end Function.Even
