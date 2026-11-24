/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Fourier transform of radial, even and real functions

A function on a finite-dimensional real inner product space is radial (`Function.IsRadial`) when
its value at `x` depends only on `‖x‖`, equivalently when it is invariant under every linear
isometry (`Function.isRadial_iff_comp_linearIsometryEquiv`).  The Fourier transform and the inverse
Fourier transform of a radial function are radial, and those of an even function are even.

The complex conjugate of the Fourier transform of `f : V → ℂ` is the inverse Fourier transform of
the conjugate of `f`.  Hence the Fourier transform of a real-valued even function is real-valued.

## Main statements

* `Function.IsRadial.fourier`: the Fourier transform of a radial function is radial.
* `Function.IsRadial.fourierInv`: the inverse Fourier transform of a radial function is radial.
* `Function.Even.fourier`, `Function.Even.fourierInv`: the Fourier transform and the inverse Fourier
  transform of an even function are even.
* `Real.conj_fourier`: `conj (𝓕 f ξ) = 𝓕⁻ (conj ∘ f) ξ`.
* `Function.Even.im_fourier_eq_zero`: the Fourier transform of a real-valued even function is
  real-valued.
-/

public section

open ComplexConjugate MeasureTheory
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

namespace Function.Even

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

/-- The Fourier transform of an even function is even. -/
theorem fourier (hf : f.Even) : (𝓕 f).Even := by
  intro ξ
  have hneg : f ∘ LinearIsometryEquiv.neg ℝ = f := funext fun x ↦ hf x
  change 𝓕 f (LinearIsometryEquiv.neg ℝ ξ) = 𝓕 f ξ
  rw [← Real.fourier_comp_linearIsometry, hneg]

/-- The inverse Fourier transform of an even function is even. -/
theorem fourierInv (hf : f.Even) : (𝓕⁻ f).Even := by
  intro ξ
  have hneg : f ∘ LinearIsometryEquiv.neg ℝ = f := funext fun x ↦ hf x
  change 𝓕⁻ f (LinearIsometryEquiv.neg ℝ ξ) = 𝓕⁻ f ξ
  rw [← Real.fourierInv_comp_linearIsometry, hneg]

end Function.Even

namespace Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The complex conjugate of the Fourier transform of `f` is the inverse Fourier transform of the
complex conjugate of `f`. -/
theorem conj_fourier (f : V → ℂ) (ξ : V) : conj (𝓕 f ξ) = 𝓕⁻ (fun x ↦ conj (f x)) ξ := by
  rw [fourier_eq, fourierInv_eq, ← integral_conj]
  congr 1 with x
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul,
    ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]

end Real

namespace Function.Even

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {f : V → ℂ}

/-- The Fourier transform of a real-valued even function is real-valued. -/
theorem im_fourier_eq_zero (hf : f.Even) (hre : ∀ x, (f x).im = 0) (ξ : V) :
    (𝓕 f ξ).im = 0 := by
  have hconj : (fun x ↦ conj (f x)) = f := funext fun x ↦ Complex.conj_eq_iff_im.mpr (hre x)
  rw [← Complex.conj_eq_iff_im, Real.conj_fourier, hconj, Real.fourierInv_eq_fourier_neg,
    hf.fourier ξ]

end Function.Even
