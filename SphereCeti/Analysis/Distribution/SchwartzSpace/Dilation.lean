/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Fourier.ChangeOfVariables

/-!
# Dilation of Schwartz functions

The dilation of a Schwartz function `f` by a nonzero real number `c` is the Schwartz function
`x ↦ f (c⁻¹ • x)`, the composition of `f` with the linear automorphism `x ↦ c⁻¹ • x`.  On a
finite-dimensional real inner product space of dimension `n`, its Fourier transform is
`ξ ↦ |c| ^ n • 𝓕 f (c • ξ)`.

## Main definitions

* `SchwartzMap.dilate`: the dilation `x ↦ f (c⁻¹ • x)` of a Schwartz function by `c ≠ 0`.

## Main statements

* `SchwartzMap.dilate_apply`: the values of the dilation.
* `SchwartzMap.fourier_dilate_apply`: the Fourier transform of the dilation,
  `𝓕 (dilate hc f) ξ = |c| ^ n • 𝓕 f (c • ξ)`.
-/

public section

open Module
open scoped FourierTransform SchwartzMap

namespace SchwartzMap

section Dilate

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {c : ℝ}

/-- The dilation of a Schwartz function `f` by `c ≠ 0`: the Schwartz function
`x ↦ f (c⁻¹ • x)`. -/
noncomputable def dilate (hc : c ≠ 0) (f : 𝓢(E, F)) : 𝓢(E, F) :=
  compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 c⁻¹ (inv_ne_zero hc)) : E ≃L[ℝ] E) f

/-- The dilation of `f` by `c` is `x ↦ f (c⁻¹ • x)`. -/
@[simp]
theorem dilate_apply (hc : c ≠ 0) (f : 𝓢(E, F)) (x : E) : dilate hc f x = f (c⁻¹ • x) :=
  (rfl)

end Dilate

section Fourier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] {c : ℝ}

/-- The Fourier transform of the dilation of `f` by `c ≠ 0` is `ξ ↦ |c| ^ n • 𝓕 f (c • ξ)`, where
`n` is the dimension. -/
@[simp]
theorem fourier_dilate_apply (hc : c ≠ 0) (f : 𝓢(E, F)) (ξ : E) :
    𝓕 (dilate hc f) ξ = |c| ^ finrank ℝ E • 𝓕 f (c • ξ) := by
  have h : ⇑(dilate hc f) = fun x ↦ f (c⁻¹ • x) := funext (dilate_apply hc f)
  -- The linear change of variables `x ↦ c⁻¹ • x` in the Fourier integral.
  rw [fourier_coe, h, TauCeti.fourier_comp_smul, fourier_coe]
  -- The scalars: `|(c⁻¹) ^ n|⁻¹ = |c| ^ n` and `(c⁻¹)⁻¹ = c`.
  simp

/-- Check that `simp` computes the values and the Fourier transform of a dilation. -/
example (hc : c ≠ 0) (f : 𝓢(E, F)) (x : E) :
    dilate hc f x = f (c⁻¹ • x) ∧ 𝓕 (dilate hc f) x = |c| ^ finrank ℝ E • 𝓕 f (c • x) := by
  simp

end Fourier

end SchwartzMap
