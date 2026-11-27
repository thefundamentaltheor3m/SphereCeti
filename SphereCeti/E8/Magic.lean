/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.E8.PlusSchwartz
public import SphereCeti.E8.MinusSchwartz

/-!
# The E8 auxiliary function and its Fourier transform

The final function combines the two already constructed Schwartz eigencomponents as
`g = (π i / 8640) a - (i / (240 π)) b`. Its Fourier transform changes the sign of the minus
component. Both functions retain explicit squared-norm profiles and radiality.

This is the assembly part of Layer 9 / MIGRATION K5, with exactly the coefficients in
`SphereCetiRoadmap/Suggested.lean` at `4ce30e4e79aa0e810e81ea38371b3fb41c2a5f6e`.
The negative coefficient of `b` follows Viazovska's equations (52), (53) and (62), consistently
with the corrected negative ray kernel; see the roadmap's `E8.magicProfile` sign calculation.
The normalization, sign inequalities, exact zeros and certificate require further results.
-/

public section

open scoped SchwartzMap FourierTransform

namespace SphereCeti.E8

/-- The squared-norm profile of Viazovska's auxiliary function. -/
noncomputable def magicProfile : 𝓢(ℝ, ℂ) :=
  (((Real.pi : ℂ) * Complex.I) / 8640) • magicPlusProfile -
    (Complex.I / (240 * (Real.pi : ℂ))) • magicMinusProfile

/-- The squared-norm profile of the Fourier transform in dimension eight. -/
noncomputable def fourierMagicProfile : 𝓢(ℝ, ℂ) :=
  (((Real.pi : ℂ) * Complex.I) / 8640) • magicPlusProfile +
    (Complex.I / (240 * (Real.pi : ℂ))) • magicMinusProfile

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The E8 auxiliary function, as a radial Schwartz function. -/
noncomputable def magic : 𝓢(E, ℂ) :=
  SchwartzMap.compNormSqCLM ℂ E magicProfile

/-- Evaluate the auxiliary function using its squared-norm profile. -/
@[simp]
theorem magic_apply (x : E) : magic x = magicProfile (‖x‖ ^ 2) :=
  SchwartzMap.compNormSqCLM_apply magicProfile x

/-- The auxiliary function is radial. -/
@[fun_prop]
theorem isRadial_magic : Function.IsRadial (magic (E := E)) :=
  SchwartzMap.isRadial_compNormSqCLM magicProfile

/-- The profile construction is exactly the prescribed combination of the eigencomponents. -/
theorem magic_eq_smul_magicPlus_sub_smul_magicMinus :
    magic (E := E) = (((Real.pi : ℂ) * Complex.I) / 8640) • magicPlus -
      (Complex.I / (240 * (Real.pi : ℂ))) • magicMinus := by
  ext x
  simp [magic_apply, magicProfile]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In dimension eight the Fourier transform reverses the coefficient of the minus component. -/
theorem fourier_magic (hE : Module.finrank ℝ E = 8) :
    𝓕 (magic (E := E)) = (((Real.pi : ℂ) * Complex.I) / 8640) • magicPlus +
      (Complex.I / (240 * (Real.pi : ℂ))) • magicMinus := by
  simp only [magic_eq_smul_magicPlus_sub_smul_magicMinus, sub_eq_add_neg,
    FourierTransform.fourier_add, FourierTransform.fourier_neg,
    FourierTransform.fourier_smul, fourier_magicPlus hE, fourier_magicMinus hE,
    smul_neg, neg_neg]

/-- Evaluate the Fourier transform using its distinct squared-norm profile. -/
@[simp]
theorem fourier_magic_apply_profile (hE : Module.finrank ℝ E = 8) (x : E) :
    𝓕 (magic (E := E)) x = fourierMagicProfile (‖x‖ ^ 2) := by
  rw [fourier_magic hE]
  simp [fourierMagicProfile]

example (x : E) : magic x = magicProfile (‖x‖ ^ 2) := by simp

example : Function.IsRadial (magic (E := E)) := by fun_prop

example (x : EuclideanSpace ℝ (Fin 8)) :
    𝓕 (magic (E := EuclideanSpace ℝ (Fin 8))) x = fourierMagicProfile (‖x‖ ^ 2) := by
  simp

end SphereCeti.E8
