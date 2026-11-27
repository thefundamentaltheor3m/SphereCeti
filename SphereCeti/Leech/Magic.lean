/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Leech.PlusSchwartz
public import SphereCeti.Leech.MinusSchwartz

/-!
# The Leech auxiliary function and its Fourier transform

The dimension-twenty-four auxiliary function combines the two Schwartz eigencomponents as
`-(π i / 113218560) a - (i / (262080 π)) b`. Its Fourier transform preserves the plus
component and reverses the minus component. Both have explicit squared-norm profiles.

This is the assembly part of Layer 9 / MIGRATION L7. The coefficients are exactly those of
`Leech.magicProfile` in `SphereCetiRoadmap/Suggested.lean` at
`4ce30e4e79aa0e810e81ea38371b3fb41c2a5f6e`, following Cohn, Kumar, Miller, Radchenko and
Viazovska, *The sphere packing problem in dimension 24*, Sections 2–4.
Special values, sign inequalities, exact zeros and the final certificate remain separate work.
-/

public section

open scoped SchwartzMap FourierTransform

namespace SphereCeti.Leech

/-- The prescribed squared-norm profile of the Leech auxiliary function. -/
noncomputable def magicProfile : 𝓢(ℝ, ℂ) :=
  (-((Real.pi : ℂ) * Complex.I) / 113218560) • magicPlusProfile -
    (Complex.I / (262080 * (Real.pi : ℂ))) • magicMinusProfile

/-- The squared-norm profile of its Fourier transform in dimension twenty-four. -/
noncomputable def fourierMagicProfile : 𝓢(ℝ, ℂ) :=
  (-((Real.pi : ℂ) * Complex.I) / 113218560) • magicPlusProfile +
    (Complex.I / (262080 * (Real.pi : ℂ))) • magicMinusProfile

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Leech auxiliary function, as a radial Schwartz function. -/
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

/-- The profile construction is exactly the prescribed combination of eigencomponents. -/
theorem magic_eq_smul_magicPlus_sub_smul_magicMinus :
    magic (E := E) = (-((Real.pi : ℂ) * Complex.I) / 113218560) • magicPlus -
      (Complex.I / (262080 * (Real.pi : ℂ))) • magicMinus := by
  ext x
  simp [magic_apply, magicProfile]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In dimension twenty-four, Fourier transformation reverses the minus component. -/
theorem fourier_magic (hE : Module.finrank ℝ E = 24) :
    𝓕 (magic (E := E)) = (-((Real.pi : ℂ) * Complex.I) / 113218560) • magicPlus +
      (Complex.I / (262080 * (Real.pi : ℂ))) • magicMinus := by
  simp only [magic_eq_smul_magicPlus_sub_smul_magicMinus, sub_eq_add_neg,
    FourierTransform.fourier_add, FourierTransform.fourier_neg,
    FourierTransform.fourier_smul, fourier_magicPlus hE, fourier_magicMinus hE,
    smul_neg, neg_neg]

/-- Evaluate the Fourier transform through its distinct squared-norm profile. -/
@[simp]
theorem fourier_magic_apply_profile (hE : Module.finrank ℝ E = 24) (x : E) :
    𝓕 (magic (E := E)) x = fourierMagicProfile (‖x‖ ^ 2) := by
  rw [fourier_magic hE]
  simp [fourierMagicProfile]

example (x : E) : magic x = magicProfile (‖x‖ ^ 2) := by simp

example : Function.IsRadial (magic (E := E)) := by fun_prop

example (x : EuclideanSpace ℝ (Fin 24)) :
    𝓕 (magic (E := EuclideanSpace ℝ (Fin 24))) x = fourierMagicProfile (‖x‖ ^ 2) := by
  simp

end SphereCeti.Leech
