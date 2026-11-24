/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Analysis.Fourier.Continuous

/-!
# Fourier eigenfunctions from exchanged pairs

Let `F` and `G` be integrable functions on a finite-dimensional real inner product space.  If the
Fourier transform exchanges them up to a scalar `s`, that is `𝓕 F = s • G` and `𝓕 G = s • F`,
then `F + G` is an eigenfunction of the Fourier transform with eigenvalue `s`.  Applied to two
exchanged pairs with a common scalar, this gives the eigenfunction property of a sum of four
pieces.

In Viazovska's construction, each Fourier eigencomponent of the magic function is the sum of four
contour pieces (the left legs, the right legs, the central leg and the vertical ray), and the
Fourier transform exchanges, up to the eigenvalue, the left legs with the right legs and the
central leg with the ray.

## Main statements

* `MeasureTheory.Integrable.fourier_add_eq_smul_add`: if `𝓕 F = s • G` and `𝓕 G = s • F`, then
  `𝓕 (F + G) = s • (F + G)`.
* `MeasureTheory.Integrable.fourier_add_add_add_eq_smul_add`: if the Fourier transform exchanges
  `F₁` with `F₂` and `F₃` with `F₄`, each time up to `s`, then
  `𝓕 (F₁ + F₂ + F₃ + F₄) = s • (F₁ + F₂ + F₃ + F₄)`.

## References

* M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991–1015.
-/

public section

open scoped FourierTransform

namespace MeasureTheory.Integrable

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If the Fourier transform exchanges integrable functions `F` and `G` up to a scalar `s`, then
`F + G` is an eigenfunction of the Fourier transform with eigenvalue `s`. -/
theorem fourier_add_eq_smul_add {s : ℂ} {F G : V → E} (hF : Integrable F) (hG : Integrable G)
    (hFG : 𝓕 F = s • G) (hGF : 𝓕 G = s • F) : 𝓕 (F + G) = s • (F + G) := by
  rw [hF.fourier_add hG, hFG, hGF, smul_add, add_comm]

/-- If the Fourier transform exchanges integrable `F₁` with `F₂` and integrable `F₃` with `F₄`,
each time up to the same scalar `s`, then `F₁ + F₂ + F₃ + F₄` is an eigenfunction of the Fourier
transform with eigenvalue `s`. -/
theorem fourier_add_add_add_eq_smul_add {s : ℂ} {F₁ F₂ F₃ F₄ : V → E} (hF₁ : Integrable F₁)
    (hF₂ : Integrable F₂) (hF₃ : Integrable F₃) (hF₄ : Integrable F₄) (h₁₂ : 𝓕 F₁ = s • F₂)
    (h₂₁ : 𝓕 F₂ = s • F₁) (h₃₄ : 𝓕 F₃ = s • F₄) (h₄₃ : 𝓕 F₄ = s • F₃) :
    𝓕 (F₁ + F₂ + F₃ + F₄) = s • (F₁ + F₂ + F₃ + F₄) := by
  rw [add_assoc (F₁ + F₂), (hF₁.add hF₂).fourier_add (hF₃.add hF₄),
    hF₁.fourier_add_eq_smul_add hF₂ h₁₂ h₂₁, hF₃.fourier_add_eq_smul_add hF₄ h₃₄ h₄₃, ← smul_add]

end MeasureTheory.Integrable
