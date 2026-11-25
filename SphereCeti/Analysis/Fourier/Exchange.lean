/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Fourier.Inversion
public import TauCeti.Analysis.Fourier.Continuous

/-!
# Fourier eigenfunctions from exchanged pairs

Let `F` and `G` be integrable functions on a finite-dimensional real inner product space.  If the
Fourier transform exchanges them up to a scalar `s`, that is `𝓕 F = s • G` and `𝓕 G = s • F`,
then `F + G` is an eigenfunction of the Fourier transform with eigenvalue `s`.  Applied to two
exchanged pairs with a common scalar, this gives the eigenfunction property of a sum of four
pieces.

One half of an exchange gives the other when `F` is continuous and even and `s ^ 2 = 1`: by
Fourier inversion, `𝓕 F = s • G` implies `𝓕 G = s • F`.  Continuity of `F` is needed for this
pointwise conclusion, since Fourier inversion recovers an integrable function with integrable
transform only almost everywhere, and changing `F` at one point changes neither `𝓕 F` nor `G`.

In Viazovska's construction, each Fourier eigencomponent of the magic function is the sum of four
contour pieces (the left legs, the right legs, the central leg and the vertical ray), and the
Fourier transform exchanges, up to the eigenvalue, the left legs with the right legs and the
central leg with the ray.

## Main statements

* `MeasureTheory.Integrable.fourier_reverse`: for `F` continuous and even and `s ^ 2 = 1`,
  `𝓕 F = s • G` implies `𝓕 G = s • F`.
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

/-- **Reversal by Fourier inversion.**  Let `F` and `G` be integrable, with `F` continuous and even,
and let `s ^ 2 = 1`.  If `𝓕 F = s • G`, then `𝓕 G = s • F`. -/
theorem fourier_reverse [CompleteSpace E] {s : ℂ} {F G : V → E} (hF : Integrable F)
    (hG : Integrable G) (hFc : Continuous F) (heven : ∀ x, F (-x) = F x) (hs : s ^ 2 = 1)
    (h : 𝓕 F = s • G) : 𝓕 G = s • F := by
  -- Since `s ^ 2 = 1`, `G = s • 𝓕 F`.
  have hGF : G = s • 𝓕 F := by
    rw [h, smul_smul, ← sq, hs, one_smul]
  -- Fourier inversion and evenness give `𝓕 (𝓕 F) = F`.
  have hint : Integrable (𝓕 F) := by
    rw [h]
    exact hG.smul s
  have hinv : 𝓕 (𝓕 F) = F := by
    funext ξ
    calc 𝓕 (𝓕 F) ξ = 𝓕⁻ (𝓕 F) (-ξ) := by rw [Real.fourierInv_eq_fourier_neg, neg_neg]
      _ = F (-ξ) := by rw [hFc.fourierInv_fourier_eq hF hint]
      _ = F ξ := heven ξ
  rw [hGF, Real.fourier_const_smul, hinv]

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
