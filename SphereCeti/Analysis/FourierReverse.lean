/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Fourier.Inversion
public import TauCeti.Analysis.Fourier.Continuous

/-!
# Reversing a Fourier identity by inversion

Let `F` and `G` be integrable functions on a finite-dimensional real inner product space, with `F`
continuous and even, and let `s` be a scalar with `s ^ 2 = 1`.  If `𝓕 F = s • G`, then
`𝓕 G = s • F`.  Continuity of `F` is needed for the pointwise conclusion: Fourier inversion
recovers an integrable function with integrable transform only almost everywhere, and changing
`F` at one point changes neither `𝓕 F` nor `G`.

The magic functions of dimensions 8 and 24 are assembled from pieces whose Fourier transforms
are exchanged in pairs up to a sign `s = ±1`; this gives each exchange in the reverse direction
from the forward one.

## Main statements

* `SphereCeti.fourier_reverse`: `𝓕 F = s • G` implies `𝓕 G = s • F` for `F` continuous and even
  and `s ^ 2 = 1`.
-/

public section

open MeasureTheory
open scoped FourierTransform

namespace SphereCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- If `𝓕 F = s • G` with `F` continuous and even, `F` and `G` integrable, and `s ^ 2 = 1`, then
`𝓕 G = s • F`. -/
theorem fourier_reverse {s : ℂ} (hs : s ^ 2 = 1) {F G : V → ℂ} (hF : Integrable F)
    (hG : Integrable G) (hFc : Continuous F) (heven : ∀ x, F (-x) = F x)
    (h : 𝓕 F = fun ξ ↦ s * G ξ) :
    𝓕 G = fun ξ ↦ s * F ξ := by
  -- Since `s ^ 2 = 1`, `G = s • 𝓕 F`.
  have hGF : G = s • 𝓕 F := by
    funext ξ
    rw [Pi.smul_apply, smul_eq_mul, h, ← mul_assoc, ← sq, hs, one_mul]
  -- Fourier inversion and evenness give `𝓕 (𝓕 F) = F`.
  have hint : Integrable (𝓕 F) := by
    rw [h]
    exact hG.const_mul s
  have hinv (ξ : V) : 𝓕 (𝓕 F) ξ = F ξ :=
    calc 𝓕 (𝓕 F) ξ = 𝓕⁻ (𝓕 F) (-ξ) := by rw [Real.fourierInv_eq_fourier_neg, neg_neg]
      _ = F (-ξ) := by rw [hFc.fourierInv_fourier_eq hF hint]
      _ = F ξ := heven ξ
  funext ξ
  rw [hGF, Real.fourier_const_smul, Pi.smul_apply, smul_eq_mul, hinv ξ]

end SphereCeti
