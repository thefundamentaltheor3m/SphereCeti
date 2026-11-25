/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian

/-!
# Poisson summation for the unit Gaussian

Let `E` be a finite-dimensional real inner product space, `Λ ⊆ E` a full lattice and
`Λ^∨ = {y ∈ E | ⟪x, y⟫ ∈ ℤ for all x ∈ Λ}` its dual lattice.  The unit Gaussian
`x ↦ exp (-π ‖x‖²)` is its own Fourier transform for the normalization
`𝓕 f w = ∫ x, exp (-2πi ⟪x, w⟫) f x`, so Poisson summation gives
`∑_{x ∈ Λ} exp (-π ‖x‖²) = (covol Λ)⁻¹ ∑_{y ∈ Λ^∨} exp (-π ‖y‖²)`.
The identity holds in every dimension; no parity or integrality condition on `Λ` is needed.
It pins down the Fourier and covolume normalizations of the Poisson summation formula, and is the
value at `τ = i` of the Jacobi theta transformation for the lattice theta series.

## Main results

* `SphereCeti.Poisson.gaussian_one`: unit-Gaussian Poisson summation for a full lattice in an
  arbitrary finite-dimensional real inner product space, in particular in
  `EuclideanSpace ℝ (Fin d)`.

## Sources

The proof specializes TauCeti's Poisson summation `SchwartzMap.tsum_eq_tsum_dual_fourier`
(`TauCeti/Analysis/Fourier/PoissonSummation.lean`) to the Schwartz Gaussian
`SchwartzMap.gaussian` (`TauCeti/Analysis/Distribution/SchwartzSpace/Gaussian.lean`) at the
origin, using Mathlib's `fourier_gaussian_innerProductSpace` for its Fourier transform.  This is
an independent formalization; no proof text is adapted from another repository.
-/

public section

open Complex
open scoped Real FourierTransform SchwartzMap

namespace SphereCeti.Poisson

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Poisson summation for the unit Gaussian.**  For a full lattice `Λ` in a finite-dimensional
real inner product space `E`,
`∑_{x ∈ Λ} exp (-π ‖x‖²) = (covol Λ)⁻¹ ∑_{y ∈ Λ^∨} exp (-π ‖y‖²)`. -/
theorem gaussian_one (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∑' x : Λ, Real.exp (-Real.pi * ‖(x : E)‖ ^ 2) =
      (ZLattice.covolume Λ)⁻¹ * ∑' y : ZLattice.dual Λ, Real.exp (-Real.pi * ‖(y : E)‖ ^ 2) := by
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  set g : 𝓢(E, ℂ) := SchwartzMap.gaussian hb
  have hg (x : E) : g x = (Real.exp (-π * ‖x‖ ^ 2) : ℂ) := by
    simp [g, SchwartzMap.gaussian_apply, ofReal_exp]
  -- `exp (-π ‖·‖²)` is its own Fourier transform: the factor `(π / π) ^ (finrank ℝ E / 2)` is `1`.
  have hFg (y : E) : 𝓕 (g : E → ℂ) y = (Real.exp (-π * ‖y‖ ^ 2) : ℂ) := by
    have hfun : (g : E → ℂ) = fun v ↦ cexp (-(π : ℂ) * ‖v‖ ^ 2) :=
      funext fun v ↦ SchwartzMap.gaussian_apply hb v
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    rw [hfun, fourier_gaussian_innerProductSpace hb, div_self hπ, one_cpow, one_mul,
      ofReal_exp]
    congr 1
    push_cast
    field_simp
  -- Poisson summation at the origin, where every phase factor is `1`.
  have h := SchwartzMap.tsum_eq_tsum_dual_fourier g Λ 0
  simp only [zero_add, inner_zero_left, ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    hg, hFg] at h
  rw [← ofReal_tsum, ← ofReal_tsum, ← ofReal_inv, ← ofReal_mul] at h
  exact_mod_cast h

/-- The theorem applied to a full lattice in `EuclideanSpace ℝ (Fin d)`. -/
example {d : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∑' x : Λ, Real.exp (-Real.pi * ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2) =
      (ZLattice.covolume Λ)⁻¹ * ∑' y : ZLattice.dual Λ,
        Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin d))‖ ^ 2) :=
  gaussian_one Λ

end SphereCeti.Poisson
