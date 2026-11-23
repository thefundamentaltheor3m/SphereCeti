/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian

/-!
# Poisson summation for the unit Gaussian

For a full lattice `Λ` in `ℝ^d` with dual lattice `Λ^∨`,
`∑_{x ∈ Λ} exp (-π ‖x‖²) = (covol Λ)⁻¹ ∑_{y ∈ Λ^∨} exp (-π ‖y‖²)`.

This checks the Fourier and covolume normalizations of TauCeti's Poisson summation
`SchwartzMap.tsum_eq_tsum_dual_fourier`: it is that formula at `v = 0` for the Schwartz Gaussian
`SchwartzMap.gaussian` with `b = π`, which is its own Fourier transform by Mathlib's
`fourier_gaussian_innerProductSpace`.  No parity of `d` is needed, unlike the theta inversion law
`ZLattice.thetaSeries_S_smul`.

## Main results

* `SphereCeti.Poisson.gaussian_one`: the roadmap target
  `SphereCeti.Suggested.Poisson.gaussian_one`, with the same statement.

This is an independent formalization; no proof text is adapted from another repository.
-/

public section

open Complex
open scoped Real FourierTransform SchwartzMap

namespace SphereCeti.Poisson

/-- Unit-Gaussian check of the Fourier and covolume normalizations, a consequence of TauCeti's
Poisson summation. -/
theorem gaussian_one {d : ℕ} (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∑' x : Λ, Real.exp (-Real.pi * ‖(x : EuclideanSpace ℝ (Fin d))‖ ^ 2) =
      (ZLattice.covolume Λ)⁻¹ * ∑' y : ZLattice.dual Λ,
        Real.exp (-Real.pi * ‖(y : EuclideanSpace ℝ (Fin d))‖ ^ 2) := by
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  set g : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := SchwartzMap.gaussian hb
  have hg (x : EuclideanSpace ℝ (Fin d)) : g x = (Real.exp (-π * ‖x‖ ^ 2) : ℂ) := by
    simp [g, SchwartzMap.gaussian_apply, ofReal_exp]
  have hFg (y : EuclideanSpace ℝ (Fin d)) :
      𝓕 (g : EuclideanSpace ℝ (Fin d) → ℂ) y = (Real.exp (-π * ‖y‖ ^ 2) : ℂ) := by
    have hfun : (g : EuclideanSpace ℝ (Fin d) → ℂ) = fun v ↦ cexp (-(π : ℂ) * ‖v‖ ^ 2) :=
      funext fun v ↦ SchwartzMap.gaussian_apply hb v
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    rw [hfun, fourier_gaussian_innerProductSpace hb, div_self hπ, one_cpow, one_mul,
      ofReal_exp]
    congr 1
    push_cast
    field_simp
  have h := SchwartzMap.tsum_eq_tsum_dual_fourier g Λ 0
  simp only [zero_add, inner_zero_left, ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    hg, hFg] at h
  rw [← ofReal_tsum, ← ofReal_tsum, ← ofReal_inv, ← ofReal_mul] at h
  exact_mod_cast h

end SphereCeti.Poisson
