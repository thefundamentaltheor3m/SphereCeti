/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Analysis.Fourier.PoissonSummation

/-!
# Poisson summation for a function vanishing off the origin of a lattice

Let `L` be a full lattice in a finite-dimensional real inner product space and `f` a Schwartz
function.  If `f` vanishes at the nonzero vectors of `L` and its Fourier transform vanishes at the
nonzero vectors of the dual lattice `L^∨`, then in TauCeti's Poisson summation formula
`SchwartzMap.tsum_eq_tsum_dual_fourier` at the origin only the terms at the origin survive, and it
becomes `𝓕 f 0 = covol(L) * f 0`.

## Main statements

* `SchwartzMap.fourier_apply_zero_eq_covolume_mul`: if `f` vanishes on `L ∖ {0}` and `𝓕 f`
  vanishes on `L^∨ ∖ {0}`, then `𝓕 f 0 = covol(L) * f 0`.
-/

public section

open scoped FourierTransform SchwartzMap

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If a Schwartz function `f` vanishes at the nonzero vectors of a full lattice `L` and its
Fourier transform vanishes at the nonzero vectors of the dual lattice, then Poisson summation at
the origin reduces to `𝓕 f 0 = covol(L) * f 0`. -/
theorem fourier_apply_zero_eq_covolume_mul (f : 𝓢(E, ℂ)) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (hf : ∀ x : L, x ≠ 0 → f x = 0)
    (hfourier : ∀ y : ZLattice.dual L, y ≠ 0 → 𝓕 f (y : E) = 0) :
    𝓕 f 0 = ZLattice.covolume L * f 0 := by
  have h := f.tsum_eq_tsum_dual_fourier L 0
  rw [tsum_eq_single 0 fun x hx ↦ by simpa using hf x hx,
    tsum_eq_single 0 fun y hy ↦ by simpa [fourier_coe] using hfourier y hy] at h
  have hcov : (ZLattice.covolume L : ℂ) ≠ 0 := by
    exact_mod_cast (ZLattice.covolume_pos L MeasureTheory.volume).ne'
  simp only [ZeroMemClass.coe_zero, zero_add, inner_zero_left, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one] at h
  rw [h, fourier_coe, mul_inv_cancel_left₀ hcov]

end SchwartzMap
