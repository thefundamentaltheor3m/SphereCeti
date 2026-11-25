/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Analysis.Fourier.PoissonSummation
public import SphereCeti.CohnElkies.Certificate

/-!
# Sharpness of Cohn–Elkies certificates for lattices

A Cohn–Elkies certificate `f` with radius `r` is sharp for a lattice `Λ` in `ℝ^d` when `f`
vanishes at the nonzero vectors of `Λ` and its Fourier transform `f̂` vanishes at the nonzero
vectors of the dual lattice.  Poisson summation over a full lattice `Λ` at the origin then reduces
to `f̂(0) = covol(Λ) · f(0)`, so the density bound `f(0) / f̂(0) · vol B(0, r / 2)` of the
certificate is `vol B(0, r / 2) / covol(Λ)`.  When the nonzero vectors of `Λ` have norm at least
`r`, this is the density of the packing of balls of radius `r / 2` centered at the points of `Λ`.

## Main definitions

* `SphereCeti.CohnElkies.Certificate.IsSharpForLattice C Λ`: the certificate `C` vanishes at the
  nonzero vectors of `Λ`, and its Fourier transform at the nonzero vectors of the dual lattice.

## Main statements

* `SphereCeti.CohnElkies.Certificate.isSharpForLattice_iff`: the defining characterization.
* `SphereCeti.CohnElkies.Certificate.IsSharpForLattice.fourier_apply_zero_eq_covolume_mul`: for a
  certificate sharp for a full lattice `Λ`, `f̂(0) = covol(Λ) · f(0)`.
* `SphereCeti.CohnElkies.Certificate.IsSharpForLattice.bound_eq`: the density bound of a
  certificate sharp for a full lattice `Λ` is `vol B(0, r / 2) / covol(Λ)`.

## References

* H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714.
-/

public section

open MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap

namespace SphereCeti.CohnElkies.Certificate

variable {d : ℕ} {r : ℝ}

/-- A certificate is sharp for a lattice `Λ` when it vanishes at the nonzero vectors of `Λ` and its
Fourier transform vanishes at the nonzero vectors of the dual lattice. -/
def IsSharpForLattice (C : Certificate d r) (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) :
    Prop :=
  (∀ x : Λ, x ≠ 0 → C.f x = 0) ∧
    ∀ y : ZLattice.dual Λ, y ≠ 0 → 𝓕 C.f (y : EuclideanSpace ℝ (Fin d)) = 0

/-- A certificate is sharp for `Λ` if and only if it vanishes at the nonzero vectors of `Λ` and its
Fourier transform vanishes at the nonzero vectors of the dual lattice. -/
theorem isSharpForLattice_iff {C : Certificate d r} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))} :
    C.IsSharpForLattice Λ ↔ (∀ x : Λ, x ≠ 0 → C.f x = 0) ∧
      ∀ y : ZLattice.dual Λ, y ≠ 0 → 𝓕 C.f (y : EuclideanSpace ℝ (Fin d)) = 0 :=
  Iff.rfl

namespace IsSharpForLattice

variable {C : Certificate d r} {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))} [DiscreteTopology Λ]
  [IsZLattice ℝ Λ]

/-- For a certificate sharp for a full lattice `Λ`, Poisson summation over `Λ` at the origin
reduces to `f̂(0) = covol(Λ) · f(0)`. -/
theorem fourier_apply_zero_eq_covolume_mul (h : C.IsSharpForLattice Λ) :
    𝓕 C.f 0 = ZLattice.covolume Λ * C.f 0 :=
  C.f.fourier_apply_zero_eq_covolume_mul Λ h.1 h.2

/-- The density bound of a certificate sharp for a full lattice `Λ` is `vol B(0, r / 2) / covol(Λ)`.
When the nonzero vectors of `Λ` have norm at least `r`, this is the density of the packing of balls
of radius `r / 2` centered at the points of `Λ`. -/
theorem bound_eq (h : C.IsSharpForLattice Λ) :
    C.bound = volume (ball (0 : EuclideanSpace ℝ (Fin d)) (r / 2)) /
      ENNReal.ofReal (ZLattice.covolume Λ) := by
  -- Taking real parts, `Re f̂(0) = covol(Λ) · Re f(0)`.
  have hre : (𝓕 C.f 0).re = ZLattice.covolume Λ * (C.f 0).re := by
    rw [h.fourier_apply_zero_eq_covolume_mul, Complex.re_ofReal_mul]
  rw [bound_def, hre, div_mul_cancel_right₀ C.f_zero_pos.ne',
    ENNReal.ofReal_inv_of_pos (ZLattice.covolume_pos Λ volume), ENNReal.div_eq_inv_mul]

end IsSharpForLattice

end SphereCeti.CohnElkies.Certificate
