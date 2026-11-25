/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.CohnElkies.Defects

/-!
# The periodic and lattice Cohn–Elkies bounds

Let `L` be a full lattice in a finite-dimensional real inner product space `E`, and let `f` be a
Schwartz function with `Re f ≤ 0` at distance at least `r` from the origin, `Re 𝓕 f ≥ 0` at the
nonzero frequencies of the dual lattice and `Re 𝓕 f(0) > 0`.  If `p` is a nonempty family of `N`
points, pairwise incongruent modulo `L`, whose nonzero differences `z + p q - p q'` with `z ∈ L`
all have norm at least `r`, then
`N / covol(L) ≤ Re f(0) / Re 𝓕 f(0)`.
The gap between the two sides is the sum of the Fourier and direct defects divided by
`N * Re 𝓕 f(0)`, and both defects are nonnegative under these hypotheses.

For a single point this is the lattice bound: if every nonzero vector of `L` has norm at least
`r`, then `1 / covol(L) ≤ Re f(0) / Re 𝓕 f(0)`.

These are the finite-pattern bounds behind the Cohn–Elkies bound for periodic packings: for a
periodic packing with center separation `r`, `N` orbits and period lattice `L`, the density is
`N / covol(L)` times the volume of a ball of radius `r / 2`.

## Main statements

* `SphereCeti.CohnElkies.card_div_covolume_le`: the periodic bound
  `N / covol(L) ≤ Re f(0) / Re 𝓕 f(0)`.
* `SphereCeti.CohnElkies.inv_covolume_le`: the lattice bound
  `1 / covol(L) ≤ Re f(0) / Re 𝓕 f(0)`.

## References

* H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714, Section 3.
-/

public section

open scoped FourierTransform SchwartzMap

namespace SphereCeti.CohnElkies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The periodic Cohn–Elkies bound.**  Let `p` be a nonempty family of `N` points pairwise
incongruent modulo a full lattice `L`, whose nonzero differences `z + p q - p q'` with `z ∈ L`
have norm at least `r`.  If `Re f ≤ 0` at distance at least `r` from the origin, `Re 𝓕 f ≥ 0` at
the nonzero dual frequencies and `Re 𝓕 f(0) > 0`, then `N / covol(L) ≤ Re f(0) / Re 𝓕 f(0)`. -/
theorem card_div_covolume_le {ι : Type*} [Fintype ι] [Nonempty ι] (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {p : ι → E} (hp : ∀ q q', p q - p q' ∈ L → q = q')
    {f : 𝓢(E, ℂ)} {r : ℝ} (hf : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0)
    (hsep : ∀ (z : L) (q q' : ι), (z : E) + p q - p q' ≠ 0 → r ≤ ‖(z : E) + p q - p q'‖)
    (hfourier : ∀ y : ZLattice.dual L, y ≠ 0 → 0 ≤ (𝓕 (f : E → ℂ) (y : E)).re)
    (hf0 : 0 < (𝓕 f 0).re) :
    (Fintype.card ι : ℝ) / ZLattice.covolume L ≤ (f 0).re / (𝓕 f 0).re := by
  -- The gap is the nonnegative sum of the defects over a positive denominator.
  have hgap := normalized_gap_eq_defects L hp f hf0.ne'
  have hdef : 0 ≤ (fourierDefect L p f + directDefect L p f) /
      ((Fintype.card ι : ℝ) * (𝓕 f 0).re) :=
    div_nonneg (add_nonneg (fourierDefect_nonneg hfourier) (directDefect_nonneg hf hsep))
      (mul_pos (Nat.cast_pos.mpr Fintype.card_pos) hf0).le
  linarith

/-- **The lattice Cohn–Elkies bound.**  If every nonzero vector of a full lattice `L` has norm at
least `r`, `Re f ≤ 0` at distance at least `r` from the origin, `Re 𝓕 f ≥ 0` at the nonzero dual
frequencies and `Re 𝓕 f(0) > 0`, then `1 / covol(L) ≤ Re f(0) / Re 𝓕 f(0)`. -/
theorem inv_covolume_le (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {f : 𝓢(E, ℂ)} {r : ℝ} (hf : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0)
    (hsep : ∀ z : L, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hfourier : ∀ y : ZLattice.dual L, y ≠ 0 → 0 ≤ (𝓕 (f : E → ℂ) (y : E)).re)
    (hf0 : 0 < (𝓕 f 0).re) :
    (ZLattice.covolume L)⁻¹ ≤ (f 0).re / (𝓕 f 0).re := by
  -- The one-point family at the origin.
  have h := card_div_covolume_le (ι := Unit) L (p := fun _ ↦ 0) (fun _ _ _ ↦ Subsingleton.elim _ _)
    hf (fun z _ _ hz ↦ by simpa using hsep z (by simpa using hz)) hfourier hf0
  simpa using h

end SphereCeti.CohnElkies
