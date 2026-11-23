/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import TauCeti.Analysis.Fourier.PoissonSummation

/-!
# Poisson summation over finitely many lattice translates

Let `L` be a full lattice in a finite-dimensional real inner product space `E`, and let
`p : ι → E` be a finite family of points, such as representatives of the orbits of the centers of
a periodic sphere packing under its period lattice.  Summing Poisson's formula
`SchwartzMap.tsum_eq_tsum_dual_fourier` over the differences `p q - p q'` gives, for a Schwartz
function `f`,

`∑' z : L, ∑ q, ∑ q', f (z + p q - p q') =
  (covolume L)⁻¹ * ∑' y : L^∨, 𝓕 f y * ‖∑ q, exp (2πi ⟪y, p q⟫)‖²`.

The squared norm on the right is the structure factor of the configuration `L + {p q}` at the
dual frequency `y`.  At a dual frequency `y`, the phase `exp (2πi ⟪y, s⟫)` depends only on the
class of `s` modulo `L`, so the structure factor does not depend on the choice of the
representatives `p q`.

## Main statements

* `SphereCeti.CohnElkies.phase_eq_of_sub_mem_lattice`: at a dual frequency, two points that differ
  by a lattice vector have the same phase.
* `SphereCeti.CohnElkies.tsum_sum_sum_eq_tsum_dual_fourier_mul_structureFactor`: Poisson summation
  over finitely many lattice translates, with the structure factor on the dual side.

## References

* H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714, proof of Theorem 3.2.
-/

public section

open Complex
open scoped Real RealInnerProductSpace SchwartzMap FourierTransform

namespace SphereCeti.CohnElkies

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At a frequency `y` in the dual of `L`, two points that differ by a vector of `L` have the same
phase `exp (2πi ⟪y, ·⟫)`. -/
theorem phase_eq_of_sub_mem_lattice {L : Submodule ℤ E} {y : E} (hy : y ∈ ZLattice.dual L)
    {s t : E} (hst : s - t ∈ L) :
    cexp (2 * π * I * ⟪y, s⟫) = cexp (2 * π * I * ⟪y, t⟫) := by
  obtain ⟨m, hm⟩ := ZLattice.mem_dual.mp hy (s - t) hst
  rw [inner_sub_right, sub_eq_iff_eq_add] at hm
  rw [hm, ofReal_add, mul_add, exp_add, ofReal_intCast, mul_comm _ (m : ℂ),
    exp_int_mul_two_pi_mul_I, one_mul]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Poisson summation over finitely many lattice translates.**  For a full lattice `L`, a finite
family of points `p`, and a Schwartz function `f`,
`∑' z : L, ∑ q, ∑ q', f (z + p q - p q') =
  (covolume L)⁻¹ * ∑' y : L^∨, 𝓕 f y * ‖∑ q, exp (2πi ⟪y, p q⟫)‖²`. -/
theorem tsum_sum_sum_eq_tsum_dual_fourier_mul_structureFactor (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι] (p : ι → E)
    (f : 𝓢(E, ℂ)) :
    ∑' z : L, ∑ q, ∑ q', f ((z : E) + p q - p q') =
      (ZLattice.covolume L : ℂ)⁻¹ * ∑' y : ZLattice.dual L,
        𝓕 f (y : E) * ((‖∑ q, cexp (2 * π * I * ⟪(y : E), p q⟫)‖ ^ 2 : ℝ) : ℂ) := by
  -- The squared norm of the amplitude is the double sum of the phases of the differences.
  have hnorm (y : E) : ((‖∑ q, cexp (2 * π * I * ⟪y, p q⟫)‖ ^ 2 : ℝ) : ℂ) =
      ∑ q, ∑ q', cexp (2 * π * I * ⟪p q - p q', y⟫) := by
    rw [ofReal_pow, ← mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun q' _ ↦ ?_
    rw [← exp_conj, ← exp_add, inner_sub_left, real_inner_comm y, real_inner_comm y]
    simp only [map_mul, map_ofNat, conj_ofReal, conj_I]
    congr 1
    push_cast
    ring
  have hleft (q q' : ι) : Summable fun z : L ↦ f ((z : E) + p q - p q') :=
    (ZLattice.summable_poisson_left L f (p q - p q')).congr fun z ↦ by
      rw [add_sub_assoc, add_comm]
  have hright (q q' : ι) : Summable fun y : ZLattice.dual L ↦
      𝓕 (f : E → ℂ) y * cexp (2 * π * I * ⟪p q - p q', (y : E)⟫) :=
    ZLattice.summable_poisson_right L f (p q - p q')
  calc ∑' z : L, ∑ q, ∑ q', f ((z : E) + p q - p q')
      = ∑ q, ∑ q', ∑' z : L, f ((p q - p q') + z) := by
        rw [Summable.tsum_finsetSum fun q _ ↦ summable_sum fun q' _ ↦ hleft q q']
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [Summable.tsum_finsetSum fun q' _ ↦ hleft q q']
        refine Finset.sum_congr rfl fun q' _ ↦ tsum_congr fun z ↦ ?_
        rw [add_sub_assoc, add_comm]
    _ = ∑ q, ∑ q', (ZLattice.covolume L : ℂ)⁻¹ * ∑' y : ZLattice.dual L,
          𝓕 (f : E → ℂ) y * cexp (2 * π * I * ⟪p q - p q', (y : E)⟫) := by
        simp only [SchwartzMap.tsum_eq_tsum_dual_fourier]
    _ = (ZLattice.covolume L : ℂ)⁻¹ * ∑' y : ZLattice.dual L,
          ∑ q, ∑ q', 𝓕 (f : E → ℂ) y * cexp (2 * π * I * ⟪p q - p q', (y : E)⟫) := by
        rw [Summable.tsum_finsetSum fun q _ ↦ summable_sum fun q' _ ↦ hright q q', Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        rw [Summable.tsum_finsetSum fun q' _ ↦ hright q q', Finset.mul_sum]
    _ = _ := by
        simp only [hnorm, Finset.mul_sum, SchwartzMap.fourier_coe]

end SphereCeti.CohnElkies
