/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.ZLattice.DualPhase
public import TauCeti.Analysis.Fourier.PoissonSummation

/-!
# Structure factors and Poisson summation over finitely many lattice translates

Let `L` be a full lattice in a finite-dimensional real inner product space `E`, and let
`p : ι → E` be a finite family of points, such as representatives of the orbits of the centers of
a periodic sphere packing under its period lattice.  The structure amplitude of `p` at a frequency
`y` is the exponential sum `A_p(y) = ∑ q, exp (2πi ⟪y, p q⟫)`, and its structure factor is the
squared norm `S_p(y) = ‖A_p(y)‖²`.  Summing Poisson's formula
`SchwartzMap.tsum_eq_tsum_dual_fourier` over the differences `p q - p q'` gives, for a Schwartz
function `f`,

`∑' z : L, ∑ q, ∑ q', f (z + p q - p q') = (covolume L)⁻¹ * ∑' y : L^∨, 𝓕 f y * S_p(y)`.

At a dual frequency `y` the phase `exp (2πi ⟪y, s⟫)` depends only on the class of `s` modulo `L`,
so the structure amplitude, and with it the structure factor, does not depend on the choice of
the points `p q` in their classes.

## Main definitions

* `SphereCeti.CohnElkies.structureAmplitude p y`: the exponential sum `∑ q, exp (2πi ⟪y, p q⟫)`.
* `SphereCeti.CohnElkies.structureFactor p y`: the squared norm of the structure amplitude.

## Main statements

* `SphereCeti.CohnElkies.structureFactor_eq_zero_iff`: the structure factor vanishes exactly
  when the structure amplitude does.
* `SphereCeti.CohnElkies.ofReal_structureFactor_eq_sum_sum`: the structure factor is the double
  sum of the phases of the differences of the points.
* `SphereCeti.CohnElkies.structureAmplitude_eq_of_sub_mem`: at a dual frequency, the structure
  amplitude does not change when each point moves by a lattice vector.
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]

/-- The structure amplitude of a finite family of points `p` at a frequency `y`: the exponential
sum `∑ q, exp (2πi ⟪y, p q⟫)`. -/
noncomputable def structureAmplitude (p : ι → E) (y : E) : ℂ :=
  ∑ q, cexp (2 * π * I * ⟪y, p q⟫)

/-- The structure amplitude is the exponential sum `∑ q, exp (2πi ⟪y, p q⟫)`. -/
theorem structureAmplitude_def (p : ι → E) (y : E) :
    structureAmplitude p y = ∑ q, cexp (2 * π * I * ⟪y, p q⟫) :=
  (rfl)

/-- The structure factor of a finite family of points `p` at a frequency `y`: the squared norm of
its structure amplitude. -/
noncomputable def structureFactor (p : ι → E) (y : E) : ℝ :=
  ‖structureAmplitude p y‖ ^ 2

/-- The structure factor is the squared norm of the structure amplitude. -/
theorem structureFactor_def (p : ι → E) (y : E) :
    structureFactor p y = ‖structureAmplitude p y‖ ^ 2 :=
  (rfl)

/-- The structure factor is nonnegative. -/
theorem structureFactor_nonneg (p : ι → E) (y : E) : 0 ≤ structureFactor p y :=
  sq_nonneg _

/-- The structure factor vanishes exactly when the structure amplitude does. -/
theorem structureFactor_eq_zero_iff (p : ι → E) (y : E) :
    structureFactor p y = 0 ↔ structureAmplitude p y = 0 := by
  rw [structureFactor_def, sq_eq_zero_iff, norm_eq_zero]

/-- The structure factor is the double sum of the phases of the differences of the points. -/
theorem ofReal_structureFactor_eq_sum_sum (p : ι → E) (y : E) :
    (structureFactor p y : ℂ) = ∑ q, ∑ q', cexp (2 * π * I * ⟪p q - p q', y⟫) := by
  -- `S_p(y) = A * conj A` for the amplitude `A`, and the product of the two sums is a double sum.
  rw [structureFactor_def, ofReal_pow, ← mul_conj', structureAmplitude_def, map_sum,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun q' _ ↦ ?_
  -- The conjugate of a phase is the phase with the opposite exponent.
  have hconj (x : E) :
      (starRingEnd ℂ) (cexp (2 * π * I * ⟪y, x⟫)) = cexp (-(2 * π * I * ⟪y, x⟫)) := by
    rw [← exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, conj_ofReal, conj_I]
    ring
  rw [hconj, ← exp_add]
  congr 1
  simp only [real_inner_comm y, inner_sub_right]
  push_cast
  ring

/-- At the zero frequency the structure factor is the square of the number of points. -/
@[simp]
theorem structureFactor_zero (p : ι → E) : structureFactor p 0 = (Fintype.card ι : ℝ) ^ 2 := by
  simp [structureFactor_def, structureAmplitude_def]

/-- Check that `simp` evaluates the structure factor at the zero frequency. -/
example (p : ι → E) (c : ℝ) : c * structureFactor p 0 = c * (Fintype.card ι : ℝ) ^ 2 := by
  simp

/-- At a frequency `y` in the dual of `L`, the structure amplitude does not change when each point
moves by a vector of `L`. -/
theorem structureAmplitude_eq_of_sub_mem {L : Submodule ℤ E} {y : E} (hy : y ∈ ZLattice.dual L)
    {p p' : ι → E} (h : ∀ q, p q - p' q ∈ L) :
    structureAmplitude p y = structureAmplitude p' y := by
  simp only [structureAmplitude_def]
  exact Finset.sum_congr rfl fun q _ ↦ ZLattice.phase_eq_of_sub_mem_lattice hy (h q)

variable [FiniteDimensional ℝ E]

/-- The direct side of Poisson summation over finitely many lattice translates is summable. -/
theorem summable_sum_sum_translates (L : Submodule ℤ E) [DiscreteTopology L] (p : ι → E)
    (f : 𝓢(E, ℂ)) : Summable fun z : L ↦ ∑ q, ∑ q', f ((z : E) + p q - p q') :=
  summable_sum fun q _ ↦ summable_sum fun q' _ ↦
    (ZLattice.summable_poisson_left L f (p q - p q')).congr fun z ↦ by
      rw [add_sub_assoc, add_comm]

variable [MeasurableSpace E] [BorelSpace E]

/-- The dual side of Poisson summation over finitely many lattice translates, the Fourier
transform times the structure factor, is summable over the dual lattice. -/
theorem summable_fourier_mul_structureFactor (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (p : ι → E) (f : 𝓢(E, ℂ)) :
    Summable fun y : ZLattice.dual L ↦ 𝓕 f (y : E) * (structureFactor p (y : E) : ℂ) := by
  simp_rw [ofReal_structureFactor_eq_sum_sum, Finset.mul_sum]
  exact summable_sum fun q _ ↦ summable_sum fun q' _ ↦
    ZLattice.summable_poisson_right L f (p q - p q')

/-- **Poisson summation over finitely many lattice translates.**  For a full lattice `L`, a finite
family of points `p`, and a Schwartz function `f`,
`∑' z : L, ∑ q, ∑ q', f (z + p q - p q') = (covolume L)⁻¹ * ∑' y : L^∨, 𝓕 f y * S_p(y)`,
where `S_p` is the structure factor of `p`. -/
theorem tsum_sum_sum_eq_tsum_dual_fourier_mul_structureFactor (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (p : ι → E) (f : 𝓢(E, ℂ)) :
    ∑' z : L, ∑ q, ∑ q', f ((z : E) + p q - p q') =
      (ZLattice.covolume L : ℂ)⁻¹ * ∑' y : ZLattice.dual L,
        𝓕 f (y : E) * (structureFactor p (y : E) : ℂ) := by
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
        simp only [ofReal_structureFactor_eq_sum_sum, Finset.mul_sum, SchwartzMap.fourier_coe]

end SphereCeti.CohnElkies
