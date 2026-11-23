/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCetiRoadmap.Suggested

public import TauCeti.Analysis.Fourier.Hardy.DiskFunction
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.FiniteSection.Stability
public import TauCeti.Analysis.Normed.Operator.Compact.Estimate
public import TauCeti.NumberTheory.ModularForms.QExpansion.Laurent

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# Coefficient construction of the E8 and Leech magic functions: target statements

This file states the main definitions and theorems of the roadmap in
`SphereCetiRoadmap/CoefficientMagic/README.md`, with `sorry` in place of the proofs and of some
definitions.  The mathematical source is *A construction of the sphere-packing magic functions in
dimensions 8 and 24*, Hexagon 2610.00330v1.  Its results are statements to be proved here; none
is assumed.  References below are to its sections and numbered results.

The statements are grouped by the milestones of the README: the two coefficient systems (C0);
the map from coefficient vectors to radial Schwartz functions (C1); Poisson summation
differentiated in a dilation parameter (C2); the moment operator, written in terms of Fourier
samples (C3); geometric decay of the solutions of the homogeneous equations (the conclusion of
C4); the family of modular forms and the explicit null vectors of its cusp matrices, and the map
from a global analytic solution to a coefficient vector (C5); the map from an arbitrary solution
in `ℓ²` of the homogeneous equations to a global analytic solution, vanishing at zero
normalization, and the coefficient theorem (C6); and the operator-theoretic argument of C8 for an
arbitrary compact operator.

Throughout, *the kernel* is the null space of the moment operator, as in the README's glossary.

Three objects of the paper have no Lean statement here, because their definitions use boundary
traces and contour data that have not yet been fixed in Lean: the contour measures `μ₀, μ₁` and
their Cauchy transforms (C3), the endpoint continuation with its domains (C4), and the compact
regularizing operator `K` of Appendix B (C8).  The README states them in prose.  No definition
with body `sorry` is put in their place: such a definition of `K`, specified only by `K c = c`
on the kernel, would also be satisfied by the orthogonal projection onto the kernel.

Radial profiles are functions of squared radius `u = ‖x‖²`, and are specified only for `u ≥ 0`.
The cusp coordinate of a modular form is `𝔮 = exp (2πiτ)`; the argument of a coefficient
generating series is `q = e^π · exp (πiτ)`.  The two are kept distinct throughout.
-/

@[expose] public section

open BigOperators MeasureTheory Metric Set Filter Module Matrix
open Complex UpperHalfPlane MatrixGroups
open scoped ENNReal FourierTransform Real Topology ModularForm CongruenceSubgroup
open scoped SchwartzMap InnerProductSpace

namespace SphereCeti.CoefficientMagic

noncomputable section

open SphereCeti.Suggested (V RadialSchwartzMap)

/-! ## Results used from the fixed versions of TauCeti and Mathlib

These `#check` lines confirm that the named results exist.  They are not targets: the roadmap
uses these results and asks only for the lemmas connecting them to the coefficient systems. -/

#check SchwartzMap.tsum_eq_tsum_dual_fourier
#check ZLattice.representationNumber
#check TauCeti.HardySpace.hasFPowerSeriesOnBall_diskFunction
#check TauCeti.HardySpace.differentiableOn_diskFunction
#check TauCeti.HardySpace.norm_diskFunction_le
#check TauCeti.HardySpace.tendsto_eLpNorm_diskFunction_sub
#check ContinuousLinearMap.exists_pos_mul_norm_le_of_compact_estimate
#check ContinuousLinearMap.norm_finiteSection_solution_sub_le
#check ContinuousLinearMap.tendsto_finiteSection_solution
#check ModularForm.levelOne_weight_two_rank_zero
#check ModularForm.levelOne_weight_four_rank_one
#check ModularForm.dimension_level_one
#check ModularForm.sturm_bound_levelOne
#check ModularForm.E₄
#check ModularForm.E₆
#check ModularForm.discriminant
#check jacobiTheta₂

/-! ## C0: the two cases and their finite data -/

/-- The two coefficient systems, in dimensions 8 and 24.  Every quantity below that depends on
the dimension is defined separately in the two cases, so that the two systems stay distinct. -/
inductive Case
  | e8
  | leech
  deriving DecidableEq, Repr

namespace Case

/-- The dimension `d`. -/
def dim : Case → ℕ
  | e8 => 8
  | leech => 24

/-- The number `n₀` such that the first shell has squared norm `2 n₀`. -/
def firstShell : Case → ℕ
  | e8 => 1
  | leech => 2

/-- The number `N` of lattice vectors on the first shell. -/
def shellCard : Case → ℕ
  | e8 => 240
  | leech => 196560

/-- The exponent `d/2 - 2` of the reciprocal integral (§2.1 and §11.1). -/
def recipExp : Case → ℕ
  | e8 => 2
  | leech => 10

/-- The scalar weight `-(d/2 - 2)` of the six-component inversion law. -/
def weight : Case → ℤ
  | e8 => -2
  | leech => -10

/-- The nonpositive coefficient modes `(j, m)`, which multiply the correction functions. -/
def corrModes : Case → Finset (Fin 4 × ℤ)
  | e8 => {(0, -2), (0, 0), (1, 0)}
  | leech => {(0, -4), (0, -2), (0, 0), (1, -2), (1, 0)}

/-- The lowest allowed exponents of the cusp coordinate `𝔮` for the six components (§6.2 and
§11.4).  These are lower bounds on orders, not exact orders. -/
def cuspExp : Case → Fin 6 → ℚ
  | e8 => ![-1, 0, 1, 1 / 2, 0, 0]
  | leech => ![-2, -1, 1, 1 / 2, -1, -1]

theorem dim_pos (D : Case) : 0 < D.dim := by cases D <;> decide

example (D : Case) : D.recipExp + 2 = D.dim / 2 := by cases D <;> decide
example (D : Case) : D.weight = -(D.recipExp : ℤ) := by cases D <;> decide
example : e8.corrModes.card = 3 ∧ leech.corrModes.card = 5 := by decide
/-- The dimension-24 system has the two modes at exponent `-2` and the mode `(0, -4)`; the
dimension-8 system does not, and is not a truncation of it. -/
example : (1, -2) ∈ leech.corrModes ∧ (1, -2) ∉ e8.corrModes ∧ (0, -4) ∉ e8.corrModes := by
  decide
/-- The exceptional mode fixed by Poisson summation sits at exponent `-2 n₀`. -/
example (D : Case) : ((0 : Fin 4), -(2 * (D.firstShell : ℤ))) ∈ D.corrModes := by
  cases D <;> decide
/-- The forced first-shell derivative `-d / (4 n₀ N)` in squared radius. -/
example : -(e8.dim : ℚ) / (4 * e8.firstShell * e8.shellCard) = -1 / 120 := by
  norm_num [dim, firstShell, shellCard]
example : -(leech.dim : ℚ) / (4 * leech.firstShell * leech.shellCard) = -1 / 65520 := by
  norm_num [dim, firstShell, shellCard]
/-- The cusp exponents sum to `1/2` in dimension 8 and to `-7/2` in dimension 24; the sum enters
the degree of the determinant bundle in the Riemann–Roch count of C7. -/
example : ∑ j, e8.cuspExp j = 1 / 2 ∧ ∑ j, leech.cuspExp j = -7 / 2 := by
  constructor <;> norm_num [cuspExp, Fin.sum_univ_succ]

end Case

/-- The common positive modes: `(j, m)` with `m > 0` even for `j = 0, 1, 2` and `m > 0` odd for
`j = 3`. -/
def posModes : Set (Fin 4 × ℤ) :=
  {p | 0 < p.2 ∧ ((p.1 ≠ 3 ∧ Even p.2) ∨ (p.1 = 3 ∧ Odd p.2))}

/-- The index set `𝓘_d` of a coefficient vector (§2.2 and §11.1). -/
def modes (D : Case) : Set (Fin 4 × ℤ) :=
  (D.corrModes : Set (Fin 4 × ℤ)) ∪ posModes

/-- The index type of a coefficient vector. -/
abbrev Index (D : Case) : Type := ↥(modes D)

/-- The coefficient Hilbert space `ℓ²(𝓘_d)`, with its standard inner product. -/
abbrev Coeff (D : Case) : Type := lp (fun _ : Index D => ℂ) 2

example : ((2 : Fin 4), (4 : ℤ)) ∈ posModes ∧ ((3 : Fin 4), (5 : ℤ)) ∈ posModes := by
  refine ⟨⟨by norm_num, Or.inl ⟨by decide, by decide⟩⟩, ⟨by norm_num, Or.inr ⟨rfl, by decide⟩⟩⟩

theorem one_zero_mem_modes (D : Case) : ((1 : Fin 4), (0 : ℤ)) ∈ modes D := by
  cases D <;> exact Or.inl (by decide)

open scoped Classical in
/-- The coefficient `c_{j,m}`, extended by zero outside the index set. -/
def coeff {D : Case} (c : Coeff D) (j : Fin 4) (m : ℤ) : ℂ :=
  if h : (j, m) ∈ modes D then c ⟨(j, m), h⟩ else 0

/-- The normalizing functional `λ(c) = c_{1,0} / 4` (§2.2). -/
def normalization (D : Case) : Coeff D →L[ℂ] ℂ :=
  (4 : ℂ)⁻¹ • lp.evalCLM ℂ (fun _ : Index D => ℂ) 2 ⟨(1, 0), one_zero_mem_modes D⟩

theorem normalization_apply (D : Case) (c : Coeff D) :
    normalization D c = coeff c 1 0 / 4 := by
  sorry

/-! ### Elementary functions -/

/-- The factor `P(u) = sin² (πu/2)`, with a double zero at every even integer. -/
def sinSq (u : ℝ) : ℝ := Real.sin (π * u / 2) ^ 2

/-- The large-parameter function `U_{m,k}` of §2.1. -/
def largeMode (m k : ℕ) (u : ℝ) : ℝ :=
  Real.exp (π * m) * sinSq u * ∫ t in Ioi (1 : ℝ), t ^ k * Real.exp (-π * (m + u) * t)

/-- The reciprocal function `V_m` of §2.1 and §11.1, with exponent `e = d/2 - 2`. -/
def recipMode (e m : ℕ) (u : ℝ) : ℝ :=
  Real.exp (π * m) * sinSq u * ∫ t in (0 : ℝ)..1, t ^ e * Real.exp (-π * (m / t + u * t))

/-- The correction function `R_{ℓ,0}` of §2.1, with its removable value at `u = ℓ`. -/
def corrSimple (ℓ : ℕ) (u : ℝ) : ℝ :=
  if u = ℓ then 0 else sinSq u * Real.exp (-π * (u - ℓ)) / (π * (u - ℓ))

/-- The correction function `R_{ℓ,1}` of §2.1, with its removable value at `u = ℓ`. -/
def corrDouble (ℓ : ℕ) (u : ℝ) : ℝ :=
  if u = ℓ then 1 / 4
  else sinSq u * Real.exp (-π * (u - ℓ)) * (1 / (π * (u - ℓ)) + 1 / (π ^ 2 * (u - ℓ) ^ 2))

/-- The closed form of `U_{m,k}` used in Lemma 3.1. -/
theorem largeMode_eq (m k : ℕ) (hm : 1 ≤ m) {u : ℝ} (hu : 0 ≤ u) :
    largeMode m k u = sinSq u * Real.exp (-π * u) *
      ∑ j ∈ Finset.range (k + 1),
        ((k.factorial : ℝ) / ((k - j).factorial : ℝ)) / (π * (m + u)) ^ (j + 1) := by
  sorry

/-- The simple correction vanishes at its removable point and has derivative `π/4` there. -/
theorem hasDerivAt_corrSimple (ℓ : ℕ) (hℓ : Even ℓ) :
    HasDerivAt (corrSimple ℓ) (π / 4) ℓ := by
  sorry

/-- The double correction has derivative `0` at its removable point, where its value is `1/4` by
definition. -/
theorem hasDerivAt_corrDouble (ℓ : ℕ) (hℓ : Even ℓ) :
    HasDerivAt (corrDouble ℓ) 0 ℓ := by
  sorry

/-- Both corrections keep the double zeros of `P` at the other even integers. -/
theorem hasDerivAt_corrSimple_of_ne (ℓ n : ℕ) (hℓ : Even ℓ) (hn : Even n) (h : n ≠ ℓ) :
    corrSimple ℓ n = 0 ∧ HasDerivAt (corrSimple ℓ) 0 n := by
  sorry

theorem hasDerivAt_corrDouble_of_ne (ℓ n : ℕ) (hℓ : Even ℓ) (hn : Even n) (h : n ≠ ℓ) :
    corrDouble ℓ n = 0 ∧ HasDerivAt (corrDouble ℓ) 0 n := by
  sorry

/-- The corrections are real-analytic, as restrictions of entire functions: the singularities are
removable.  Here `⊤` is the analytic order `ω`. -/
theorem contDiff_corrSimple (ℓ : ℕ) (hℓ : Even ℓ) : ContDiff ℝ ⊤ (corrSimple ℓ) := by
  sorry

theorem contDiff_corrDouble (ℓ : ℕ) (hℓ : Even ℓ) : ContDiff ℝ ⊤ (corrDouble ℓ) := by
  sorry

/-- The function multiplying the coefficient `c_{j,m}` in the ansatz of §2.2 and §11.1.  Positive
modes use `U_{m,0}`, `U_{m,1}`, `U_{m,2} + V_m` for `j = 0, 1, 2` and `U_{m,0} - 2 V_m` for
`j = 3`; a nonpositive mode `m = -ℓ` uses `e^{-πℓ} R_{ℓ,j}`. -/
def modeFun (D : Case) (p : Fin 4 × ℤ) (u : ℝ) : ℝ :=
  if 0 < p.2 then
    match p.1 with
    | 0 => largeMode p.2.toNat 0 u
    | 1 => largeMode p.2.toNat 1 u
    | 2 => largeMode p.2.toNat 2 u + recipMode D.recipExp p.2.toNat u
    | 3 => largeMode p.2.toNat 0 u - 2 * recipMode D.recipExp p.2.toNat u
  else if p.1 = 0 then Real.exp (π * p.2) * corrSimple (-p.2).toNat u
  else Real.exp (π * p.2) * corrDouble (-p.2).toNat u

example (D : Case) (u : ℝ) : modeFun D (1, 0) u = corrDouble 0 u := by
  simp [modeFun]
example (D : Case) (u : ℝ) :
    modeFun D (0, -4) u = Real.exp (π * (-4 : ℤ)) * corrSimple 4 u := by
  simp [modeFun]
example (D : Case) (u : ℝ) :
    modeFun D (3, 5) u = largeMode 5 0 u - 2 * recipMode D.recipExp 5 u := by
  simp [modeFun]

/-- The squared-radius profile `Φ_c` of §2.2 and §11.1, for `u ≥ 0`.  The value for `u < 0` is
not part of the specification. -/
def profile (D : Case) (c : Coeff D) (u : ℝ) : ℂ :=
  ∑' i : Index D, c i * (modeFun D i.1 u : ℂ)

/-- The series defining the profile converges absolutely on the half-line. -/
theorem summable_profile (D : Case) (c : Coeff D) {u : ℝ} (hu : 0 ≤ u) :
    Summable fun i : Index D => c i * (modeFun D i.1 u : ℂ) := by
  sorry

/-! ## C1: Schwartz synthesis -/

/-- The synthesis map `c ↦ f_c` of Lemma 3.1, into the canonical radial Schwartz space.  It is
constructed directly there; no extension of the profile to `u < 0` enters its specification. -/
def synth (D : Case) : Coeff D →L[ℂ] RadialSchwartzMap ℂ (V D.dim) ℂ := by
  sorry

/-- The defining equation of the synthesis map. -/
theorem synth_apply (D : Case) (c : Coeff D) (x : V D.dim) :
    synth D c x = profile D c (‖x‖ ^ 2) := by
  sorry

/-- Distinct coefficient vectors give distinct functions. -/
theorem synth_injective (D : Case) : Function.Injective (synth D) := by
  sorry

/-- The value at the origin is the normalization. -/
theorem profile_zero (D : Case) (c : Coeff D) : profile D c 0 = normalization D c := by
  sorry

/-- The zeros on every shell forced by the factor `P` (Lemma 3.1 and §11.2). -/
theorem profile_shell (D : Case) (c : Coeff D) (n : ℕ) (hn : D.firstShell ≤ n) :
    profile D c (2 * n) = 0 := by
  sorry

/-- The first-shell derivative is carried by the exceptional coefficient `c_{0,-2n₀}`. -/
theorem hasDerivAt_profile_firstShell (D : Case) (c : Coeff D) :
    HasDerivAt (profile D c)
      (π / 4 * Real.exp (-(2 * π * D.firstShell)) * coeff c 0 (-(2 * (D.firstShell : ℤ))))
      (2 * D.firstShell) := by
  sorry

/-- The double zeros on every later shell forced by the factor `P`. -/
theorem hasDerivAt_profile_laterShell (D : Case) (c : Coeff D) (n : ℕ)
    (hn : D.firstShell < n) : HasDerivAt (profile D c) 0 (2 * n) := by
  sorry

/-- A point of squared norm `v`. -/
def radialPoint (D : Case) (v : ℝ) : V D.dim :=
  EuclideanSpace.single (⟨0, D.dim_pos⟩ : Fin D.dim) (Real.sqrt v)

theorem norm_radialPoint_sq (D : Case) {v : ℝ} (hv : 0 ≤ v) : ‖radialPoint D v‖ ^ 2 = v := by
  sorry

/-- The squared-radius profile `G_c` of the Fourier transform, for `v ≥ 0`. -/
def fourierProfile (D : Case) (c : Coeff D) (v : ℝ) : ℂ :=
  𝓕 (synth D c : 𝓢(V D.dim, ℂ)) (radialPoint D v)

/-- The defining equation of the Fourier profile. -/
theorem fourier_synth_apply (D : Case) (c : Coeff D) (ξ : V D.dim) :
    𝓕 (synth D c : 𝓢(V D.dim, ℂ)) ξ = fourierProfile D c (‖ξ‖ ^ 2) := by
  sorry

/-- The Fourier profile is differentiable at every positive squared radius, so `deriv` below is
a genuine derivative. -/
theorem differentiableAt_fourierProfile (D : Case) (c : Coeff D) {v : ℝ} (hv : 0 < v) :
    DifferentiableAt ℝ (fourierProfile D c) v := by
  sorry

/-! ## The sample equations -/

/-- The homogeneous Fourier-sample equations of Theorems 2.1 and 11.1: the Fourier profile and its
squared-radius derivative vanish at `2n` for `n ≥ n₀`.  Normalization is not included. -/
def IsSampleSolution (D : Case) (c : Coeff D) : Prop :=
  ∀ n : ℕ, D.firstShell ≤ n →
    fourierProfile D c (2 * n) = 0 ∧ deriv (fourierProfile D c) (2 * n) = 0

/-- The solution space of the homogeneous sample equations in the whole space `ℓ²(𝓘_d)`. -/
def sampleKernel (D : Case) : Submodule ℂ (Coeff D) where
  carrier := {c | IsSampleSolution D c}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

theorem mem_sampleKernel {D : Case} {c : Coeff D} :
    c ∈ sampleKernel D ↔ IsSampleSolution D c := Iff.rfl

/-- The kernel is closed. -/
theorem isClosed_sampleKernel (D : Case) : IsClosed (sampleKernel D : Set (Coeff D)) := by
  sorry

/-! ## C2: differentiated Poisson summation -/

namespace Poisson

/-- The dilation identity behind Lemma 3.2, for an arbitrary lattice and Schwartz function. -/
theorem dilation {d : ℕ} (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (f : 𝓢(V d, ℂ)) {t : ℝ} (ht : 0 < t) :
    ∑' x : Λ, f (Real.sqrt t • (x : V d)) =
      ((ZLattice.covolume Λ : ℂ)⁻¹) * ((t ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        ∑' y : ZLattice.dual Λ, 𝓕 f ((Real.sqrt t)⁻¹ • (y : V d)) := by
  sorry

/-- The dilated lattice sum may be differentiated termwise in the dilation parameter. -/
theorem hasDerivAt_dilation {d : ℕ} (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (f : 𝓢(V d, ℂ)) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∑' x : Λ, f (Real.sqrt s • (x : V d)))
      (∑' x : Λ, deriv (fun s : ℝ => f (Real.sqrt s • (x : V d))) t) t := by
  sorry

/-- The generic first-shell identity.  For a self-dual lattice of covolume one whose shortest
nonzero vectors have squared norm `s`, and a radial Schwartz function with squared-radius
profiles `Φ` and `G`: if `Φ` vanishes on every shell and to second order beyond the first, and
`G` vanishes to second order on every shell, then `G 0 = Φ 0` and the first-shell derivative of
`Φ` is forced.  The derivative is in squared radius, not in radius. -/
theorem firstShell_deriv {d : ℕ} (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hdual : ZLattice.dual Λ = Λ) (hcov : ZLattice.covolume Λ = 1)
    (f : 𝓢(V d, ℂ)) (Φ G : ℝ → ℂ)
    (hΦ : ∀ x, f x = Φ (‖x‖ ^ 2)) (hG : ∀ ξ, 𝓕 f ξ = G (‖ξ‖ ^ 2))
    {s : ℝ} (hs : 0 < s) (hmin : ∀ x : Λ, x ≠ 0 → s ≤ ‖(x : V d)‖ ^ 2)
    (hΦ0 : ∀ x : Λ, x ≠ 0 → Φ (‖(x : V d)‖ ^ 2) = 0)
    (hΦ1 : ∀ x : Λ, s < ‖(x : V d)‖ ^ 2 → deriv Φ (‖(x : V d)‖ ^ 2) = 0)
    (hG0 : ∀ x : Λ, x ≠ 0 → G (‖(x : V d)‖ ^ 2) = 0)
    (hG1 : ∀ x : Λ, x ≠ 0 → deriv G (‖(x : V d)‖ ^ 2) = 0) :
    G 0 = Φ 0 ∧
      s * (ZLattice.representationNumber Λ s : ℂ) * deriv Φ s = -((d : ℂ) / 2) * Φ 0 := by
  sorry

end Poisson

/-- The Poisson identity at the origin, on the kernel (Lemma 3.2 and §11.2): the Fourier profile
at the origin is the normalization. -/
theorem fourierProfile_zero_of_mem_sampleKernel (D : Case) {c : Coeff D}
    (hc : c ∈ sampleKernel D) : fourierProfile D c 0 = normalization D c := by
  sorry

/-- The Poisson identity on the first shell forces the first-shell derivative `-(d / (4 n₀ N₁))
λ(c)`, where `N₁` is the first-shell count. -/
theorem hasDerivAt_profile_firstShell_of_mem_sampleKernel (D : Case) {c : Coeff D}
    (hc : c ∈ sampleKernel D) :
    HasDerivAt (profile D c)
      (-((D.dim : ℂ) / (4 * D.firstShell * D.shellCard)) * normalization D c)
      (2 * D.firstShell) := by
  sorry

/-- The exceptional coefficient in dimension 8: `c_{0,-2} = -e^{2π} λ(c) / (30π)`. -/
theorem coeff_exceptional_e8 {c : Coeff .e8} (hc : c ∈ sampleKernel .e8) :
    coeff c 0 (-2) = -(Real.exp (2 * π) / (30 * π) : ℝ) * normalization .e8 c := by
  sorry

/-- The exceptional coefficient in dimension 24: `c_{0,-4} = -e^{4π} λ(c) / (16380π)`. -/
theorem coeff_exceptional_leech {c : Coeff .leech} (hc : c ∈ sampleKernel .leech) :
    coeff c 0 (-4) = -(Real.exp (4 * π) / (16380 * π) : ℝ) * normalization .leech c := by
  sorry

/-! ## C3: the moment operator in sample coordinates

By Lemma 4.1 and §11.3, the moment of degree `n - 1` of the contour measure `μ₀` is
`8π G_c(2n)` and that of `μ₁` is `-8 G_c'(2n)`.  The operator below is the paper's moment operator
with its rows indexed by `k = n - n₀`: in dimension 24 the two moments of degree zero are not
rows, and in dimension 8 they are.  The contour measures themselves are stated only in the
README. -/

/-- The moment operator `M_d` of §4.4 and §11.3, from `ℓ²(𝓘_d)` to `ℓ²` of the index set
`{0, 1} × ℕ` of rows: row `(ν, k)`, with `k = n - n₀`, is the paper's moment of `μ_ν` of degree
`k + n₀ - 1`, that is `k + 1` in dimension 24 and `k` in dimension 8. -/
def momentOp (D : Case) : Coeff D →L[ℂ] lp (fun _ : Fin 2 × ℕ => ℂ) 2 := by
  sorry

theorem momentOp_apply_zero (D : Case) (c : Coeff D) (k : ℕ) :
    momentOp D c (0, k) = 8 * π * fourierProfile D c (2 * (k + D.firstShell : ℕ)) := by
  sorry

theorem momentOp_apply_one (D : Case) (c : Coeff D) (k : ℕ) :
    momentOp D c (1, k) = -8 * deriv (fourierProfile D c) (2 * (k + D.firstShell : ℕ)) := by
  sorry

/-- The null space of the moment operator is the solution space of the sample equations. -/
theorem ker_momentOp (D : Case) : LinearMap.ker (momentOp D).toLinearMap = sampleKernel D := by
  sorry

/-- The geometric moment estimate of §4.4, with ratio `e^{-π}`. -/
theorem exists_norm_momentOp_apply_le (D : Case) :
    ∃ C : ℝ, ∀ (c : Coeff D) (ν : Fin 2) (k : ℕ),
      ‖momentOp D c (ν, k)‖ ≤ C * ‖c‖ * Real.exp (-π * k) := by
  sorry

/-- The moment operator is compact. -/
theorem isCompactOperator_momentOp (D : Case) : IsCompactOperator (momentOp D) := by
  sorry

/-! ## Generating series and the global analytic problem -/

/-- The generating series `A_j` of §4.1 and §11.3, as a Laurent series in `q`. -/
def genSeries {D : Case} (c : Coeff D) (j : Fin 4) (q : ℂ) : ℂ :=
  ∑' m : ℤ, coeff c j m * q ^ m

/-- The generating series converge absolutely on the punctured unit disk. -/
theorem summable_genSeries {D : Case} (c : Coeff D) (j : Fin 4) {q : ℂ} (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) : Summable fun m : ℤ => coeff c j m * q ^ m := by
  sorry

/-- The argument `q = e^π · exp (πiτ)` of the generating series (§6.1).  It is not the
cusp coordinate `𝔮 = exp (2πiτ)`: `q² = e^{2π} 𝔮`. -/
def seriesArg (τ : ℍ) : ℂ := Real.exp π * cexp (π * Complex.I * τ)

/-- The translation matrix `J_tr` of §6.1. -/
def glueTranslate : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal ![1, 1, 1, -1, 1, 1]

/-- The frame matrix `S_frm(τ)` of §6.1. -/
def frame (τ : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1, τ, τ ^ 2, 1, 0, 0;
     0, 1, 2 * τ, 0, 0, 0;
     0, τ⁻¹, 1, 2, 0, 0;
     0, 0, 1, 2, 0, 0;
     0, 0, -1 - 2 * τ, 0, -1, 0;
     0, 0, τ ^ 2, 1, 0, -1]

/-- The matrix `S_swap` interchanging the two triples. -/
def swapTriples : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.of fun i j => if (i.val + 3) % 6 = j.val then 1 else 0

/-- The inversion matrix `J_inv(τ) = S_frm(-1/τ)⁻¹ S_swap S_frm(τ)` of §6.1.  It has no
dimension parameter. -/
def glueInvert (τ : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  (frame (-τ⁻¹))⁻¹ * swapTriples * frame τ

/-! ### The constant splitting into two blocks

Used by the vanishing argument of §8 and by the family of modular forms of C5. -/

/-- The constant change of variables of §8:
`a₀⁺ = (a₀ + a₅)/2`, `a₁⁺ = (a₁ + a₂ + a₄)/2`, `a₂⁺ = a₂`,
`a₀⁻ = (a₀ - a₅)/2`, `a₁⁻ = (a₁ - a₂ - a₄)/2`, `a₂⁻ = a₃`. -/
def splitting : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1 / 2, 0, 0, 0, 0, 1 / 2;
     0, 1 / 2, 1 / 2, 0, 1 / 2, 0;
     0, 0, 1, 0, 0, 0;
     1 / 2, 0, 0, 0, 0, -1 / 2;
     0, 1 / 2, -1 / 2, 0, -1 / 2, 0;
     0, 0, 0, 1, 0, 0]

/-- The inversion matrix in split coordinates, without its scalar weight factor: the triangular
plus block and the minus block of §8. -/
def splitInvert (τ : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![τ⁻¹ ^ 2, 0, 0, 0, 0, 0;
     2 * τ⁻¹, 1, 0, 0, 0, 0;
     1, τ, τ ^ 2, 0, 0, 0;
     0, 0, 0, -1 / 2, τ⁻¹ - τ / 2, 3 / 2;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 1 / 2, τ / 2, 1 / 2]

/-- The splitting is invertible. -/
theorem isUnit_det_splitting : IsUnit splitting.det := by
  sorry

/-- The splitting block-diagonalizes the inversion matrix. -/
theorem splitting_mul_glueInvert {τ : ℂ} (hτ : τ ≠ 0) :
    splitting * glueInvert τ = splitInvert τ * splitting := by
  sorry

/-- In split coordinates only the last component, `a₂⁻ = a₃`, is antiperiodic. -/
theorem splitting_mul_glueTranslate :
    splitting * glueTranslate = Matrix.diagonal ![1, 1, 1, 1, 1, -1] * splitting := by
  sorry

/-- A global analytic solution: six holomorphic functions on the upper half-plane satisfying the
translation and inversion laws and the cusp bounds of §6.1–§6.2 and §11.4.  Every field is
an equation or an analytic condition.  The cusp field says that near the cusp each component is
`𝔮` to its exponent times a function of `𝔮` that is analytic at `𝔮 = 0`; the half-power is
`exp (πiτ)`.  No normalization is imposed. -/
structure IsGlobalSolution (D : Case) (a : Fin 6 → ℍ → ℂ) : Prop where
  holo : ∀ j, DifferentiableOn ℂ (a j ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im}
  translate : ∀ τ : ℍ, (fun j => a j ((1 : ℝ) +ᵥ τ)) = glueTranslate *ᵥ fun j => a j τ
  invert : ∀ τ : ℍ, (fun j => a j (ModularGroup.S • τ)) =
    (τ : ℂ) ^ D.weight • (glueInvert τ *ᵥ fun j => a j τ)
  cusp : ∀ j, ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
    ∀ᶠ τ : ℍ in atImInfty,
      a j τ = cexp (2 * π * Complex.I * (D.cuspExp j : ℂ) * τ) * g (cexp (2 * π * Complex.I * τ))

/-- The space `GlobalSolution d` of global analytic solutions.  It is defined without reference
to an orbifold or a sheaf. -/
def globalSolution (D : Case) : Submodule ℂ (Fin 6 → ℍ → ℂ) where
  carrier := {a | IsGlobalSolution D a}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry

theorem mem_globalSolution {D : Case} {a : Fin 6 → ℍ → ℂ} :
    a ∈ globalSolution D ↔ IsGlobalSolution D a := Iff.rfl

/-- The relation of §6.1 between a coefficient vector and the first four components of a global
analytic solution: for `Im τ > 1`, where the series converge,
`(a₀, a₁, a₂, a₃)(τ) = (A₀, -i A₁, -A₂, A₃)(q)` with `q = seriesArg τ`. -/
def IsSeriesOf {D : Case} (c : Coeff D) (a : Fin 6 → ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, 1 < τ.im →
    a 0 τ = genSeries c 0 (seriesArg τ) ∧ a 1 τ = -Complex.I * genSeries c 1 (seriesArg τ) ∧
    a 2 τ = -genSeries c 2 (seriesArg τ) ∧ a 3 τ = genSeries c 3 (seriesArg τ)

/-- The first four components determine a global analytic solution (Lemma 6.1, injectivity). -/
theorem eq_zero_of_isGlobalSolution_of_first_four {D : Case} {a : Fin 6 → ℍ → ℂ}
    (ha : IsGlobalSolution D a) (h : ∀ j : Fin 6, j.val < 4 → a j = 0) : a = 0 := by
  sorry

/-! ### C5 (analytic part): from a global analytic solution to coefficients

This is Lemma 6.1 and the reverse direction of Lemma 11.2.  A cusp bound `𝔮^κ` on `a_j`,
`j ≤ 3`, together with `q² = e^{2π} 𝔮`, gives `c_{j,m} = 0` for `m < 2κ` and for
`m ≢ 2κ (mod 2)`, so the extracted coefficients are indexed by the modes.  Applied to
`Witness.section8` and `Witness.section24` below (global analytic solutions once
`isGlobalSolution_candidate8` and `isGlobalSolution_candidate24` are proved), it gives elements of
the kernel with normalizations `180π` and `98280π`; rescaling gives normalized solutions of the
sample equations. -/

/-- Laurent extraction: a global analytic solution gives a coefficient vector in the kernel. -/
def ofGlobalSolution (D : Case) : globalSolution D →ₗ[ℂ] sampleKernel D := by
  sorry

/-- The extracted coefficients are the Laurent coefficients of the first four components. -/
theorem isSeriesOf_ofGlobalSolution (D : Case) (a : globalSolution D) :
    IsSeriesOf (ofGlobalSolution D a : Coeff D) a := by
  sorry

theorem ofGlobalSolution_injective (D : Case) : Function.Injective (ofGlobalSolution D) := by
  sorry

/-- Extracted coefficients are absolutely summable with weight `r^m` for every `1 < r < e^π`:
the generating series are holomorphic for `|q| < e^π`.  The bound is in the series argument `q`,
not in the cusp coordinate. -/
theorem summable_ofGlobalSolution_weighted (D : Case) (a : globalSolution D) {r : ℝ}
    (hr : 1 < r) (hr' : r < Real.exp π) :
    Summable fun i : Index D => ‖(ofGlobalSolution D a : Coeff D) i‖ * r ^ i.1.2 := by
  sorry

/-! ### C4: local continuation, uniformly on the kernel

The endpoint analysis continues the four generating series of every element of the kernel to a
disk of some radius `R > 1`, with bounds controlled by the coefficient norm.  Only its conclusion is
stated here.  It gives geometric decay and `ℓ¹` membership; the stronger statement for every
`r < e^π` is `summable_weighted_of_mem_sampleKernel` below, which needs the global continuation. -/

theorem exists_geometric_decay (D : Case) :
    ∃ R : ℝ, 1 < R ∧ ∃ C : ℝ, ∀ c ∈ sampleKernel D, ∀ i : Index D,
      ‖c i‖ ≤ C * ‖c‖ * R ^ (-i.1.2) := by
  sorry

/-- Every element of the kernel is absolutely summable. -/
theorem summable_norm_of_mem_sampleKernel (D : Case) {c : Coeff D} (hc : c ∈ sampleKernel D) :
    Summable fun i : Index D => ‖c i‖ := by
  sorry

/-! ### C6 (continuation): from an arbitrary element of the kernel to a global analytic solution

This is Lemma 6.3, Proposition 6.4 and the forward direction of Lemma 11.2.  The map is defined
on the whole kernel in `ℓ²`.  Uniqueness in `ℓ²` needs this: a map defined only on the solutions
constructed in C5 would give uniqueness only among those. -/

/-- Global continuation: every element of the kernel gives a global analytic solution. -/
def toGlobalSolution (D : Case) : sampleKernel D →ₗ[ℂ] globalSolution D := by
  sorry

/-- The first four components of the continuation are the generating series of the vector. -/
theorem isSeriesOf_toGlobalSolution (D : Case) (c : sampleKernel D) :
    IsSeriesOf (c : Coeff D) (toGlobalSolution D c) := by
  sorry

theorem ofGlobalSolution_toGlobalSolution (D : Case) (c : sampleKernel D) :
    ofGlobalSolution D (toGlobalSolution D c) = c := by
  sorry

theorem toGlobalSolution_ofGlobalSolution (D : Case) (a : globalSolution D) :
    toGlobalSolution D (ofGlobalSolution D a) = a := by
  sorry

/-- The analytic correspondence `ker M_d ≃ GlobalSolution d` (Proposition 6.4, Lemma 11.2). -/
def kernelEquivGlobalSolution (D : Case) : sampleKernel D ≃ₗ[ℂ] globalSolution D :=
  LinearEquiv.ofLinearMap (toGlobalSolution D) (ofGlobalSolution D)
    (LinearMap.ext (toGlobalSolution_ofGlobalSolution D))
    (LinearMap.ext (ofGlobalSolution_toGlobalSolution D))

/-- Weighted decay of every element of the kernel, for every `1 < r < e^π`. -/
theorem summable_weighted_of_mem_sampleKernel (D : Case) {c : Coeff D}
    (hc : c ∈ sampleKernel D) {r : ℝ} (hr : 1 < r) (hr' : r < Real.exp π) :
    Summable fun i : Index D => ‖c i‖ * r ^ i.1.2 := by
  sorry

/-! ## C5 (modular-forms part): a family of modular forms and the null vectors of its cusp matrices

See `MODULAR_EXISTENCE.md`.  The theta quartics `H₂ = θ₂⁴` and `H₄ = θ₄⁴` are written here
through Mathlib's two-variable Jacobi theta function, because neither pinned dependency provides
them; Sphere-Packing-Lean's `H₂`, `H₄` replace these two definitions after the Layer 0
migration. -/

namespace Witness

/-- `θ₂(τ)⁴`, with `θ₂(τ) = ∑ exp (πi (n + 1/2)² τ)`. -/
def H₂ (τ : ℍ) : ℂ := (cexp (π * Complex.I * τ / 4) * jacobiTheta₂ (τ / 2) τ) ^ 4

/-- `θ₄(τ)⁴`, with `θ₄(τ) = ∑ (-1)ⁿ exp (πi n² τ)`. -/
def H₄ (τ : ℍ) : ℂ := jacobiTheta₂ (1 / 2) τ ^ 4

/-- The theta transformation laws in the conventions of the note. -/
theorem H₂_S (τ : ℍ) : H₂ (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * H₄ τ := by
  sorry

theorem H₄_S (τ : ℍ) : H₄ (ModularGroup.S • τ) = -(τ : ℂ) ^ 2 * H₂ τ := by
  sorry

theorem H₂_T (τ : ℍ) : H₂ ((1 : ℝ) +ᵥ τ) = -H₂ τ := by
  sorry

theorem H₄_T (τ : ℍ) : H₄ ((1 : ℝ) +ᵥ τ) = H₄ τ + H₂ τ := by
  sorry

/-- Jacobi's identity and the product formula for the discriminant, in one statement. -/
theorem discriminant_eq_H (τ : ℍ) :
    ModularForm.discriminant τ = (H₂ τ * (H₂ τ + H₄ τ) * H₄ τ) ^ 2 / 256 := by
  sorry

/-- The two-dimensional representation (3) of the note. -/
def rhoS : Matrix (Fin 2) (Fin 2) ℂ := !![-1 / 2, 3 / 2; 1 / 2, 1 / 2]

def rhoT : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The vector-valued form `V₂ = (a, b)` with `a = θ₄⁴ + θ₂⁴/2`, `b = -θ₂⁴/2`. -/
def V₂ (τ : ℍ) : Fin 2 → ℂ := ![H₄ τ + H₂ τ / 2, -H₂ τ / 2]

/-- The vector-valued form `W₄ = (-a² + 3b², 2ab)`. -/
def W₄ (τ : ℍ) : Fin 2 → ℂ :=
  ![-(V₂ τ 0) ^ 2 + 3 * (V₂ τ 1) ^ 2, 2 * V₂ τ 0 * V₂ τ 1]

theorem V₂_S (τ : ℍ) : V₂ (ModularGroup.S • τ) = (τ : ℂ) ^ 2 • (rhoS *ᵥ V₂ τ) := by
  sorry

theorem V₂_T (τ : ℍ) : V₂ ((1 : ℝ) +ᵥ τ) = rhoT *ᵥ V₂ τ := by
  sorry

theorem W₄_S (τ : ℍ) : W₄ (ModularGroup.S • τ) = (τ : ℂ) ^ 4 • (rhoS *ᵥ W₄ τ) := by
  sorry

theorem W₄_T (τ : ℍ) : W₄ ((1 : ℝ) +ᵥ τ) = rhoT *ᵥ W₄ τ := by
  sorry

/-- The determinant identity `det [V₂, W₄]² = 576 Δ`: the two columns are pointwise
independent on the upper half-plane. -/
theorem det_V₂_W₄_sq (τ : ℍ) :
    (V₂ τ 0 * W₄ τ 1 - V₂ τ 1 * W₄ τ 0) ^ 2 = 576 * ModularForm.discriminant τ := by
  sorry

/-- The normalized derivative `D₀ = (2πi)⁻¹ d/dτ = 𝔮 d/d𝔮`.  The paper's block formulas use the
ordinary derivative `d/dτ = (2πi) D₀`. -/
def qDeriv (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  (2 * π * Complex.I)⁻¹ * deriv (f ∘ UpperHalfPlane.ofComplex) τ

/-- The plus block (1) of the note, built from scalar functions of weights `k`, `k + 2`,
`k + 4`.  The factors `2πi` convert the normalized derivative to the ordinary one. -/
def plusBlock (k : ℤ) (F B₀ C₀ : ℍ → ℂ) : Fin 3 → ℍ → ℂ :=
  ![F,
    fun τ => (2 * π * Complex.I) * (2 / (k : ℂ) * qDeriv F τ + B₀ τ),
    fun τ => (2 * π * Complex.I) ^ 2 *
      (qDeriv (qDeriv F) τ / ((k : ℂ) * (k + 1)) + qDeriv B₀ τ / ((k : ℂ) + 2) + C₀ τ)]

/-- The triangular inversion laws (2) of the note. -/
theorem plusBlock_S {k : ℤ} (hk0 : k ≠ 0) (hk1 : k ≠ -1) (hk2 : k ≠ -2) {F B₀ C₀ : ℍ → ℂ}
    (hF : DifferentiableOn ℂ (F ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im})
    (hB : DifferentiableOn ℂ (B₀ ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im})
    (hFS : ∀ τ : ℍ, F (ModularGroup.S • τ) = (τ : ℂ) ^ k * F τ)
    (hBS : ∀ τ : ℍ, B₀ (ModularGroup.S • τ) = (τ : ℂ) ^ (k + 2) * B₀ τ)
    (hCS : ∀ τ : ℍ, C₀ (ModularGroup.S • τ) = (τ : ℂ) ^ (k + 4) * C₀ τ) (τ : ℍ) :
    plusBlock k F B₀ C₀ 0 (ModularGroup.S • τ) = (τ : ℂ) ^ k * plusBlock k F B₀ C₀ 0 τ ∧
    plusBlock k F B₀ C₀ 1 (ModularGroup.S • τ) =
      (τ : ℂ) ^ (k + 2) * plusBlock k F B₀ C₀ 1 τ +
        2 * (τ : ℂ) ^ (k + 1) * plusBlock k F B₀ C₀ 0 τ ∧
    plusBlock k F B₀ C₀ 2 (ModularGroup.S • τ) =
      (τ : ℂ) ^ (k + 4) * plusBlock k F B₀ C₀ 2 τ +
        (τ : ℂ) ^ (k + 3) * plusBlock k F B₀ C₀ 1 τ +
        (τ : ℂ) ^ (k + 2) * plusBlock k F B₀ C₀ 0 τ := by
  sorry

/-- The six functions (4) of the note, from a plus block `p` and a minus block `(m₀, 0, m₂)`. -/
def sixFields (p : Fin 3 → ℍ → ℂ) (m₀ m₂ : ℍ → ℂ) : Fin 6 → ℍ → ℂ :=
  ![p 0 + m₀, p 1, p 2, m₂, p 1 - p 2, p 0 - m₀]

/-- The six functions built from the two blocks are the inverse splitting of a plus block `p`
and a minus block `(m₀, 0, m₂)`. -/
theorem splitting_mulVec_sixFields (p : Fin 3 → ℍ → ℂ) (m₀ m₂ : ℍ → ℂ) (τ : ℍ) :
    (splitting *ᵥ fun j => sixFields p m₀ m₂ j τ) =
      ![p 0 τ, p 1 τ, p 2 τ, m₀ τ, 0, m₂ τ] := by
  sorry

local notation "E₄" => (ModularForm.E₄ : ℍ → ℂ)
local notation "E₆" => (ModularForm.E₆ : ℍ → ℂ)
local notation "Δ" => (ModularForm.discriminant : ℍ → ℂ)

/-- The six-parameter family (8)–(9) of the note in dimension 8, in the parameter order
`(u, v, w, x, r, s)`. -/
def candidate8 (v : Fin 6 → ℂ) : Fin 6 → ℍ → ℂ :=
  sixFields
    (plusBlock (-4) (fun τ => v 0 * E₄ τ ^ 2 / Δ τ) (fun τ => v 1 * E₄ τ * E₆ τ / Δ τ)
      (fun τ => (v 2 * E₄ τ ^ 3 + v 3 * E₆ τ ^ 2) / Δ τ))
    (fun τ => (v 4 * E₄ τ ^ 2 * V₂ τ 0 + v 5 * E₆ τ * W₄ τ 0) / Δ τ)
    (fun τ => (v 4 * E₄ τ ^ 2 * V₂ τ 1 + v 5 * E₆ τ * W₄ τ 1) / Δ τ)

/-- The eight-parameter family (12)–(13) of the note in dimension 24, in the parameter order
`(u, v, w, x, y, r, s, t)`. -/
def candidate24 (v : Fin 8 → ℂ) : Fin 6 → ℍ → ℂ :=
  sixFields
    (plusBlock (-12) (fun τ => (v 0 * E₄ τ ^ 3 + v 1 * E₆ τ ^ 2) / Δ τ ^ 2)
      (fun τ => v 2 * E₄ τ ^ 2 * E₆ τ / Δ τ ^ 2)
      (fun τ => (v 3 * E₄ τ ^ 4 + v 4 * E₄ τ * E₆ τ ^ 2) / Δ τ ^ 2))
    (fun τ => (v 5 * E₄ τ ^ 3 * V₂ τ 0 + v 6 * E₆ τ ^ 2 * V₂ τ 0 +
      v 7 * E₄ τ * E₆ τ * W₄ τ 0) / Δ τ ^ 2)
    (fun τ => (v 5 * E₄ τ ^ 3 * V₂ τ 1 + v 6 * E₆ τ ^ 2 * V₂ τ 1 +
      v 7 * E₄ τ * E₆ τ * W₄ τ 1) / Δ τ ^ 2)

/-- The cusp-condition matrix `C₈` (10) of the note. -/
def cuspMatrix8 : Matrix (Fin 5) (Fin 6) ℚ :=
  !![1 / 2, 1, 0, 0, 0, 0;
     1 / 12, 1 / 2, 1, 1, 0, 0;
     0, 0, 744, -984, 0, 0;
     0, 0, 0, 0, -8, -16;
     1, 0, 0, 0, -1, 1]

/-- The cusp-condition matrix `C₂₄` (14) of the note. -/
def cuspMatrix24 : Matrix (Fin 7) (Fin 8) ℚ :=
  !![1 / 3, 1 / 3, 1, 0, 0, 0, 0, 0;
     1 / 33, 1 / 33, 1 / 5, 1, 1, 0, 0, 0;
     64 / 11, -80 / 11, 12 / 5, 1008, -720, 0, 0, 0;
     0, 0, 0, 401544, -54648, 0, 0, 0;
     0, 0, 0, 0, 0, -8, -8, -16;
     0, 0, 0, 0, 0, -6176, 7648, 3008;
     1, 1, 0, 0, 0, -1, -1, 1]

/-- The rational null vector (11) of the note. -/
def witness8 : Fin 6 → ℚ := ![-3, 3 / 2, -41 / 144, -31 / 144, -2, 1]

/-- The rational null vector (15) of the note. -/
def witness24 : Fin 8 → ℚ :=
  ![-49 / 8, 25 / 8, 1, -23 / 1760, -169 / 1760, -8 / 9, -10 / 9, 1]

/-- The two rational vectors are null vectors of the cusp matrices.  This is exact rational
arithmetic, proved here; it involves no modular forms.  The ranks and the identification of the
rows with Laurent coefficients are checked only by the script. -/
example : cuspMatrix8 *ᵥ witness8 = 0 := by
  ext i; fin_cases i <;>
    norm_num [cuspMatrix8, witness8, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

example : cuspMatrix24 *ᵥ witness24 = 0 := by
  ext i; fin_cases i <;>
    norm_num [cuspMatrix24, witness24, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Every member of the dimension-8 family is holomorphic and satisfies the translation and
inversion laws, whatever the parameters. -/
theorem candidate8_holo (v : Fin 6 → ℂ) (j : Fin 6) :
    DifferentiableOn ℂ (candidate8 v j ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
  sorry

theorem candidate8_translate (v : Fin 6 → ℂ) (τ : ℍ) :
    (fun j => candidate8 v j ((1 : ℝ) +ᵥ τ)) = glueTranslate *ᵥ fun j => candidate8 v j τ := by
  sorry

theorem candidate8_invert (v : Fin 6 → ℂ) (τ : ℍ) :
    (fun j => candidate8 v j (ModularGroup.S • τ)) =
      (τ : ℂ) ^ Case.e8.weight • (glueInvert τ *ᵥ fun j => candidate8 v j τ) := by
  sorry

/-- Every member of the dimension-24 family is holomorphic and satisfies the translation and
inversion laws, whatever the parameters. -/
theorem candidate24_holo (v : Fin 8 → ℂ) (j : Fin 6) :
    DifferentiableOn ℂ (candidate24 v j ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
  sorry

theorem candidate24_translate (v : Fin 8 → ℂ) (τ : ℍ) :
    (fun j => candidate24 v j ((1 : ℝ) +ᵥ τ)) = glueTranslate *ᵥ fun j => candidate24 v j τ := by
  sorry

theorem candidate24_invert (v : Fin 8 → ℂ) (τ : ℍ) :
    (fun j => candidate24 v j (ModularGroup.S • τ)) =
      (τ : ℂ) ^ Case.leech.weight • (glueInvert τ *ᵥ fun j => candidate24 v j τ) := by
  sorry

/-- A parameter vector annihilated by the cusp matrix gives a global analytic solution: beyond
the laws above, which hold for every parameter vector, this is the statement that the cusp
bounds of all six functions hold.

Since the script finds rank 5 (resp. 7), this target is equivalent to `candidate8 witness8`
(resp. `candidate24 witness24`) being a global analytic solution; its truth depends on the matrix
only through its null space, not on the rows being the correct Laurent coefficients.  That
identification, required by §8 of the note and checked by the script, has no Lean statement
yet; it is to be stated with TauCeti's Laurent expansions in `𝔮`. -/
theorem isGlobalSolution_candidate8 (v : Fin 6 → ℂ)
    (hv : (cuspMatrix8.map (algebraMap ℚ ℂ)) *ᵥ v = 0) :
    IsGlobalSolution .e8 (candidate8 v) := by
  sorry

theorem isGlobalSolution_candidate24 (v : Fin 8 → ℂ)
    (hv : (cuspMatrix24.map (algebraMap ℚ ℂ)) *ᵥ v = 0) :
    IsGlobalSolution .leech (candidate24 v) := by
  sorry

/-- The parametrizations are injective (§6 of the note).  This is a consistency check; the
existence proof through the explicit null vectors does not use it. -/
theorem candidate8_injective : Function.Injective candidate8 := by
  sorry

theorem candidate24_injective : Function.Injective candidate24 := by
  sorry

/-- The global analytic solution in dimension 8 given by the null vector `witness8`.  That it is
one is `isGlobalSolution_candidate8`, which is not yet proved.  The name is historical: this is a
global analytic solution, not a section of a bundle. -/
def section8 : globalSolution .e8 :=
  ⟨candidate8 fun i => (witness8 i : ℂ), by sorry⟩

/-- The global analytic solution in dimension 24 given by the null vector `witness24`.  That it is
one is `isGlobalSolution_candidate24`, which is not yet proved.  The name is historical, as for
`section8`. -/
def section24 : globalSolution .leech :=
  ⟨candidate24 fun i => (witness24 i : ℂ), by sorry⟩

/-- The normalization (16) of the coefficient vector of `section8`: `λ = 180π`. -/
theorem normalization_section8 :
    normalization .e8 (ofGlobalSolution .e8 section8 : Coeff .e8) = 180 * π := by
  sorry

/-- The normalization (16) of the coefficient vector of `section24`: `λ = 98280π`. -/
theorem normalization_section24 :
    normalization .leech (ofGlobalSolution .leech section24 : Coeff .leech) = 98280 * π := by
  sorry

end Witness

/-- Existence (C5): a normalized element of the kernel, constructed from `Witness.section8`
and `Witness.section24`, using neither of the known magic functions, nor interpolation, nor
Riemann–Roch. -/
theorem exists_mem_sampleKernel_normalized (D : Case) :
    ∃ c ∈ sampleKernel D, normalization D c = 1 := by
  sorry

/-! ## C6: vanishing and the coefficient theorem -/

/-- Vanishing at zero normalization (Proposition 8.1, Lemma 11.4), for the entire kernel. -/
theorem eq_zero_of_mem_sampleKernel_of_normalization_eq_zero (D : Case) {c : Coeff D}
    (hc : c ∈ sampleKernel D) (h : normalization D c = 0) : c = 0 := by
  sorry

/-- The homogeneous sample equations have a one-dimensional solution space in `ℓ²(𝓘_d)`. -/
theorem finrank_sampleKernel (D : Case) : Module.finrank ℂ (sampleKernel D) = 1 := by
  sorry

/-- Theorems 2.1 and 11.1: the normalized system has exactly one solution in `ℓ²(𝓘_d)`. -/
theorem existsUnique_normalized (D : Case) :
    ∃! c : Coeff D, c ∈ sampleKernel D ∧ normalization D c = 1 := by
  sorry

/-- The normalized coefficient solution `c_*`. -/
def solution (D : Case) : Coeff D := by
  sorry

theorem solution_mem (D : Case) : solution D ∈ sampleKernel D := by
  sorry

@[simp]
theorem normalization_solution (D : Case) : normalization D (solution D) = 1 := by
  sorry

/-- The entries of the normalized solution are real. -/
theorem solution_im (D : Case) (i : Index D) : (solution D i).im = 0 := by
  sorry

/-- The constructed function `f_{c_*}`. -/
def magic (D : Case) : RadialSchwartzMap ℂ (V D.dim) ℂ := synth D (solution D)

theorem magic_apply (D : Case) (x : V D.dim) :
    magic D x = profile D (solution D) (‖x‖ ^ 2) :=
  synth_apply D _ x

/-- Both normalizations: `f(0) = f̂(0) = 1`. -/
theorem magic_zero (D : Case) : magic D 0 = 1 := by
  sorry

theorem fourier_magic_zero (D : Case) : 𝓕 (magic D : 𝓢(V D.dim, ℂ)) 0 = 1 := by
  sorry

/-- The forced first-shell derivative, in squared radius: `-1/120` and `-1/65520`. -/
theorem hasDerivAt_profile_solution_e8 :
    HasDerivAt (profile .e8 (solution .e8)) (-1 / 120) 2 := by
  sorry

theorem hasDerivAt_profile_solution_leech :
    HasDerivAt (profile .leech (solution .leech)) (-1 / 65520) 4 := by
  sorry

/-! ## C8: the abstract positive equation

The argument of Theorem 9.1, for bounded operators `K` (compact), `A` and `λ`, to be applied
with `A = M_d`.  The operator `K` of Appendix B is stated only in the README; these theorems are
to be applied to it.  Convergence
of the Galerkin approximations then follows from TauCeti's results on finite sections. -/

namespace Regularized

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The positive operator `N = (I - K)* (I - K) + A* A + λ* λ` of §9. -/
def positiveOp (K : E →L[ℂ] E) (A : E →L[ℂ] F) (lam : E →L[ℂ] ℂ) : E →L[ℂ] E :=
  ContinuousLinearMap.adjoint (1 - K) ∘L (1 - K) + ContinuousLinearMap.adjoint A ∘L A +
    ContinuousLinearMap.adjoint lam ∘L lam

/-- The quadratic form of the positive operator (§9). -/
theorem inner_positiveOp_self (K : E →L[ℂ] E) (A : E →L[ℂ] F) (lam : E →L[ℂ] ℂ) (c : E) :
    ⟪positiveOp K A lam c, c⟫_ℂ = ((‖c - K c‖ ^ 2 + ‖A c‖ ^ 2 + ‖lam c‖ ^ 2 : ℝ) : ℂ) := by
  sorry

/-- Coercivity: compactness of `K` and vanishing at zero normalization give a positive lower
bound.  The constant is existential; it justifies no numerical computation. -/
theorem exists_coercive {K : E →L[ℂ] E} (hK : IsCompactOperator K) (A : E →L[ℂ] F)
    (lam : E →L[ℂ] ℂ) (hvan : ∀ c, A c = 0 → lam c = 0 → c = 0) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ c : E, κ * ‖c‖ ^ 2 ≤ ‖c - K c‖ ^ 2 + ‖A c‖ ^ 2 + ‖lam c‖ ^ 2 := by
  sorry

/-- The positive operator is boundedly invertible. -/
theorem isUnit_positiveOp {K : E →L[ℂ] E} (hK : IsCompactOperator K) (A : E →L[ℂ] F)
    (lam : E →L[ℂ] ℂ) (hvan : ∀ c, A c = 0 → lam c = 0 → c = 0) :
    IsUnit (positiveOp K A lam) := by
  sorry

/-- The solution of the positive equation is the normalized element of the null space of `A`.
Invertibility alone does not give this: the proof uses a vector `b` with `A b = 0` and
`λ b = 1`, the property `K c = c` on the null space of `A`, and vanishing at zero
normalization. -/
theorem eq_of_positiveOp_apply_eq {K : E →L[ℂ] E} {A : E →L[ℂ] F} {lam : E →L[ℂ] ℂ}
    (hfix : ∀ c, A c = 0 → K c = c) (hvan : ∀ c, A c = 0 → lam c = 0 → c = 0)
    {b : E} (hb : A b = 0) (hb1 : lam b = 1) {c : E}
    (hc : positiveOp K A lam c = ContinuousLinearMap.adjoint lam 1) : c = b := by
  sorry

end Regularized

end

end SphereCeti.CoefficientMagic
