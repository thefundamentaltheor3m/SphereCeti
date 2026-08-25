/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib
public import TauCeti.LinearAlgebra.IntegralLattice.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular

/-!
# Pinned compatibility model for Sphere-Packing-Lean `main`

This file is a roadmap-local model of the public definitions at
`thefundamentaltheor3m/Sphere-Packing-Lean@bad3de916074748eb88b7d1ee6dbf9494361ad17`.
It exists only because that production snapshot uses Lean/Mathlib `v4.32.0`, while SphereCeti
starts at Lean `v4.34.0-rc1` and imports a recent TauCeti snapshot.

The structures and density definitions below pin the semantic starting point.  They are not a
fork of the production library.  The first migration layer upgrades Sphere-Packing-Lean and then
replaces every use of this namespace by direct imports of the production declarations.  No theorem
may depend on a definitional accident of this compatibility model.
-/

public section

open BigOperators MeasureTheory Metric
open scoped ENNReal FourierTransform Pointwise SchwartzMap
open Set Filter Module

namespace SphereCeti.Pinned

noncomputable section

/-- The ambient Euclidean space in dimension `d`. -/
abbrev V (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-! ## Packing definitions pinned from production `main` -/

/-- A set of centers with an explicit positive separation.  This matches the production structure
field-for-field. -/
structure SpherePacking (d : ℕ) where
  centers : Set (V d)
  separation : ℝ
  separation_pos : 0 < separation := by positivity
  centers_dist : Pairwise (separation ≤ dist · · : centers → centers → Prop)

/-- A sphere packing invariant under translation by a full Euclidean lattice.  This matches the
production extension fields. -/
structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  lattice : Submodule ℤ (V d)
  lattice_action : ∀ ⦃x y⦄, x ∈ lattice → y ∈ centers → x + y ∈ centers
  lattice_discrete : DiscreteTopology lattice := by infer_instance
  lattice_isZLattice : IsZLattice ℝ lattice := by infer_instance

variable {d : ℕ}

/-- Directional form of the separation field. -/
@[grind]
theorem SpherePacking.centers_dist' (P : SpherePacking d) (x y : V d)
    (hx : x ∈ P.centers) (hy : y ∈ P.centers) (hxy : x ≠ y) :
    P.separation ≤ dist x y := by
  have hsub : (⟨x, hx⟩ : P.centers) ≠ ⟨y, hy⟩ := Subtype.coe_ne_coe.mp hxy
  have h := P.centers_dist hsub
  simpa only [Subtype.dist_eq] using h

instance PeriodicSpherePacking.instLatticeDiscrete (P : PeriodicSpherePacking d) :
    DiscreteTopology P.lattice := P.lattice_discrete

instance PeriodicSpherePacking.instIsZLattice (P : PeriodicSpherePacking d) :
    IsZLattice ℝ P.lattice := P.lattice_isZLattice

/-- The open balls of radius half the separation around all centers. -/
abbrev SpherePacking.balls (P : SpherePacking d) : Set (V d) :=
  ⋃ x : P.centers, ball (x : V d) (P.separation / 2)

/-- Density observed inside the ball of radius `R`. -/
noncomputable def SpherePacking.finiteDensity (P : SpherePacking d) (R : ℝ) : ℝ≥0∞ :=
  volume (P.balls ∩ ball 0 R) / volume (ball (0 : V d) R)

/-- Upper asymptotic density, pinned as a limsup of finite densities. -/
noncomputable def SpherePacking.density (P : SpherePacking d) : ℝ≥0∞ :=
  limsup P.finiteDensity atTop

/-- Supremal density over periodic sphere packings. -/
noncomputable def PeriodicSpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ P : PeriodicSpherePacking d, P.density

/-- Supremal density over all sphere packings. -/
noncomputable def SpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ P : SpherePacking d, P.density

/-- Positive scaling of a sphere packing.  The target API preserves the production semantics. -/
noncomputable def SpherePacking.scale (P : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    SpherePacking d := by
  sorry

/-- Positive scaling of a periodic sphere packing. -/
noncomputable def PeriodicSpherePacking.scale (P : PeriodicSpherePacking d) {c : ℝ} (hc : 0 < c) :
    PeriodicSpherePacking d := by
  sorry

@[simp]
theorem SpherePacking.scale_centers (P : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (P.scale hc).centers = c • P.centers := by
  sorry

@[simp]
theorem SpherePacking.scale_separation (P : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (P.scale hc).separation = c * P.separation := by
  sorry

@[simp]
theorem PeriodicSpherePacking.scale_toSpherePacking (P : PeriodicSpherePacking d)
    {c : ℝ} (hc : 0 < c) :
    (P.scale hc).toSpherePacking = P.toSpherePacking.scale hc := by
  sorry

@[simp]
theorem SpherePacking.scale_density (P : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (P.scale hc).density = P.density := by
  sorry

@[simp]
theorem PeriodicSpherePacking.scale_density (P : PeriodicSpherePacking d)
    {c : ℝ} (hc : 0 < c) :
    (P.scale hc).density = P.density := by
  sorry

/-! ## Radial Schwartz functions pinned from production `main` -/

namespace Function

/-- A function is radial when it is constant on norm fibers. -/
def IsRadial {E F : Type*} [Norm E] (f : E → F) : Prop :=
  ∀ ⦃x y : E⦄, ‖x‖ = ‖y‖ → f x = f y

@[simp]
theorem isRadial_iff {E F : Type*} [Norm E] (f : E → F) :
    IsRadial f ↔ ∀ ⦃x y : E⦄, ‖x‖ = ‖y‖ → f x = f y := Iff.rfl

end Function

/-- The submodule of radial Schwartz functions, matching the production API shape. -/
def RadialSchwartzMap (𝕜 E F : Type*) [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F] : Submodule 𝕜 𝓢(E, F) where
  carrier := {f | Function.IsRadial f}
  zero_mem' := by simp [Function.IsRadial]
  add_mem' := by
    intro f g hf hg x y hxy
    simp only [add_apply]
    rw [hf hxy, hg hxy]
  smul_mem' := by
    intro c f hf x y hxy
    simp only [smul_apply]
    rw [hf hxy]

namespace RadialSchwartzMap

section

variable {𝕜 E F : Type*} [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F]

instance instFunLike : FunLike (RadialSchwartzMap 𝕜 E F) E F where
  coe f := f.1
  coe_injective := DFunLike.coe_injective.comp Subtype.val_injective

@[simp, norm_cast]
theorem coe_coe (f : RadialSchwartzMap 𝕜 E F) : ⇑(f : 𝓢(E, F)) = f := rfl

end

/-- The production theorem that Fourier is an involution on radial Schwartz maps.  The real scalar
structures on `E` and `F` are the ones derived from the inner product and complex structures, so
that the Schwartz-space Fourier transform instance applies. -/
theorem fourier_apply_apply {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F]
    [SMulCommClass ℂ 𝕜 F] [SMulCommClass ℝ 𝕜 F] [CompleteSpace F]
    (f : RadialSchwartzMap 𝕜 E F) :
    𝓕 (𝓕 (f : 𝓢(E, F))) = (f : 𝓢(E, F)) := by
  sorry

end RadialSchwartzMap

/-! ## Dimension-eight declarations pinned from production `main` -/

/-- Roadmap-local stand-in for the production `E8Lattice`. -/
noncomputable def E8Lattice : Submodule ℤ (V 8) := by
  sorry

noncomputable instance E8Lattice.discreteTopology : DiscreteTopology E8Lattice := by
  sorry

noncomputable instance E8Lattice.isZLattice : IsZLattice ℝ E8Lattice := by
  sorry

/-- Roadmap-local stand-in for the production `E8Packing`. -/
noncomputable def E8Packing : PeriodicSpherePacking 8 := by
  sorry

/-- The pinned density normalization of the production E8 packing. -/
theorem E8Packing_density :
    E8Packing.density = ENNReal.ofReal (Real.pi ^ 4 / 384) := by
  sorry

end

end SphereCeti.Pinned
