/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Pinned

public import TauCeti.Analysis.Complex.UpperHalfPlane.ResToImagAxis
public import TauCeti.Analysis.Fourier.Continuous
public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
public import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular
public import TauCeti.NumberTheory.ModularForms.QExpansion.BigO
public import TauCeti.NumberTheory.ModularForms.ResToImagAxis
public import TauCeti.NumberTheory.ModularForms.STransform
public import TauCeti.NumberTheory.ModularForms.SturmBound

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Suggested SphereCeti target signatures

The accompanying `README.md` is the definitive roadmap.  This file gives suggested Lean shapes for
important objects and endpoints; it is deliberately nonexhaustive, and declaration names or binder
order may change when implementation reveals a better Mathlib-shaped API.  It contains `sorry`
because it specifies work to be done.

Unlike an ordinary TauCetiRoadmap target file, this package directly imports the exact TauCeti
snapshot named in `lakefile.toml`.  The bootstrap `SphereCeti.Pinned` namespace models the public
Sphere-Packing-Lean definitions at the pinned production snapshot.  PR A2 deletes that namespace
after PR A1 establishes exact production imports on this toolchain.
-/

public section

open BigOperators MeasureTheory Metric Set Filter Module
open Complex UpperHalfPlane MatrixGroups
open scoped ENNReal FourierTransform Real Topology ModularForm CongruenceSubgroup
open scoped Pointwise SchwartzMap InnerProductSpace Manifold

namespace SphereCeti.Suggested

noncomputable section

universe u

abbrev V (d : ℕ) := SphereCeti.Pinned.V d
abbrev SpherePacking (d : ℕ) := SphereCeti.Pinned.SpherePacking d
abbrev PeriodicSpherePacking (d : ℕ) := SphereCeti.Pinned.PeriodicSpherePacking d
abbrev SpherePackingConstant := SphereCeti.Pinned.SpherePackingConstant
abbrev PeriodicSpherePackingConstant := SphereCeti.Pinned.PeriodicSpherePackingConstant
abbrev RadialSchwartzMap := SphereCeti.Pinned.RadialSchwartzMap

/-! ## Layer 0: exact dependency and declaration contracts -/

#check TauCeti.IntegralLattice
#check TauCeti.IntegralLattice.IsEven
#check TauCeti.IntegralLattice.IsUnimodular
#check TauCeti.IntegralLattice.Isometry
#check TauCeti.IntegralLattice.ofGramMatrix
#check UpperHalfPlane.resToImagAxis
#check UpperHalfPlane.resToImagAxis_slash_S
#check TauCeti.UpperHalfPlane.cuspFunction_isBigO_pow_of_qExpansion_coeff_eq_zero
#check TauCeti.ModularForm.sturm_bound_finiteIndex
#check TauCeti.continuous_fourier_of_integrable

#check SphereCeti.Pinned.SpherePacking
#check SphereCeti.Pinned.PeriodicSpherePacking
#check SphereCeti.Pinned.PeriodicSpherePacking.addAction
#check SphereCeti.Pinned.SpherePacking.balls
#check SphereCeti.Pinned.SpherePacking.finiteDensity
#check SphereCeti.Pinned.SpherePacking.density
#check SphereCeti.Pinned.SpherePackingConstant
#check SphereCeti.Pinned.PeriodicSpherePackingConstant
#check SphereCeti.Pinned.RadialSchwartzMap
#check SphereCeti.Pinned.E8Lattice
#check SphereCeti.Pinned.E8Packing
#check SphereCeti.Pinned.E8Packing_density

/-! ## Layer 1: packing semantics, scaling, and congruence -/

namespace SpherePacking

@[grind]
theorem separation_le_dist {d : ℕ} (P : SpherePacking d) {x y : V d}
    (hx : x ∈ P.centers) (hy : y ∈ P.centers) (hxy : x ≠ y) :
    P.separation ≤ dist x y := by
  exact P.centers_dist' x y hx hy hxy

/-- Every packing density lies below the global packing constant. -/
theorem density_le_constant {d : ℕ} (P : SpherePacking d) :
    P.density ≤ SpherePackingConstant d := by
  sorry

/-- Density observed in a ball centered at an arbitrary basepoint. -/
noncomputable def finiteDensityAt {d : ℕ} (P : SpherePacking d) (a : V d) (R : ℝ) : ℝ≥0∞ :=
  volume (P.balls ∩ ball a R) / volume (ball a R)

/-- Upper asymptotic density computed from balls centered at `a`. -/
noncomputable def densityAt {d : ℕ} (P : SpherePacking d) (a : V d) : ℝ≥0∞ :=
  limsup (P.finiteDensityAt a) atTop

/-- Changing the fixed basepoint does not change upper asymptotic density. -/
theorem densityAt_eq_density {d : ℕ} (P : SpherePacking d) (a : V d) :
    P.densityAt a = P.density := by
  sorry

/-- Transport a packing by a real affine isometry. -/
noncomputable def map {d : ℕ} (e : V d ≃ᵃⁱ[ℝ] V d) (P : SpherePacking d) :
    SpherePacking d := by
  sorry

@[simp]
theorem map_centers {d : ℕ} (e : V d ≃ᵃⁱ[ℝ] V d) (P : SpherePacking d) :
    (P.map e).centers = e '' P.centers := by
  sorry

@[simp]
theorem map_separation {d : ℕ} (e : V d ≃ᵃⁱ[ℝ] V d) (P : SpherePacking d) :
    (P.map e).separation = P.separation := by
  sorry

/-- Affine isometries preserve density; translations use `densityAt_eq_density`. -/
@[simp]
theorem map_density {d : ℕ} (e : V d ≃ᵃⁱ[ℝ] V d) (P : SpherePacking d) :
    (P.map e).density = P.density := by
  sorry

/-- Congruence is equality after transport by a real affine isometry. -/
def IsCongruent {d : ℕ} (P Q : SpherePacking d) : Prop :=
  ∃ e : V d ≃ᵃⁱ[ℝ] V d, P.map e = Q

/-- Similarity permits one positive scaling before congruence.  This is the scale-free uniqueness
notion appropriate to `SpherePackingConstant`. -/
def IsSimilar {d : ℕ} (P Q : SpherePacking d) : Prop :=
  ∃ (c : ℝ) (hc : 0 < c), IsCongruent (P.scale hc) Q

@[refl]
theorem isCongruent_refl {d : ℕ} (P : SpherePacking d) : P.IsCongruent P := by
  sorry

@[symm]
theorem IsCongruent.symm {d : ℕ} {P Q : SpherePacking d} (h : P.IsCongruent Q) :
    Q.IsCongruent P := by
  sorry

@[trans]
theorem IsCongruent.trans {d : ℕ} {P Q R : SpherePacking d}
    (hPQ : P.IsCongruent Q) (hQR : Q.IsCongruent R) : P.IsCongruent R := by
  sorry

@[refl]
theorem isSimilar_refl {d : ℕ} (P : SpherePacking d) : P.IsSimilar P := by
  sorry

@[symm]
theorem IsSimilar.symm {d : ℕ} {P Q : SpherePacking d} (h : P.IsSimilar Q) :
    Q.IsSimilar P := by
  sorry

@[trans]
theorem IsSimilar.trans {d : ℕ} {P Q R : SpherePacking d}
    (hPQ : P.IsSimilar Q) (hQR : Q.IsSimilar R) : P.IsSimilar R := by
  sorry

@[simp]
theorem congruent_density {d : ℕ} {P Q : SpherePacking d} (h : P.IsCongruent Q) :
    P.density = Q.density := by
  sorry

@[simp]
theorem similar_density {d : ℕ} {P Q : SpherePacking d} (h : P.IsSimilar Q) :
    P.density = Q.density := by
  sorry

/-- Positive density supplies a center for the rigidity argument. -/
theorem density_pos_imp_centers_nonempty {d : ℕ} {P : SpherePacking d}
    (h : 0 < P.density) : P.centers.Nonempty := by
  sorry

end SpherePacking

namespace PeriodicSpherePacking

/-- Periodic density lies below the periodic packing constant. -/
theorem density_le_constant {d : ℕ} (P : PeriodicSpherePacking d) :
    P.density ≤ PeriodicSpherePackingConstant d := by
  sorry

/-- Forgetting periodicity proves the easy inequality between the two constants. -/
theorem constant_le_general (d : ℕ) :
    PeriodicSpherePackingConstant d ≤ SpherePackingConstant d := by
  sorry

/-- Positive scaling preserves the density of a periodic sphere packing. -/
@[simp]
theorem scale_density {d : ℕ} (P : PeriodicSpherePacking d) {c : ℝ} (hc : 0 < c) :
    (P.scale hc).density = P.density := by
  sorry

end PeriodicSpherePacking

/-! ## Layer 2: real Euclidean lattices and TauCeti integral presentations -/

namespace EuclideanLattice

/-- The Euclidean dual lattice for the Mathlib Fourier convention. -/
@[expose] def dual {d : ℕ} (Λ : Submodule ℤ (V d)) : Submodule ℤ (V d) :=
  LinearMap.BilinForm.dualSubmodule (innerₗ (V d)) Λ

/-- The finite shell at a prescribed squared norm.  Discreteness is required at construction time,
so cardinalities cannot silently use `Set.ncard`'s infinite-set fallback. -/
noncomputable def normSqShell {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] (a : ℝ) : Finset Λ := by
  sorry

@[simp]
theorem mem_normSqShell {d : ℕ} {Λ : Submodule ℤ (V d)} [DiscreteTopology Λ]
    {a : ℝ} {x : Λ} :
    x ∈ normSqShell Λ a ↔ ‖(x : V d)‖ ^ 2 = a := by
  sorry

/-- Coefficient indexed by a literal integer squared norm. -/
def thetaNormCoeff {d : ℕ} (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] (n : ℕ) : ℕ :=
  (normSqShell Λ n).card

/-- Coefficient indexed by half the squared norm; for an even lattice, coefficient `n` counts
vectors of squared norm `2n`. -/
def thetaEvenCoeff {d : ℕ} (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] (n : ℕ) : ℕ :=
  (normSqShell Λ (2 * n)).card

/-- A lower bound on every nonzero squared norm. -/
def MinNormSqAtLeast {d : ℕ} (Λ : Submodule ℤ (V d)) (a : ℝ) : Prop :=
  ∀ x : Λ, x ≠ 0 → a ≤ ‖(x : V d)‖ ^ 2

/-- The lower bound is attained. -/
def HasMinNormSq {d : ℕ} (Λ : Submodule ℤ (V d)) (a : ℝ) : Prop :=
  MinNormSqAtLeast Λ a ∧ ∃ x : Λ, x ≠ 0 ∧ ‖(x : V d)‖ ^ 2 = a

@[grind]
theorem normSq_lower_bound {d : ℕ} {Λ : Submodule ℤ (V d)} {a : ℝ}
    (h : MinNormSqAtLeast Λ a) (x : Λ) (hx : x ≠ 0) :
    a ≤ ‖(x : V d)‖ ^ 2 := h x hx

/-- The integer span of a Euclidean point set. -/
def generatedSubmodule {d : ℕ} (S : Set (V d)) : Submodule ℤ (V d) :=
  Submodule.span ℤ S

/-- A concrete integral Gram presentation of a real Euclidean lattice.  TauCeti owns the algebraic
integral-lattice object; SphereCeti records the comparison with the existing real `ZLattice`. -/
structure IntegralPresentation {d : ℕ} (Λ : Submodule ℤ (V d)) where
  basis : Basis (Fin d) ℤ Λ
  gram : Matrix (Fin d) (Fin d) ℤ
  gram_isSymm : gram.IsSymm
  gram_spec : ∀ i j,
    ((gram i j : ℤ) : ℝ) = ⟪((basis i : Λ) : V d), ((basis j : Λ) : V d)⟫_ℝ

/-- Constructor that derives Gram symmetry from the real inner-product specification. -/
noncomputable def IntegralPresentation.ofBasis {d : ℕ} {Λ : Submodule ℤ (V d)}
    (basis : Basis (Fin d) ℤ Λ) (gram : Matrix (Fin d) (Fin d) ℤ)
    (gram_spec : ∀ i j,
      ((gram i j : ℤ) : ℝ) = ⟪((basis i : Λ) : V d), ((basis j : Λ) : V d)⟫_ℝ) :
    IntegralPresentation Λ := by
  sorry

@[simp]
theorem IntegralPresentation.ofBasis_basis {d : ℕ} {Λ : Submodule ℤ (V d)}
    (basis : Basis (Fin d) ℤ Λ) (gram : Matrix (Fin d) (Fin d) ℤ)
    (gram_spec : ∀ i j,
      ((gram i j : ℤ) : ℝ) = ⟪((basis i : Λ) : V d), ((basis j : Λ) : V d)⟫_ℝ) :
    (IntegralPresentation.ofBasis basis gram gram_spec).basis = basis := by
  sorry

@[simp]
theorem IntegralPresentation.ofBasis_gram {d : ℕ} {Λ : Submodule ℤ (V d)}
    (basis : Basis (Fin d) ℤ Λ) (gram : Matrix (Fin d) (Fin d) ℤ)
    (gram_spec : ∀ i j,
      ((gram i j : ℤ) : ℝ) = ⟪((basis i : Λ) : V d), ((basis j : Λ) : V d)⟫_ℝ) :
    (IntegralPresentation.ofBasis basis gram gram_spec).gram = gram := by
  sorry

/-- The TauCeti rational integral lattice associated to an integral presentation. -/
noncomputable def IntegralPresentation.toIntegralLattice {d : ℕ}
    {Λ : Submodule ℤ (V d)} (P : IntegralPresentation Λ) :
    TauCeti.IntegralLattice (Fin d → ℚ) :=
  TauCeti.IntegralLattice.ofGramMatrix (Pi.basisFun ℚ (Fin d)) P.gram P.gram_isSymm

abbrev IntegralPresentation.IsEven {d : ℕ} {Λ : Submodule ℤ (V d)}
    (P : IntegralPresentation Λ) : Prop := P.toIntegralLattice.IsEven

abbrev IntegralPresentation.IsUnimodular {d : ℕ} {Λ : Submodule ℤ (V d)}
    (P : IntegralPresentation Λ) : Prop := P.toIntegralLattice.IsUnimodular

abbrev IntegralPresentation.IsPosDef {d : ℕ} {Λ : Submodule ℤ (V d)}
    (P : IntegralPresentation Λ) : Prop := P.toIntegralLattice.IsPosDef

/-- A presentation of a full Euclidean lattice is automatically positive definite. -/
theorem IntegralPresentation.isPosDef {d : ℕ} {Λ : Submodule ℤ (V d)}
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (P : IntegralPresentation Λ) :
    P.IsPosDef := by
  sorry

/-- Cohn--Elkies Lemma 8.2 in generic API form.  A full-dimensional set containing zero whose
pairwise squared distances are even integers generates a discrete full-rank even integral lattice.
The conclusion is expressed through the real/TauCeti presentation bridge used throughout this
roadmap. -/
theorem generatedSubmodule_evenIntegral_full {d : ℕ}
    (S : Set (V d)) (hzero : 0 ∈ S)
    (hspan : Submodule.span ℝ S = ⊤)
    (heven : ∀ x ∈ S, ∀ y ∈ S, ∃ n : ℤ, ‖x - y‖ ^ 2 = 2 * n) :
    ∃ (_ : DiscreteTopology (generatedSubmodule S))
      (_ : IsZLattice ℝ (generatedSubmodule S))
      (G : IntegralPresentation (generatedSubmodule S)),
      G.IsEven := by
  sorry

/-- The real carrier and TauCeti's Gram-coordinate carrier are integrally equivalent. -/
noncomputable def IntegralPresentation.carrierEquiv {d : ℕ}
    {Λ : Submodule ℤ (V d)} (P : IntegralPresentation Λ) :
    Λ ≃ₗ[ℤ] P.toIntegralLattice.carrier := by
  sorry

/-- The real dual and TauCeti's rational dual carrier have the same integral coordinates. -/
noncomputable def IntegralPresentation.dualCarrierEquiv {d : ℕ}
    {Λ : Submodule ℤ (V d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : IntegralPresentation Λ) :
    EuclideanLattice.dual Λ ≃ₗ[ℤ] P.toIntegralLattice.dualCarrier := by
  sorry

/-- Explicit membership comparison through the rational dual-carrier coordinates. -/
theorem IntegralPresentation.mem_dual_iff_exists_dualCarrier_coordinates {d : ℕ}
    {Λ : Submodule ℤ (V d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : IntegralPresentation Λ) (x : V d) :
    x ∈ EuclideanLattice.dual Λ ↔
      ∃ q : P.toIntegralLattice.dualCarrier,
        x = ∑ i : Fin d, ((q : Fin d → ℚ) i : ℝ) • ((P.basis i : Λ) : V d) := by
  sorry

/-- The determinant/covolume bridge used to move between TauCeti's Gram discriminant and Mathlib's
real Haar covolume. -/
theorem IntegralPresentation.covolume_sq_eq_discriminant {d : ℕ}
    {Λ : Submodule ℤ (V d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : IntegralPresentation Λ) :
    ZLattice.covolume Λ ^ 2 = P.toIntegralLattice.discriminant := by
  sorry

/-- Unimodularity agrees exactly with real covolume one. -/
theorem IntegralPresentation.isUnimodular_iff_covolume_eq_one {d : ℕ}
    {Λ : Submodule ℤ (V d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : IntegralPresentation Λ) :
    P.IsUnimodular ↔ ZLattice.covolume Λ = 1 := by
  sorry

/-- A unimodular presentation identifies the real dual lattice with the original carrier. -/
theorem IntegralPresentation.dual_eq_self_of_isUnimodular {d : ℕ}
    {Λ : Submodule ℤ (V d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : IntegralPresentation Λ) (h : P.IsUnimodular) :
    EuclideanLattice.dual Λ = Λ := by
  sorry

/-- Rootlessness in the even-lattice normalization means absence of squared norm `2`. -/
def IsRootless {W : Type*} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) : Prop := L.vectorsOfNorm 2 = ∅

/-- Presentation coordinates preserve each exact squared-norm shell. -/
noncomputable def IntegralPresentation.normSqShellEquiv {d : ℕ}
    {Λ : Submodule ℤ (V d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : IntegralPresentation Λ) (n : ℕ) :
    ↑(normSqShell Λ n) ≃ ↑(P.toIntegralLattice.vectorsOfNorm n) := by
  sorry

/-- The algebraic root condition is exactly emptiness of the real norm-two shell. -/
theorem IntegralPresentation.isRootless_iff_normSqShell_two_empty {d : ℕ}
    {Λ : Submodule ℤ (V d)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : IntegralPresentation Λ) :
    IsRootless P.toIntegralLattice ↔ normSqShell Λ 2 = ∅ := by
  sorry

/-- Extend an algebraic classification isometry to the ambient real Euclidean space. -/
noncomputable def IntegralPresentation.realIsometryOfIsometry {d : ℕ}
    {Λ Μ : Submodule ℤ (V d)} (P : IntegralPresentation Λ)
    (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice) :
    V d ≃ₗᵢ[ℝ] V d := by
  sorry

@[simp]
theorem IntegralPresentation.realIsometry_maps_carrier {d : ℕ}
    {Λ Μ : Submodule ℤ (V d)} (P : IntegralPresentation Λ)
    (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice) :
    realIsometryOfIsometry P Q e '' (Λ : Set (V d)) = (Μ : Set (V d)) := by
  sorry

/-- Add translations to the real linear extension supplied by a classification isometry. -/
noncomputable def IntegralPresentation.affineIsometryOfIsometry {d : ℕ}
    {Λ Μ : Submodule ℤ (V d)} (P : IntegralPresentation Λ)
    (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice)
    (v w : V d) : V d ≃ᵃⁱ[ℝ] V d := by
  sorry

@[simp]
theorem IntegralPresentation.affineIsometry_maps_coset {d : ℕ}
    {Λ Μ : Submodule ℤ (V d)} (P : IntegralPresentation Λ)
    (Q : IntegralPresentation Μ)
    (e : TauCeti.IntegralLattice.Isometry P.toIntegralLattice Q.toIntegralLattice)
    (v w : V d) :
    affineIsometryOfIsometry P Q e v w '' (v +ᵥ (Λ : Set (V d))) =
      w +ᵥ (Μ : Set (V d)) := by
  sorry

end EuclideanLattice

/-! ## Layer 3: canonical lattice packings and finite periodic patterns -/

namespace PeriodicSpherePacking

/-- The canonical packing whose centers are a full Euclidean lattice. -/
noncomputable def ofZLattice {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ x : Λ, x ≠ 0 → r ≤ ‖(x : V d)‖) :
    PeriodicSpherePacking d := by
  sorry

@[simp]
theorem ofZLattice_centers {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ x : Λ, x ≠ 0 → r ≤ ‖(x : V d)‖) :
    (ofZLattice Λ r hr hsep).centers = Λ := by
  sorry

@[simp]
theorem ofZLattice_lattice {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ x : Λ, x ≠ 0 → r ≤ ‖(x : V d)‖) :
    (ofZLattice Λ r hr hsep).lattice = Λ := by
  sorry

@[simp]
theorem ofZLattice_separation {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ x : Λ, x ≠ 0 → r ≤ ‖(x : V d)‖) :
    (ofZLattice Λ r hr hsep).separation = r := by
  sorry

/-- Basis-free density formula for the one-orbit lattice packing. -/
theorem ofZLattice_density {d : ℕ} (hd : 0 < d)
    (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ x : Λ, x ≠ 0 → r ≤ ‖(x : V d)‖) :
    (ofZLattice Λ r hr hsep).density =
      volume (ball (0 : V d) (r / 2)) / ENNReal.ofReal (ZLattice.covolume Λ) := by
  sorry

/-- Canonical quotient of centers by the period-lattice action. -/
abbrev Orbit {d : ℕ} (P : PeriodicSpherePacking d) := Quotient P.addAction.orbitRel

/-- The canonical orbit quotient is finite. -/
noncomputable instance orbitFinite {d : ℕ} (P : PeriodicSpherePacking d) :
    Finite P.Orbit := by
  sorry

noncomputable instance orbitFintype {d : ℕ} (P : PeriodicSpherePacking d) :
    Fintype P.Orbit := Fintype.ofFinite P.Orbit

/-- The canonical number of center orbits. -/
noncomputable def numOrbits {d : ℕ} (P : PeriodicSpherePacking d) : ℕ :=
  Fintype.card P.Orbit

/-- Canonical number of center orbits per unit covolume. -/
@[expose] noncomputable def centerIntensity {d : ℕ} (P : PeriodicSpherePacking d) : ℝ :=
  (P.numOrbits : ℝ) / ZLattice.covolume P.lattice

/-- The canonical orbit representative, chosen through `Quotient.out`.  Phases and structure
factors at dual frequencies are independent of the choice; production's basis-relative
fundamental-domain representatives realize the same quotient through
`addActionOrbitRelEquiv'`. -/
noncomputable def orbitRep {d : ℕ} (P : PeriodicSpherePacking d) (q : P.Orbit) : V d :=
  ((Quotient.out q : P.centers) : V d)

theorem orbitRep_mem_centers {d : ℕ} (P : PeriodicSpherePacking d) (q : P.Orbit) :
    P.orbitRep q ∈ P.centers :=
  (Quotient.out q).2

/-- Every center differs from its orbit's representative by a period. -/
theorem exists_lattice_vadd_orbitRep {d : ℕ} (P : PeriodicSpherePacking d) (x : P.centers) :
    ∃ z : P.lattice, (x : V d) = (z : V d) + P.orbitRep (Quotient.mk _ x) := by
  sorry

/-- Distinct orbits have representatives in distinct lattice cosets. -/
theorem orbitRep_sub_mem_lattice_iff {d : ℕ} (P : PeriodicSpherePacking d) (q q' : P.Orbit) :
    P.orbitRep q - P.orbitRep q' ∈ P.lattice ↔ q = q' := by
  sorry

/-- Basis-free periodic density formula with a finite orbit count. -/
theorem density_eq_numOrbits_mul_ballVolume_div_covolume {d : ℕ} (hd : 0 < d)
    (P : PeriodicSpherePacking d) :
    P.density = P.numOrbits * volume (ball (0 : V d) (P.separation / 2)) /
      ENNReal.ofReal (ZLattice.covolume P.lattice) := by
  sorry

/-- The centered coordinate box of radius `R`. -/
def centeredBox (d : ℕ) (R : ℝ) : Set (V d) :=
  {x | ∀ i, |x i| ≤ R}

/-- Coordinate box of radius `R` centered at `a`. -/
def centeredBoxAt {d : ℕ} (a : V d) (R : ℝ) : Set (V d) :=
  a +ᵥ centeredBox d R

/-- Centers of a packing lying in a translated box.  Separation makes this set finite. -/
noncomputable def finitePatternInBoxAt {d : ℕ} (P : SpherePacking d)
    (a : V d) (R : ℝ) :
    Finset P.centers := by
  sorry

@[simp]
theorem mem_finitePatternInBoxAt {d : ℕ} (P : SpherePacking d) (a : V d) (R : ℝ)
    (x : P.centers) :
    x ∈ finitePatternInBoxAt P a R ↔ (x : V d) ∈ centeredBoxAt a R := by
  sorry

/-- The origin-centered specialization retained for production compatibility. -/
noncomputable def finitePatternInBox {d : ℕ} (P : SpherePacking d) (R : ℝ) :
    Finset P.centers :=
  finitePatternInBoxAt P 0 R

@[simp]
theorem mem_finitePatternInBox {d : ℕ} (P : SpherePacking d) (R : ℝ)
    (x : P.centers) :
    x ∈ finitePatternInBox P R ↔ (x : V d) ∈ centeredBox d R := by
  simp [finitePatternInBox, centeredBoxAt, mem_finitePatternInBoxAt]

/-- Periodically repeat a translated finite box patch, leaving a guard band of one separation
between neighboring boxes. -/
noncomputable def periodicizeCentersAt {d : ℕ} (P : SpherePacking d)
    (a : V d) (R : ℝ) : Set (V d) :=
  {x | ∃ z : Fin d → ℤ, ∃ s ∈ finitePatternInBoxAt P a R,
    x = (s : V d) + fun i => (2 * (R + P.separation)) * (z i : ℝ)}

/-- Origin-centered periodicized centers retained for production compatibility. -/
noncomputable def periodicizeCenters {d : ℕ} (P : SpherePacking d) (R : ℝ) : Set (V d) :=
  periodicizeCentersAt P 0 R

/-- The periodic packing obtained from a guarded translated box patch. -/
noncomputable def ofFinitePatternInBoxAt {d : ℕ} (P : SpherePacking d)
    (a : V d) (R : ℝ) (hR : 0 < R) : PeriodicSpherePacking d := by
  sorry

@[simp]
theorem ofFinitePatternInBoxAt_centers {d : ℕ} (P : SpherePacking d)
    (a : V d) (R : ℝ) (hR : 0 < R) :
    (ofFinitePatternInBoxAt P a R hR).centers = periodicizeCentersAt P a R := by
  sorry

@[simp]
theorem ofFinitePatternInBoxAt_separation {d : ℕ} (P : SpherePacking d)
    (a : V d) (R : ℝ) (hR : 0 < R) :
    (ofFinitePatternInBoxAt P a R hR).separation = P.separation := by
  sorry

/-- Origin-centered periodicization retained as a transparent specialization. -/
noncomputable def ofFinitePatternInBox {d : ℕ} (P : SpherePacking d)
    (R : ℝ) (hR : 0 < R) : PeriodicSpherePacking d :=
  ofFinitePatternInBoxAt P 0 R hR

@[simp]
theorem ofFinitePatternInBox_centers {d : ℕ} (P : SpherePacking d)
    (R : ℝ) (hR : 0 < R) :
    (ofFinitePatternInBox P R hR).centers = periodicizeCenters P R := by
  simp [ofFinitePatternInBox, periodicizeCenters]

@[simp]
theorem ofFinitePatternInBox_separation {d : ℕ} (P : SpherePacking d)
    (R : ℝ) (hR : 0 < R) :
    (ofFinitePatternInBox P R hR).separation = P.separation := by
  simp [ofFinitePatternInBox]

/-- Guarded repetition preserves the packing inequality across distinct box translates. -/
theorem periodicizeAt_isPacking {d : ℕ} (P : SpherePacking d)
    (a : V d) (R : ℝ) (hR : 0 < R) :
    Pairwise (P.separation ≤ dist · · :
      (ofFinitePatternInBoxAt P a R hR).centers →
        (ofFinitePatternInBoxAt P a R hR).centers → Prop) := by
  sorry

/-- Exact density of a guarded translated periodicization. -/
theorem density_periodicizeAt {d : ℕ} (hd : 0 < d) (P : SpherePacking d)
    (a : V d) (R : ℝ) (hR : 0 < R) :
    (ofFinitePatternInBoxAt P a R hR).density =
      (finitePatternInBoxAt P a R).card *
        volume (ball (0 : V d) (P.separation / 2)) /
          ENNReal.ofReal ((2 * (R + P.separation)) ^ d) := by
  sorry

/-- Packing-volume density represented by the centers in a translated box before guard loss. -/
noncomputable def boxPackingDensity {d : ℕ} (P : SpherePacking d)
    (a : V d) (R : ℝ) : ℝ≥0∞ :=
  (finitePatternInBoxAt P a R).card *
    volume (ball (0 : V d) (P.separation / 2)) /
      ENNReal.ofReal ((2 * R) ^ d)

/-- The coordinate-box boundary layer of thickness `t`. -/
def boxBoundaryLayer (d : ℕ) (R t : ℝ) : Set (V d) :=
  centeredBox d (R + t) \ centeredBox d (R - t)

/-- A fixed-width boundary layer is negligible compared with the box volume. -/
theorem boundaryLayer_volume_div_volume_tendsto_zero {d : ℕ} (hd : 0 < d)
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ => volume (boxBoundaryLayer d R t) / volume (centeredBox d R))
      atTop (𝓝 0) := by
  sorry

/-- Fubini/Følner bridge from ball-limsup density to translated coordinate boxes.  The favorable
translation and the finite-density radius may depend on the scale, and the box half-width can be
required to exceed any prescribed lower bound. -/
theorem exists_translatedBox_normalizedCount_ge_finiteDensity_sub {d : ℕ} (hd : 0 < d)
    (P : SpherePacking d) (ε : ℝ≥0∞) (hε : 0 < ε) (R₀ : ℝ) :
    ∃ T : ℝ, ∃ a : V d, ∃ R : ℝ,
      max R₀ 0 < R ∧ R < T ∧
      P.density ≤ P.finiteDensity T + ε ∧
      P.finiteDensity T ≤ boxPackingDensity P a R + ε := by
  sorry

/-- Consequently, arbitrarily large translated boxes approximate the ball-limsup density. -/
theorem exists_translatedBox_density_ge_density_sub {d : ℕ} (hd : 0 < d)
    (P : SpherePacking d) (ε : ℝ≥0∞) (hε : 0 < ε) (R₀ : ℝ) :
    ∃ a : V d, ∃ R : ℝ,
      max R₀ 0 < R ∧ P.density ≤ boxPackingDensity P a R + ε := by
  sorry

/-- Every packing density is approximated from below by guarded periodicization of a translated
box supplied by the averaging theorem. -/
theorem exists_periodic_density_ge_density_sub {d : ℕ} (hd : 0 < d)
    (P : SpherePacking d) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ Q : PeriodicSpherePacking d, P.density ≤ Q.density + ε := by
  sorry

/-- Periodic approximation: periodic and unrestricted packing constants agree. -/
theorem constant_eq_general (d : ℕ) :
    PeriodicSpherePackingConstant d = SpherePackingConstant d := by
  sorry

end PeriodicSpherePacking

/-! ## Layer 4: Poisson summation and the Cohn--Elkies certificate -/

namespace EuclideanLattice

/-- The real dual of a full Euclidean lattice is discrete. -/
noncomputable instance dualDiscrete {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] : DiscreteTopology (dual Λ) := by
  sorry

/-- The real dual of a full Euclidean lattice is again full. -/
noncomputable instance dualIsZLattice {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] : IsZLattice ℝ (dual Λ) := by
  sorry

/-- Taking the real dual twice recovers the original full lattice. -/
theorem dual_dual {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] : dual (dual Λ) = Λ := by
  sorry

/-- The dual covolume is the reciprocal covolume. -/
theorem covolume_dual {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ZLattice.covolume (dual Λ) = (ZLattice.covolume Λ)⁻¹ := by
  sorry

end EuclideanLattice

/-! The generic real-lattice dual, Poisson summation, and theta-series theory is owned by the
TauCeti ThetaSeries roadmap.  The `ThetaSeries` namespace here and in Layer 5 carries
deletion-bound stand-ins shaped exactly like that roadmap's targets: they are deleted and
replaced by direct TauCeti imports when the roadmap is implemented, and they must not grow into
a second generic implementation.  SphereCeti keeps the orbit Poisson identity, the certificate
theory, the presentation bridges, and the E8/Leech-facing corollaries. -/

namespace ThetaSeries

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Stand-in for the roadmap's `dual`: literally Mathlib's `BilinForm.dualSubmodule` for the
inner product, and definitionally `EuclideanLattice.dual` in the ambient packing space. -/
@[expose] def dual (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) L

/-- Stand-in for the roadmap's shifted Poisson summation. -/
theorem poissonSummation (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(E, ℂ)) (v : E) :
    ∑' ℓ : L, f (v + (ℓ : E)) =
      ((ZLattice.covolume L : ℂ)⁻¹) *
        ∑' m : dual L, 𝓕 (fun x : E => f x) (m : E) *
          Complex.exp (2 * Real.pi * Complex.I * ⟪v, (m : E)⟫_ℝ) := by
  sorry

/-- Stand-in for the roadmap's lattice-side summability. -/
theorem summable_poisson_left (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(E, ℂ)) (v : E) :
    Summable fun ℓ : L => f (v + (ℓ : E)) := by
  sorry

/-- Stand-in for the roadmap's dual-side summability. -/
theorem summable_poisson_right (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(E, ℂ)) (v : E) :
    Summable fun m : dual L => 𝓕 (fun x : E => f x) (m : E) *
      Complex.exp (2 * Real.pi * Complex.I * ⟪v, (m : E)⟫_ℝ) := by
  sorry

end ThetaSeries

namespace EuclideanLattice

/-- The packing-space dual is the roadmap's dual, definitionally. -/
theorem dual_eq_thetaSeries_dual {d : ℕ} (Λ : Submodule ℤ (V d)) :
    dual Λ = ThetaSeries.dual Λ := rfl

end EuclideanLattice

namespace Poisson

/-- Unit-Gaussian acceptance test for the Fourier and covolume normalization, consuming the
`ThetaSeries` stand-in. -/
theorem gaussian_one {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    ∑' x : Λ, Real.exp (-Real.pi * ‖(x : V d)‖ ^ 2) =
      (ZLattice.covolume Λ)⁻¹ * ∑' y : EuclideanLattice.dual Λ,
        Real.exp (-Real.pi * ‖(y : V d)‖ ^ 2) := by
  sorry

end Poisson

namespace CohnElkies

/-- A general, not necessarily radial, Schwartz certificate. -/
structure Certificate (d : ℕ) (r : ℝ) where
  radius_pos : 0 < r
  f : 𝓢(V d, ℂ)
  real_f : ∀ x, (f x).im = 0
  real_fourier : ∀ x, (𝓕 f x).im = 0
  nonpos_of_radius_le_norm : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0
  fourier_nonneg : ∀ x, 0 ≤ (𝓕 f x).re
  fourier_zero_pos : 0 < (𝓕 f 0).re

/-- The density bound supplied by the certificate. -/
def Certificate.bound {d : ℕ} {r : ℝ} (C : Certificate d r) : ℝ≥0∞ :=
  ENNReal.ofReal ((C.f 0).re / (𝓕 C.f 0).re) * volume (ball (0 : V d) (r / 2))

/-- The common normalization used by the magic functions. -/
def Certificate.IsNormalized {d : ℕ} {r : ℝ} (C : Certificate d r) : Prop :=
  C.f 0 = 1 ∧ 𝓕 C.f 0 = 1

/-- Radial functions feed the generic certificate without contaminating the generic theorem with a
radiality hypothesis. -/
noncomputable def Certificate.ofRadial {d : ℕ} {r : ℝ}
    (hr : 0 < r) (f : RadialSchwartzMap ℂ (V d) ℂ)
    (hreal : ∀ x, (f x).im = 0)
    (hrealFourier : ∀ x, (𝓕 (f : 𝓢(V d, ℂ)) x).im = 0)
    (hnonpos : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0)
    (hfourierNonneg : ∀ x, 0 ≤ (𝓕 (f : 𝓢(V d, ℂ)) x).re)
    (hfourierZeroPos : 0 < (𝓕 (f : 𝓢(V d, ℂ)) 0).re) :
    Certificate d r where
  radius_pos := hr
  f := f
  real_f := hreal
  real_fourier := hrealFourier
  nonpos_of_radius_le_norm := hnonpos
  fourier_nonneg := hfourierNonneg
  fourier_zero_pos := hfourierZeroPos

@[simp]
theorem Certificate.ofRadial_f {d : ℕ} {r : ℝ}
    (hr : 0 < r) (f : RadialSchwartzMap ℂ (V d) ℂ)
    (hreal : ∀ x, (f x).im = 0)
    (hrealFourier : ∀ x, (𝓕 (f : 𝓢(V d, ℂ)) x).im = 0)
    (hnonpos : ∀ x, r ≤ ‖x‖ → (f x).re ≤ 0)
    (hfourierNonneg : ∀ x, 0 ≤ (𝓕 (f : 𝓢(V d, ℂ)) x).re)
    (hfourierZeroPos : 0 < (𝓕 (f : 𝓢(V d, ℂ)) 0).re) :
    (Certificate.ofRadial hr f hreal hrealFourier hnonpos hfourierNonneg
      hfourierZeroPos).f = (f : 𝓢(V d, ℂ)) := by
  simp [Certificate.ofRadial]

/-- Fourier inversion and nonnegativity make the direct value at zero strictly positive. -/
theorem Certificate.f_zero_pos {d : ℕ} {r : ℝ} (C : Certificate d r) :
    0 < (C.f 0).re := by
  sorry

/-- Every certificate supplies a strictly positive density bound. -/
theorem Certificate.bound_pos {d : ℕ} {r : ℝ} (C : Certificate d r) :
    0 < C.bound := by
  sorry

/-- The unrestricted Cohn--Elkies upper bound. -/
theorem bound {d : ℕ} {r : ℝ} (hd : 0 < d) (C : Certificate d r) :
    SpherePackingConstant d ≤ C.bound := by
  sorry

/-- Sharpness for a one-orbit lattice packing. -/
def Certificate.IsSharpForLattice {d : ℕ} {r : ℝ}
    (C : Certificate d r) (Λ : Submodule ℤ (V d)) : Prop :=
  (∀ x : Λ, x ≠ 0 → C.f (x : V d) = 0) ∧
  (∀ y : EuclideanLattice.dual Λ, y ≠ 0 → 𝓕 C.f (y : V d) = 0)

/-- The finite complex Fourier amplitude of the canonical orbit representatives. -/
noncomputable def structureAmplitude {d : ℕ} (P : PeriodicSpherePacking d) (y : V d) : ℂ :=
  ∑ q : P.Orbit, Complex.exp (2 * Real.pi * Complex.I * ⟪y, P.orbitRep q⟫_ℝ)

/-- Changing an orbit representative by a period does not change its phase at a dual frequency. -/
theorem phase_eq_of_sub_mem_lattice {d : ℕ} {P : PeriodicSpherePacking d}
    (y : EuclideanLattice.dual P.lattice) (s t : P.centers)
    (hst : (s : V d) - (t : V d) ∈ P.lattice) :
    Complex.exp (2 * Real.pi * Complex.I * ⟪(y : V d), (s : V d)⟫_ℝ) =
      Complex.exp (2 * Real.pi * Complex.I * ⟪(y : V d), (t : V d)⟫_ℝ) := by
  sorry

/-- The nonnegative real structure factor is the squared norm of the amplitude. -/
@[expose] noncomputable def structureFactor {d : ℕ} (P : PeriodicSpherePacking d)
    (y : V d) : ℝ :=
  ‖structureAmplitude P y‖ ^ 2

theorem structureFactor_nonneg {d : ℕ} (P : PeriodicSpherePacking d) (y : V d) :
    0 ≤ structureFactor P y :=
  sq_nonneg _

theorem structureFactor_eq_zero_iff {d : ℕ} (P : PeriodicSpherePacking d) (y : V d) :
    structureFactor P y = 0 ↔ structureAmplitude P y = 0 := by
  simp [structureFactor]

/-- Phase of a canonical center orbit at a dual frequency. -/
noncomputable def orbitPhase {d : ℕ} (P : PeriodicSpherePacking d)
    (y : EuclideanLattice.dual P.lattice) : P.Orbit → ℂ := by
  sorry

@[simp]
theorem orbitPhase_mk {d : ℕ} (P : PeriodicSpherePacking d)
    (y : EuclideanLattice.dual P.lattice) (s : P.centers) :
    orbitPhase P y (Quotient.mk _ s) =
      Complex.exp (2 * Real.pi * Complex.I * ⟪(y : V d), (s : V d)⟫_ℝ) := by
  sorry

/-- Pattern-independent structure factor on the canonical orbit quotient. -/
@[expose] noncomputable def orbitStructureFactor {d : ℕ} (P : PeriodicSpherePacking d)
    (y : EuclideanLattice.dual P.lattice) : ℝ :=
  ‖∑ q : P.Orbit, orbitPhase P y q‖ ^ 2

theorem orbitStructureFactor_nonneg {d : ℕ} (P : PeriodicSpherePacking d)
    (y : EuclideanLattice.dual P.lattice) : 0 ≤ orbitStructureFactor P y :=
  sq_nonneg _

/-- At a dual frequency, the representative-based structure factor is the canonical one. -/
theorem structureFactor_eq_orbitStructureFactor {d : ℕ} (P : PeriodicSpherePacking d)
    (y : EuclideanLattice.dual P.lattice) :
    structureFactor P (y : V d) = orbitStructureFactor P y := by
  sorry

/-- Summing shifted Poisson over the canonical representatives produces the squared structure
amplitude. -/
theorem poisson_orbitReps {d : ℕ} (P : PeriodicSpherePacking d) (f : 𝓢(V d, ℂ)) :
    ∑' z : P.lattice, ∑ q : P.Orbit, ∑ q' : P.Orbit,
        f ((z : V d) + P.orbitRep q - P.orbitRep q') =
      ((ZLattice.covolume P.lattice : ℂ)⁻¹) *
        ∑' y : EuclideanLattice.dual P.lattice,
          𝓕 f (y : V d) * (structureFactor P (y : V d) : ℂ) := by
  sorry

/-- Pattern-independent equality conditions for a periodic packing.  On the direct side every
nonzero center difference lies in the zero set of `f`; on the Fourier side either `f̂` or the
canonical orbit structure factor vanishes at each nonzero dual frequency. -/
def Certificate.IsSharpForPeriodic {d : ℕ} {r : ℝ}
    (C : Certificate d r) (P : PeriodicSpherePacking d) : Prop :=
  (∀ x : P.centers, ∀ y : P.centers, x ≠ y →
      C.f ((x : V d) - (y : V d)) = 0) ∧
  (∀ y : EuclideanLattice.dual P.lattice, y ≠ 0 →
      𝓕 C.f (y : V d) = 0 ∨ orbitStructureFactor P y = 0)

/-- Negative of the nontrivial direct-side sum over the canonical representatives. -/
noncomputable def directDefect {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d) : ℝ :=
  -∑' z : P.lattice, ∑ q : P.Orbit, ∑ q' : P.Orbit,
    if (z : V d) + P.orbitRep q - P.orbitRep q' = 0 then 0
    else (C.f ((z : V d) + P.orbitRep q - P.orbitRep q')).re

/-- Nonzero-frequency Fourier contribution. -/
noncomputable def fourierDefect {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d) : ℝ :=
  (ZLattice.covolume P.lattice)⁻¹ *
    ∑' y : EuclideanLattice.dual P.lattice,
      if y = 0 then 0
      else (𝓕 C.f (y : V d)).re * structureFactor P (y : V d)

theorem directDefect_nonneg {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d)
    (hsep : r = P.separation) : 0 ≤ directDefect C P := by
  sorry

theorem fourierDefect_nonneg {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d) :
    0 ≤ fourierDefect C P := by
  sorry

/-- Exact real-valued equality behind the periodic Cohn--Elkies bound. -/
theorem defect_identity {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d) :
    (P.numOrbits : ℝ) * (C.f 0).re -
        (P.numOrbits : ℝ) ^ 2 / ZLattice.covolume P.lattice *
          (𝓕 C.f 0).re =
      fourierDefect C P + directDefect C P := by
  sorry

/-- The center-intensity gap is the sum of the two nonnegative defects. -/
theorem normalized_gap_eq_defects {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d)
    (horbits : 0 < P.numOrbits) :
    (C.f 0).re / (𝓕 C.f 0).re -
        (P.numOrbits : ℝ) / ZLattice.covolume P.lattice =
      (fourierDefect C P + directDefect C P) /
        ((P.numOrbits : ℝ) * (𝓕 C.f 0).re) := by
  sorry

/-- Equality in the periodic bound forces every termwise sharpness condition. -/
theorem isSharpForPeriodic_of_density_eq_bound {d : ℕ} {r : ℝ} (hd : 0 < d)
    (C : Certificate d r) (P : PeriodicSpherePacking d)
    (hsep : r = P.separation) (h : P.density = C.bound) :
    C.IsSharpForPeriodic P := by
  sorry

/-- Sharpness gives equality once the canonical orbit quotient is nonempty. -/
theorem density_eq_bound_of_isSharpForPeriodic {d : ℕ} {r : ℝ} (hd : 0 < d)
    (C : Certificate d r) (P : PeriodicSpherePacking d)
    (hsep : r = P.separation) (horbits : 0 < P.numOrbits)
    (hsharp : C.IsSharpForPeriodic P) : P.density = C.bound := by
  sorry

/-- The lattice sharpness relation identifies the bound with the canonical lattice-packing
density. -/
theorem bound_eq_lattice_density_of_isSharp {d : ℕ} {r : ℝ} (hd : 0 < d)
    (C : Certificate d r)
    (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hsep : ∀ x : Λ, x ≠ 0 → r ≤ ‖(x : V d)‖)
    (hsharp : C.IsSharpForLattice Λ) :
    C.bound = (PeriodicSpherePacking.ofZLattice Λ r C.radius_pos hsep).density := by
  sorry

end CohnElkies

/-! ## Layer 5: lattice theta series -/

namespace ThetaSeries

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Stand-in for the roadmap's shell at a real squared norm. -/
def shell (L : Submodule ℤ E) (t : ℝ) : Set L := {v : L | ‖(v : E)‖ ^ 2 = t}

/-- Stand-in for the roadmap's representation number. -/
noncomputable def repNum (L : Submodule ℤ E) (t : ℝ) : ℕ := (shell L t).ncard

/-- Stand-in for the roadmap's evenness of a real lattice. -/
def IsEven (L : Submodule ℤ E) : Prop := ∀ x ∈ L, ∃ m : ℤ, ‖x‖ ^ 2 = 2 * (m : ℝ)

/-- Stand-in for the roadmap's unimodularity of a real lattice. -/
def IsUnimodular (L : Submodule ℤ E) : Prop := L = dual L

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Stand-in for the roadmap's theta series; the exponent is `π i ‖v‖² τ`. -/
noncomputable def thetaSeries (τ : UpperHalfPlane) : ℂ :=
  ∑' v : L, Complex.exp (Real.pi * Complex.I * (‖(v : E)‖ ^ 2 : ℝ) * (τ : ℂ))

variable [MeasurableSpace E] [BorelSpace E]

/-- Stand-in for the roadmap's theta inversion, Poisson summation at the Gaussian. -/
theorem thetaSeries_neg_inv (k : ℕ) (hn : Module.finrank ℝ E = 2 * k) (τ : UpperHalfPlane) :
    thetaSeries L (ModularGroup.S • τ) =
      ((ZLattice.covolume L : ℂ)⁻¹) * (-Complex.I) ^ k * (τ : ℂ) ^ k *
        thetaSeries (dual L) τ := by
  sorry

/-- Stand-in for the roadmap's theta modular form of an even unimodular lattice. -/
noncomputable def thetaForm (k : ℕ) (hn : Module.finrank ℝ E = 2 * k)
    (he : IsEven L) (hu : IsUnimodular L) : ModularForm 𝒮ℒ (k : ℤ) := by
  sorry

@[simp]
theorem coe_thetaForm (k : ℕ) (hn : Module.finrank ℝ E = 2 * k)
    (he : IsEven L) (hu : IsUnimodular L) :
    ⇑(thetaForm L k hn he hu) = thetaSeries L := by
  sorry

/-- Stand-in for the roadmap's q-expansion coefficients of the theta form. -/
theorem qExpansion_thetaForm_coeff (k : ℕ) (hn : Module.finrank ℝ E = 2 * k)
    (he : IsEven L) (hu : IsUnimodular L) (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 (thetaForm L k hn he hu)).coeff m =
      (repNum L (2 * m) : ℂ) := by
  sorry

/-- Stand-in for the roadmap's rank-eight classification. -/
theorem thetaForm_eq_E₄ (hn : Module.finrank ℝ E = 8)
    (he : IsEven L) (hu : IsUnimodular L) :
    thetaForm L 4 (by omega) he hu = ModularForm.E₄ := by
  sorry

/-- Stand-in for the roadmap's rank-eight root count. -/
theorem repNum_two_rank_eight (hn : Module.finrank ℝ E = 8)
    (he : IsEven L) (hu : IsUnimodular L) :
    repNum L 2 = 240 := by
  sorry

/-- Stand-in for the roadmap's rank-24 classification by the root count. -/
theorem thetaForm_rank_24 (hn : Module.finrank ℝ E = 24)
    (he : IsEven L) (hu : IsUnimodular L) :
    (thetaForm L 12 (by omega) he hu : UpperHalfPlane → ℂ) =
      fun τ => (ModularForm.E₄ τ) ^ 3 +
        ((repNum L 2 : ℂ) - 720) * ModularForm.discriminant τ := by
  sorry

/-- Stand-in for the roadmap's rootless rank-24 Leech identity. -/
theorem coe_thetaForm_rank_24_rootless (hn : Module.finrank ℝ E = 24)
    (he : IsEven L) (hu : IsUnimodular L) (hr : repNum L 2 = 0) :
    (thetaForm L 12 (by omega) he hu : UpperHalfPlane → ℂ) =
      fun τ => (ModularForm.E₄ τ) ^ 3 - 720 * ModularForm.discriminant τ := by
  sorry

end ThetaSeries

namespace Theta

/-- The packing-facing theta series is the roadmap stand-in, applied in the ambient space. -/
noncomputable abbrev latticeTheta {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] : UpperHalfPlane → ℂ :=
  ThetaSeries.thetaSeries Λ

/-- The normalized weight-four Eisenstein series used in the E8 identity. -/
noncomputable def E4 : ModularForm 𝒮ℒ 4 := ModularForm.E₄

/-- Root count, i.e. the squared-norm-two shell cardinality. -/
noncomputable def rootCard {d : ℕ} (Λ : Submodule ℤ (V d)) : ℕ :=
  ThetaSeries.repNum Λ 2

/-- The root count agrees with the presentation-indexed even coefficient. -/
theorem rootCard_eq_thetaEvenCoeff {d : ℕ} (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] :
    rootCard Λ = EuclideanLattice.thetaEvenCoeff Λ 1 := by
  sorry

/-- Bridge: an even integral presentation makes the real lattice even in the roadmap's sense. -/
theorem isEven_real_of_presentation {d : ℕ} {Λ : Submodule ℤ (V d)}
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ) (heven : P.IsEven) :
    ThetaSeries.IsEven Λ := by
  sorry

/-- Bridge: a unimodular integral presentation makes the real lattice unimodular in the
roadmap's sense. -/
theorem isUnimodular_real_of_presentation {d : ℕ} {Λ : Submodule ℤ (V d)}
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ) (hunimodular : P.IsUnimodular) :
    ThetaSeries.IsUnimodular Λ := by
  sorry

/-- SphereCeti corollary of the roadmap's rank-eight classification, through the presentation
bridge, in the form the E8 package consumes. -/
theorem theta_eq_E4_of_even_unimodular
    (Λ : Submodule ℤ (V 8)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    latticeTheta Λ = fun τ => E4 τ := by
  sorry

/-- SphereCeti corollary of the roadmap's rank-24 classification. -/
theorem theta_rank24_eq_E4_cubed_add_rootCard_sub_720_Delta
    (Λ : Submodule ℤ (V 24)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    latticeTheta Λ = fun τ =>
      (E4 τ) ^ 3 + ((rootCard Λ : ℤ) - 720) * ModularForm.discriminant τ := by
  sorry

/-- SphereCeti corollary of the roadmap's rootless rank-24 Leech identity. -/
theorem theta_rank24_rootless_eq_E4_cubed_sub_720_Delta
    (Λ : Submodule ℤ (V 24)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular)
    (hrootless : rootCard Λ = 0) :
    latticeTheta Λ = fun τ =>
      (E4 τ) ^ 3 - 720 * ModularForm.discriminant τ := by
  sorry

end Theta

/-! ## Layer 6: E8 and Leech lattice data -/

namespace E8

abbrev lattice : Submodule ℤ (V 8) := SphereCeti.Pinned.E8Lattice
abbrev packing : PeriodicSpherePacking 8 := SphereCeti.Pinned.E8Packing

/-- Canonical algebraic E8 reference object, reusing TauCeti's existing E8 lattice model. -/
noncomputable def integralLattice : TauCeti.IntegralLattice (Fin 8 → ℚ) := by
  sorry

/-- Required upstream dependency: every positive-definite even unimodular rank-eight lattice is
E8.  Its intended home is TauCeti's IntegralLattices and Root Systems development, whose ADE
decomposition and root-count identification prove it; SphereCeti consumes exactly this endpoint
and does not restate the root-system machinery.  Local implementation with exactly this
statement is available whenever coordination or timing requires it.
Positive-definiteness supplies nondegeneracy internally. -/
theorem even_unimodular_rank_eight_unique
    {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hrank : Module.finrank ℚ W = 8)
    (hpos : L.IsPosDef) (heven : L.IsEven) (hunimodular : L.IsUnimodular) :
    Nonempty (TauCeti.IntegralLattice.Isometry L integralLattice) := by
  sorry

/-- The explicit production basis and integer Gram matrix packaged for TauCeti. -/
noncomputable def integralPresentation : EuclideanLattice.IntegralPresentation lattice := by
  sorry

/-- Identification of the presentation extracted from the real E8 lattice with the canonical
algebraic E8 reference object. -/
noncomputable def integralLatticeIsometry :
    TauCeti.IntegralLattice.Isometry integralPresentation.toIntegralLattice integralLattice := by
  sorry

@[simp]
theorem integralPresentation_even : integralPresentation.IsEven := by
  sorry

@[simp]
theorem integralPresentation_unimodular : integralPresentation.IsUnimodular := by
  sorry

/-- Minimum squared norm two, proved independently of theta-series classification. -/
theorem hasMinNormSq : EuclideanLattice.HasMinNormSq lattice 2 := by
  sorry

/-- E8 has 240 roots. -/
theorem rootCard : Theta.rootCard lattice = 240 := by
  sorry

/-- The analytic theta identity. -/
theorem theta_eq_E4 : Theta.latticeTheta lattice = fun τ => Theta.E4 τ := by
  sorry

@[simp]
theorem packing_centers : packing.centers = lattice := by
  sorry

@[simp]
theorem packing_lattice : packing.lattice = lattice := by
  sorry

@[simp]
theorem packing_separation : packing.separation = Real.sqrt 2 := by
  sorry

/-- The E8 packing has density `π ^ 4 / 384`. -/
theorem packing_density :
    packing.density = ENNReal.ofReal (Real.pi ^ 4 / 384) := by
  exact SphereCeti.Pinned.E8Packing_density

end E8

namespace Leech

/-- Canonical algebraic Leech reference object. -/
noncomputable def integralLattice : TauCeti.IntegralLattice (Fin 24 → ℚ) := by
  sorry

/-- Required upstream dependency: every positive-definite rootless even unimodular rank-24
lattice is Leech.  Its intended home is a TauCeti Niemeier-completeness extension of the
Integral Lattices roadmap: that roadmap defines the twenty-four reference lattices but does not
prove completeness, so this endpoint remains a mandatory dependency here.  SphereCeti consumes
exactly this statement and does not restate the Niemeier case list or selection machinery; local
implementation with exactly this statement is available whenever coordination or timing requires
it.  Positive-definiteness supplies nondegeneracy internally. -/
theorem rootless_even_unimodular_rank_twentyFour_unique
    {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hrank : Module.finrank ℚ W = 24)
    (hpos : L.IsPosDef) (heven : L.IsEven) (hunimodular : L.IsUnimodular)
    (hrootless : EuclideanLattice.IsRootless L) :
    Nonempty (TauCeti.IntegralLattice.Isometry L integralLattice) := by
  sorry

/-- Hamming weight of a binary word. -/
def binaryHammingWeight (x : Fin 24 → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

/-- Exact generator matrix for the extended binary Golay code.  Its first 23 columns are the first
12 shifts of `1 + X + X^5 + X^6 + X^7 + X^9 + X^11`; column 23 is the parity extension. -/
def golayGeneratorMatrix : Matrix (Fin 12) (Fin 24) (ZMod 2) := fun i j =>
  if j.val = 23 then 1
  else if (j.val + 23 - i.val) % 23 ∈ ({0, 1, 5, 6, 7, 9, 11} : Finset ℕ) then 1
  else 0

/-- The first twelve columns form the pinned unitriangular row-reduction certificate. -/
def golayPivotMinor : Matrix (Fin 12) (Fin 12) (ZMod 2) := fun i j =>
  golayGeneratorMatrix i ⟨j.val, by omega⟩

/-- Executable check that the pivot minor is upper triangular with diagonal one. -/
theorem golayPivotMinor_unitriangular :
    (∀ i j : Fin 12, j < i → golayPivotMinor i j = 0) ∧
      ∀ i : Fin 12, golayPivotMinor i i = 1 := by
  constructor
  · intro i j hji
    fin_cases i <;> fin_cases j <;> norm_num at hji <;> decide
  · intro i
    fin_cases i <;> decide

/-- Executable check that every parity-extended generator row has weight eight. -/
theorem golayGeneratorMatrix_rowWeight :
    ∀ i : Fin 12, binaryHammingWeight (golayGeneratorMatrix i) = 8 := by
  intro i
  fin_cases i <;> decide

/-- The extended binary Golay code is the row span of the pinned generator matrix. -/
noncomputable def extendedBinaryGolay : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun i => golayGeneratorMatrix i)

/-- Orthogonal code for the standard binary dot product. -/
noncomputable def binaryDualCode
    (C : Submodule (ZMod 2) (Fin 24 → ZMod 2)) :
    Submodule (ZMod 2) (Fin 24 → ZMod 2) := by
  sorry

@[simp]
theorem mem_binaryDualCode (C : Submodule (ZMod 2) (Fin 24 → ZMod 2))
    (x : Fin 24 → ZMod 2) :
    x ∈ binaryDualCode C ↔ ∀ c ∈ C, ∑ i, x i * c i = 0 := by
  sorry

/-- Weight enumerator of a finite binary code. -/
noncomputable def binaryWeightEnumerator
    (C : Submodule (ZMod 2) (Fin 24 → ZMod 2)) : Polynomial ℤ := by
  classical
  exact ∑ c : (Fin 24 → ZMod 2),
    if c ∈ C then Polynomial.X ^ binaryHammingWeight c else 0

theorem extendedBinaryGolay_finrank :
    Module.finrank (ZMod 2) extendedBinaryGolay = 12 := by
  sorry

theorem extendedBinaryGolay_card : Nat.card extendedBinaryGolay = 2 ^ 12 := by
  sorry

theorem extendedBinaryGolay_selfDual :
    binaryDualCode extendedBinaryGolay = extendedBinaryGolay := by
  sorry

theorem extendedBinaryGolay_doublyEven (c : extendedBinaryGolay) :
    4 ∣ binaryHammingWeight (c : Fin 24 → ZMod 2) := by
  sorry

theorem extendedBinaryGolay_minWeight (c : extendedBinaryGolay) (hc : c ≠ 0) :
    8 ≤ binaryHammingWeight (c : Fin 24 → ZMod 2) := by
  sorry

theorem extendedBinaryGolay_exists_weight_eight :
    ∃ c : extendedBinaryGolay, binaryHammingWeight (c : Fin 24 → ZMod 2) = 8 := by
  sorry

theorem extendedBinaryGolay_weightEnumerator :
    binaryWeightEnumerator extendedBinaryGolay =
      1 + 759 * Polynomial.X ^ 8 + 2576 * Polynomial.X ^ 12 +
        759 * Polynomial.X ^ 16 + Polynomial.X ^ 24 := by
  sorry

def allOneWord : Fin 24 → ZMod 2 := fun _ => 1

theorem allOneWord_mem_extendedBinaryGolay : allOneWord ∈ extendedBinaryGolay := by
  sorry

theorem extendedBinaryGolay_weight_even (c : extendedBinaryGolay) :
    Even (binaryHammingWeight (c : Fin 24 → ZMod 2)) := by
  sorry

/-- Binary word selecting coordinates in one residue class modulo four. -/
def residueWord (a : Fin 24 → ℤ) (r : ZMod 4) : Fin 24 → ZMod 2 := fun i =>
  if (a i : ZMod 4) = r then 1 else 0

/-- Integral coordinate condition whose `1 / sqrt 8` scaling is the Leech lattice. -/
def IsLeechIntegralCoordinate (a : Fin 24 → ℤ) : Prop :=
  (∀ i, ((∑ j, a j : ℤ) : ZMod 8) = 4 * (a i : ZMod 8)) ∧
    ∀ r : ZMod 4, residueWord a r ∈ extendedBinaryGolay

/-- Public coordinate/glue construction of the Leech lattice.  It is not the naive unshifted
Construction-A lattice. -/
noncomputable def lattice : Submodule ℤ (V 24) := by
  sorry

/-- Exact scaled-coordinate membership theorem for the Leech lattice. -/
theorem mem_lattice_iff_scaled_golay_coordinates (x : V 24) :
    x ∈ lattice ↔ ∃ a : Fin 24 → ℤ, IsLeechIntegralCoordinate a ∧
      x = WithLp.toLp 2 fun i => (a i : ℝ) / Real.sqrt 8 := by
  sorry

/-- Published row-basis matrix; the actual basis vectors are these rows divided by `sqrt 8`. -/
def basisCoordinateMatrix : Matrix (Fin 24) (Fin 24) ℤ := ![
  ![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
  ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
  ![2, 0, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0],
  ![2, 0, 0, 2, 2, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0],
  ![2, 2, 0, 0, 2, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0],
  ![0, 2, 2, 2, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0],
  ![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
]

/-- Exact determinant certificate for the published integer basis matrix. -/
theorem basisCoordinateMatrix_det : basisCoordinateMatrix.det = 8 ^ 12 := by
  sorry

/-- The 24 explicit real basis vectors. -/
noncomputable def basisVector (i : Fin 24) : V 24 :=
  WithLp.toLp 2 fun j => (basisCoordinateMatrix i j : ℝ) / Real.sqrt 8

theorem basisVector_mem (i : Fin 24) : basisVector i ∈ lattice := by
  sorry

/-- The explicit rows span exactly the coordinate/glue lattice. -/
theorem span_basisVectors_eq_lattice :
    Submodule.span ℤ (Set.range basisVector) = lattice := by
  sorry

noncomputable instance lattice_discrete : DiscreteTopology lattice := by
  sorry

noncomputable instance lattice_isZLattice : IsZLattice ℝ lattice := by
  sorry

/-- Explicit computational basis/Gram presentation. -/
noncomputable def integralPresentation : EuclideanLattice.IntegralPresentation lattice := by
  sorry

/-- Identification with the canonical algebraic Leech reference object. -/
noncomputable def integralLatticeIsometry :
    TauCeti.IntegralLattice.Isometry integralPresentation.toIntegralLattice integralLattice := by
  sorry

@[simp]
theorem integralPresentation_even : integralPresentation.IsEven := by
  sorry

@[simp]
theorem integralPresentation_unimodular : integralPresentation.IsUnimodular := by
  sorry

/-- Minimum squared norm four; in particular the lattice is rootless. -/
theorem hasMinNormSq : EuclideanLattice.HasMinNormSq lattice 4 := by
  sorry

@[simp]
theorem rootCard : Theta.rootCard lattice = 0 := by
  sorry

/-- First nonzero shell cardinality. -/
theorem shellCard_four : EuclideanLattice.thetaEvenCoeff lattice 2 = 196560 := by
  sorry

/-- The Leech theta identity. -/
theorem theta_eq_E4_cubed_sub_720_Delta :
    Theta.latticeTheta lattice = fun τ =>
      (Theta.E4 τ) ^ 3 - 720 * ModularForm.discriminant τ := by
  sorry

/-- Canonical lattice packing with separation two. -/
noncomputable def packing : PeriodicSpherePacking 24 := by
  sorry

@[simp]
theorem packing_centers : packing.centers = lattice := by
  sorry

@[simp]
theorem packing_lattice : packing.lattice = lattice := by
  sorry

@[simp]
theorem packing_separation : packing.separation = 2 := by
  sorry

/-- Density of unit balls centered at the Leech lattice. -/
theorem packing_density :
    packing.density = ENNReal.ofReal (Real.pi ^ 12 / Nat.factorial 12) := by
  sorry

end Leech

/-! ## Layer 7: radial profiles, parametric integration, and signed kernels -/

namespace MagicFunction

/-- Compose a one-variable Schwartz profile with squared norm. -/
noncomputable def ofNormSq {d : ℕ} (f : 𝓢(ℝ, ℂ)) :
    RadialSchwartzMap ℂ (V d) ℂ := by
  sorry

@[simp]
theorem ofNormSq_apply {d : ℕ} (f : 𝓢(ℝ, ℂ)) (x : V d) :
    ofNormSq f x = f (‖x‖ ^ 2) := by
  sorry

/-- Exact local zero order, expressed by a nonvanishing continuous cofactor. -/
def HasExactZeroOrder (f : ℝ → ℂ) (a : ℝ) (m : ℕ) : Prop :=
  ∃ g : ℝ → ℂ, ContinuousAt g a ∧ g a ≠ 0 ∧
    ∀ᶠ x in 𝓝 a, f x = (x - a) ^ m * g x

/-- Exact local order gives the quantitative lower bound required by the stability roadmap in
`UPSTREAM.md`. -/
theorem HasExactZeroOrder.quantitativeLowerBound {f : ℝ → ℂ} {a : ℝ} {m : ℕ}
    (h : HasExactZeroOrder f a m) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in 𝓝 a, c * |x - a| ^ m ≤ ‖f x‖ := by
  sorry

/-- The only Fourier eigenvalues used by the E8 and Leech component constructions. -/
inductive FourierSign
  | plus
  | minus

namespace FourierSign

/-- Complex scalar represented by a Fourier sign. -/
@[expose] def scalar : FourierSign → ℂ
  | .plus => 1
  | .minus => -1

@[simp]
theorem scalar_plus : scalar .plus = 1 := rfl

@[simp]
theorem scalar_minus : scalar .minus = -1 := rfl

@[simp]
theorem scalar_sq (sign : FourierSign) : sign.scalar ^ 2 = 1 := by
  cases sign <;> simp [scalar]

end FourierSign

/- The signed transformation laws are consumed directly by the Layer 8 transport theorems.  No
bundled kernel datum, opaque constructor, or free complex eigenvalue is part of the target
surface: the finite Fourier sign occurs in the transformation law that determines it, and the
concrete components connect to the contour machinery through explicit characteristic
equations. -/

end MagicFunction

/-! ## Layer 8: contour deformation and magic-integral transport

All required finite deformations use straight segments and their images under the Möbius
inversion `z ↦ -1/z`; all required unbounded deformations use axis-aligned rectangles.  The
declarations are shaped for the production `SpherePacking.Contour` and
`SpherePacking.Integration` namespaces; Mathlib's `curveIntegral`, `Path.segment`, and
curve-integral Poincaré lemma are consumed directly. -/

namespace Contour

/-! ### Ownership contracts for the two contour tools -/

#check @Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
#check @curveIntegral
#check @ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl

/-! ### Unbounded branch: open rectangles -/

/-- Deformation of a horizontal edge into the two vertical half-lines above its endpoints, off a
countable exceptional set, matching the generality of Mathlib's bounded rectangle theorem.  The
half-line integrability hypotheses are explicit, and the top edge is controlled by convergence of
the top-edge integrals to zero. -/
theorem horizontal_add_vertical_eq_vertical_of_tendsto_top
    {f : ℂ → ℂ} {x₁ x₂ y : ℝ} {s : Set ℂ} (hs : s.Countable)
    (hcont : ContinuousOn f {z : ℂ | z.re ∈ Set.uIcc x₁ x₂ ∧ y ≤ z.im})
    (hdiff : ∀ z ∈ {z : ℂ | z.re ∈ Set.Ioo (min x₁ x₂) (max x₁ x₂) ∧ y < z.im} \ s,
      DifferentiableAt ℂ f z)
    (hint₁ : IntegrableOn (fun t : ℝ => f (x₁ + t * Complex.I)) (Set.Ioi y))
    (hint₂ : IntegrableOn (fun t : ℝ => f (x₂ + t * Complex.I)) (Set.Ioi y))
    (htop : Tendsto (fun m : ℝ => ∫ x in x₁..x₂, f (x + m * Complex.I)) atTop (𝓝 0)) :
    (∫ x in x₁..x₂, f (x + y * Complex.I))
        + Complex.I * ∫ t in Set.Ioi y, f (x₂ + t * Complex.I)
      = Complex.I * ∫ t in Set.Ioi y, f (x₁ + t * Complex.I) := by
  sorry

/-- The top-edge hypothesis follows from uniform decay of `f` on the edge as the imaginary part
grows.  Interval integrability of each edge is an explicit hypothesis, so a non-integrable
integral's junk value cannot satisfy the conclusion vacuously. -/
theorem tendsto_top_edge_of_uniform_decay
    {f : ℂ → ℂ} {x₁ x₂ : ℝ}
    (hint : ∀ m : ℝ, IntervalIntegrable (fun x : ℝ => f (x + m * Complex.I)) volume x₁ x₂)
    (hdecay : TendstoUniformlyOn (fun m : ℝ => fun x : ℝ => f (x + m * Complex.I)) 0 atTop
      (Set.uIcc x₁ x₂)) :
    Tendsto (fun m : ℝ => ∫ x in x₁..x₂, f (x + m * Complex.I)) atTop (𝓝 0) := by
  sorry

/-! ### Finite branch: curve-integral transport -/

/-- The scalar one-form `v ↦ F z * v` of a function `F : ℂ → ℂ`. -/
@[expose]
noncomputable def scalarOneForm (F : ℂ → ℂ) : ℂ → ℂ →L[ℂ] ℂ :=
  fun z => F z • ContinuousLinearMap.id ℂ ℂ

@[simp]
theorem scalarOneForm_apply (F : ℂ → ℂ) (z v : ℂ) : scalarOneForm F z v = F z * v := rfl

/- The interval-integral/segment bridge is Mathlib's `curveIntegral_segment`, consumed
directly. -/
#check @curveIntegral_segment

/-- Change of variables along a segment, with an honest chain-rule hypothesis: `f` is continuous
on the segment, differentiable along its interior with derivative `f'`, and the kernels
correspond under the substitution.  The image path is Mathlib's `Path.map'`. -/
theorem curveIntegral_segment_change_of_variables
    {F G f f' : ℂ → ℂ} {a b : ℂ}
    (hf : ContinuousOn f (Set.range ⇑(Path.segment a b)))
    (hderiv : ∀ z ∈ Set.range ⇑(Path.segment a b) \ {a, b}, HasDerivAt f (f' z) z)
    (hlaw : ∀ z ∈ Set.range ⇑(Path.segment a b) \ {a, b}, F z = f' z * G (f z)) :
    (∫ᶜ z in Path.segment a b, scalarOneForm F z)
      = ∫ᶜ z in (Path.segment a b).map' hf, scalarOneForm G z := by
  sorry

/-- Bundled closedness of a one-form on a set: differentiability with continuity up to the
closure, and symmetry of the within-derivative on tangent vectors.  This is a local adapter for
the hypotheses of Mathlib's curve-integral Poincaré lemma, which takes them separately. -/
structure ClosedOneFormOn (ω : ℂ → ℂ →L[ℂ] ℂ) (s : Set ℂ) : Prop where
  diffContOnCl : DiffContOnCl ℝ ω s
  symm : ∀ x ∈ s, ∀ u ∈ tangentConeAt ℝ s x, ∀ v ∈ tangentConeAt ℝ s x,
    fderivWithin ℝ ω s x u v = fderivWithin ℝ ω s x v u

/-- One-way discharge: differentiability with closure continuity of `F` makes its scalar
one-form closed.  The converse is not a target. -/
theorem ClosedOneFormOn.of_diffContOnCl {F : ℂ → ℂ} {s : Set ℂ}
    (hF : DiffContOnCl ℂ F s) : ClosedOneFormOn (scalarOneForm F) s := by
  sorry

/-! ### Finite branch: the Möbius wedge and the signed permutations -/

/-- The Möbius inversion `z ↦ -1/z`. -/
@[expose]
noncomputable def mobiusInv : ℂ → ℂ := fun z => -z⁻¹

@[simp]
theorem mobiusInv_apply (z : ℂ) : mobiusInv z = -z⁻¹ := rfl

theorem hasDerivAt_mobiusInv {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt mobiusInv ((z ^ 2)⁻¹) z := by
  sorry

theorem mobiusInv_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < (mobiusInv z).im := by
  sorry

/-- The wedge: an open convex subset of the upper half-plane whose closure meets the real axis
only at `1`. -/
def wedgeSet : Set ℂ := {z | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im}

theorem isOpen_wedgeSet : IsOpen wedgeSet := by
  sorry

theorem convex_wedgeSet : Convex ℝ wedgeSet := by
  sorry

theorem closure_wedgeSet_inter_real : closure wedgeSet ∩ {z : ℂ | z.im = 0} = {1} := by
  sorry

/-- The left legs of the magic contour: `-1 → -1+i → i`. -/
noncomputable def leftLegs (Ψ : ℂ → ℂ) : ℂ :=
  (∫ᶜ z in Path.segment (-1) (-1 + Complex.I), scalarOneForm Ψ z)
    + ∫ᶜ z in Path.segment (-1 + Complex.I) Complex.I, scalarOneForm Ψ z

/-- The right legs of the magic contour: `1 → 1+i → i`. -/
noncomputable def rightLegs (Ψ : ℂ → ℂ) : ℂ :=
  (∫ᶜ z in Path.segment 1 (1 + Complex.I), scalarOneForm Ψ z)
    + ∫ᶜ z in Path.segment (1 + Complex.I) Complex.I, scalarOneForm Ψ z

/-- Signed contour permutation for a single pair of kernels: under the signed Möbius
transformation law on the upper half-plane, with `Ψ` continuous on the left legs and the
transported one-form closed on the wedge, the left-leg integrals equal the correspondingly
signed right-leg integrals.  Radial families instantiate this statement. -/
theorem perm_leftLegs_eq_smul_rightLegs (sign : MagicFunction.FourierSign)
    {Ψ Ψ' : ℂ → ℂ}
    (hcont : ContinuousOn Ψ
      (segment ℝ (-1) (-1 + Complex.I) ∪ segment ℝ (-1 + Complex.I) Complex.I))
    (hlaw : ∀ z : ℂ, 0 < z.im → Ψ z = sign.scalar * (z ^ 2)⁻¹ * Ψ' (mobiusInv z))
    (hclosed : ClosedOneFormOn (scalarOneForm Ψ') wedgeSet) :
    leftLegs Ψ = sign.scalar * rightLegs Ψ' := by
  sorry

/-! ### Closing deliverable: the generic component Fourier identity -/

/-- The exponential kernel of a contour component at radial parameter `r`. -/
noncomputable def expKernel (g : ℂ → ℂ) (r : ℝ) : ℂ → ℂ :=
  fun z => g z * Complex.exp (Real.pi * Complex.I * (r : ℂ) * z)

/-- Absolute product integrability of the left-leg component integrand: the explicit hypothesis
required to interchange the Fourier integral with the two segment integrals.  Lean's junk value
for a non-integrable integral cannot vacuously satisfy the Fourier identity below. -/
def ComponentIntegrable (k : ℕ) (g : ℂ → ℂ) : Prop :=
  ∀ p : ℂ × ℂ, p ∈ ({(-1, -1 + Complex.I), (-1 + Complex.I, Complex.I)} : Set (ℂ × ℂ)) →
    Integrable
      (fun q : V (2 * k) × ℝ =>
        ‖g (p.1 + q.2 • (p.2 - p.1))‖ *
          Real.exp (-Real.pi * ‖q.1‖ ^ 2 * (p.1 + q.2 • (p.2 - p.1)).im))
      (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))

/-- Generic left/right Fourier identity.  In even dimension `2k`, the Fourier transform of the
radial left-leg component of `g` is computed from explicit hypotheses: absolute product
integrability, continuity of the Gaussian-transformed source kernel on the left legs, the
`r`-free signed Möbius law relating that kernel to `g'`, and closedness of the transported
kernels on the wedge. -/
theorem fourier_leftComponent {k : ℕ} (hk : 0 < k)
    (sign : MagicFunction.FourierSign) {g g' : ℂ → ℂ}
    (hint : ComponentIntegrable k g)
    (hcont : ∀ r : ℝ, 0 ≤ r → ContinuousOn
      (fun z : ℂ =>
        (Complex.I / z) ^ k * g z *
          Complex.exp (Real.pi * Complex.I * (r : ℂ) * mobiusInv z))
      (segment ℝ (-1) (-1 + Complex.I) ∪ segment ℝ (-1 + Complex.I) Complex.I))
    (hlaw : ∀ z : ℂ, 0 < z.im →
      (Complex.I / z) ^ k * g z = sign.scalar * (z ^ 2)⁻¹ * g' (mobiusInv z))
    (hclosed : ∀ r : ℝ, 0 ≤ r →
      ClosedOneFormOn (scalarOneForm (expKernel g' r)) wedgeSet) :
    𝓕 (fun x : V (2 * k) => leftLegs (expKernel g (‖x‖ ^ 2)))
      = fun ξ : V (2 * k) => sign.scalar * rightLegs (expKernel g' (‖ξ‖ ^ 2)) := by
  sorry

/-- The central leg of the magic contour: the segment from `0` to `i`. -/
noncomputable def centralLeg (Ψ : ℂ → ℂ) : ℂ :=
  ∫ᶜ z in Path.segment 0 Complex.I, scalarOneForm Ψ z

/-- The vertical ray of the magic contour, from `i` towards `i∞`. -/
noncomputable def verticalRay (Ψ : ℂ → ℂ) : ℂ :=
  Complex.I * ∫ t in Set.Ioi (1 : ℝ), Ψ (t * Complex.I)

/-- Absolute product integrability of the central-leg component integrand. -/
def CentralIntegrable (k : ℕ) (g : ℂ → ℂ) : Prop :=
  Integrable
    (fun q : V (2 * k) × ℝ =>
      ‖g (q.2 • Complex.I)‖ * Real.exp (-Real.pi * ‖q.1‖ ^ 2 * q.2))
    (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))

/-- Generic central-pair Fourier identity.  The Möbius inversion carries the central segment onto
the vertical ray directly, so no wedge homotopy is required; the transported ray integrability is
an explicit hypothesis. -/
theorem fourier_centralComponent {k : ℕ} (hk : 0 < k)
    (sign : MagicFunction.FourierSign) {g g' : ℂ → ℂ}
    (hint : CentralIntegrable k g)
    (hint' : ∀ r : ℝ, 0 ≤ r → IntegrableOn
      (fun t : ℝ => ‖g' (t * Complex.I)‖ * Real.exp (-Real.pi * r * t)) (Set.Ioi 1))
    (hlaw : ∀ z : ℂ, 0 < z.im →
      (Complex.I / z) ^ k * g z = sign.scalar * (z ^ 2)⁻¹ * g' (mobiusInv z)) :
    𝓕 (fun x : V (2 * k) => centralLeg (expKernel g (‖x‖ ^ 2)))
      = fun ξ : V (2 * k) => sign.scalar * verticalRay (expKernel g' (‖ξ‖ ^ 2)) := by
  sorry

/-- Reversal by Fourier involution and evenness: for integrable even functions and a sign with
square one, `𝓕 F = s • G` implies `𝓕 G = s • F`.  This supplies the right-to-left and
ray-to-central directions of the assembly from the left-to-right and central-to-ray
identities. -/
theorem fourier_reverse {d : ℕ} (sign : MagicFunction.FourierSign) {F G : V d → ℂ}
    (hF : Integrable F) (hG : Integrable G)
    (heven : ∀ x, F (-x) = F x)
    (h : 𝓕 F = fun ξ => sign.scalar * G ξ) :
    𝓕 G = fun ξ => sign.scalar * F ξ := by
  sorry

/-- The full six-piece magic contour component: left legs, right legs, central leg, and vertical
ray, each with its own kernel. -/
noncomputable def sixPieceComponent (k : ℕ) (gL gR gC gRay : ℂ → ℂ) (x : V (2 * k)) : ℂ :=
  leftLegs (expKernel gL (‖x‖ ^ 2)) + rightLegs (expKernel gR (‖x‖ ^ 2))
    + centralLeg (expKernel gC (‖x‖ ^ 2)) + verticalRay (expKernel gRay (‖x‖ ^ 2))

/-- Transparent six-piece assembly: when each piece is integrable and the four piecewise Fourier
identities exchange left with right and central with ray at the common sign, the assembled
component is a Fourier eigenfunction with that sign.  The E8 and Leech components instantiate
this theorem through their characteristic equations; no bundled kernel record and no opaque
constructor stands between them and the contour machinery. -/
theorem fourier_sixPieceComponent {k : ℕ} (hk : 0 < k)
    (sign : MagicFunction.FourierSign) {gL gR gC gRay : ℂ → ℂ}
    (hintL : Integrable (fun x : V (2 * k) => leftLegs (expKernel gL (‖x‖ ^ 2))))
    (hintR : Integrable (fun x : V (2 * k) => rightLegs (expKernel gR (‖x‖ ^ 2))))
    (hintC : Integrable (fun x : V (2 * k) => centralLeg (expKernel gC (‖x‖ ^ 2))))
    (hintRay : Integrable (fun x : V (2 * k) => verticalRay (expKernel gRay (‖x‖ ^ 2))))
    (hLR : 𝓕 (fun x : V (2 * k) => leftLegs (expKernel gL (‖x‖ ^ 2)))
      = fun ξ : V (2 * k) => sign.scalar * rightLegs (expKernel gR (‖ξ‖ ^ 2)))
    (hRL : 𝓕 (fun x : V (2 * k) => rightLegs (expKernel gR (‖x‖ ^ 2)))
      = fun ξ : V (2 * k) => sign.scalar * leftLegs (expKernel gL (‖ξ‖ ^ 2)))
    (hCRay : 𝓕 (fun x : V (2 * k) => centralLeg (expKernel gC (‖x‖ ^ 2)))
      = fun ξ : V (2 * k) => sign.scalar * verticalRay (expKernel gRay (‖ξ‖ ^ 2)))
    (hRayC : 𝓕 (fun x : V (2 * k) => verticalRay (expKernel gRay (‖x‖ ^ 2)))
      = fun ξ : V (2 * k) => sign.scalar * centralLeg (expKernel gC (‖ξ‖ ^ 2))) :
    𝓕 (sixPieceComponent k gL gR gC gRay)
      = fun ξ : V (2 * k) => sign.scalar * sixPieceComponent k gL gR gC gRay ξ := by
  sorry

end Contour

/-! ## Layer 9: dimension-specific magic certificates and strict zero sets -/

namespace E8

/- The final Cohn--Elkies auxiliary function is not a Fourier eigenfunction.  It is the
dimension-specific linear combination below of a `+1` and a `-1` eigenfunction. -/
noncomputable def magicPlusProfile : 𝓢(ℝ, ℂ) := by
  sorry

noncomputable def magicMinusProfile : 𝓢(ℝ, ℂ) := by
  sorry

noncomputable def magicPlus : RadialSchwartzMap ℂ (V 8) ℂ :=
  MagicFunction.ofNormSq magicPlusProfile

noncomputable def magicMinus : RadialSchwartzMap ℂ (V 8) ℂ :=
  MagicFunction.ofNormSq magicMinusProfile

@[simp]
theorem magicPlus_apply (x : V 8) : magicPlus x = magicPlusProfile (‖x‖ ^ 2) :=
  MagicFunction.ofNormSq_apply _ _

@[simp]
theorem magicMinus_apply (x : V 8) : magicMinus x = magicMinusProfile (‖x‖ ^ 2) :=
  MagicFunction.ofNormSq_apply _ _

/-- Kernels of the six-piece contour presentation of the `+1` component.  Production sources are
the `MagicFunction.a` integrals `I₁`–`I₆`: `I₁/I₂` share the left kernel, `I₃/I₄` the right,
`I₅` the central, and `I₆` the ray kernel. -/
noncomputable def plusKernelLeft : ℂ → ℂ := by
  sorry

noncomputable def plusKernelRight : ℂ → ℂ := by
  sorry

noncomputable def plusKernelCentral : ℂ → ℂ := by
  sorry

noncomputable def plusKernelRay : ℂ → ℂ := by
  sorry

/-- Kernels of the six-piece contour presentation of the `-1` component.  Production sources are
the `MagicFunction.b` integrals `J₁`–`J₆`. -/
noncomputable def minusKernelLeft : ℂ → ℂ := by
  sorry

noncomputable def minusKernelRight : ℂ → ℂ := by
  sorry

noncomputable def minusKernelCentral : ℂ → ℂ := by
  sorry

noncomputable def minusKernelRay : ℂ → ℂ := by
  sorry

/-- Characteristic equation of the `+1` component: the profile is the six-piece contour
component of its kernels.  This connects `fourier_magicPlus` to the generic Layer 8 Fourier
identities and forbids an unconnected implementation of the profile. -/
theorem magicPlus_eq_sixPieceComponent (x : V 8) :
    magicPlus x =
      Contour.sixPieceComponent 4 plusKernelLeft plusKernelRight
        plusKernelCentral plusKernelRay x := by
  sorry

/-- Characteristic equation of the `-1` component. -/
theorem magicMinus_eq_sixPieceComponent (x : V 8) :
    magicMinus x =
      Contour.sixPieceComponent 4 minusKernelLeft minusKernelRight
        minusKernelCentral minusKernelRay x := by
  sorry

/-! Concrete facts feeding the `+1` kernels into the generic contour identities. -/

theorem plusKernels_componentIntegrable : Contour.ComponentIntegrable 4 plusKernelLeft := by
  sorry

theorem plusKernels_centralIntegrable : Contour.CentralIntegrable 4 plusKernelCentral := by
  sorry

theorem plusKernels_cont : ∀ r : ℝ, 0 ≤ r → ContinuousOn
    (fun z : ℂ => (Complex.I / z) ^ 4 * plusKernelLeft z *
      Complex.exp (Real.pi * Complex.I * (r : ℂ) * Contour.mobiusInv z))
    (segment ℝ (-1) (-1 + Complex.I) ∪ segment ℝ (-1 + Complex.I) Complex.I) := by
  sorry

theorem plusKernels_law_leftRight : ∀ z : ℂ, 0 < z.im →
    (Complex.I / z) ^ 4 * plusKernelLeft z =
      (MagicFunction.FourierSign.plus).scalar * (z ^ 2)⁻¹ *
        plusKernelRight (Contour.mobiusInv z) := by
  sorry

theorem plusKernels_closed : ∀ r : ℝ, 0 ≤ r →
    Contour.ClosedOneFormOn (Contour.scalarOneForm (Contour.expKernel plusKernelRight r))
      Contour.wedgeSet := by
  sorry

theorem plusKernels_law_centralRay : ∀ z : ℂ, 0 < z.im →
    (Complex.I / z) ^ 4 * plusKernelCentral z =
      (MagicFunction.FourierSign.plus).scalar * (z ^ 2)⁻¹ *
        plusKernelRay (Contour.mobiusInv z) := by
  sorry

theorem plusKernels_rayIntegrable : ∀ r : ℝ, 0 ≤ r → IntegrableOn
    (fun t : ℝ => ‖plusKernelRay (t * Complex.I)‖ * Real.exp (-Real.pi * r * t))
    (Set.Ioi 1) := by
  sorry

theorem plusKernels_integrablePieces :
    Integrable (fun x : V 8 => Contour.leftLegs (Contour.expKernel plusKernelLeft (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 8 => Contour.rightLegs (Contour.expKernel plusKernelRight (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 8 =>
      Contour.centralLeg (Contour.expKernel plusKernelCentral (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 8 =>
      Contour.verticalRay (Contour.expKernel plusKernelRay (‖x‖ ^ 2))) := by
  sorry

/-- Contour Fourier identity for the `+1` kernels: an application of the generic identities with
no independent analytic content. -/
theorem fourier_sixPiece_plus :
    𝓕 (Contour.sixPieceComponent 4 plusKernelLeft plusKernelRight plusKernelCentral
        plusKernelRay)
      = fun ξ : V 8 => (MagicFunction.FourierSign.plus).scalar *
          Contour.sixPieceComponent 4 plusKernelLeft plusKernelRight plusKernelCentral
            plusKernelRay ξ := by
  obtain ⟨hL, hR, hC, hRay⟩ := plusKernels_integrablePieces
  have hLR := Contour.fourier_leftComponent (k := 4) (by norm_num) .plus
    plusKernels_componentIntegrable plusKernels_cont plusKernels_law_leftRight
    plusKernels_closed
  have hCRay := Contour.fourier_centralComponent (k := 4) (by norm_num) .plus
    plusKernels_centralIntegrable plusKernels_rayIntegrable plusKernels_law_centralRay
  have hRL := Contour.fourier_reverse .plus hL hR (fun x => by simp) hLR
  have hRayC := Contour.fourier_reverse .plus hC hRay (fun x => by simp) hCRay
  exact Contour.fourier_sixPieceComponent (by norm_num) .plus hL hR hC hRay hLR hRL hCRay hRayC

/-! Concrete facts feeding the `-1` kernels into the generic contour identities. -/

theorem minusKernels_componentIntegrable : Contour.ComponentIntegrable 4 minusKernelLeft := by
  sorry

theorem minusKernels_centralIntegrable : Contour.CentralIntegrable 4 minusKernelCentral := by
  sorry

theorem minusKernels_cont : ∀ r : ℝ, 0 ≤ r → ContinuousOn
    (fun z : ℂ => (Complex.I / z) ^ 4 * minusKernelLeft z *
      Complex.exp (Real.pi * Complex.I * (r : ℂ) * Contour.mobiusInv z))
    (segment ℝ (-1) (-1 + Complex.I) ∪ segment ℝ (-1 + Complex.I) Complex.I) := by
  sorry

theorem minusKernels_law_leftRight : ∀ z : ℂ, 0 < z.im →
    (Complex.I / z) ^ 4 * minusKernelLeft z =
      (MagicFunction.FourierSign.minus).scalar * (z ^ 2)⁻¹ *
        minusKernelRight (Contour.mobiusInv z) := by
  sorry

theorem minusKernels_closed : ∀ r : ℝ, 0 ≤ r →
    Contour.ClosedOneFormOn (Contour.scalarOneForm (Contour.expKernel minusKernelRight r))
      Contour.wedgeSet := by
  sorry

theorem minusKernels_law_centralRay : ∀ z : ℂ, 0 < z.im →
    (Complex.I / z) ^ 4 * minusKernelCentral z =
      (MagicFunction.FourierSign.minus).scalar * (z ^ 2)⁻¹ *
        minusKernelRay (Contour.mobiusInv z) := by
  sorry

theorem minusKernels_rayIntegrable : ∀ r : ℝ, 0 ≤ r → IntegrableOn
    (fun t : ℝ => ‖minusKernelRay (t * Complex.I)‖ * Real.exp (-Real.pi * r * t))
    (Set.Ioi 1) := by
  sorry

theorem minusKernels_integrablePieces :
    Integrable (fun x : V 8 => Contour.leftLegs (Contour.expKernel minusKernelLeft (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 8 =>
      Contour.rightLegs (Contour.expKernel minusKernelRight (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 8 =>
      Contour.centralLeg (Contour.expKernel minusKernelCentral (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 8 =>
      Contour.verticalRay (Contour.expKernel minusKernelRay (‖x‖ ^ 2))) := by
  sorry

/-- Contour Fourier identity for the `-1` kernels. -/
theorem fourier_sixPiece_minus :
    𝓕 (Contour.sixPieceComponent 4 minusKernelLeft minusKernelRight minusKernelCentral
        minusKernelRay)
      = fun ξ : V 8 => (MagicFunction.FourierSign.minus).scalar *
          Contour.sixPieceComponent 4 minusKernelLeft minusKernelRight minusKernelCentral
            minusKernelRay ξ := by
  obtain ⟨hL, hR, hC, hRay⟩ := minusKernels_integrablePieces
  have hLR := Contour.fourier_leftComponent (k := 4) (by norm_num) .minus
    minusKernels_componentIntegrable minusKernels_cont minusKernels_law_leftRight
    minusKernels_closed
  have hCRay := Contour.fourier_centralComponent (k := 4) (by norm_num) .minus
    minusKernels_centralIntegrable minusKernels_rayIntegrable minusKernels_law_centralRay
  have hRL := Contour.fourier_reverse .minus hL hR (fun x => by simp) hLR
  have hRayC := Contour.fourier_reverse .minus hC hRay (fun x => by simp) hCRay
  exact Contour.fourier_sixPieceComponent (by norm_num) .minus hL hR hC hRay hLR hRL hCRay hRayC

/-- The Fourier eigenfunction identity for the `+1` component is glue: the characteristic
equation, the Schwartz/function Fourier bridge, and the contour Fourier identity. -/
theorem fourier_magicPlus :
    𝓕 (magicPlus : 𝓢(V 8, ℂ)) = (magicPlus : 𝓢(V 8, ℂ)) := by
  have hchar : ⇑((magicPlus : 𝓢(V 8, ℂ))) =
      Contour.sixPieceComponent 4 plusKernelLeft plusKernelRight plusKernelCentral
        plusKernelRay := by
    funext x
    rw [SphereCeti.Pinned.RadialSchwartzMap.coe_coe]
    exact magicPlus_eq_sixPieceComponent x
  ext ξ
  calc (𝓕 (magicPlus : 𝓢(V 8, ℂ))) ξ
      = 𝓕 ((magicPlus : 𝓢(V 8, ℂ)) : V 8 → ℂ) ξ :=
        congrFun (SchwartzMap.fourier_coe _) ξ
    _ = (fun ξ' : V 8 => (MagicFunction.FourierSign.plus).scalar *
          Contour.sixPieceComponent 4 plusKernelLeft plusKernelRight plusKernelCentral
            plusKernelRay ξ') ξ := by rw [hchar, fourier_sixPiece_plus]
    _ = (magicPlus : 𝓢(V 8, ℂ)) ξ := by
        simp only [MagicFunction.FourierSign.scalar_plus, one_mul, ← hchar]

/-- The Fourier eigenfunction identity for the `-1` component, by the same glue. -/
theorem fourier_magicMinus :
    𝓕 (magicMinus : 𝓢(V 8, ℂ)) = -(magicMinus : 𝓢(V 8, ℂ)) := by
  have hchar : ⇑((magicMinus : 𝓢(V 8, ℂ))) =
      Contour.sixPieceComponent 4 minusKernelLeft minusKernelRight minusKernelCentral
        minusKernelRay := by
    funext x
    rw [SphereCeti.Pinned.RadialSchwartzMap.coe_coe]
    exact magicMinus_eq_sixPieceComponent x
  ext ξ
  calc (𝓕 (magicMinus : 𝓢(V 8, ℂ))) ξ
      = 𝓕 ((magicMinus : 𝓢(V 8, ℂ)) : V 8 → ℂ) ξ :=
        congrFun (SchwartzMap.fourier_coe _) ξ
    _ = (fun ξ' : V 8 => (MagicFunction.FourierSign.minus).scalar *
          Contour.sixPieceComponent 4 minusKernelLeft minusKernelRight minusKernelCentral
            minusKernelRay ξ') ξ := by rw [hchar, fourier_sixPiece_minus]
    _ = (-(magicMinus : 𝓢(V 8, ℂ))) ξ := by
        simp only [MagicFunction.FourierSign.scalar_minus, neg_one_mul, ← hchar, neg_apply]

/-- Viazovska's E8 norm-squared profile with the production normalization. -/
noncomputable def magicProfile : 𝓢(ℝ, ℂ) :=
  (((Real.pi : ℂ) * Complex.I) / 8640) • magicPlusProfile -
    (Complex.I / (240 * (Real.pi : ℂ))) • magicMinusProfile

/-- Viazovska's E8 auxiliary function with the production normalization. -/
noncomputable def magic : RadialSchwartzMap ℂ (V 8) ℂ :=
  MagicFunction.ofNormSq magicProfile

@[simp]
theorem magic_apply (x : V 8) : magic x = magicProfile (‖x‖ ^ 2) :=
  MagicFunction.ofNormSq_apply _ _

/-- Norm-squared profile of the distinct Fourier transform. -/
noncomputable def fourierMagicProfile : 𝓢(ℝ, ℂ) :=
  (((Real.pi : ℂ) * Complex.I) / 8640) • magicPlusProfile +
    (Complex.I / (240 * (Real.pi : ℂ))) • magicMinusProfile

/-- Fourier transform of the final auxiliary function, with the minus component sign reversed. -/
theorem fourier_magic : 𝓕 (magic : 𝓢(V 8, ℂ)) =
    (((Real.pi : ℂ) * Complex.I) / 8640) • (magicPlus : 𝓢(V 8, ℂ)) +
      (Complex.I / (240 * (Real.pi : ℂ))) • (magicMinus : 𝓢(V 8, ℂ)) := by
  sorry

@[simp]
theorem fourier_magic_apply_profile (x : V 8) :
    𝓕 (magic : 𝓢(V 8, ℂ)) x = fourierMagicProfile (‖x‖ ^ 2) := by
  sorry

/-- Exact direct-side zeros outside the origin.  Absence of extraneous zeros is the input needed for
periodic uniqueness, not merely for optimal density. -/
theorem magic_zero_iff {x : V 8} (hx : x ≠ 0) :
    magic x = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ ‖x‖ ^ 2 = 2 * n := by
  sorry

/-- The Fourier-side zeros outside the origin are exactly the E8 shell radii. -/
theorem fourier_magic_zero_iff {x : V 8} (hx : x ≠ 0) :
    𝓕 (magic : 𝓢(V 8, ℂ)) x = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ ‖x‖ ^ 2 = 2 * n := by
  sorry

/-- Direct-side nonpositivity beyond the packing threshold. -/
theorem magic_re_nonpos_of_sqrtTwo_le_norm {x : V 8} (hx : Real.sqrt 2 ≤ ‖x‖) :
    (magic x).re ≤ 0 := by
  sorry

/-- Strict negativity away from the shell zeros. -/
theorem magic_re_lt_zero_of_sqrtTwo_le_norm_of_not_shell {x : V 8}
    (hx : Real.sqrt 2 ≤ ‖x‖)
    (hnot : ¬∃ n : ℕ, 1 ≤ n ∧ ‖x‖ ^ 2 = 2 * n) :
    (magic x).re < 0 := by
  sorry

/-- Fourier-side nonnegativity. -/
theorem fourier_magic_re_nonneg (x : V 8) :
    0 ≤ (𝓕 (magic : 𝓢(V 8, ℂ)) x).re := by
  sorry

/-- Fourier-side strict positivity away from the shell zeros. -/
theorem fourier_magic_re_pos_of_not_shell {x : V 8}
    (hnot : ¬∃ n : ℕ, 1 ≤ n ∧ ‖x‖ ^ 2 = 2 * n) :
    0 < (𝓕 (magic : 𝓢(V 8, ℂ)) x).re := by
  sorry

/-- The final direct auxiliary function is real-valued. -/
theorem magic_im_eq_zero (x : V 8) : (magic x).im = 0 := by
  sorry

/-- The distinct Fourier transform is also real-valued. -/
theorem fourier_magic_im_eq_zero (x : V 8) :
    (𝓕 (magic : 𝓢(V 8, ℂ)) x).im = 0 := by
  sorry

/-- The threshold shell is a simple direct-side zero. -/
theorem magicProfile_exactZeroOrder_at_firstShell :
    MagicFunction.HasExactZeroOrder magicProfile 2 1 := by
  sorry

/-- Every later direct-side shell is a double zero. -/
theorem magicProfile_exactZeroOrder_at_laterShell (n : ℕ) (hn : 2 ≤ n) :
    MagicFunction.HasExactZeroOrder magicProfile (2 * n) 2 := by
  sorry

/-- Every nonzero E8 shell is a double Fourier-side zero. -/
theorem fourierMagicProfile_exactZeroOrder (n : ℕ) (hn : 1 ≤ n) :
    MagicFunction.HasExactZeroOrder fourierMagicProfile (2 * n) 2 := by
  sorry

/-- Normalized Cohn--Elkies certificate. -/
@[expose] noncomputable def certificate : CohnElkies.Certificate 8 (Real.sqrt 2) :=
  CohnElkies.Certificate.ofRadial (Real.sqrt_pos.2 (by norm_num)) magic
    magic_im_eq_zero fourier_magic_im_eq_zero
    (fun _ hx => magic_re_nonpos_of_sqrtTwo_le_norm hx) fourier_magic_re_nonneg
    (fourier_magic_re_pos_of_not_shell (by
      rintro ⟨n, hn, hnorm⟩
      norm_num at hnorm
      omega))

@[simp]
theorem certificate_f : certificate.f = (magic : 𝓢(V 8, ℂ)) := by
  simp [certificate]

@[simp]
theorem certificate_normalized : certificate.IsNormalized := by
  sorry

/-- The exact shell zeros make the certificate sharp on the E8 lattice. -/
theorem certificate_isSharpForLattice : certificate.IsSharpForLattice lattice := by
  sorry

/-- The certificate bound equals the E8 density through lattice sharpness. -/
theorem certificate_bound_eq_density : certificate.bound = packing.density := by
  sorry

/-- Density optimality. -/
theorem isOptimal : SpherePackingConstant 8 = packing.density := by
  sorry

end E8

namespace Leech

/- The final Leech auxiliary function is the exact linear combination of the two Fourier
eigencomponents constructed in Sections 2 and 3 of Cohn--Kumar--Miller--Radchenko--Viazovska. -/
noncomputable def magicPlusProfile : 𝓢(ℝ, ℂ) := by
  sorry

noncomputable def magicMinusProfile : 𝓢(ℝ, ℂ) := by
  sorry

noncomputable def magicPlus : RadialSchwartzMap ℂ (V 24) ℂ :=
  MagicFunction.ofNormSq magicPlusProfile

noncomputable def magicMinus : RadialSchwartzMap ℂ (V 24) ℂ :=
  MagicFunction.ofNormSq magicMinusProfile

@[simp]
theorem magicPlus_apply (x : V 24) : magicPlus x = magicPlusProfile (‖x‖ ^ 2) :=
  MagicFunction.ofNormSq_apply _ _

@[simp]
theorem magicMinus_apply (x : V 24) : magicMinus x = magicMinusProfile (‖x‖ ^ 2) :=
  MagicFunction.ofNormSq_apply _ _

/-- Kernels of the six-piece contour presentation of the dimension-24 `+1` component. -/
noncomputable def plusKernelLeft : ℂ → ℂ := by
  sorry

noncomputable def plusKernelRight : ℂ → ℂ := by
  sorry

noncomputable def plusKernelCentral : ℂ → ℂ := by
  sorry

noncomputable def plusKernelRay : ℂ → ℂ := by
  sorry

/-- Kernels of the six-piece contour presentation of the dimension-24 `-1` component. -/
noncomputable def minusKernelLeft : ℂ → ℂ := by
  sorry

noncomputable def minusKernelRight : ℂ → ℂ := by
  sorry

noncomputable def minusKernelCentral : ℂ → ℂ := by
  sorry

noncomputable def minusKernelRay : ℂ → ℂ := by
  sorry

/-- Characteristic equation of the dimension-24 `+1` component. -/
theorem magicPlus_eq_sixPieceComponent (x : V 24) :
    magicPlus x =
      Contour.sixPieceComponent 12 plusKernelLeft plusKernelRight
        plusKernelCentral plusKernelRay x := by
  sorry

/-- Characteristic equation of the dimension-24 `-1` component. -/
theorem magicMinus_eq_sixPieceComponent (x : V 24) :
    magicMinus x =
      Contour.sixPieceComponent 12 minusKernelLeft minusKernelRight
        minusKernelCentral minusKernelRay x := by
  sorry

/-! Concrete facts feeding the dimension-24 kernels into the generic contour identities. -/

theorem plusKernels_componentIntegrable : Contour.ComponentIntegrable 12 plusKernelLeft := by
  sorry

theorem plusKernels_centralIntegrable : Contour.CentralIntegrable 12 plusKernelCentral := by
  sorry

theorem plusKernels_cont : ∀ r : ℝ, 0 ≤ r → ContinuousOn
    (fun z : ℂ => (Complex.I / z) ^ 12 * plusKernelLeft z *
      Complex.exp (Real.pi * Complex.I * (r : ℂ) * Contour.mobiusInv z))
    (segment ℝ (-1) (-1 + Complex.I) ∪ segment ℝ (-1 + Complex.I) Complex.I) := by
  sorry

theorem plusKernels_law_leftRight : ∀ z : ℂ, 0 < z.im →
    (Complex.I / z) ^ 12 * plusKernelLeft z =
      (MagicFunction.FourierSign.plus).scalar * (z ^ 2)⁻¹ *
        plusKernelRight (Contour.mobiusInv z) := by
  sorry

theorem plusKernels_closed : ∀ r : ℝ, 0 ≤ r →
    Contour.ClosedOneFormOn (Contour.scalarOneForm (Contour.expKernel plusKernelRight r))
      Contour.wedgeSet := by
  sorry

theorem plusKernels_law_centralRay : ∀ z : ℂ, 0 < z.im →
    (Complex.I / z) ^ 12 * plusKernelCentral z =
      (MagicFunction.FourierSign.plus).scalar * (z ^ 2)⁻¹ *
        plusKernelRay (Contour.mobiusInv z) := by
  sorry

theorem plusKernels_rayIntegrable : ∀ r : ℝ, 0 ≤ r → IntegrableOn
    (fun t : ℝ => ‖plusKernelRay (t * Complex.I)‖ * Real.exp (-Real.pi * r * t))
    (Set.Ioi 1) := by
  sorry

theorem plusKernels_integrablePieces :
    Integrable (fun x : V 24 => Contour.leftLegs (Contour.expKernel plusKernelLeft (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 24 =>
      Contour.rightLegs (Contour.expKernel plusKernelRight (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 24 =>
      Contour.centralLeg (Contour.expKernel plusKernelCentral (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 24 =>
      Contour.verticalRay (Contour.expKernel plusKernelRay (‖x‖ ^ 2))) := by
  sorry

/-- Contour Fourier identity for the dimension-24 `+1` kernels. -/
theorem fourier_sixPiece_plus :
    𝓕 (Contour.sixPieceComponent 12 plusKernelLeft plusKernelRight plusKernelCentral
        plusKernelRay)
      = fun ξ : V 24 => (MagicFunction.FourierSign.plus).scalar *
          Contour.sixPieceComponent 12 plusKernelLeft plusKernelRight plusKernelCentral
            plusKernelRay ξ := by
  obtain ⟨hL, hR, hC, hRay⟩ := plusKernels_integrablePieces
  have hLR := Contour.fourier_leftComponent (k := 12) (by norm_num) .plus
    plusKernels_componentIntegrable plusKernels_cont plusKernels_law_leftRight
    plusKernels_closed
  have hCRay := Contour.fourier_centralComponent (k := 12) (by norm_num) .plus
    plusKernels_centralIntegrable plusKernels_rayIntegrable plusKernels_law_centralRay
  have hRL := Contour.fourier_reverse .plus hL hR (fun x => by simp) hLR
  have hRayC := Contour.fourier_reverse .plus hC hRay (fun x => by simp) hCRay
  exact Contour.fourier_sixPieceComponent (by norm_num) .plus hL hR hC hRay hLR hRL hCRay hRayC

theorem minusKernels_componentIntegrable : Contour.ComponentIntegrable 12 minusKernelLeft := by
  sorry

theorem minusKernels_centralIntegrable : Contour.CentralIntegrable 12 minusKernelCentral := by
  sorry

theorem minusKernels_cont : ∀ r : ℝ, 0 ≤ r → ContinuousOn
    (fun z : ℂ => (Complex.I / z) ^ 12 * minusKernelLeft z *
      Complex.exp (Real.pi * Complex.I * (r : ℂ) * Contour.mobiusInv z))
    (segment ℝ (-1) (-1 + Complex.I) ∪ segment ℝ (-1 + Complex.I) Complex.I) := by
  sorry

theorem minusKernels_law_leftRight : ∀ z : ℂ, 0 < z.im →
    (Complex.I / z) ^ 12 * minusKernelLeft z =
      (MagicFunction.FourierSign.minus).scalar * (z ^ 2)⁻¹ *
        minusKernelRight (Contour.mobiusInv z) := by
  sorry

theorem minusKernels_closed : ∀ r : ℝ, 0 ≤ r →
    Contour.ClosedOneFormOn (Contour.scalarOneForm (Contour.expKernel minusKernelRight r))
      Contour.wedgeSet := by
  sorry

theorem minusKernels_law_centralRay : ∀ z : ℂ, 0 < z.im →
    (Complex.I / z) ^ 12 * minusKernelCentral z =
      (MagicFunction.FourierSign.minus).scalar * (z ^ 2)⁻¹ *
        minusKernelRay (Contour.mobiusInv z) := by
  sorry

theorem minusKernels_rayIntegrable : ∀ r : ℝ, 0 ≤ r → IntegrableOn
    (fun t : ℝ => ‖minusKernelRay (t * Complex.I)‖ * Real.exp (-Real.pi * r * t))
    (Set.Ioi 1) := by
  sorry

theorem minusKernels_integrablePieces :
    Integrable (fun x : V 24 =>
      Contour.leftLegs (Contour.expKernel minusKernelLeft (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 24 =>
      Contour.rightLegs (Contour.expKernel minusKernelRight (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 24 =>
      Contour.centralLeg (Contour.expKernel minusKernelCentral (‖x‖ ^ 2))) ∧
    Integrable (fun x : V 24 =>
      Contour.verticalRay (Contour.expKernel minusKernelRay (‖x‖ ^ 2))) := by
  sorry

/-- Contour Fourier identity for the dimension-24 `-1` kernels. -/
theorem fourier_sixPiece_minus :
    𝓕 (Contour.sixPieceComponent 12 minusKernelLeft minusKernelRight minusKernelCentral
        minusKernelRay)
      = fun ξ : V 24 => (MagicFunction.FourierSign.minus).scalar *
          Contour.sixPieceComponent 12 minusKernelLeft minusKernelRight minusKernelCentral
            minusKernelRay ξ := by
  obtain ⟨hL, hR, hC, hRay⟩ := minusKernels_integrablePieces
  have hLR := Contour.fourier_leftComponent (k := 12) (by norm_num) .minus
    minusKernels_componentIntegrable minusKernels_cont minusKernels_law_leftRight
    minusKernels_closed
  have hCRay := Contour.fourier_centralComponent (k := 12) (by norm_num) .minus
    minusKernels_centralIntegrable minusKernels_rayIntegrable minusKernels_law_centralRay
  have hRL := Contour.fourier_reverse .minus hL hR (fun x => by simp) hLR
  have hRayC := Contour.fourier_reverse .minus hC hRay (fun x => by simp) hCRay
  exact Contour.fourier_sixPieceComponent (by norm_num) .minus hL hR hC hRay hLR hRL hCRay hRayC

/-- The dimension-24 `+1` eigenfunction identity is glue over the characteristic equation and
the contour Fourier identity. -/
theorem fourier_magicPlus :
    𝓕 (magicPlus : 𝓢(V 24, ℂ)) = (magicPlus : 𝓢(V 24, ℂ)) := by
  have hchar : ((magicPlus : 𝓢(V 24, ℂ)) : V 24 → ℂ) =
      Contour.sixPieceComponent 12 plusKernelLeft plusKernelRight plusKernelCentral
        plusKernelRay := by
    funext x
    rw [SphereCeti.Pinned.RadialSchwartzMap.coe_coe]
    exact magicPlus_eq_sixPieceComponent x
  ext ξ
  calc (𝓕 (magicPlus : 𝓢(V 24, ℂ))) ξ
      = 𝓕 ((magicPlus : 𝓢(V 24, ℂ)) : V 24 → ℂ) ξ :=
        congrFun (SchwartzMap.fourier_coe _) ξ
    _ = (fun ξ' : V 24 => (MagicFunction.FourierSign.plus).scalar *
          Contour.sixPieceComponent 12 plusKernelLeft plusKernelRight plusKernelCentral
            plusKernelRay ξ') ξ := by rw [hchar, fourier_sixPiece_plus]
    _ = (magicPlus : 𝓢(V 24, ℂ)) ξ := by
        simp only [MagicFunction.FourierSign.scalar_plus, one_mul, ← hchar]

/-- The dimension-24 `-1` eigenfunction identity, by the same glue. -/
theorem fourier_magicMinus :
    𝓕 (magicMinus : 𝓢(V 24, ℂ)) = -(magicMinus : 𝓢(V 24, ℂ)) := by
  have hchar : ((magicMinus : 𝓢(V 24, ℂ)) : V 24 → ℂ) =
      Contour.sixPieceComponent 12 minusKernelLeft minusKernelRight minusKernelCentral
        minusKernelRay := by
    funext x
    rw [SphereCeti.Pinned.RadialSchwartzMap.coe_coe]
    exact magicMinus_eq_sixPieceComponent x
  ext ξ
  calc (𝓕 (magicMinus : 𝓢(V 24, ℂ))) ξ
      = 𝓕 ((magicMinus : 𝓢(V 24, ℂ)) : V 24 → ℂ) ξ :=
        congrFun (SchwartzMap.fourier_coe _) ξ
    _ = (fun ξ' : V 24 => (MagicFunction.FourierSign.minus).scalar *
          Contour.sixPieceComponent 12 minusKernelLeft minusKernelRight minusKernelCentral
            minusKernelRay ξ') ξ := by rw [hchar, fourier_sixPiece_minus]
    _ = (-(magicMinus : 𝓢(V 24, ℂ))) ξ := by
        simp only [MagicFunction.FourierSign.scalar_minus, neg_one_mul, ← hchar, neg_apply]

/-- The dimension-24 norm-squared profile with the coefficients from the published proof. -/
noncomputable def magicProfile : 𝓢(ℝ, ℂ) :=
  (-((Real.pi : ℂ) * Complex.I) / 113218560) • magicPlusProfile -
    (Complex.I / (262080 * (Real.pi : ℂ))) • magicMinusProfile

/-- The dimension-24 auxiliary function, with the coefficients from the published proof. -/
noncomputable def magic : RadialSchwartzMap ℂ (V 24) ℂ :=
  MagicFunction.ofNormSq magicProfile

@[simp]
theorem magic_apply (x : V 24) : magic x = magicProfile (‖x‖ ^ 2) :=
  MagicFunction.ofNormSq_apply _ _

/-- Norm-squared profile of the distinct Fourier transform. -/
noncomputable def fourierMagicProfile : 𝓢(ℝ, ℂ) :=
  (-((Real.pi : ℂ) * Complex.I) / 113218560) • magicPlusProfile +
    (Complex.I / (262080 * (Real.pi : ℂ))) • magicMinusProfile

/-- Fourier transform of the final auxiliary function, with the minus component sign reversed. -/
theorem fourier_magic : 𝓕 (magic : 𝓢(V 24, ℂ)) =
    (-((Real.pi : ℂ) * Complex.I) / 113218560) • (magicPlus : 𝓢(V 24, ℂ)) +
      (Complex.I / (262080 * (Real.pi : ℂ))) • (magicMinus : 𝓢(V 24, ℂ)) := by
  sorry

@[simp]
theorem fourier_magic_apply_profile (x : V 24) :
    𝓕 (magic : 𝓢(V 24, ℂ)) x = fourierMagicProfile (‖x‖ ^ 2) := by
  sorry

/-- Exact zero set outside the origin: squared norms `2n` for `n ≥ 2`. -/
theorem magic_zero_iff {x : V 24} (hx : x ≠ 0) :
    magic x = 0 ↔ ∃ n : ℕ, 2 ≤ n ∧ ‖x‖ ^ 2 = 2 * n := by
  sorry

/-- The Fourier-side zeros outside the origin are exactly the Leech shell radii. -/
theorem fourier_magic_zero_iff {x : V 24} (hx : x ≠ 0) :
    𝓕 (magic : 𝓢(V 24, ℂ)) x = 0 ↔ ∃ n : ℕ, 2 ≤ n ∧ ‖x‖ ^ 2 = 2 * n := by
  sorry

/-- Direct-side nonpositivity beyond the packing threshold. -/
theorem magic_re_nonpos_of_two_le_norm {x : V 24} (hx : 2 ≤ ‖x‖) :
    (magic x).re ≤ 0 := by
  sorry

/-- Strict negativity away from shell zeros. -/
theorem magic_re_lt_zero_of_two_le_norm_of_not_shell {x : V 24}
    (hx : 2 ≤ ‖x‖)
    (hnot : ¬∃ n : ℕ, 2 ≤ n ∧ ‖x‖ ^ 2 = 2 * n) :
    (magic x).re < 0 := by
  sorry

/-- Fourier-side nonnegativity. -/
theorem fourier_magic_re_nonneg (x : V 24) :
    0 ≤ (𝓕 (magic : 𝓢(V 24, ℂ)) x).re := by
  sorry

/-- Fourier-side strict positivity away from the shell zeros. -/
theorem fourier_magic_re_pos_of_not_shell {x : V 24}
    (hnot : ¬∃ n : ℕ, 2 ≤ n ∧ ‖x‖ ^ 2 = 2 * n) :
    0 < (𝓕 (magic : 𝓢(V 24, ℂ)) x).re := by
  sorry

/-- The final direct auxiliary function is real-valued. -/
theorem magic_im_eq_zero (x : V 24) : (magic x).im = 0 := by
  sorry

/-- The distinct Fourier transform is also real-valued. -/
theorem fourier_magic_im_eq_zero (x : V 24) :
    (𝓕 (magic : 𝓢(V 24, ℂ)) x).im = 0 := by
  sorry

/-- The threshold shell is a simple direct-side zero. -/
theorem magicProfile_exactZeroOrder_at_firstShell :
    MagicFunction.HasExactZeroOrder magicProfile 4 1 := by
  sorry

/-- Every later direct-side shell is a double zero. -/
theorem magicProfile_exactZeroOrder_at_laterShell (n : ℕ) (hn : 3 ≤ n) :
    MagicFunction.HasExactZeroOrder magicProfile (2 * n) 2 := by
  sorry

/-- Every nonzero Leech shell is a double Fourier-side zero. -/
theorem fourierMagicProfile_exactZeroOrder (n : ℕ) (hn : 2 ≤ n) :
    MagicFunction.HasExactZeroOrder fourierMagicProfile (2 * n) 2 := by
  sorry

@[expose] noncomputable def certificate : CohnElkies.Certificate 24 2 :=
  CohnElkies.Certificate.ofRadial (by norm_num) magic
    magic_im_eq_zero fourier_magic_im_eq_zero
    (fun _ hx => magic_re_nonpos_of_two_le_norm hx) fourier_magic_re_nonneg
    (fourier_magic_re_pos_of_not_shell (by
      rintro ⟨n, hn, hnorm⟩
      norm_num at hnorm
      omega))

@[simp]
theorem certificate_f : certificate.f = (magic : 𝓢(V 24, ℂ)) := by
  simp [certificate]

@[simp]
theorem certificate_normalized : certificate.IsNormalized := by
  sorry

/-- The exact shell zeros make the certificate sharp on the Leech lattice. -/
theorem certificate_isSharpForLattice : certificate.IsSharpForLattice lattice := by
  sorry

/-- The certificate bound equals the Leech density through lattice sharpness. -/
theorem certificate_bound_eq_density : certificate.bound = packing.density := by
  sorry

/-- Density optimality. -/
theorem isOptimal : SpherePackingConstant 24 = packing.density := by
  sorry

end Leech

/-! ## Layer 10: equality, rigidity, and uniqueness among periodic packings -/

namespace Rigidity

/-- Every nonzero pairwise difference has an allowed E8 squared distance. -/
def HasE8DistanceSpectrum (P : SpherePacking 8) : Prop :=
  ∀ x ∈ P.centers, ∀ y ∈ P.centers, x ≠ y →
    ∃ n : ℕ, 1 ≤ n ∧ ‖x - y‖ ^ 2 = 2 * n

/-- Every nonzero pairwise difference has an allowed Leech squared distance. -/
def HasLeechDistanceSpectrum (P : SpherePacking 24) : Prop :=
  ∀ x ∈ P.centers, ∀ y ∈ P.centers, x ≠ y →
    ∃ n : ℕ, 2 ≤ n ∧ ‖x - y‖ ^ 2 = 2 * n

/-- Equality in the E8 Cohn--Elkies bound forces the full distance spectrum. -/
theorem e8_distanceSpectrum_of_optimalPeriodic
    (P : PeriodicSpherePacking 8)
    (hsep : P.separation = Real.sqrt 2)
    (hopt : P.density = E8.packing.density) :
    HasE8DistanceSpectrum P.toSpherePacking := by
  sorry

/-- Equality in the Leech bound forces its full distance spectrum. -/
theorem leech_distanceSpectrum_of_optimalPeriodic
    (P : PeriodicSpherePacking 24)
    (hsep : P.separation = 2)
    (hopt : P.density = Leech.packing.density) :
    HasLeechDistanceSpectrum P.toSpherePacking := by
  sorry

/-- Polarization turns even squared norms of all differences into integral inner products after
translation by a center. -/
theorem integral_inner_of_even_distanceSpectrum {d : ℕ} (X : Set (V d)) (x₀ : V d)
    (hx₀ : x₀ ∈ X)
    (heven : ∀ x ∈ X, ∀ y ∈ X, ∃ n : ℤ, ‖x - y‖ ^ 2 = 2 * n) :
    ∀ x ∈ X, ∀ y ∈ X, ∃ n : ℤ, ⟪x - x₀, y - x₀⟫_ℝ = n := by
  sorry

/-- The subgroup generated by a translated optimal periodic pattern is a full integral Euclidean
lattice. -/
def generatedIntegralLattice {d : ℕ} (P : PeriodicSpherePacking d)
    (x₀ : V d) : Submodule ℤ (V d) :=
  EuclideanLattice.generatedSubmodule ((fun x => x - x₀) '' P.centers)

/-- The translated periodic center set is contained in its generated subgroup. -/
theorem translated_centers_subset_generatedIntegralLattice {d : ℕ}
    (P : PeriodicSpherePacking d) (x₀ : V d) :
    (fun x => x - x₀) '' P.centers ⊆ generatedIntegralLattice P x₀ := by
  sorry

/-- Cohn--Elkies Lemma 8.2 in API form.  A full-dimensional set containing zero whose pairwise
squared distances are even integers generates a discrete full-rank even integral lattice.  The
period lattice of a periodic packing supplies the full-dimensionality hypothesis. -/
theorem generatedIntegralLattice_evenIntegral_full {d : ℕ}
    (P : PeriodicSpherePacking d) (x₀ : V d) (hx₀ : x₀ ∈ P.centers)
    (heven : ∀ x ∈ P.centers, ∀ y ∈ P.centers,
      ∃ n : ℤ, ‖x - y‖ ^ 2 = 2 * n) :
    ∃ (_ : DiscreteTopology (generatedIntegralLattice P x₀))
      (_ : IsZLattice ℝ (generatedIntegralLattice P x₀))
      (G : EuclideanLattice.IntegralPresentation
        (generatedIntegralLattice P x₀)),
      G.IsEven := by
  sorry

/-- The original period lattice is contained in the subgroup generated by a translated periodic
center set: translating a center by a period produces another center. -/
theorem periodLattice_le_generatedIntegralLattice {d : ℕ}
    (P : PeriodicSpherePacking d) (x₀ : V d) (hx₀ : x₀ ∈ P.centers) :
    P.lattice ≤ generatedIntegralLattice P x₀ := by
  sorry

/-- Quotient of a larger additive lattice by the relative subgroup cut out by a smaller one. -/
abbrev RelativeQuotient {d : ℕ} (Λ Γ : Submodule ℤ (V d)) :=
  Γ.toAddSubgroup ⧸ Λ.toAddSubgroup.addSubgroupOf Γ.toAddSubgroup

/-- Relative quotients of full Euclidean lattices are finite. -/
noncomputable instance relativeQuotientFinite {d : ℕ}
    (Λ Γ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    [DiscreteTopology Γ] [IsZLattice ℝ Γ] : Finite (RelativeQuotient Λ Γ) := by
  sorry

/-- A center orbit maps to the coset of its translate in the generated lattice. -/
noncomputable def orbitEmbeddingGeneratedQuotient {d : ℕ}
    (P : PeriodicSpherePacking d) (x₀ : V d) (hx₀ : x₀ ∈ P.centers) :
    P.Orbit ↪ RelativeQuotient P.lattice (generatedIntegralLattice P x₀) := by
  sorry

/-- Characteristic equation for the orbit-to-relative-quotient embedding. -/
theorem orbitEmbeddingGeneratedQuotient_mk {d : ℕ}
    (P : PeriodicSpherePacking d) (x₀ : V d) (hx₀ : x₀ ∈ P.centers)
    (s : P.centers) :
    ∃ g : generatedIntegralLattice P x₀,
      (g : V d) = (s : V d) - x₀ ∧
      orbitEmbeddingGeneratedQuotient P x₀ hx₀ (Quotient.mk _ s) =
        QuotientAddGroup.mk'
          (P.lattice.toAddSubgroup.addSubgroupOf
            (generatedIntegralLattice P x₀).toAddSubgroup) g := by
  sorry

/-- Distinct center orbits inject into the now-finite relative quotient. -/
theorem numOrbits_le_relIndex_generated {d : ℕ}
    (P : PeriodicSpherePacking d) (x₀ : V d) (hx₀ : x₀ ∈ P.centers)
    [DiscreteTopology (generatedIntegralLattice P x₀)]
    [IsZLattice ℝ (generatedIntegralLattice P x₀)] :
    P.numOrbits ≤ P.lattice.toAddSubgroup.relIndex
      (generatedIntegralLattice P x₀).toAddSubgroup := by
  sorry

/-- The covolume/index step is exactly Mathlib's correctly oriented theorem. -/
theorem covolume_div_covolume_eq_relIndex_generated {d : ℕ}
    (P : PeriodicSpherePacking d) (x₀ : V d)
    [DiscreteTopology (generatedIntegralLattice P x₀)]
    [IsZLattice ℝ (generatedIntegralLattice P x₀)]
    (hle : P.lattice ≤ generatedIntegralLattice P x₀) :
    ZLattice.covolume P.lattice /
        ZLattice.covolume (generatedIntegralLattice P x₀) =
      P.lattice.toAddSubgroup.relIndex
        (generatedIntegralLattice P x₀).toAddSubgroup :=
  ZLattice.covolume_div_covolume_eq_relIndex' _ _ hle

/-- A full integral Euclidean lattice has covolume at least one: the square of its covolume is the
absolute value of a nonzero integer Gram determinant.  This lemma packages the real/TauCeti bridge
needed by the uniqueness proof. -/
theorem one_le_covolume_of_integralPresentation {d : ℕ}
    (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (G : EuclideanLattice.IntegralPresentation Λ) :
    1 ≤ ZLattice.covolume Λ := by
  sorry

/-- The candidate normalization has one canonical center orbit per unit covolume. -/
def HasUnitCenterDensity {d : ℕ} (P : PeriodicSpherePacking d) : Prop :=
  P.centerIntensity = 1

/-- Positivity of lattice covolume converts unit intensity to the cross-multiplied identity used
by the quotient/index squeeze. -/
theorem hasUnitCenterDensity_iff_covolume_eq_numOrbits {d : ℕ}
    (P : PeriodicSpherePacking d) :
    HasUnitCenterDensity P ↔ ZLattice.covolume P.lattice = P.numOrbits := by
  sorry

/-- Optimal E8 density at separation `√2` is equivalent to one center per unit volume. -/
theorem e8_hasUnitCenterDensity_of_optimal
    (P : PeriodicSpherePacking 8)
    (hsep : P.separation = Real.sqrt 2)
    (hopt : P.density = E8.packing.density) :
    HasUnitCenterDensity P := by
  sorry

/-- Optimal Leech density at separation `2` is equivalent to one center per unit volume. -/
theorem leech_hasUnitCenterDensity_of_optimal
    (P : PeriodicSpherePacking 24)
    (hsep : P.separation = 2)
    (hopt : P.density = Leech.packing.density) :
    HasUnitCenterDensity P := by
  sorry

/-- Cohn--Elkies' covolume/index squeeze.  An optimal unit-center-density pattern contained in a
full integral generated lattice has generated covolume one, and the quotient index is exactly the
number of pattern representatives. -/
theorem generated_covolume_eq_one_and_index_eq_numOrbits {d : ℕ}
    (P : PeriodicSpherePacking d) (x₀ : V d) (hx₀ : x₀ ∈ P.centers)
    (_ : DiscreteTopology (generatedIntegralLattice P x₀))
    (_ : IsZLattice ℝ (generatedIntegralLattice P x₀))
    (G : EuclideanLattice.IntegralPresentation (generatedIntegralLattice P x₀))
    (hunit : HasUnitCenterDensity P) :
    ZLattice.covolume (generatedIntegralLattice P x₀) = 1 ∧
      P.lattice.toAddSubgroup.relIndex
        (generatedIntegralLattice P x₀).toAddSubgroup = P.numOrbits := by
  sorry

/-- Equality of quotient cardinalities says every generated-lattice coset is represented by a
center.  Consequently the translated periodic center set is the entire generated lattice. -/
theorem translated_centers_eq_generatedIntegralLattice {d : ℕ}
    (P : PeriodicSpherePacking d) (x₀ : V d) (hx₀ : x₀ ∈ P.centers)
    (hindex : P.lattice.toAddSubgroup.relIndex
      (generatedIntegralLattice P x₀).toAddSubgroup = P.numOrbits) :
    (fun x => x - x₀) '' P.centers =
      (generatedIntegralLattice P x₀ : Set (V d)) := by
  sorry

/-- Once the center set has been identified with the generated lattice, the original packing
separation applies to every nonzero lattice vector.  This is deliberately downstream of the
covolume/index argument; evenness alone would not supply the Leech minimum norm. -/
theorem generated_minNorm_of_centers_eq {d : ℕ}
    (P : PeriodicSpherePacking d) (x₀ : V d) (hx₀ : x₀ ∈ P.centers)
    (hcenters : (fun x => x - x₀) '' P.centers =
      (generatedIntegralLattice P x₀ : Set (V d))) :
    ∀ x : generatedIntegralLattice P x₀,
      x ≠ 0 → P.separation ≤ ‖(x : V d)‖ := by
  sorry

/-- The E8 equality conditions produce a positive-definite even unimodular rank-eight integral
presentation of the generated lattice and show that all centers form one lattice coset. -/
theorem e8_reduction_to_evenUnimodular
    (P : PeriodicSpherePacking 8)
    (hsep : P.separation = Real.sqrt 2)
    (hopt : P.density = E8.packing.density) :
    ∃ (Λ : Submodule ℤ (V 8)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (G : EuclideanLattice.IntegralPresentation Λ) (v : V 8),
      G.IsEven ∧ G.IsUnimodular ∧ P.centers = v +ᵥ (Λ : Set (V 8)) := by
  sorry

/-- The Leech equality conditions produce a rootless positive-definite even unimodular rank-24
lattice and one lattice coset. -/
theorem leech_reduction_to_rootless_evenUnimodular
    (P : PeriodicSpherePacking 24)
    (hsep : P.separation = 2)
    (hopt : P.density = Leech.packing.density) :
    ∃ (Λ : Submodule ℤ (V 24)) (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ)
      (G : EuclideanLattice.IntegralPresentation Λ) (v : V 24),
      G.IsEven ∧ G.IsUnimodular ∧ EuclideanLattice.MinNormSqAtLeast Λ 4 ∧
        P.centers = v +ᵥ (Λ : Set (V 24)) := by
  sorry

end Rigidity

namespace E8

/-- Viazovska's uniqueness conclusion: E8 is the unique optimal periodic packing up to similarity.
There is deliberately no uniqueness statement over all packings, since finite defects do not change
upper density. -/
theorem uniqueOptimalPeriodic (P : PeriodicSpherePacking 8)
    (hopt : P.density = SpherePackingConstant 8) :
    SpherePacking.IsSimilar P.toSpherePacking packing.toSpherePacking := by
  sorry

/-- Lattice-packing uniqueness as a corollary. -/
theorem uniqueOptimalLattice
    (Λ : Submodule ℤ (V 8)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ x : Λ, x ≠ 0 → r ≤ ‖(x : V 8)‖)
    (hopt : (PeriodicSpherePacking.ofZLattice Λ r hr hsep).density = SpherePackingConstant 8) :
    SpherePacking.IsSimilar (PeriodicSpherePacking.ofZLattice Λ r hr hsep).toSpherePacking
      packing.toSpherePacking := by
  sorry

end E8

namespace Leech

/-- The Leech lattice is the unique optimal periodic packing up to similarity. -/
theorem uniqueOptimalPeriodic (P : PeriodicSpherePacking 24)
    (hopt : P.density = SpherePackingConstant 24) :
    SpherePacking.IsSimilar P.toSpherePacking packing.toSpherePacking := by
  sorry

/-- Lattice-packing uniqueness as a corollary. -/
theorem uniqueOptimalLattice
    (Λ : Submodule ℤ (V 24)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ x : Λ, x ≠ 0 → r ≤ ‖(x : V 24)‖)
    (hopt : (PeriodicSpherePacking.ofZLattice Λ r hr hsep).density = SpherePackingConstant 24) :
    SpherePacking.IsSimilar (PeriodicSpherePacking.ofZLattice Λ r hr hsep).toSpherePacking
      packing.toSpherePacking := by
  sorry

end Leech

/-! ## Layer 11: literal summit theorems -/

theorem spherePackingConstant_eight :
    SpherePackingConstant 8 = ENNReal.ofReal (Real.pi ^ 4 / 384) := by
  rw [E8.isOptimal, E8.packing_density]

theorem spherePackingConstant_twentyFour :
    SpherePackingConstant 24 = ENNReal.ofReal (Real.pi ^ 12 / Nat.factorial 12) := by
  rw [Leech.isOptimal, Leech.packing_density]

end

end SphereCeti.Suggested
