/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Pinned

public import TauCeti.Analysis.Complex.UpperHalfPlane.ResToImagAxis
public import TauCeti.Analysis.Contour.Cauchy.Goursat
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
#check TauCeti.Contour.circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg
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
def dual {d : ℕ} (Λ : Submodule ℤ (V d)) : Submodule ℤ (V d) :=
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

/-- Finite representatives for the center orbits modulo the period lattice. -/
structure FundamentalPattern {d : ℕ} (P : PeriodicSpherePacking d) where
  reps : Finset P.centers
  covers : ∀ x : P.centers, ∃ z : P.lattice, ∃ s ∈ reps,
    (x : V d) = (z : V d) + (s : V d)
  unique_mod_lattice : ∀ s ∈ reps, ∀ t ∈ reps,
    (s : V d) - (t : V d) ∈ P.lattice → s = t

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

/-- Every chosen fundamental pattern has the canonical orbit cardinality. -/
theorem FundamentalPattern.card_eq_numOrbits {d : ℕ} {P : PeriodicSpherePacking d}
    (D : FundamentalPattern P) : D.reps.card = P.numOrbits := by
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

namespace Poisson

/-- Shifted Poisson summation in the repository's Fourier and Haar normalizations. -/
theorem shifted {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : 𝓢(V d, ℂ)) (a : V d) :
    ∑' x : Λ, f ((x : V d) + a) =
      ((ZLattice.covolume Λ : ℂ)⁻¹) * ∑' y : EuclideanLattice.dual Λ,
        𝓕 f (y : V d) *
          Complex.exp (2 * Real.pi * Complex.I * ⟪(y : V d), a⟫_ℝ) := by
  sorry

/-- Unshifted Poisson summation. -/
theorem unshifted {d : ℕ} (Λ : Submodule ℤ (V d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : 𝓢(V d, ℂ)) :
    ∑' x : Λ, f (x : V d) =
      ((ZLattice.covolume Λ : ℂ)⁻¹) *
        ∑' y : EuclideanLattice.dual Λ, 𝓕 f (y : V d) := by
  sorry

/-- Unit-Gaussian acceptance test for the Fourier and covolume normalization. -/
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

/-- The finite complex Fourier amplitude of a periodic pattern. -/
def structureAmplitude {d : ℕ} {P : PeriodicSpherePacking d}
    (D : P.FundamentalPattern) (y : V d) : ℂ :=
  ∑ s ∈ D.reps, Complex.exp (2 * Real.pi * Complex.I * ⟪y, s⟫_ℝ)

/-- Changing an orbit representative by a period does not change its phase at a dual frequency. -/
theorem phase_eq_of_sub_mem_lattice {d : ℕ} {P : PeriodicSpherePacking d}
    (y : EuclideanLattice.dual P.lattice) (s t : P.centers)
    (hst : (s : V d) - (t : V d) ∈ P.lattice) :
    Complex.exp (2 * Real.pi * Complex.I * ⟪(y : V d), (s : V d)⟫_ℝ) =
      Complex.exp (2 * Real.pi * Complex.I * ⟪(y : V d), (t : V d)⟫_ℝ) := by
  sorry

/-- The nonnegative real structure factor is the squared norm of the amplitude. -/
@[expose] def structureFactor {d : ℕ} {P : PeriodicSpherePacking d}
    (D : P.FundamentalPattern) (y : V d) : ℝ :=
  ‖structureAmplitude D y‖ ^ 2

theorem structureFactor_nonneg {d : ℕ} {P : PeriodicSpherePacking d}
    (D : P.FundamentalPattern) (y : V d) : 0 ≤ structureFactor D y :=
  sq_nonneg _

theorem structureFactor_eq_zero_iff {d : ℕ} {P : PeriodicSpherePacking d}
    (D : P.FundamentalPattern) (y : V d) :
    structureFactor D y = 0 ↔ structureAmplitude D y = 0 := by
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

/-- A chosen fundamental pattern computes the canonical orbit structure factor. -/
theorem structureFactor_eq_orbitStructureFactor {d : ℕ} {P : PeriodicSpherePacking d}
    (D : P.FundamentalPattern) (y : EuclideanLattice.dual P.lattice) :
    structureFactor D (y : V d) = orbitStructureFactor P y := by
  sorry

/-- Summing shifted Poisson over a finite pattern produces the squared structure amplitude. -/
theorem poisson_finitePattern {d : ℕ} {P : PeriodicSpherePacking d}
    (D : P.FundamentalPattern) (f : 𝓢(V d, ℂ)) :
    ∑' z : P.lattice, ∑ s ∈ D.reps, ∑ t ∈ D.reps,
        f ((z : V d) + (s : V d) - (t : V d)) =
      ((ZLattice.covolume P.lattice : ℂ)⁻¹) *
        ∑' y : EuclideanLattice.dual P.lattice,
          𝓕 f (y : V d) * (structureFactor D (y : V d) : ℂ) := by
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

/-- Negative of the nontrivial direct-side sum. -/
noncomputable def directDefect {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d) (D : P.FundamentalPattern) : ℝ :=
  -∑' z : P.lattice, ∑ s ∈ D.reps, ∑ t ∈ D.reps,
    if (z : V d) + (s : V d) - (t : V d) = 0 then 0
    else (C.f ((z : V d) + (s : V d) - (t : V d))).re

/-- Nonzero-frequency Fourier contribution. -/
noncomputable def fourierDefect {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d) (D : P.FundamentalPattern) : ℝ :=
  (ZLattice.covolume P.lattice)⁻¹ *
    ∑' y : EuclideanLattice.dual P.lattice,
      if y = 0 then 0
      else (𝓕 C.f (y : V d)).re * structureFactor D (y : V d)

theorem directDefect_nonneg {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d) (D : P.FundamentalPattern)
    (hsep : r = P.separation) : 0 ≤ directDefect C P D := by
  sorry

theorem fourierDefect_nonneg {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d) (D : P.FundamentalPattern) :
    0 ≤ fourierDefect C P D := by
  sorry

/-- Exact real-valued equality behind the periodic Cohn--Elkies bound. -/
theorem defect_identity {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d) (D : P.FundamentalPattern) :
    (P.numOrbits : ℝ) * (C.f 0).re -
        (P.numOrbits : ℝ) ^ 2 / ZLattice.covolume P.lattice *
          (𝓕 C.f 0).re =
      fourierDefect C P D + directDefect C P D := by
  sorry

/-- The center-intensity gap is the sum of the two nonnegative defects. -/
theorem normalized_gap_eq_defects {d : ℕ} {r : ℝ} (C : Certificate d r)
    (P : PeriodicSpherePacking d) (D : P.FundamentalPattern)
    (horbits : 0 < P.numOrbits) :
    (C.f 0).re / (𝓕 C.f 0).re -
        (P.numOrbits : ℝ) / ZLattice.covolume P.lattice =
      (fourierDefect C P D + directDefect C P D) /
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

namespace Theta

/-- The analytic convention is `Σ exp(π i τ ‖x‖²)`. -/
def latticeTheta {d : ℕ} (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ]
    (τ : UpperHalfPlane) : ℂ :=
  ∑' x : Λ,
    Complex.exp (Real.pi * Complex.I * (τ : ℂ) * (‖(x : V d)‖ ^ 2 : ℂ))

/-- Normal convergence and holomorphy on the upper half-plane. -/
theorem latticeTheta_mDifferentiable {d : ℕ}
    (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (latticeTheta Λ) := by
  sorry

/-- The q-expansion of an even integral presentation.  Here `q = exp(2πiτ)` and coefficient `n`
counts squared norm `2n`. -/
theorem latticeTheta_qExpansion_of_even {d : ℕ}
    (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ) (heven : P.IsEven)
    (τ : UpperHalfPlane) :
    latticeTheta Λ τ =
      ∑' n : ℕ, (EuclideanLattice.thetaEvenCoeff Λ n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ)) := by
  sorry

/-- Even squared norms give invariance under the modular translation `T`. -/
theorem latticeTheta_T_transform_of_even {d : ℕ}
    (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ) (heven : P.IsEven)
    (τ : UpperHalfPlane) :
    latticeTheta Λ (ModularGroup.T • τ) = latticeTheta Λ τ := by
  sorry

/-- Poisson summation gives the dual-lattice S-transformation. -/
theorem latticeTheta_S_transform {k : ℕ}
    (Λ : Submodule ℤ (V (2 * k))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (τ : UpperHalfPlane) :
    latticeTheta Λ (ModularGroup.S • τ) =
      (((τ : ℂ) / Complex.I) ^ k / ZLattice.covolume Λ) *
        latticeTheta (EuclideanLattice.dual Λ) τ := by
  sorry

/-- Unimodularity specializes the dual/covolume formula to the level-one `S` law. -/
theorem latticeTheta_S_transform_of_unimodular {k : ℕ}
    (Λ : Submodule ℤ (V (8 * k))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ) (hunimodular : P.IsUnimodular)
    (τ : UpperHalfPlane) :
    latticeTheta Λ (ModularGroup.S • τ) =
      ((τ : ℂ) / Complex.I) ^ (4 * k) * latticeTheta Λ τ := by
  sorry

/-- For an even unimodular lattice in dimensions divisible by eight, theta is a level-one modular
form of weight half the rank. -/
noncomputable def latticeThetaModularForm {k : ℕ}
    (Λ : Submodule ℤ (V (8 * k))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    ModularForm 𝒮ℒ (4 * k) := by
  sorry

@[simp]
theorem coe_latticeThetaModularForm {k : ℕ}
    (Λ : Submodule ℤ (V (8 * k))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    ⇑(latticeThetaModularForm Λ P heven hunimodular) = latticeTheta Λ := by
  sorry

/-- The theta modular form has constant coefficient one. -/
theorem latticeThetaModularForm_qExpansion_coeff_zero {k : ℕ}
    (Λ : Submodule ℤ (V (8 * k))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    (UpperHalfPlane.qExpansion 1
      (latticeThetaModularForm Λ P heven hunimodular)).coeff 0 = 1 := by
  sorry

/-- The first nonconstant coefficient counts the squared-norm-two shell. -/
theorem latticeThetaModularForm_qExpansion_coeff_one {k : ℕ}
    (Λ : Submodule ℤ (V (8 * k))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    (UpperHalfPlane.qExpansion 1
      (latticeThetaModularForm Λ P heven hunimodular)).coeff 1 =
        EuclideanLattice.thetaEvenCoeff Λ 1 := by
  sorry

/-- The normalized weight-four Eisenstein series used in the E8 identity. -/
noncomputable def E4 : ModularForm 𝒮ℒ 4 := ModularForm.E₄

/-- The cube of `E4`, cast to its canonical weight-twelve structured type. -/
noncomputable def E4Cubed : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by norm_num) (E4.pow 3)

@[simp]
theorem E4Cubed_apply (τ : UpperHalfPlane) : E4Cubed τ = (E4 τ) ^ 3 := by
  change (E4.pow 3) τ = (E4 τ) ^ 3
  exact congrFun (ModularForm.coe_pow E4 3) τ

/-- The discriminant viewed in the same structured weight-twelve space as `E4Cubed`. -/
noncomputable def Delta : ModularForm 𝒮ℒ 12 :=
  (CuspForm.discriminant : ModularForm 𝒮ℒ 12)

@[simp]
theorem Delta_apply (τ : UpperHalfPlane) : Delta τ = ModularForm.discriminant τ := by
  simp [Delta, CuspForm.coe_discriminant]

/-- Weight-four level-one modular forms are scalar multiples of `E4`. -/
theorem weight_four_eq_constant_mul_E4 (F : ModularForm 𝒮ℒ 4) :
    ∃ a : ℂ, F = a • E4 := by
  sorry

/-- Weight-twelve level-one modular forms are linear combinations of `E4^3` and `Delta`. -/
theorem weight_twelve_eq_a_mul_E4_cubed_add_b_mul_Delta
    (F : ModularForm 𝒮ℒ 12) :
    ∃ a b : ℂ, F = a • E4Cubed + b • Delta := by
  sorry

/-- Root count, i.e. the squared-norm-two shell cardinality. -/
def rootCard {d : ℕ} (Λ : Submodule ℤ (V d)) [DiscreteTopology Λ] : ℕ :=
  EuclideanLattice.thetaEvenCoeff Λ 1

/-- Every even unimodular rank-eight theta series is E4. -/
theorem theta_eq_E4_of_even_unimodular
    (Λ : Submodule ℤ (V 8)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    latticeTheta Λ = fun τ => E4 τ := by
  sorry

/-- Every even unimodular rank-24 theta series is determined by its root count. -/
theorem theta_rank24_eq_E4_cubed_add_rootCard_sub_720_Delta
    (Λ : Submodule ℤ (V 24)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (P : EuclideanLattice.IntegralPresentation Λ)
    (heven : P.IsEven) (hunimodular : P.IsUnimodular) :
    latticeTheta Λ = fun τ =>
      (E4 τ) ^ 3 + ((rootCard Λ : ℤ) - 720) * ModularForm.discriminant τ := by
  sorry

/-- A rootless even unimodular rank-24 lattice has the Leech theta series. -/
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

/-- Irreducible simply-laced root-system types used by the rank-eight classification. -/
inductive ADEType
  | A (n : ℕ)
  | D (n : ℕ)
  | e6
  | e7
  | e8
  deriving DecidableEq

/-- The index ranges for actual irreducible simply-laced root systems. -/
def ADEType.Valid : ADEType → Prop
  | .A n => 1 ≤ n
  | .D n => 4 ≤ n
  | .e6 | .e7 | .e8 => True

def ADEType.rank : ADEType → ℕ
  | .A n => n
  | .D n => n
  | .e6 => 6
  | .e7 => 7
  | .e8 => 8

def ADEType.rootCount : ADEType → ℕ
  | .A n => n * (n + 1)
  | .D n => 2 * n * (n - 1)
  | .e6 => 72
  | .e7 => 126
  | .e8 => 240

/-- Finite norm-two root set of a positive-definite integral lattice. -/
noncomputable def normTwoRoots {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hpos : L.IsPosDef) : Finset L := by
  sorry

@[simp]
theorem mem_normTwoRoots {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hpos : L.IsPosDef) (x : L) :
    x ∈ normTwoRoots L hpos ↔ x ∈ L.vectorsOfNorm 2 := by
  sorry

/-- Root sublattice generated by the norm-two vectors. -/
noncomputable def rootSubmodule {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hpos : L.IsPosDef) : Submodule ℤ L :=
  Submodule.span ℤ (normTwoRoots L hpos : Set L)

/-- ADE components extracted from the finite crystallographic root system. -/
noncomputable def rootComponents {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hpos : L.IsPosDef) : Multiset ADEType := by
  sorry

/-- Every component extracted from a crystallographic root system has a valid Dynkin index. -/
theorem rootComponents_valid {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hpos : L.IsPosDef) :
    ∀ t ∈ rootComponents L hpos, t.Valid := by
  sorry

/-- Component ranks add to the rank of the span of the root system. -/
theorem rootComponents_rank {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hpos : L.IsPosDef) :
    ((rootComponents L hpos).map ADEType.rank).sum =
      Module.finrank ℚ (Submodule.span ℚ
        ((fun x : L => (x : W)) '' (normTwoRoots L hpos : Set L))) := by
  sorry

/-- Component root counts add to the cardinality of the norm-two root set. -/
theorem rootComponents_rootCount {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hpos : L.IsPosDef) :
    ((rootComponents L hpos).map ADEType.rootCount).sum =
      (normTwoRoots L hpos).card := by
  sorry

/-- In rank eight the roots span the ambient rational space. -/
theorem normTwoRoots_span_of_even_unimodular_rank_eight
    {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hrank : Module.finrank ℚ W = 8)
    (hpos : L.IsPosDef) (heven : L.IsEven) (hunimodular : L.IsUnimodular) :
    Submodule.span ℚ ((fun x : L => (x : W)) '' (normTwoRoots L hpos : Set L)) = ⊤ := by
  sorry

/-- Theta classification supplies the exact root count used by ADE identification. -/
theorem normTwoRoots_card_eq_240
    {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hrank : Module.finrank ℚ W = 8)
    (hpos : L.IsPosDef) (heven : L.IsEven) (hunimodular : L.IsUnimodular) :
    (normTwoRoots L hpos).card = 240 := by
  sorry

/-- Rank eight and 240 roots force one irreducible component of type E8. -/
theorem rootComponents_eq_e8
    {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hrank : Module.finrank ℚ W = 8)
    (hpos : L.IsPosDef) (heven : L.IsEven) (hunimodular : L.IsUnimodular) :
    rootComponents L hpos = {.e8} := by
  sorry

/-- Unimodularity makes the E8 root sublattice have index one. -/
theorem rootSubmodule_relIndex_eq_one
    {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hrank : Module.finrank ℚ W = 8)
    (hpos : L.IsPosDef) (heven : L.IsEven) (hunimodular : L.IsUnimodular) :
    (rootSubmodule L hpos).toAddSubgroup.relIndex ⊤ = 1 := by
  sorry

/-- Classification target: every positive-definite even unimodular rank-eight lattice is E8.
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

/-- The 24 Niemeier cases, named by their root systems; `leech` is the unique empty-root case. -/
inductive NiemeierType
  | leech
  | A1_24
  | A2_12
  | A3_8
  | A4_6
  | A5_4_D4
  | A6_4
  | A7_2_D5_2
  | A8_3
  | A9_2_D6
  | A11_D7_E6
  | A12_2
  | A15_D9
  | A17_E7
  | A24
  | D4_6
  | D6_4
  | D8_3
  | D10_E7_2
  | D12_2
  | D16_E8
  | D24
  | E6_4
  | E8_3
  deriving DecidableEq

/-- Canonical integral lattice for each Niemeier root-system/glue-code case. -/
noncomputable def niemeierLattice : NiemeierType →
    TauCeti.IntegralLattice (Fin 24 → ℚ) := by
  intro t
  sorry

@[simp]
theorem niemeierLattice_leech : niemeierLattice .leech = integralLattice := by
  sorry

/-- Case selected by the Niemeier root-system and glue-code classification. -/
noncomputable def niemeierTypeOf
    {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hrank : Module.finrank ℚ W = 24)
    (hpos : L.IsPosDef) (heven : L.IsEven) (hunimodular : L.IsUnimodular) :
    NiemeierType := by
  sorry

/-- Niemeier classification in the exact isometry form consumed by SphereCeti. -/
theorem niemeierClassificationIsometry
    {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hrank : Module.finrank ℚ W = 24)
    (hpos : L.IsPosDef) (heven : L.IsEven) (hunimodular : L.IsUnimodular) :
    Nonempty (TauCeti.IntegralLattice.Isometry L
      (niemeierLattice (niemeierTypeOf L hrank hpos heven hunimodular))) := by
  sorry

/-- The classified lattice has no norm-two vectors exactly in the Leech case. -/
theorem vectorsOfNorm_two_eq_empty_iff_niemeierType_eq_leech
    {W : Type u} [AddCommGroup W] [Module ℚ W]
    (L : TauCeti.IntegralLattice W) (hrank : Module.finrank ℚ W = 24)
    (hpos : L.IsPosDef) (heven : L.IsEven) (hunimodular : L.IsUnimodular) :
    L.vectorsOfNorm 2 = ∅ ↔ niemeierTypeOf L hrank hpos heven hunimodular = .leech := by
  sorry

/-- Classification target: every positive-definite rootless even unimodular rank-24 lattice is
Leech.  Positive-definiteness supplies nondegeneracy internally. -/
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

/-! ## Layer 7: common radial machinery and Fourier signs -/

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

/- A generic modular-kernel constructor is deliberately not a target yet.  The concrete E8 and
Leech component proofs first expose their exact signed transformation laws; only their proven
common hypotheses are then extracted into shared declarations.  This prevents an unconstrained
eigenvalue field from making a zero-function implementation satisfy an intended construction. -/

/-- TauCeti's meromorphic circle Goursat theorem is used directly for closed-circle residue-free
steps. -/
example {A : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hA : MeromorphicOn A (closedBall c R))
    (hord : ∀ z ∈ closedBall c R, 0 ≤ meromorphicOrderAt A z) :
    circleIntegral A c R = 0 :=
  TauCeti.Contour.circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg hR hA hord

end MagicFunction

/-! ## Layer 8: dimension-specific magic certificates and strict zero sets -/

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

theorem fourier_magicPlus :
    𝓕 (magicPlus : 𝓢(V 8, ℂ)) = (magicPlus : 𝓢(V 8, ℂ)) := by
  sorry

theorem fourier_magicMinus :
    𝓕 (magicMinus : 𝓢(V 8, ℂ)) = -(magicMinus : 𝓢(V 8, ℂ)) := by
  sorry

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

theorem fourier_magicPlus :
    𝓕 (magicPlus : 𝓢(V 24, ℂ)) = (magicPlus : 𝓢(V 24, ℂ)) := by
  sorry

theorem fourier_magicMinus :
    𝓕 (magicMinus : 𝓢(V 24, ℂ)) = -(magicMinus : 𝓢(V 24, ℂ)) := by
  sorry

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

/-! ## Layer 9: equality, rigidity, and uniqueness among periodic packings -/

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

/-! ## Layer 10: literal summit theorems -/

theorem spherePackingConstant_eight :
    SpherePackingConstant 8 = ENNReal.ofReal (Real.pi ^ 4 / 384) := by
  rw [E8.isOptimal, E8.packing_density]

theorem spherePackingConstant_twentyFour :
    SpherePackingConstant 24 = ENNReal.ofReal (Real.pi ^ 12 / Nat.factorial 12) := by
  rw [Leech.isOptimal, Leech.packing_density]

end

end SphereCeti.Suggested
