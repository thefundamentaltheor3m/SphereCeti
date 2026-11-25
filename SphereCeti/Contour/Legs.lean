/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCeti.Contour.SegmentChangeOfVariables
public import SphereCeti.Contour.Wedge

import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import TauCeti.Topology.Path.Map

/-!
# The left and right legs of the magic contour

The magic contour contains the broken line `-1 → -1 + i → i`, its left legs, and the broken line
`1 → 1 + i → i`, its right legs.  For `Ψ : ℂ → ℂ`, this file defines `leftLegs Ψ` and
`rightLegs Ψ`, the sums of the contour integrals `∫ Ψ(z) dz` along the two segments of each broken
line, and compares them under the inversion `z ↦ -1/z`.  The inversion maps the left legs onto
the circular arcs from `1` to `(1 + i) / 2` and from `(1 + i) / 2` to `i`; these arcs and the
right legs lie in the closure of the wedge `W = {z | 0 < Im z, |Re z - 1| < Im z}`.

The main result is the signed contour permutation for a single pair of kernels `Ψ, Ψ' : ℂ → ℂ`
and a scalar `s : ℂ`: if `Ψ z = s * (z ^ 2)⁻¹ * Ψ' (-z⁻¹)` for every `z` in the upper half-plane
and the one-form `Ψ' dz` is closed on `W`, then `leftLegs Ψ = s * rightLegs Ψ'`.  The theorem
assumes nothing about `Ψ` beyond this transformation law.

## Main definitions

* `SphereCeti.Contour.leftLegs Ψ`: the sum of the contour integrals of `Ψ` along `[-1, -1 + i]`
  and `[-1 + i, i]`.
* `SphereCeti.Contour.rightLegs Ψ`: the sum of the contour integrals of `Ψ` along `[1, 1 + i]` and
  `[1 + i, i]`.

## Main results

* `SphereCeti.Contour.perm_leftLegs_eq_smul_rightLegs`: the signed contour permutation
  `leftLegs Ψ = s * rightLegs Ψ'`.

## References

* M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991–1015, Section 4.
* The theorem and its proof are adapted from Sphere-Packing-Lean
  (`thefundamentaltheor3m/Sphere-Packing-Lean`) at commit
  `01f23eccf963c50250c9e48dd103e8cc88c36f85`, file
  `SpherePacking/Contour/MobiusInv/WedgeSetContour.lean` (`curveIntegral_segment_neg_inv`,
  `curveIntegral_segment_pos_inv`, `perm_J12_contour_h1_mobiusInv_wedgeSet`,
  `perm_J12_contour_h2_mobiusInv_wedgeSet`, `perm_J12_contour_mobiusInv_wedgeSet` and
  `perm_I12_contour_mobiusInv_wedgeSet`), where they are stated for families of kernels indexed
  by a radial parameter and for the scalars `-1` and `1`.
-/

public section

open Set AffineMap Complex

namespace SphereCeti.Contour

/-- The left legs `-1 → -1 + i → i` of the magic contour: the sum of the contour integrals of `Ψ`
along the segments `[-1, -1 + i]` and `[-1 + i, i]`. -/
noncomputable def leftLegs (Ψ : ℂ → ℂ) : ℂ :=
  (∫ᶜ z in Path.segment (-1) (-1 + Complex.I), scalarOneForm Ψ z)
    + ∫ᶜ z in Path.segment (-1 + Complex.I) Complex.I, scalarOneForm Ψ z

/-- The left legs of `Ψ` are the sum of its contour integrals along `[-1, -1 + i]` and
`[-1 + i, i]`. -/
theorem leftLegs_def (Ψ : ℂ → ℂ) :
    leftLegs Ψ = (∫ᶜ z in Path.segment (-1) (-1 + Complex.I), scalarOneForm Ψ z)
      + ∫ᶜ z in Path.segment (-1 + Complex.I) Complex.I, scalarOneForm Ψ z := (rfl)

/-- The right legs `1 → 1 + i → i` of the magic contour: the sum of the contour integrals of `Ψ`
along the segments `[1, 1 + i]` and `[1 + i, i]`. -/
noncomputable def rightLegs (Ψ : ℂ → ℂ) : ℂ :=
  (∫ᶜ z in Path.segment 1 (1 + Complex.I), scalarOneForm Ψ z)
    + ∫ᶜ z in Path.segment (1 + Complex.I) Complex.I, scalarOneForm Ψ z

/-- The right legs of `Ψ` are the sum of its contour integrals along `[1, 1 + i]` and
`[1 + i, i]`. -/
theorem rightLegs_def (Ψ : ℂ → ℂ) :
    rightLegs Ψ = (∫ᶜ z in Path.segment 1 (1 + Complex.I), scalarOneForm Ψ z)
      + ∫ᶜ z in Path.segment (1 + Complex.I) Complex.I, scalarOneForm Ψ z := (rfl)

/-- Along a segment `[a, b]` whose open part lies in the upper half-plane and on which
`z ↦ -z⁻¹` is continuous, the signed inversion law `Ψ z = s * (z ^ 2)⁻¹ * Ψ' (-z⁻¹)` turns the
contour integral of `Ψ` into `s` times the contour integral of `Ψ'` along the image of the
segment under `z ↦ -z⁻¹`. -/
private theorem curveIntegral_segment_eq_mul_curveIntegral_map' {s a b : ℂ} {Ψ Ψ' : ℂ → ℂ}
    (hlaw : ∀ z : ℂ, 0 < z.im → Ψ z = s * (z ^ 2)⁻¹ * Ψ' (-z⁻¹))
    (hf : ContinuousOn (fun z : ℂ => -z⁻¹) (range (Path.segment a b)))
    (him : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < (lineMap a b y).im) :
    (∫ᶜ z in Path.segment a b, scalarOneForm Ψ z)
      = s * ∫ᶜ z in (Path.segment a b).map' hf, scalarOneForm Ψ' z := by
  -- The points of the segment other than its endpoints are the points `lineMap a b y`,
  -- `y ∈ (0, 1)`.
  have him' : ∀ z ∈ range (Path.segment a b) \ {a, b}, 0 < z.im := by
    rintro z ⟨hz, hzab⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hzab
    rw [Path.range_segment] at hz
    obtain ⟨y, hy, rfl⟩ := (openSegment_eq_image_lineMap ℝ a b).subset
      (mem_openSegment_of_ne_left_right (Ne.symm hzab.1) (Ne.symm hzab.2) hz)
    exact him y hy
  have hω : (fun z => scalarOneForm (fun w => s * Ψ' w) z) = fun z => s • scalarOneForm Ψ' z := by
    funext z
    ext
    simp
  rw [curveIntegral_segment_change_of_variables (G := fun w => s * Ψ' w)
      (f' := fun z => (z ^ 2)⁻¹) hf
      (fun z hz => by
        have hz0 : z ≠ 0 := fun h => (him' z hz).ne' (by simp [h])
        simpa using (hasDerivAt_inv hz0).fun_neg)
      (fun z hz => by rw [hlaw z (him' z hz)]; ring),
    hω, curveIntegral_fun_smul, smul_eq_mul]

/-- Let `Ψ z = s * (z ^ 2)⁻¹ * Ψ' (-z⁻¹)` for every `z` with `0 < Im z`, and let `Ψ' dz` be closed
on the wedge.  Let the segment `[p₀, p₁]` avoid `0`, and suppose that for every `y ∈ (0, 1)` the
points `-(lineMap p₀ p₁ y)⁻¹` and `lineMap q₀ q₁ y` lie in the wedge.  Then
`∫_{[p₀, p₁]} Ψ dz + s ∫_{[-p₁⁻¹, q₁]} Ψ' dz = s ∫_{[q₀, q₁]} Ψ' dz + s ∫_{[-p₀⁻¹, q₀]} Ψ' dz`. -/
private theorem curveIntegral_segment_add_mul_curveIntegral_segment_eq {s p₀ p₁ q₀ q₁ : ℂ}
    {Ψ Ψ' : ℂ → ℂ} (hlaw : ∀ z : ℂ, 0 < z.im → Ψ z = s * (z ^ 2)⁻¹ * Ψ' (-z⁻¹))
    (hclosed : ClosedOneFormOn (scalarOneForm Ψ') wedgeSet)
    (hne : ∀ y ∈ Icc (0 : ℝ) 1, lineMap p₀ p₁ y ≠ 0)
    (hmem : ∀ y ∈ Ioo (0 : ℝ) 1,
      -(lineMap p₀ p₁ y)⁻¹ ∈ wedgeSet ∧ lineMap q₀ q₁ y ∈ wedgeSet) :
    (∫ᶜ z in Path.segment p₀ p₁, scalarOneForm Ψ z)
        + s * ∫ᶜ z in Path.segment (-p₁⁻¹) q₁, scalarOneForm Ψ' z
      = s * (∫ᶜ z in Path.segment q₀ q₁, scalarOneForm Ψ' z)
        + s * ∫ᶜ z in Path.segment (-p₀⁻¹) q₀, scalarOneForm Ψ' z := by
  have hf : ContinuousOn (fun z : ℂ => -z⁻¹) (range (Path.segment p₀ p₁)) :=
    (continuousOn_inv₀.mono (by rintro _ ⟨y, rfl⟩; exact hne y y.2)).neg
  -- The open segment lies in the upper half-plane, since its image under `z ↦ -z⁻¹` does.
  have him : ∀ y ∈ Ioo (0 : ℝ) 1, 0 < (lineMap p₀ p₁ y).im := fun y hy =>
    TauCeti.im_neg_inv_pos.1 (mem_wedgeSet.1 (hmem y hy).1).1
  rw [curveIntegral_segment_eq_mul_curveIntegral_map' hlaw hf him]
  -- The straight-line homotopy from the image of `[p₀, p₁]` to `[q₀, q₁]`.
  set φ := ContinuousMap.Homotopy.affine ((Path.segment p₀ p₁).map' hf : C(unitInterval, ℂ))
    (Path.segment q₀ q₁ : C(unitInterval, ℂ))
  have hφ (x y : unitInterval) :
      φ (x, y) = lineMap (-(lineMap p₀ p₁ (y : ℝ))⁻¹) (lineMap q₀ q₁ (y : ℝ)) (x : ℝ) := by
    simp [φ]
  have key := φ.curveIntegral_add_curveIntegral_eq_of_diffContOnCl ?_ hclosed.diffContOnCl
    hclosed.symm ?_
  · -- The homotopy's end segments are `[-p₁⁻¹, q₁]` and `[-p₀⁻¹, q₀]`, up to casts of endpoints.
    simp only [φ, ContinuousMap.Homotopy.evalAt_affine] at key
    rw [← Path.cast_segment (by simp :
          ((Path.segment p₀ p₁).map' hf : C(unitInterval, ℂ)) 1 = -p₁⁻¹)
        (by simp : (Path.segment q₀ q₁ : C(unitInterval, ℂ)) 1 = q₁), curveIntegral_cast,
      ← Path.cast_segment (by simp :
          ((Path.segment p₀ p₁).map' hf : C(unitInterval, ℂ)) 0 = -p₀⁻¹)
        (by simp : (Path.segment q₀ q₁ : C(unitInterval, ℂ)) 0 = q₀), curveIntegral_cast] at key
    linear_combination s * key
  · -- The open square is mapped into the wedge, by convexity.
    intro x hx y hy
    rw [hφ]
    obtain ⟨h₁, h₂⟩ := hmem y ⟨hy.1, hy.2⟩
    exact convex_wedgeSet.lineMap_mem h₁ h₂ ⟨hx.1.le, hx.2.le⟩
  · -- On the closed square the homotopy is `(x, y) ↦ lineMap (-(lineMap p₀ p₁ y)⁻¹) _ x`.
    have : EqOn (fun xy : ℝ × ℝ ↦ IccExtend zero_le_one (φ.extend xy.1) xy.2)
        (fun xy ↦ lineMap (-(lineMap p₀ p₁ xy.2)⁻¹) (lineMap q₀ q₁ xy.2) xy.1) (Icc 0 1) := by
      rw [Icc_prod_eq]
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      lift x to unitInterval using hx
      lift y to unitInterval using hy
      simp [hφ]
    refine .congr ?_ this
    fun_prop (disch := intro xy hxy; exact hne xy.2 ⟨hxy.1.2, hxy.2.2⟩)

/-- **Signed contour permutation.**  Let `s : ℂ` and `Ψ, Ψ' : ℂ → ℂ` satisfy
`Ψ z = s * (z ^ 2)⁻¹ * Ψ' (-z⁻¹)` for every `z` with `0 < Im z`, and let the one-form `Ψ' dz` be
closed on the wedge.  Then the left legs of `Ψ` are `s` times the right legs of `Ψ'`:
`∫_{-1}^{-1+i} Ψ dz + ∫_{-1+i}^{i} Ψ dz = s (∫_{1}^{1+i} Ψ' dz + ∫_{1+i}^{i} Ψ' dz)`. -/
theorem perm_leftLegs_eq_smul_rightLegs {s : ℂ} {Ψ Ψ' : ℂ → ℂ}
    (hlaw : ∀ z : ℂ, 0 < z.im → Ψ z = s * (z ^ 2)⁻¹ * Ψ' (-z⁻¹))
    (hclosed : ClosedOneFormOn (scalarOneForm Ψ') wedgeSet) :
    leftLegs Ψ = s * rightLegs Ψ' := by
  have hne₁ : ∀ y ∈ Icc (0 : ℝ) 1, lineMap (-1 : ℂ) (-1 + I) y ≠ 0 := fun y _ h => by
    simpa [lineMap_apply_module'] using congr_arg re h
  have hne₂ : ∀ y ∈ Icc (0 : ℝ) 1, lineMap (-1 + I : ℂ) I y ≠ 0 := fun y _ h => by
    simpa [lineMap_apply_module'] using congr_arg im h
  have hmem₁ : ∀ y ∈ Ioo (0 : ℝ) 1,
      -(lineMap (-1 : ℂ) (-1 + I) y)⁻¹ ∈ wedgeSet ∧ lineMap (1 : ℂ) (1 + I) y ∈ wedgeSet := by
    rintro y ⟨hy0, hy1⟩
    simp [lineMap_apply_module', Complex.normSq_apply]
    have hd : 0 < 1 + y * y := by positivity
    refine ⟨⟨?_, ?_, ?_⟩, hy0⟩ <;> field_simp <;> nlinarith
  have hmem₂ : ∀ y ∈ Ioo (0 : ℝ) 1,
      -(lineMap (-1 + I : ℂ) I y)⁻¹ ∈ wedgeSet ∧ lineMap (1 + I : ℂ) I y ∈ wedgeSet := by
    rintro y ⟨hy0, hy1⟩
    simp [lineMap_apply_module', Complex.normSq_apply]
    have hd : 0 < (y + -1) * (y + -1) + 1 := by nlinarith [mul_self_nonneg (y + -1)]
    refine ⟨⟨?_, ?_, ?_⟩, by linarith, hy1⟩ <;> field_simp <;> nlinarith
  -- The homotopies start or end at a single point, since `-(-1)⁻¹ = 1` and `-I⁻¹ = I`.
  have h₀ : (∫ᶜ z in Path.segment (-(-1 : ℂ)⁻¹) 1, scalarOneForm Ψ' z) = 0 := by
    rw [(by norm_num : -(-1 : ℂ)⁻¹ = 1), Path.segment_same, curveIntegral_refl]
  have h₁ : (∫ᶜ z in Path.segment (-I⁻¹) I, scalarOneForm Ψ' z) = 0 := by
    rw [(by simp : -I⁻¹ = I), Path.segment_same, curveIntegral_refl]
  have k₁ := curveIntegral_segment_add_mul_curveIntegral_segment_eq hlaw hclosed hne₁ hmem₁
  have k₂ := curveIntegral_segment_add_mul_curveIntegral_segment_eq hlaw hclosed hne₂ hmem₂
  rw [h₀] at k₁
  rw [h₁] at k₂
  rw [leftLegs_def, rightLegs_def]
  linear_combination k₁ + k₂

end SphereCeti.Contour
