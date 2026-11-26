/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
public import Mathlib.Topology.Homotopy.Affine
public import SphereCeti.Contour.SegmentChangeOfVariables
public import SphereCeti.Contour.Wedge

/-!
# Signed permutation of the contour legs under `z ↦ -1/z`

Write `∫_γ F(z) dz` for the contour integral of `F : ℂ → ℂ` along a path `γ`.  The *left legs*
of a contour are the two segments `-1 → -1 + i → i`, and the *right legs* are the two segments
`1 → 1 + i → i`.  The inversion `z ↦ -1/z` maps the left legs onto two circular arcs
`1 → (1 + i)/2 → i`, which lie in the closure of the wedge
`W = {z | 0 < Im z, |Re z - 1| < Im z}`, together with the right legs.

Suppose `Ψ z = s z⁻² Ψ'(-1/z)` on the upper half-plane for some `s ∈ ℂ`, and that the one-form
`Ψ' dz` is closed on `W`.  Substituting `w = -1/z`, with `dw = z⁻² dz`, turns the integral of `Ψ`
over each left leg into `s` times the integral of `Ψ'` over its image arc; a straight-line
homotopy inside `W` moves each arc onto the corresponding right leg.  The two homotopies differ by
the segment `(1 + i)/2 → 1 + i`, whose contributions cancel.  Hence the sum of the integrals of `Ψ`
over the left legs is `s` times the sum of the integrals of `Ψ'` over the right legs.

No continuity of `Ψ` is needed: on the interiors of the left legs the transformation law
determines `Ψ` from `Ψ'`, which is continuous up to the boundary of `W`.

## Main definitions

* `SphereCeti.Contour.leftLegs Ψ`: the integral of `Ψ` over the legs `-1 → -1 + i → i`.
* `SphereCeti.Contour.rightLegs Ψ`: the integral of `Ψ` over the legs `1 → 1 + i → i`.

## Main results

* `SphereCeti.Contour.perm_leftLegs_eq_smul_rightLegs`: `leftLegs Ψ = s * rightLegs Ψ'`.

## Provenance

The statement follows the `gauss2` branch of Sphere-Packing-Lean at commit
`01f23eccf963c50250c9e48dd103e8cc88c36f85`, file
`SpherePacking/Contour/MobiusInv/WedgeSetContour.lean`.  The proofs in this file were written
independently of that source; no proof text is copied from it.
-/

public section

open Set Complex AffineMap

namespace SphereCeti.Contour

/-- The integral of `Ψ dz` over the left legs `-1 → -1 + i → i`. -/
noncomputable def leftLegs (Ψ : ℂ → ℂ) : ℂ :=
  (∫ᶜ z in Path.segment (-1) (-1 + I), scalarOneForm Ψ z)
    + ∫ᶜ z in Path.segment (-1 + I) I, scalarOneForm Ψ z

/-- The integral of `Ψ dz` over the right legs `1 → 1 + i → i`. -/
noncomputable def rightLegs (Ψ : ℂ → ℂ) : ℂ :=
  (∫ᶜ z in Path.segment 1 (1 + I), scalarOneForm Ψ z)
    + ∫ᶜ z in Path.segment (1 + I) I, scalarOneForm Ψ z

/-- `-1/z` lies in the wedge when `Im z > 0`, `-Re z - |z|² < Im z` and `|z|² + Re z < Im z`. -/
private lemma neg_inv_mem_wedgeSet {z : ℂ} (h₀ : 0 < z.im) (h₁ : -z.re - normSq z < z.im)
    (h₂ : normSq z + z.re < z.im) : -z⁻¹ ∈ wedgeSet := by
  have hn : 0 < normSq z := normSq_pos.mpr fun h => by simp [h] at h₀
  simp only [mem_wedgeSet, neg_re, neg_im, inv_re, inv_im, neg_div, neg_neg]
  refine ⟨div_pos h₀ hn, ?_, ?_⟩
  · have e : -(z.re / normSq z) - 1 = (-z.re - normSq z) / normSq z := by field_simp
    rw [e, div_lt_div_iff_of_pos_right hn]
    exact h₁
  · have e : 1 - -(z.re / normSq z) = (normSq z + z.re) / normSq z := by
      field_simp
      ring
    rw [e, div_lt_div_iff_of_pos_right hn]
    exact h₂

/-- One leg of the permutation.  Let the segment `a → b` avoid `0`, lie in the upper half-plane
away from its endpoints, and have its image under `z ↦ -1/z` in the wedge away from its endpoints,
as does the segment `c → d`.  Then the integral of `Ψ` over `a → b` is `s` times the integral of
`Ψ'` over `c → d`, corrected by the two side segments `-1/a → c` and `-1/b → d`. -/
private lemma curveIntegral_segment_eq_of_neg_inv (s : ℂ) {Ψ Ψ' : ℂ → ℂ} {a b c d : ℂ}
    (hlaw : ∀ z : ℂ, 0 < z.im → Ψ z = s * (z ^ 2)⁻¹ * Ψ' (-z⁻¹))
    (hclosed : ClosedOneFormOn (scalarOneForm Ψ') wedgeSet)
    (hne : ∀ t ∈ unitInterval, lineMap a b t ≠ 0)
    (him : ∀ t ∈ unitInterval, lineMap a b t ≠ a → lineMap a b t ≠ b → 0 < (lineMap a b t).im)
    (hab : ∀ t ∈ Ioo (0 : ℝ) 1, -(lineMap a b t)⁻¹ ∈ wedgeSet)
    (hcd : ∀ t ∈ Ioo (0 : ℝ) 1, lineMap c d t ∈ wedgeSet) :
    (∫ᶜ z in Path.segment a b, scalarOneForm Ψ z)
      = s * ((∫ᶜ z in Path.segment c d, scalarOneForm Ψ' z)
        + (∫ᶜ z in Path.segment (-a⁻¹) c, scalarOneForm Ψ' z)
        - ∫ᶜ z in Path.segment (-b⁻¹) d, scalarOneForm Ψ' z) := by
  have hne' : ∀ z ∈ range (Path.segment a b), z ≠ 0 := by
    rintro _ ⟨t, rfl⟩
    exact hne t t.2
  have hf : ContinuousOn (fun z : ℂ => -z⁻¹) (range (Path.segment a b)) :=
    (continuousOn_inv₀.mono fun z hz => hne' z hz).neg
  -- Substitute `w = -1/z` along the segment.
  have hcov := curveIntegral_segment_change_of_variables (F := Ψ) (G := fun w => s * Ψ' w)
    (f' := fun z => (z ^ 2)⁻¹) hf
    (fun z hz => by
      convert (hasDerivAt_inv (hne' z hz.1)).neg using 1
      simp)
    (fun z hz => by
      obtain ⟨⟨t, rfl⟩, hz⟩ := hz
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz
      rw [hlaw ((Path.segment a b) t) (him t t.2 hz.1 hz.2)]
      ring)
  set A := (Path.segment a b).map' hf
  have hsmul : (fun z => scalarOneForm (fun w => s * Ψ' w) z) = fun z => s • scalarOneForm Ψ' z := by
    funext z
    ext
    simp
  rw [hsmul, curveIntegral_fun_smul, smul_eq_mul] at hcov
  rw [hcov]
  congr 1
  -- Move the image arc onto the segment `c → d` by a straight-line homotopy inside the wedge.
  set φ := ContinuousMap.Homotopy.affine (A : C(unitInterval, ℂ)) (Path.segment c d : C(unitInterval, ℂ))
  have key := φ.curveIntegral_add_curveIntegral_eq_of_diffContOnCl (t := wedgeSet)
    (ω := scalarOneForm Ψ') ?_ hclosed.diffContOnCl hclosed.symm ?_
  · have h0 : ∫ᶜ z in φ.evalAt 0, scalarOneForm Ψ' z
        = ∫ᶜ z in Path.segment (-a⁻¹) c, scalarOneForm Ψ' z := by
      dsimp [φ]
      rw [← Path.cast_segment A.source (Path.segment c d).source, curveIntegral_cast]
    have h1 : ∫ᶜ z in φ.evalAt 1, scalarOneForm Ψ' z
        = ∫ᶜ z in Path.segment (-b⁻¹) d, scalarOneForm Ψ' z := by
      dsimp [φ]
      rw [← Path.cast_segment A.target (Path.segment c d).target, curveIntegral_cast]
    rw [h0, h1] at key
    linear_combination key
  · intro x hx y hy
    have hy' : (y : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨hy.1, hy.2⟩
    exact convex_wedgeSet.lineMap_mem (hab y hy') (hcd y hy') ⟨x.2.1, x.2.2⟩
  · have heq : EqOn (fun xy : ℝ × ℝ => IccExtend zero_le_one (φ.extend xy.1) xy.2)
        (fun xy => lineMap (-(lineMap a b xy.2 : ℂ)⁻¹) (lineMap c d xy.2) xy.1) (Icc 0 1) := by
      rw [Icc_prod_eq]
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      lift x to unitInterval using hx
      lift y to unitInterval using hy
      simp [φ, A]
      rfl
    refine ContDiffOn.congr ?_ heq
    have hP : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => ((1 - xy.2) • a + xy.2 • b)⁻¹) (Icc 0 1) := by
      refine ContDiffOn.inv (by fun_prop) fun xy hxy => ?_
      have h := hne xy.2 ⟨hxy.1.2, hxy.2.2⟩
      rwa [lineMap_apply_module] at h
    simp only [lineMap_apply_module]
    fun_prop

/-- Signed permutation of the contour legs.  If `Ψ z = s z⁻² Ψ'(-1/z)` on the upper half-plane and
the one-form `Ψ' dz` is closed on the wedge, then the integral of `Ψ dz` over the left legs
`-1 → -1 + i → i` is `s` times the integral of `Ψ' dz` over the right legs `1 → 1 + i → i`. -/
theorem perm_leftLegs_eq_smul_rightLegs (s : ℂ) {Ψ Ψ' : ℂ → ℂ}
    (hlaw : ∀ z : ℂ, 0 < z.im → Ψ z = s * (z ^ 2)⁻¹ * Ψ' (-z⁻¹))
    (hclosed : ClosedOneFormOn (scalarOneForm Ψ') wedgeSet) :
    leftLegs Ψ = s * rightLegs Ψ' := by
  -- The leg `-1 → -1 + i` goes to `1 → 1 + i`, up to the segment `(1 + i)/2 → 1 + i`.
  have h₁ := curveIntegral_segment_eq_of_neg_inv s (a := -1) (b := -1 + I) (c := 1) (d := 1 + I)
    hlaw hclosed
    (fun t _ h => by
      have h' := congrArg re h
      simp [lineMap_apply_module] at h'
      linarith)
    (fun t ht hta _ => by
      rcases ht.1.eq_or_lt with h0 | h0
      · simp [← h0] at hta
      · simpa [lineMap_apply_module] using h0)
    (fun t ht => by
      refine neg_inv_mem_wedgeSet ?_ ?_ ?_ <;>
        simp [lineMap_apply_module, normSq_apply] <;> nlinarith [ht.1, ht.2])
    (fun t ht => by simpa [lineMap_apply_module] using ht.1)
  -- The leg `-1 + i → i` goes to `1 + i → i`, up to the same segment, reversed in sign.
  have h₂ := curveIntegral_segment_eq_of_neg_inv s (a := -1 + I) (b := I) (c := 1 + I) (d := I)
    hlaw hclosed
    (fun t _ h => by simpa [lineMap_apply_module, Complex.ext_iff] using congrArg im h)
    (fun t _ _ _ => by simp [lineMap_apply_module])
    (fun t ht => by
      refine neg_inv_mem_wedgeSet ?_ ?_ ?_ <;>
        simp [lineMap_apply_module, normSq_apply] <;> nlinarith [ht.1, ht.2])
    (fun t ht => by simp [lineMap_apply_module]; constructor <;> linarith [ht.1, ht.2])
  have e₁ : -(-1 : ℂ)⁻¹ = 1 := by simp
  have e₂ : -(-1 + I)⁻¹ = (1 + I) / 2 := by
    have : (-1 + I) ≠ 0 := by simp [Complex.ext_iff]
    field_simp
    ring_nf
    simp [I_sq]
    ring
  have e₃ : -I⁻¹ = I := by simp
  rw [e₁, e₂, Path.segment_same, curveIntegral_refl] at h₁
  rw [e₂, e₃, Path.segment_same, curveIntegral_refl] at h₂
  rw [leftLegs, rightLegs, h₁, h₂]
  ring

end SphereCeti.Contour
