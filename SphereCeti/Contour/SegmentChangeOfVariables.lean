/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import SphereCeti.Contour.ClosedOneForm

/-!
# Change of variables along a segment

Contour integrals are Mathlib's `curveIntegral` of the scalar one-form `scalarOneForm F` along
`Path.segment a b`.  The parametrisation `z(t) = a + t (b - a)`, `0 ≤ t ≤ 1`, turns the contour
integral of `F : ℂ → ℂ` along the segment `[a, b]` into the interval integral
`∫₀¹ F(z(t)) (b - a) dt`.

Let `f` be continuous on the segment `[a, b] ⊆ ℂ` and complex differentiable at its interior
points with derivative `f'`, and suppose `F z = f' z * G (f z)` there.  Then the contour integral
of `F` along the segment equals the contour integral of `G` along its image under `f`:
`∫_{[a, b]} F(z) dz = ∫_{f ∘ [a, b]} G(w) dw`.  This is the substitution `w = f z` in contour
integrals, used for instance with the inversion `z ↦ -1/z` to move segments of a contour.

The image path is `Path.map'`.  No integrability hypothesis is needed: the two sides are interval
integrals over `[0, 1]` whose integrands agree at every interior parameter, so the integrals agree
whether or not they converge.

## Main results

* `SphereCeti.Contour.curveIntegral_segment_scalarOneForm`: the contour integral along `[a, b]` as
  an interval integral over the parametrisation `z(t) = a + t (b - a)`.
* `SphereCeti.Contour.curveIntegral_segment_change_of_variables`: the substitution formula above.

## Provenance

The change-of-variables statement follows the `gauss2` branch of Sphere-Packing-Lean at commit
`01f23eccf963c50250c9e48dd103e8cc88c36f85`, file
`SpherePacking/Contour/MobiusInv/WedgeSetContour.lean`.  The proofs in this file were written
independently of that source; no proof text is copied from it.
-/

public section

open Set AffineMap
open scoped Topology

namespace SphereCeti.Contour

/-- The contour integral of `F` along the segment `[a, b]` is the interval integral
`∫₀¹ F(a + t (b - a)) (b - a) dt`. -/
theorem curveIntegral_segment_scalarOneForm (F : ℂ → ℂ) (a b : ℂ) :
    (∫ᶜ z in Path.segment a b, scalarOneForm F z) =
      ∫ t in (0 : ℝ)..1, F (a + t * (b - a)) * (b - a) := by
  rw [curveIntegral_segment]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [scalarOneForm_apply, lineMap_apply_module', Complex.real_smul, add_comm]

/-- Change of variables along a segment: if `f` is continuous on the segment from `a` to `b`, has
derivative `f' z` at each interior point `z`, and `F z = f' z * G (f z)` there, then the contour
integral of `F` along the segment equals the contour integral of `G` along its image under `f`. -/
theorem curveIntegral_segment_change_of_variables
    {F G f f' : ℂ → ℂ} {a b : ℂ}
    (hf : ContinuousOn f (Set.range ⇑(Path.segment a b)))
    (hderiv : ∀ z ∈ Set.range ⇑(Path.segment a b) \ {a, b}, HasDerivAt f (f' z) z)
    (hlaw : ∀ z ∈ Set.range ⇑(Path.segment a b) \ {a, b}, F z = f' z * G (f z)) :
    (∫ᶜ z in Path.segment a b, scalarOneForm F z)
      = ∫ᶜ z in (Path.segment a b).map' hf, scalarOneForm G z := by
  rw [curveIntegral_segment, curveIntegral_eq_intervalIntegral_deriv]
  refine intervalIntegral.integral_congr_ae_restrict ?_
  rw [uIoc_of_le zero_le_one, ← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
  -- At an interior parameter `t`, the chain rule and the substitution law make the integrands
  -- equal: `F (lineMap a b t) * (b - a) = G (f (lineMap a b t)) * (f' (lineMap a b t) * (b - a))`.
  -- When `a = b` both integrands vanish.
  -- Near an interior parameter, the extended image path is `f ∘ lineMap a b`.
  have hext : ((Path.segment a b).map' hf).extend =ᶠ[𝓝 t] fun s => f (lineMap a b s) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    rw [Path.extend_apply _ hs]
    rfl
  rw [hext.deriv_eq, hext.self_of_nhds, scalarOneForm_apply, scalarOneForm_apply]
  rcases eq_or_ne a b with rfl | hab
  · simp
  have hz : lineMap a b t ∈ Set.range ⇑(Path.segment a b) \ {a, b} := by
    refine ⟨⟨⟨t, Ioo_subset_Icc_self ht⟩, rfl⟩, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨fun h => (lineMap_eq_left_iff.mp h).elim hab ht.1.ne',
      fun h => (lineMap_eq_right_iff.mp h).elim hab ht.2.ne⟩
  have hd : HasDerivAt (fun s : ℝ => f (lineMap a b s)) (f' (lineMap a b t) * (b - a)) t :=
    HasDerivAt.comp t (hderiv _ hz) hasDerivAt_lineMap
  rw [hd.deriv, hlaw _ hz]
  ring

end SphereCeti.Contour
