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

The finite branch of the Layer 8 contour deformation substitutes `z ↦ f z` (for instance the
inversion `z ↦ -1/z`) in curve integrals of scalar one-forms along straight segments.  This file
proves that substitution for Mathlib's `curveIntegral` along `Path.segment a b`, with the image
path given by Mathlib's `Path.map'`.

No integrability hypothesis is needed.  Both curve integrals are interval integrals over `[0, 1]`,
and at every interior parameter `t` the chain rule and the substitution law make the two
integrands equal: `F (lineMap a b t) * (b - a) = G (f (lineMap a b t)) * (f' (lineMap a b t) *
(b - a))`.  The integrands therefore agree almost everywhere, so the integrals agree whether or not
they converge.  When `a = b` both integrands vanish.

## Main results

* `SphereCeti.Contour.curveIntegral_segment_change_of_variables`: the roadmap target
  `SphereCeti.Suggested.Contour.curveIntegral_segment_change_of_variables`, with the same
  statement.

## Provenance

The definitions and statements are the roadmap's Layer 8 targets, which are based on the `gauss2`
branch of Sphere-Packing-Lean at commit `01f23eccf963c50250c9e48dd103e8cc88c36f85`, file
`SpherePacking/Contour/MobiusInv/WedgeSetContour.lean` (see `PROVENANCE.md`, section 4).  The
proofs in this file were written independently of that source; no proof text is copied from it.
-/

public section

open Set AffineMap
open scoped Topology

namespace SphereCeti.Contour

/-- Change of variables along a segment, with a genuine chain-rule hypothesis: `f` is continuous
on the segment, differentiable along its interior with derivative `f'`, and the kernels
correspond under the substitution.  The image path is Mathlib's `Path.map'`. -/
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
