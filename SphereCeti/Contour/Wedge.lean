/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Basic

/-!
# The wedge at `1` in the upper half-plane

This file studies the open wedge

`W = {z ∈ ℂ | 0 < Im z, |Re z - 1| < Im z}`,

the region of the upper half-plane lying strictly above both lines `Im z = Re z - 1` and
`Im z = 1 - Re z` through the point `1`. It is a right-angled cone with apex `1` opening upwards.

The wedge is the domain of the homotopies in the finite part of the magic-contour deformation,
which compares the legs `-1 → -1 + i → i` with the legs `1 → 1 + i → i` under the inversion
`z ↦ -1/z`. Openness and convexity let straight-line homotopies between such paths stay inside an
open set, and the closure of `W` touches the real axis only at the apex `1`.

## Main definitions and results

* `SphereCeti.Contour.wedgeSet`: the wedge `W`.
* `SphereCeti.Contour.mem_wedgeSet`: membership in `W` as three strict coordinate inequalities.
* `SphereCeti.Contour.isOpen_wedgeSet`: `W` is open.
* `SphereCeti.Contour.convex_wedgeSet`: `W` is convex over `ℝ`.
* `SphereCeti.Contour.closure_wedgeSet_inter_real`: the closure of `W` meets the real axis
  exactly in `{1}`.

## Provenance

The definition and statements follow the `gauss2` branch of Sphere-Packing-Lean at commit
`01f23eccf963c50250c9e48dd103e8cc88c36f85`, file
`SpherePacking/Contour/MobiusInv/WedgeSetContour.lean`. The proofs in this file were written
independently of that source; no proof text is copied from it.
-/

public section

open Set Filter
open scoped Topology

namespace SphereCeti.Contour

/-- The open wedge `{z | 0 < Im z, |Re z - 1| < Im z}` with apex `1` in the upper half-plane. -/
def wedgeSet : Set ℂ := {z | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im}

/-- A complex number `z` lies in the wedge exactly when `0 < Im z`, `Re z - 1 < Im z`, and
`1 - Re z < Im z`. -/
@[simp]
theorem mem_wedgeSet {z : ℂ} :
    z ∈ wedgeSet ↔ 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im :=
  Iff.rfl

/-- The wedge is an open subset of `ℂ`. -/
theorem isOpen_wedgeSet : IsOpen wedgeSet :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    ((isOpen_lt (by fun_prop) Complex.continuous_im).inter
      (isOpen_lt (by fun_prop) Complex.continuous_im))

/-- The wedge is convex over `ℝ`. -/
theorem convex_wedgeSet : Convex ℝ wedgeSet := by
  -- The wedge is the intersection of three open half-planes cut out by the real-linear
  -- functionals `Im`, `Im - Re`, and `Im + Re`, each of which is convex.
  have h : wedgeSet = {z | 0 < Complex.imLm z} ∩
      ({z | -1 < (Complex.imLm - Complex.reLm) z} ∩ {z | 1 < (Complex.imLm + Complex.reLm) z}) := by
    ext z
    simp only [mem_wedgeSet, mem_inter_iff, mem_ofPred_eq, LinearMap.sub_apply,
      LinearMap.add_apply, Complex.imLm_coe, Complex.reLm_coe]
    constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> exact ⟨h₁, by linarith, by linarith⟩
  rw [h]
  exact (convex_halfSpace_gt Complex.imLm.isLinear 0).inter
    ((convex_halfSpace_gt (Complex.imLm - Complex.reLm).isLinear _).inter
      (convex_halfSpace_gt (Complex.imLm + Complex.reLm).isLinear _))

/-- The closure of the wedge meets the real axis `{z | Im z = 0}` exactly at the apex `1`. -/
theorem closure_wedgeSet_inter_real : closure wedgeSet ∩ {z : ℂ | z.im = 0} = {1} := by
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hz, him⟩
    -- The closure lies in the closed wedge, where `Im z = 0` forces `Re z = 1`.
    have hsub : closure wedgeSet ⊆
        {w : ℂ | 0 ≤ w.im ∧ w.re - 1 ≤ w.im ∧ 1 - w.re ≤ w.im} :=
      closure_minimal (fun w hw => ⟨hw.1.le, hw.2.1.le, hw.2.2.le⟩)
        ((isClosed_le continuous_const Complex.continuous_im).inter
          ((isClosed_le (by fun_prop) Complex.continuous_im).inter
            (isClosed_le (by fun_prop) Complex.continuous_im)))
    obtain ⟨-, h₂, h₃⟩ := hsub hz
    apply Complex.ext
    · simp only [Complex.one_re]
      linarith
    · simpa using him
  · rintro rfl
    refine ⟨?_, by simp⟩
    -- `1` is the limit of the points `1 + t i` of the wedge as `t → 0⁺`.
    have ht : Tendsto (fun t : ℝ => (1 : ℂ) + t * Complex.I) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous (fun t : ℝ => (1 : ℂ) + t * Complex.I) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with t ht0
    have ht0' : (0 : ℝ) < t := ht0
    refine ⟨?_, ?_, ?_⟩ <;> simpa using ht0'

/-! ### Automation checks -/

/-- Check that `simp` unfolds membership in the wedge to coordinate inequalities. -/
example : (1 + Complex.I : ℂ) ∈ wedgeSet := by
  simp

end SphereCeti.Contour
