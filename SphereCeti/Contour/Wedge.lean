/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Topology

/-!
# The wedge of the signed contour permutations

The finite branch of the Layer 8 contour deformation compares the left legs `-1 → -1+i → i` of
the magic contour with the right legs `1 → 1+i → i` under the inversion `z ↦ -1/z`.  The
homotopies of that argument take place in the wedge

`{z : 0 < Im z, |Re z - 1| < Im z}`,

an open convex subset of the upper half-plane whose closure meets the real axis only at `1`.
This file defines the wedge and proves those three geometric facts.

## Main definitions and results

* `SphereCeti.Contour.wedgeSet`: the wedge, with the defining formula of the roadmap's
  `SphereCeti.Suggested.Contour.wedgeSet`.
* `SphereCeti.Contour.isOpen_wedgeSet`, `SphereCeti.Contour.convex_wedgeSet`, and
  `SphereCeti.Contour.closure_wedgeSet_inter_real`: the roadmap targets of the same names, with
  the same statements.

This is an independent formalization; no proof text is adapted from another repository.
-/

public section

open Set Filter
open scoped Topology

namespace SphereCeti.Contour

/-- The wedge: an open convex subset of the upper half-plane whose closure meets the real axis
only at `1`. -/
@[expose]
def wedgeSet : Set ℂ := {z | 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im}

theorem mem_wedgeSet {z : ℂ} :
    z ∈ wedgeSet ↔ 0 < z.im ∧ z.re - 1 < z.im ∧ 1 - z.re < z.im :=
  Iff.rfl

theorem isOpen_wedgeSet : IsOpen wedgeSet :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    ((isOpen_lt (by fun_prop) Complex.continuous_im).inter
      (isOpen_lt (by fun_prop) Complex.continuous_im))

/-- The wedge is the intersection of three open half-planes cut out by real-linear functionals. -/
theorem convex_wedgeSet : Convex ℝ wedgeSet := by
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

end SphereCeti.Contour
