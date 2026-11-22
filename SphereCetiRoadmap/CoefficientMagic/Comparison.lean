/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SphereCeti contributors
-/

module

public import SphereCetiRoadmap.CoefficientMagic.Suggested

/-!
# Coefficient construction: comparison with the existing magic functions

This file states milestone C9: the functions constructed from the coefficient systems are the
magic functions of the original roadmap, `SphereCeti.Suggested.E8.magic` and
`SphereCeti.Suggested.Leech.magic`, and they give the same Cohn–Elkies certificates.

The comparison targets are the two equalities `magic_e8_eq` and `magic_leech_eq`.  Everything
else in this file, including the two profile equalities on the half-line `u ≥ 0`, is **proved**
from them and from targets of the original roadmap: the sign inequalities, real-valuedness and exact
zeros are transferred, not reproved.  The dependency of each transferred statement on the
original sign proofs is therefore visible in its proof term.  The coefficient construction in
`SphereCetiRoadmap.CoefficientMagic.Suggested` is independent of this file, and gives no
independent proof of the sign inequalities.

Only the normalization of the certificates is independent of the comparison: it follows from
`magic_zero` and `fourier_magic_zero`, and is stated as the two equations of
`CohnElkies.Certificate.IsNormalized`.
-/

@[expose] public section

open Complex
open scoped FourierTransform SchwartzMap Real

namespace SphereCeti.CoefficientMagic.Comparison

noncomputable section

open SphereCeti.Suggested

/-! ## The constructed functions at the literal dimensions

`Case.dim .e8` and `Case.dim .leech` unfold to `8` and `24`.  The two definitions below restate
`magic` at the literal dimensions used by the original roadmap, so that no cast appears in the
comparison. -/

/-- The coefficient construction in dimension 8, as a radial Schwartz function on `V 8`. -/
def magic8 : RadialSchwartzMap ℂ (V 8) ℂ := magic .e8

/-- The coefficient construction in dimension 24, as a radial Schwartz function on `V 24`. -/
def magic24 : RadialSchwartzMap ℂ (V 24) ℂ := magic .leech

theorem magic8_zero : magic8 0 = 1 := magic_zero .e8

theorem fourier_magic8_zero : 𝓕 (magic8 : 𝓢(V 8, ℂ)) 0 = 1 := fourier_magic_zero .e8

theorem magic24_zero : magic24 0 = 1 := magic_zero .leech

theorem fourier_magic24_zero : 𝓕 (magic24 : 𝓢(V 24, ℂ)) 0 = 1 := fourier_magic_zero .leech

/-! ## Dimension 8 -/

/-- The coefficient construction in dimension 8 is Viazovska's function, with the sign
convention of `E8.magicProfile`. -/
theorem magic_e8_eq : (magic8 : 𝓢(V 8, ℂ)) = (E8.magic : 𝓢(V 8, ℂ)) := by
  sorry

theorem magic_e8_apply (x : V 8) : magic8 x = E8.magic x :=
  congrArg (fun f : 𝓢(V 8, ℂ) => f x) magic_e8_eq

theorem fourier_magic_e8_apply (x : V 8) :
    𝓕 (magic8 : 𝓢(V 8, ℂ)) x = 𝓕 (E8.magic : 𝓢(V 8, ℂ)) x := by
  rw [magic_e8_eq]

/-- Equality of squared-radius profiles on the half-line.  No equality is asserted for `u < 0`,
where the coefficient profile is not specified. -/
theorem profile_solution_e8 {u : ℝ} (hu : 0 ≤ u) :
    profile .e8 (solution .e8) u = E8.magicProfile u := by
  have hn : ‖(radialPoint .e8 u : V 8)‖ ^ 2 = u := norm_radialPoint_sq .e8 hu
  have key : profile .e8 (solution .e8) (‖(radialPoint .e8 u : V 8)‖ ^ 2) =
      E8.magicProfile (‖(radialPoint .e8 u : V 8)‖ ^ 2) :=
    (magic_apply .e8 (radialPoint .e8 u)).symm.trans
      ((magic_e8_apply (radialPoint .e8 u)).trans (E8.magic_apply (radialPoint .e8 u)))
  exact (congrArg (profile .e8 (solution .e8)) hn.symm).trans
    (key.trans (congrArg E8.magicProfile hn))

/-- Transferred from `E8.magic_im_eq_zero`. -/
theorem magic_e8_im_eq_zero (x : V 8) : (magic8 x).im = 0 := by
  rw [magic_e8_apply]; exact E8.magic_im_eq_zero x

/-- Transferred from `E8.fourier_magic_im_eq_zero`. -/
theorem fourier_magic_e8_im_eq_zero (x : V 8) : (𝓕 (magic8 : 𝓢(V 8, ℂ)) x).im = 0 := by
  rw [fourier_magic_e8_apply]; exact E8.fourier_magic_im_eq_zero x

/-- Transferred from `E8.magic_re_nonpos_of_sqrtTwo_le_norm`. -/
theorem magic_e8_re_nonpos {x : V 8} (hx : Real.sqrt 2 ≤ ‖x‖) : (magic8 x).re ≤ 0 := by
  rw [magic_e8_apply]; exact E8.magic_re_nonpos_of_sqrtTwo_le_norm hx

/-- Transferred from `E8.fourier_magic_re_nonneg`. -/
theorem fourier_magic_e8_re_nonneg (x : V 8) : 0 ≤ (𝓕 (magic8 : 𝓢(V 8, ℂ)) x).re := by
  rw [fourier_magic_e8_apply]; exact E8.fourier_magic_re_nonneg x

/-- Transferred from `E8.magic_zero_iff`. -/
theorem magic_e8_zero_iff {x : V 8} (hx : x ≠ 0) :
    magic8 x = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ ‖x‖ ^ 2 = 2 * n := by
  rw [magic_e8_apply]; exact E8.magic_zero_iff hx

/-- Transferred from `E8.fourier_magic_zero_iff`. -/
theorem fourier_magic_e8_zero_iff {x : V 8} (hx : x ≠ 0) :
    𝓕 (magic8 : 𝓢(V 8, ℂ)) x = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ ‖x‖ ^ 2 = 2 * n := by
  rw [fourier_magic_e8_apply]; exact E8.fourier_magic_zero_iff hx

/-- The Cohn–Elkies certificate built from the coefficient construction, through the shared
constructor `Certificate.ofRadial`. -/
def certificate8 : CohnElkies.Certificate 8 (Real.sqrt 2) :=
  CohnElkies.Certificate.ofRadial (Real.sqrt_pos.2 (by norm_num)) (magic8)
    magic_e8_im_eq_zero fourier_magic_e8_im_eq_zero
    (fun _ hx => magic_e8_re_nonpos hx) fourier_magic_e8_re_nonneg
    (by rw [fourier_magic8_zero]; norm_num)

@[simp]
theorem certificate8_f : certificate8.f = (magic8 : 𝓢(V 8, ℂ)) := by
  simp [certificate8]

/-- The function of the new certificate is that of the original one. -/
theorem certificate8_f_eq : certificate8.f = E8.certificate.f := by
  rw [certificate8_f, E8.certificate_f, magic_e8_eq]

/-- Both normalizations of the new certificate, from the coefficient theorem alone: these are the
two conjuncts of `CohnElkies.Certificate.IsNormalized`. -/
theorem certificate8_f_zero : certificate8.f 0 = 1 ∧ 𝓕 certificate8.f 0 = 1 := by
  rw [certificate8_f]; exact ⟨magic8_zero, fourier_magic8_zero⟩

/-! ## Dimension 24 -/

/-- The coefficient construction in dimension 24 is the function of Cohn, Kumar, Miller,
Radchenko and Viazovska. -/
theorem magic_leech_eq : (magic24 : 𝓢(V 24, ℂ)) = (Leech.magic : 𝓢(V 24, ℂ)) := by
  sorry

theorem magic_leech_apply (x : V 24) : magic24 x = Leech.magic x :=
  congrArg (fun f : 𝓢(V 24, ℂ) => f x) magic_leech_eq

theorem fourier_magic_leech_apply (x : V 24) :
    𝓕 (magic24 : 𝓢(V 24, ℂ)) x = 𝓕 (Leech.magic : 𝓢(V 24, ℂ)) x := by
  rw [magic_leech_eq]

/-- Equality of squared-radius profiles on the half-line. -/
theorem profile_solution_leech {u : ℝ} (hu : 0 ≤ u) :
    profile .leech (solution .leech) u = Leech.magicProfile u := by
  have hn : ‖(radialPoint .leech u : V 24)‖ ^ 2 = u := norm_radialPoint_sq .leech hu
  have key : profile .leech (solution .leech) (‖(radialPoint .leech u : V 24)‖ ^ 2) =
      Leech.magicProfile (‖(radialPoint .leech u : V 24)‖ ^ 2) :=
    (magic_apply .leech (radialPoint .leech u)).symm.trans
      ((magic_leech_apply (radialPoint .leech u)).trans (Leech.magic_apply (radialPoint .leech u)))
  exact (congrArg (profile .leech (solution .leech)) hn.symm).trans
    (key.trans (congrArg Leech.magicProfile hn))

/-- Transferred from `Leech.magic_im_eq_zero`. -/
theorem magic_leech_im_eq_zero (x : V 24) : (magic24 x).im = 0 := by
  rw [magic_leech_apply]; exact Leech.magic_im_eq_zero x

/-- Transferred from `Leech.fourier_magic_im_eq_zero`. -/
theorem fourier_magic_leech_im_eq_zero (x : V 24) :
    (𝓕 (magic24 : 𝓢(V 24, ℂ)) x).im = 0 := by
  rw [fourier_magic_leech_apply]; exact Leech.fourier_magic_im_eq_zero x

/-- Transferred from `Leech.magic_re_nonpos_of_two_le_norm`. -/
theorem magic_leech_re_nonpos {x : V 24} (hx : 2 ≤ ‖x‖) : (magic24 x).re ≤ 0 := by
  rw [magic_leech_apply]; exact Leech.magic_re_nonpos_of_two_le_norm hx

/-- Transferred from `Leech.fourier_magic_re_nonneg`. -/
theorem fourier_magic_leech_re_nonneg (x : V 24) :
    0 ≤ (𝓕 (magic24 : 𝓢(V 24, ℂ)) x).re := by
  rw [fourier_magic_leech_apply]; exact Leech.fourier_magic_re_nonneg x

/-- Transferred from `Leech.magic_zero_iff_of_two_le_norm`, with its scope `‖x‖ ≥ 2`. -/
theorem magic_leech_zero_iff_of_two_le_norm {x : V 24} (hx : 2 ≤ ‖x‖) :
    magic24 x = 0 ↔ ∃ n : ℕ, 2 ≤ n ∧ ‖x‖ ^ 2 = 2 * n := by
  rw [magic_leech_apply]; exact Leech.magic_zero_iff_of_two_le_norm hx

/-- The Cohn–Elkies certificate built from the coefficient construction. -/
def certificate24 : CohnElkies.Certificate 24 2 :=
  CohnElkies.Certificate.ofRadial (by norm_num) (magic24)
    magic_leech_im_eq_zero fourier_magic_leech_im_eq_zero
    (fun _ hx => magic_leech_re_nonpos hx) fourier_magic_leech_re_nonneg
    (by rw [fourier_magic24_zero]; norm_num)

@[simp]
theorem certificate24_f : certificate24.f = (magic24 : 𝓢(V 24, ℂ)) := by
  simp [certificate24]

/-- The function of the new certificate is that of the original one. -/
theorem certificate24_f_eq : certificate24.f = Leech.certificate.f := by
  rw [certificate24_f, Leech.certificate_f, magic_leech_eq]

/-- Both normalizations of the new certificate, from the coefficient theorem alone: these are the
two conjuncts of `CohnElkies.Certificate.IsNormalized`. -/
theorem certificate24_f_zero : certificate24.f 0 = 1 ∧ 𝓕 certificate24.f 0 = 1 := by
  rw [certificate24_f]; exact ⟨magic24_zero, fourier_magic24_zero⟩

end

end SphereCeti.CoefficientMagic.Comparison
