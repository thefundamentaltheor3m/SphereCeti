/-
Copyright (c) 2026 Bakhyt Momunov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Contour.ClosedOneForm
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Conjugation and reflection of contour integrals

Reflection in the imaginary axis reverses the conjugated tangent vector. Consequently,
the integrals of conjugate kernels on reflected segments have cancelling real parts.
A real kernel integrated vertically also has zero real part. These are common contour
ingredients for the Layer 9 reality proofs of the E8 and Leech auxiliary functions.

The proofs are independent consequences of Mathlib's segment parametrization and
conjugation of Bochner integrals, at Mathlib commit
`1b1ccf4b088b32fa3f23f2de1127433254a81e1e`,
`Mathlib/MeasureTheory/Integral/{CurveIntegral/Basic,Bochner/ContinuousLinearMap}.lean`.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace SphereCeti.Contour

/-- Reflecting a segment in the imaginary axis negates its conjugated integral.
No convergence assumption is needed for this identity of totalized integrals. -/
theorem conj_curveIntegral_segment (F : ℂ → ℂ) (a b : ℂ) :
    conj (∫ᶜ z in Path.segment a b, scalarOneForm F z) =
      -(∫ᶜ z in Path.segment (-conj a) (-conj b),
        scalarOneForm (fun z ↦ conj (F (-conj z))) z) := by
  simp only [curveIntegral_segment, scalarOneForm_apply,
    intervalIntegral.integral_of_le zero_le_one]
  rw [← integral_conj, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul, map_add, map_mul, map_sub,
    map_neg, conj_ofReal, conj_conj]
  have hp : -((t : ℂ) * (-b - -a) + -a) =
      (t : ℂ) * (b - a) + a := by ring
  rw [hp]
  ring

/-- A kernel and its reflected conjugate contribute opposite real parts. -/
theorem re_curveIntegral_segment_add_reflected
    {F G : ℂ → ℂ} (h : ∀ z, G (-conj z) = conj (F z)) (a b : ℂ) :
    ((∫ᶜ z in Path.segment a b, scalarOneForm F z) +
      (∫ᶜ z in Path.segment (-conj a) (-conj b), scalarOneForm G z)).re = 0 := by
  have hG : G = fun z ↦ conj (F (-conj z)) := by
    funext z
    simpa using h (-conj z)
  have he := congrArg Complex.re (conj_curveIntegral_segment F a b)
  rw [hG]
  simp only [Complex.add_re, conj_re, neg_re] at *
  linarith

/-- Multiplication by the vertical tangent makes an integral of real values imaginary. -/
theorem re_I_mul_integral_eq_zero {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ)
    (hreal : ∀ᵐ t ∂μ, (f t).im = 0) :
    (I * ∫ t, f t ∂μ).re = 0 := by
  have hi : (∫ t, f t ∂μ).im = 0 := by
    change RCLike.im (∫ t, f t ∂μ) = 0
    rw [← integral_im hf]
    exact integral_eq_zero_of_ae hreal
  simp [mul_re, hi]

end SphereCeti.Contour
