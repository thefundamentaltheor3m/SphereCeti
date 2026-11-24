/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Bakhyt Momunov
-/

module

public import TauCeti.Analysis.Complex.LaplaceTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivatives of truncated Laplace transforms

For an interval-integrable kernel `f`, the truncated Laplace transform
`z ↦ ∫ t in a..b, f t * exp (-z t)` is entire by TauCeti's
`differentiable_intervalIntegral_mul_cexp_neg_mul`. This file supplies its explicit first and
iterated derivatives: each derivative inserts a factor `-t` into the integrand. No regularity
of `f` beyond interval integrability is needed.

The real-parameter version allows an arbitrary complex coefficient `c`, with each derivative
inserting `-c t`. Specializing to `c = π` and `(0, 1]` gives the derivative formulas and
smoothness of the bounded-interval profiles used by the magic functions. Composing the profile
with squared norm is smooth even at the origin.

This is a shared prerequisite for README Layer 7 and MIGRATION J3, differentiation under
parameterized integrals and smoothness of the derivative families. It does not establish the
decay or the Schwartz bounds of the dimension-specific magic functions.

## Provenance

The first-derivative proof adapts the dominated-differentiation argument of
`TauCeti.differentiable_intervalIntegral_mul_cexp_neg_mul`, from
`TauCetiProject/TauCeti@83769e442d55cda9d85b3927a93b286831c595ff`, file
`TauCeti/Analysis/Complex/LaplaceTransform.lean` (Tau Ceti contributors, Apache-2.0), retaining
the derivative supplied by Mathlib's theorem instead of discarding it. The iterated derivative
formulas and real-parameter corollaries are new consequences. Smoothness reuses TauCeti's
existing entire-function result.

The intended upstream home is TauCeti's complex Laplace-transform API, beside the existing
truncated-transform theorem.
-/

public section

open Filter MeasureTheory Set Metric
open scoped Topology Complex Interval ContDiff

namespace TauCeti

variable {f : ℝ → ℂ} {a b : ℝ}

/-- The derivative of a truncated Laplace transform is the same transform with kernel `-t f(t)`.
The interval may have either orientation. -/
theorem hasDerivAt_intervalIntegral_mul_cexp_neg_mul
    (hf : IntervalIntegrable f volume a b) (z₀ : ℂ) :
    HasDerivAt (fun z : ℂ ↦ ∫ t in a..b, f t * cexp (-z * t))
      (∫ t in a..b, (-(t : ℂ)) * f t * cexp (-z₀ * t)) z₀ := by
  set C := max |a| |b|
  set K := Real.exp ((‖z₀‖ + 1) * C)
  have habs : ∀ t ∈ Ι a b, |t| ≤ C := by
    intro t ht
    rcases le_total a b with hab | hab
    · rw [uIoc_of_le hab] at ht
      exact abs_le_max_abs_abs ht.1.le ht.2
    · rw [uIoc_of_ge hab] at ht
      exact (abs_le_max_abs_abs ht.1.le ht.2).trans_eq (max_comm _ _)
  have hexp : ∀ t ∈ Ι a b, ∀ z ∈ ball z₀ 1, ‖cexp (-z * t)‖ ≤ K := by
    intro t ht z hz
    rw [Complex.norm_exp, Complex.re_mul_ofReal, Complex.neg_re]
    refine Real.exp_le_exp.mpr ?_
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_sub_norm_le z z₀
      rw [mem_ball_iff_norm] at hz
      linarith
    calc -z.re * t ≤ |z.re| * |t| := (le_abs_self _).trans_eq (by rw [abs_mul, abs_neg])
      _ ≤ (‖z₀‖ + 1) * C :=
        mul_le_mul ((Complex.abs_re_le_norm z).trans hz') (habs t ht) (abs_nonneg _)
          (by positivity)
  have hcont : ∀ z : ℂ, Continuous fun t : ℝ ↦ cexp (-z * t) := fun z ↦ by fun_prop
  have hderiv := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun z t ↦ f t * (cexp (-z * t) * (-(t : ℂ))))
    (bound := fun t ↦ C * K * ‖f t‖) (ball_mem_nhds z₀ one_pos)
    (.of_forall fun z ↦ hf.def'.aestronglyMeasurable.mul (hcont z).aestronglyMeasurable)
    (hf.mul_continuousOn (hcont z₀).continuousOn)
    (hf.def'.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ ↦
      cexp (-z₀ * t) * (-(t : ℂ))).aestronglyMeasurable)
    (.of_forall fun t ht z hz ↦ by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      calc ‖f t‖ * (‖cexp (-z * t)‖ * |t|) ≤ ‖f t‖ * (K * C) := by
              gcongr
              exacts [hexp t ht z hz, habs t ht]
        _ = C * K * ‖f t‖ := by ring)
    (hf.norm.const_mul _)
    (.of_forall fun t _ z _ ↦ by
      have h := ((hasDerivAt_id' z).neg.mul_const (t : ℂ)).cexp.const_mul (f t)
      simpa using h)).2
  convert hderiv using 1
  apply intervalIntegral.integral_congr
  intro t _
  ring

/-- Every complex derivative of a truncated Laplace transform is obtained by inserting a power
of `-t` into the integrand. -/
theorem iteratedDeriv_intervalIntegral_mul_cexp_neg_mul
    (hf : IntervalIntegrable f volume a b) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun z : ℂ ↦ ∫ t in a..b, f t * cexp (-z * t)) z =
      ∫ t in a..b, (-(t : ℂ)) ^ n * f t * cexp (-z * t) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    have hfn : IntervalIntegrable (fun t : ℝ ↦ (-(t : ℂ)) ^ n * f t) volume a b :=
      hf.continuousOn_mul (by fun_prop)
    rw [(hasDerivAt_intervalIntegral_mul_cexp_neg_mul hfn z).deriv]
    apply intervalIntegral.integral_congr
    intro t _
    ring

/-- The derivative with respect to a real parameter, for an arbitrary complex coefficient `c`,
inserts the factor `-c t`. -/
theorem hasDerivAt_intervalIntegral_mul_cexp_neg_mul_real
    (hf : IntervalIntegrable f volume a b) (c : ℂ) (r : ℝ) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in a..b, f t * cexp (-(c * (r : ℂ)) * t))
      (∫ t in a..b, (-c * (t : ℂ)) * f t * cexp (-(c * (r : ℂ)) * t)) r := by
  have h := ((hasDerivAt_intervalIntegral_mul_cexp_neg_mul hf (c * (r : ℂ))).comp
    (r : ℂ) ((hasDerivAt_id' (r : ℂ)).const_mul c)).comp_ofReal
  convert h using 1
  · rfl
  · rw [mul_one, ← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _
    ring

/-- Every real derivative of a truncated Laplace transform with coefficient `c` is obtained by
inserting the corresponding power of `-c t`. -/
theorem iteratedDeriv_intervalIntegral_mul_cexp_neg_mul_real
    (hf : IntervalIntegrable f volume a b) (c : ℂ) (n : ℕ) (r : ℝ) :
    iteratedDeriv n
        (fun r : ℝ ↦ ∫ t in a..b, f t * cexp (-(c * (r : ℂ)) * t)) r =
      ∫ t in a..b, (-c * (t : ℂ)) ^ n * f t * cexp (-(c * (r : ℂ)) * t) := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    have hfn : IntervalIntegrable (fun t : ℝ ↦ (-c * (t : ℂ)) ^ n * f t) volume a b :=
      hf.continuousOn_mul (by fun_prop)
    rw [(hasDerivAt_intervalIntegral_mul_cexp_neg_mul_real hfn c r).deriv]
    apply intervalIntegral.integral_congr
    intro t _
    ring

/-- Truncated Laplace transforms with a real parameter are smooth for any complex coefficient.
This reuses the existing entire-function theorem. -/
theorem contDiff_intervalIntegral_mul_cexp_neg_mul_real
    (hf : IntervalIntegrable f volume a b) (c : ℂ) :
    ContDiff ℝ ∞ (fun r : ℝ ↦ ∫ t in a..b, f t * cexp (-(c * (r : ℂ)) * t)) := by
  have h : ContDiff ℂ ∞ (fun z : ℂ ↦ ∫ t in a..b, f t * cexp (-z * t)) :=
    (differentiable_intervalIntegral_mul_cexp_neg_mul hf).contDiff
  exact (h.restrict_scalars ℝ).comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- The first derivative of the profile on `(0, 1]` in the sphere-packing normalization. -/
theorem hasDerivAt_integral_Ioc_mul_cexp_neg_pi_mul
    (hf : IntegrableOn f (Ioc 0 1)) (r : ℝ) :
    HasDerivAt (fun r : ℝ ↦ ∫ t in Ioc (0 : ℝ) 1,
        f t * cexp (-(Real.pi : ℂ) * (r : ℂ) * t))
      (∫ t in Ioc (0 : ℝ) 1,
        (-(Real.pi : ℂ) * (t : ℂ)) * f t * cexp (-(Real.pi : ℂ) * (r : ℂ) * t)) r := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le (a := 0) (b := 1)
    zero_le_one).mpr hf
  simpa only [intervalIntegral.integral_of_le zero_le_one, neg_mul] using
    hasDerivAt_intervalIntegral_mul_cexp_neg_mul_real hi (Real.pi : ℂ) r

/-- All real derivatives of the profile on `(0, 1]` in the sphere-packing normalization. -/
theorem iteratedDeriv_integral_Ioc_mul_cexp_neg_pi_mul
    (hf : IntegrableOn f (Ioc 0 1)) (n : ℕ) (r : ℝ) :
    iteratedDeriv n (fun r : ℝ ↦ ∫ t in Ioc (0 : ℝ) 1,
        f t * cexp (-(Real.pi : ℂ) * (r : ℂ) * t)) r =
      ∫ t in Ioc (0 : ℝ) 1,
        (-(Real.pi : ℂ) * (t : ℂ)) ^ n * f t *
          cexp (-(Real.pi : ℂ) * (r : ℂ) * t) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le (a := 0) (b := 1)
    zero_le_one).mpr hf
  simpa only [intervalIntegral.integral_of_le zero_le_one, neg_mul] using
    iteratedDeriv_intervalIntegral_mul_cexp_neg_mul_real hi (Real.pi : ℂ) n r

/-- The bounded-interval magic-function profile is smooth on all of `ℝ`, including `r = 0`. -/
theorem contDiff_integral_Ioc_mul_cexp_neg_pi_mul (hf : IntegrableOn f (Ioc 0 1)) :
    ContDiff ℝ ∞ (fun r : ℝ ↦ ∫ t in Ioc (0 : ℝ) 1,
      f t * cexp (-(Real.pi : ℂ) * (r : ℂ) * t)) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le (a := 0) (b := 1)
    zero_le_one).mpr hf
  simpa only [intervalIntegral.integral_of_le zero_le_one, neg_mul] using
    contDiff_intervalIntegral_mul_cexp_neg_mul_real hi (Real.pi : ℂ)

/-- Substituting squared norm into a bounded-interval magic-function profile gives a smooth
function on a real inner product space, including at the origin. -/
theorem contDiff_integral_Ioc_mul_cexp_neg_pi_mul_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hf : IntegrableOn f (Ioc 0 1)) :
    ContDiff ℝ ∞ (fun x : E ↦ ∫ t in Ioc (0 : ℝ) 1,
      f t * cexp (-(Real.pi : ℂ) * (‖x‖ ^ 2 : ℝ) * t)) :=
  (contDiff_integral_Ioc_mul_cexp_neg_pi_mul hf).comp (contDiff_norm_sq ℝ)

/-! ## Normalization checks -/

/-- At the origin, the second derivative has the positive `π²`-weighted second moment. -/
example (hf : IntegrableOn f (Ioc 0 1)) :
    iteratedDeriv 2 (fun r : ℝ ↦ ∫ t in Ioc (0 : ℝ) 1,
        f t * cexp (-(Real.pi : ℂ) * (r : ℂ) * t)) 0 =
      ∫ t in Ioc (0 : ℝ) 1, ((Real.pi : ℂ) * (t : ℂ)) ^ 2 * f t := by
  simpa using iteratedDeriv_integral_Ioc_mul_cexp_neg_pi_mul hf 2 0

/-- At the origin, the first derivative is the negative `π`-weighted first moment of the kernel. -/
example (hf : IntegrableOn f (Ioc 0 1)) :
    deriv (fun r : ℝ ↦ ∫ t in Ioc (0 : ℝ) 1,
        f t * cexp (-(Real.pi : ℂ) * (r : ℂ) * t)) 0 =
      ∫ t in Ioc (0 : ℝ) 1, (-(Real.pi : ℂ) * (t : ℂ)) * f t := by
  simpa using (hasDerivAt_integral_Ioc_mul_cexp_neg_pi_mul hf 0).deriv

end TauCeti
