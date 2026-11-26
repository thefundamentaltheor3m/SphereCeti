/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.Distribution.SchwartzSpace.CompNormSq
public import SphereCeti.Leech.MinusKernels
public import SphereCeti.Contour.SixPiece
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import SphereCeti.Contour.SchwartzProfile
import SphereCeti.Leech.MinusEigen
import SphereCeti.Leech.MinusKernelRegularity

/-!
# The Leech minus component as a radial Schwartz function

The exponentially decaying kernel `ψ_S` gives a Schwartz profile for the prescribed inverted
contour with power ten and negative ray coefficient. Its defining contour identity identifies
the resulting radial Schwartz function with the existing `-1` Fourier eigencomponent.

The contour is the Leech minus component of Cohn–Kumar–Miller–Radchenko–Viazovska
(Annals of Mathematics 185 (2017), Section 3).
The analytic construction is supplied by `Contour.SchwartzProfile`; no roadmap admissions are
used to define the function or to prove its properties.
-/

public section

open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology Real SchwartzMap FourierTransform

namespace SphereCeti.Leech

private theorem psiSExt_decay : (fun τ : UpperHalfPlane ↦ psiSExt τ)
    =O[UpperHalfPlane.atImInfty] fun τ ↦ Real.exp (-π * τ.im) :=
  isBigO_psiS.congr_left fun τ ↦ (psiSExt_of_im_pos τ.im_pos).symm

/-- The one-variable Schwartz profile of the Leech minus contour eigencomponent. -/
noncomputable def magicMinusProfile : 𝓢(ℝ, ℂ) :=
  Contour.schwartzProfileOfIsBigO 10 (-2) Real.pi_pos differentiableOn_psiSExt psiSExt_decay

/-- At every nonnegative parameter, the profile is the prescribed six-piece contour. -/
theorem magicMinusProfile_eq_contour {r : ℝ} (hr : 0 ≤ r) :
    magicMinusProfile r = Contour.leftLegs (Contour.expKernel minusKernelLeft r) +
      Contour.rightLegs (Contour.expKernel minusKernelRight r) +
      Contour.centralLeg (Contour.expKernel minusKernelCentral r) +
      Contour.verticalRay (Contour.expKernel minusKernelRay r) := by
  unfold magicMinusProfile
  rw [funext minusKernelLeft_eq_psiSExt, funext minusKernelRight_eq_psiSExt,
    funext minusKernelCentral_eq_psiSExt, funext minusKernelRay_def]
  exact Contour.schwartzProfileOfIsBigO_eq_contour 10 (-2) Real.pi_pos
    differentiableOn_psiSExt psiSExt_decay hr

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Leech minus component as a Schwartz function on a real inner product space. -/
noncomputable def magicMinus : 𝓢(E, ℂ) :=
  SchwartzMap.compNormSqCLM ℂ E magicMinusProfile

/-- Evaluate the radial minus component at squared norm. -/
@[simp]
theorem magicMinus_apply (x : E) : magicMinus x = magicMinusProfile (‖x‖ ^ 2) :=
  SchwartzMap.compNormSqCLM_apply magicMinusProfile x

/-- The minus component is radial. -/
@[fun_prop]
theorem isRadial_magicMinus : Function.IsRadial (magicMinus (E := E)) :=
  SchwartzMap.isRadial_compNormSqCLM magicMinusProfile

/-- The Schwartz minus function has exactly the prescribed contour presentation. -/
theorem magicMinus_eq_sixPieceComponent (x : E) :
    magicMinus x = Contour.sixPieceComponent minusKernelLeft minusKernelRight
      minusKernelCentral minusKernelRay x := by
  rw [magicMinus_apply, Contour.sixPieceComponent_def]
  exact magicMinusProfile_eq_contour (sq_nonneg ‖x‖)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In dimension twenty-four the Schwartz minus component is negated by the Fourier transform. -/
theorem fourier_magicMinus (hE : Module.finrank ℝ E = 24) :
    𝓕 (magicMinus (E := E)) = -magicMinus := by
  have heq : (magicMinus : E → ℂ) = Contour.sixPieceComponent minusKernelLeft minusKernelRight
      minusKernelCentral minusKernelRay := funext magicMinus_eq_sixPieceComponent
  apply DFunLike.coe_injective
  rw [SchwartzMap.fourier_coe, heq, fourier_sixPiece_minus hE]
  ext x
  simp only [neg_apply, heq]

example (x : E) : magicMinus x = magicMinusProfile (‖x‖ ^ 2) := by simp

example : Function.IsRadial (magicMinus (E := E)) := by fun_prop

end Radial

end SphereCeti.Leech
