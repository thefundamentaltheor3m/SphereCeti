/-
Copyright (c) 2026 SphereCeti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bakhyt Momunov
-/

module

public import SphereCeti.Analysis.Distribution.SchwartzSpace.CompNormSq
public import SphereCeti.Leech.PlusKernels
public import SphereCeti.Contour.SixPiece
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import SphereCeti.Contour.SchwartzProfile
import SphereCeti.Leech.PlusEigen

/-!
# The Leech plus component as a radial Schwartz function

The exponentially decaying kernel `φ` gives a Schwartz profile for the prescribed inverted
contour with power ten and positive ray coefficient. Its defining contour identity identifies
the resulting radial Schwartz function with the existing `+1` Fourier eigencomponent.

The contour is the Leech plus component of Cohn–Kumar–Miller–Radchenko–Viazovska
(Annals of Mathematics 185 (2017), Section 2).
The analytic construction is supplied by `Contour.SchwartzProfile`; no roadmap admissions are
used to define the function or to prove its properties.
-/

public section

open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology Real SchwartzMap FourierTransform

namespace SphereCeti.Leech

private theorem varphiExt_decay : (fun τ : UpperHalfPlane ↦ varphiExt τ)
    =O[UpperHalfPlane.atImInfty] fun τ ↦ Real.exp (-(2 * π) * τ.im) := by
  exact (isBigO_varphi.congr_left fun τ ↦ (varphiExt_of_im_pos τ.im_pos).symm).congr_right
    fun τ ↦ by ring_nf

/-- The one-variable Schwartz profile of the Leech plus contour eigencomponent. -/
noncomputable def magicPlusProfile : 𝓢(ℝ, ℂ) :=
  Contour.schwartzProfileOfIsBigO 10 2 Real.two_pi_pos differentiableOn_varphiExt varphiExt_decay

/-- At every nonnegative parameter, the profile is the prescribed six-piece contour. -/
theorem magicPlusProfile_eq_contour {r : ℝ} (hr : 0 ≤ r) :
    magicPlusProfile r = Contour.leftLegs (Contour.expKernel plusKernelLeft r) +
      Contour.rightLegs (Contour.expKernel plusKernelRight r) +
      Contour.centralLeg (Contour.expKernel plusKernelCentral r) +
      Contour.verticalRay (Contour.expKernel plusKernelRay r) := by
  unfold magicPlusProfile
  rw [funext plusKernelLeft_def, funext plusKernelRight_def,
    funext plusKernelCentral_def, funext plusKernelRay_def]
  exact Contour.schwartzProfileOfIsBigO_eq_contour 10 2 Real.two_pi_pos
    differentiableOn_varphiExt varphiExt_decay hr

section Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Leech plus component as a Schwartz function on a real inner product space. -/
noncomputable def magicPlus : 𝓢(E, ℂ) :=
  SchwartzMap.compNormSqCLM ℂ E magicPlusProfile

/-- Evaluate the radial plus component at squared norm. -/
@[simp]
theorem magicPlus_apply (x : E) : magicPlus x = magicPlusProfile (‖x‖ ^ 2) :=
  SchwartzMap.compNormSqCLM_apply magicPlusProfile x

/-- The plus component is radial. -/
@[fun_prop]
theorem isRadial_magicPlus : Function.IsRadial (magicPlus (E := E)) :=
  SchwartzMap.isRadial_compNormSqCLM magicPlusProfile

/-- The Schwartz plus function has exactly the prescribed contour presentation. -/
theorem magicPlus_eq_sixPieceComponent (x : E) :
    magicPlus x = Contour.sixPieceComponent plusKernelLeft plusKernelRight
      plusKernelCentral plusKernelRay x := by
  rw [magicPlus_apply, Contour.sixPieceComponent_def]
  exact magicPlusProfile_eq_contour (sq_nonneg ‖x‖)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In dimension twenty-four the Schwartz plus component is fixed by the Fourier transform. -/
theorem fourier_magicPlus (hE : Module.finrank ℝ E = 24) :
    𝓕 (magicPlus (E := E)) = magicPlus := by
  have heq : (magicPlus : E → ℂ) = Contour.sixPieceComponent plusKernelLeft plusKernelRight
      plusKernelCentral plusKernelRay := funext magicPlus_eq_sixPieceComponent
  apply DFunLike.coe_injective
  rw [SchwartzMap.fourier_coe, heq, fourier_sixPiece_plus hE]

example (x : E) : magicPlus x = magicPlusProfile (‖x‖ ^ 2) := by simp

example : Function.IsRadial (magicPlus (E := E)) := by fun_prop

end Radial

end SphereCeti.Leech
