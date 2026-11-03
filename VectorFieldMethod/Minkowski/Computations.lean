/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.VectorFields
public import VectorFieldMethod.Minkowski.WaveOperator
public import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Explicit computations with the Minkowski operators

These computations check the definitions of the coordinate layer against the standard formulas.
The values on the coordinate functions themselves (`∂_t t = 1`, `L_a t = x_a`, `Ω_ab x_c = ...`,
`S x_a = x_a`, ...) are the `@[simp]` lemmas next to the definitions; this file treats the
quadratic functions `t²`, `x_a²`, `r²` and `t² - r²`.

The radius `r = |x|` is not differentiable at `x = 0`, so every computation involving `r` goes
through `r² = ∑ a, x_a²` (`radius_sq`).

## Main statements

* `dAlembertian_timeCoord_sq_sub_radius_sq`: `□(t² - r²) = -8`.
* `dAlembertian_timeCoord_sq`: `□(t²) = -2`; `dAlembertian_spaceCoord_sq`: `□(x_a²) = 2`.
* `boost_timeCoord_sq_sub_radius_sq`: `L_a (t² - r²) = 0`.
* `rotation_radius_sq`: `Ω_ab (r²) = 0`.
* `scaling_timeCoord_sq_sub_radius_sq`: `S (t² - r²) = 2 (t² - r²)`.
-/

@[expose] public noncomputable section

namespace VectorFieldMethod.Minkowski

/-! ### First derivatives of the quadratic functions -/

/-- `V (t²) = 2 t V⁰`. -/
theorem derivAlong_timeCoord_sq (V : Spacetime → Spacetime) :
    derivAlong V (fun p ↦ timeCoord p ^ 2) = fun p ↦ 2 * timeCoord p * (V p).1 := by
  funext p
  rw [derivAlong_eq_of_hasFDerivAt ((hasFDerivAt_timeCoord p).pow 2)]
  simp [timeCoord]

/-- `V (x_a²) = 2 x_a Vᵃ`. -/
theorem derivAlong_spaceCoord_sq (V : Spacetime → Spacetime) (a : Fin 3) :
    derivAlong V (fun p ↦ spaceCoord a p ^ 2) = fun p ↦ 2 * spaceCoord a p * (V p).2 a := by
  funext p
  rw [derivAlong_eq_of_hasFDerivAt ((hasFDerivAt_spaceCoord a p).pow 2)]
  simp [spaceCoord]

/-- `V (r²) = 2 ∑ a, x_a Vᵃ`. -/
theorem derivAlong_radius_sq (V : Spacetime → Spacetime) :
    derivAlong V (fun p ↦ radius p ^ 2) = fun p ↦ 2 * ∑ a, spaceCoord a p * (V p).2 a := by
  funext p
  rw [radius_sq_eq_sum, derivAlong_eq_of_hasFDerivAt
    (HasFDerivAt.fun_sum fun a _ ↦ (hasFDerivAt_spaceCoord a p).pow 2)]
  simp [spaceCoord, Finset.mul_sum, mul_assoc]

/-- `V (t² - r²) = 2 t V⁰ - 2 ∑ a, x_a Vᵃ`. -/
theorem derivAlong_timeCoord_sq_sub_radius_sq (V : Spacetime → Spacetime) :
    derivAlong V (fun p ↦ timeCoord p ^ 2 - radius p ^ 2) =
      fun p ↦ 2 * timeCoord p * (V p).1 - 2 * ∑ a, spaceCoord a p * (V p).2 a := by
  funext p
  have hr : (fun p ↦ timeCoord p ^ 2 - radius p ^ 2) =
      fun p ↦ timeCoord p ^ 2 - ∑ a, spaceCoord a p ^ 2 := by
    simp_rw [radius_sq]
  rw [hr, derivAlong_eq_of_hasFDerivAt (((hasFDerivAt_timeCoord p).pow 2).fun_sub
    (HasFDerivAt.fun_sum fun a _ ↦ (hasFDerivAt_spaceCoord a p).pow 2))]
  simp [timeCoord, spaceCoord, Finset.mul_sum, mul_assoc]

/-- `∂_t (t² - r²) = 2 t`. -/
theorem timeDeriv_timeCoord_sq_sub_radius_sq :
    ∂ₜ (fun p ↦ timeCoord p ^ 2 - radius p ^ 2) = fun p ↦ 2 * timeCoord p := by
  rw [timeDeriv, derivAlong_timeCoord_sq_sub_radius_sq]
  funext p
  simp [timeField]

/-- `∂_a (t² - r²) = -2 x_a`. -/
theorem spaceDeriv_timeCoord_sq_sub_radius_sq (a : Fin 3) :
    ∂ₓ[a] (fun p ↦ timeCoord p ^ 2 - radius p ^ 2) = fun p ↦ -2 * spaceCoord a p := by
  rw [spaceDeriv, derivAlong_timeCoord_sq_sub_radius_sq]
  funext p
  simp [spaceField, PiLp.single_apply]

/-! ### The wave operator -/

/-- `□(t² - r²) = -8`. -/
theorem dAlembertian_timeCoord_sq_sub_radius_sq :
    □ (fun p ↦ timeCoord p ^ 2 - radius p ^ 2) = fun _ ↦ -8 := by
  funext p
  rw [dAlembertian_eq, timeDeriv_timeCoord_sq_sub_radius_sq]
  simp_rw [spaceDeriv_timeCoord_sq_sub_radius_sq]
  simp only [timeDeriv, spaceDeriv, derivAlong_const_mul]
  simp [timeField, spaceField]
  norm_num

/-- `□(t²) = -2`. -/
theorem dAlembertian_timeCoord_sq : □ (fun p ↦ timeCoord p ^ 2) = fun _ ↦ -2 := by
  funext p
  simp [dAlembertian_eq, timeDeriv, spaceDeriv, derivAlong_timeCoord_sq, derivAlong_const_mul,
    timeField, spaceField]

/-- `□(x_a²) = 2`. -/
theorem dAlembertian_spaceCoord_sq (a : Fin 3) : □ (fun p ↦ spaceCoord a p ^ 2) = fun _ ↦ 2 := by
  have ht : ∂ₜ (fun p ↦ spaceCoord a p ^ 2) = fun _ ↦ 0 := by
    rw [timeDeriv, derivAlong_spaceCoord_sq]
    funext q
    simp [timeField]
  have hs (b : Fin 3) : ∂ₓ[b] (fun p ↦ spaceCoord a p ^ 2) =
      fun q ↦ (if b = a then 2 else 0) * spaceCoord a q := by
    rw [spaceDeriv, derivAlong_spaceCoord_sq]
    funext q
    by_cases h : b = a
    · subst h
      simp [spaceField, mul_comm]
    · simp [spaceField, h, Ne.symm h]
  funext p
  simp only [dAlembertian_eq, ht, hs]
  simp only [timeDeriv_const, spaceDeriv, derivAlong_const_mul]
  simp [spaceField]

/-! ### Rotations, boosts and scaling -/

/-- `L_a (t² - r²) = 0`. -/
theorem boost_timeCoord_sq_sub_radius_sq (a : Fin 3) :
    boost a (fun p ↦ timeCoord p ^ 2 - radius p ^ 2) = fun _ ↦ 0 := by
  rw [boost, derivAlong_timeCoord_sq_sub_radius_sq]
  funext p
  simp [boostField, PiLp.single_apply]
  ring

/-- `Ω_ab (r²) = 0`. -/
theorem rotation_radius_sq (a b : Fin 3) : rotation a b (fun p ↦ radius p ^ 2) = fun _ ↦ 0 := by
  rw [rotation, derivAlong_radius_sq]
  funext p
  simp [rotationField, PiLp.single_apply, mul_sub]
  ring

/-- `S (t² - r²) = 2 (t² - r²)`. -/
theorem scaling_timeCoord_sq_sub_radius_sq :
    scaling (fun p ↦ timeCoord p ^ 2 - radius p ^ 2) =
      fun p ↦ 2 * (timeCoord p ^ 2 - radius p ^ 2) := by
  rw [scaling, derivAlong_timeCoord_sq_sub_radius_sq]
  funext p
  rw [radius_sq]
  simp only [scalingField, sq, timeCoord, spaceCoord]
  ring

end VectorFieldMethod.Minkowski
