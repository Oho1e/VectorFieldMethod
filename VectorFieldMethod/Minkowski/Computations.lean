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

These computations are for real-valued functions (`F = ℝ`). The section "Sanity checks" at the end
applies the operators to complex-valued and vector-valued functions.
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

/-! ### Sanity checks

The operators act on functions with values in an arbitrary real normed space `F`. The first
examples apply them to complex-valued and vector-valued functions, through the commutation with
continuous linear maps (`dAlembertian_comp_left`, `kleinGordon_comp_left`), the homogeneity under
complex scalars (`timeDeriv_const_smul_field`, `dAlembertian_const_smul_field`), and the reduction
of a genuinely complex-valued function to its real and imaginary parts (`Complex.reCLM`,
`Complex.imCLM`). The last examples check that for `F = ℝ`, where `•` is multiplication, the
definitions and the defining formulas are the real-valued ones, by `rfl` or by the general lemma
itself. -/

/-- `□ (t² + i x₁²) = -2 + 2i`, by reduction to the real part `t²` and the imaginary part `x₁²`.
(The Lean index `0` of `spaceCoord` is the mathematical index `1`.) -/
example :
    □ (fun p ↦ ((timeCoord p ^ 2 : ℝ) : ℂ) + Complex.I * ((spaceCoord 0 p ^ 2 : ℝ) : ℂ)) =
      fun _ ↦ -2 + 2 * Complex.I := by
  set w : Spacetime → ℂ :=
    fun p ↦ ((timeCoord p ^ 2 : ℝ) : ℂ) + Complex.I * ((spaceCoord 0 p ^ 2 : ℝ) : ℂ)
  have hw (p : Spacetime) : ContDiffAt ℝ 2 w p := by
    have h : w = fun p ↦ Complex.ofRealCLM (timeCoord p ^ 2) +
        Complex.I * Complex.ofRealCLM (spaceCoord 0 p ^ 2) := rfl
    rw [h]
    fun_prop
  have hre : Complex.reCLM ∘ w = fun p ↦ timeCoord p ^ 2 := by
    funext p
    simp [w, -Complex.ofReal_pow]
  have him : Complex.imCLM ∘ w = fun p ↦ spaceCoord 0 p ^ 2 := by
    funext p
    simp [w, -Complex.ofReal_pow]
  funext p
  apply Complex.ext
  · rw [← Complex.reCLM_apply, ← dAlembertian_comp_left Complex.reCLM (hw p), hre,
      dAlembertian_timeCoord_sq]
    simp
  · rw [← Complex.imCLM_apply, ← dAlembertian_comp_left Complex.imCLM (hw p), him,
      dAlembertian_spaceCoord_sq]
    simp

/-- Homogeneity under complex scalars, without hypotheses on `u`. -/
example (u : Spacetime → ℂ) :
    ∂ₜ (Complex.I • u) = Complex.I • ∂ₜ u ∧ □ (Complex.I • u) = Complex.I • □ u :=
  ⟨timeDeriv_const_smul_field _ u, dAlembertian_const_smul_field _ u⟩

/-- `□ (t²) = -2` for `t²` as a complex-valued function. -/
example : □ (fun p ↦ ((timeCoord p ^ 2 : ℝ) : ℂ)) = fun _ ↦ -2 := by
  funext p
  have h : (fun p ↦ ((timeCoord p ^ 2 : ℝ) : ℂ)) = Complex.ofRealCLM ∘ fun p ↦ timeCoord p ^ 2 :=
    rfl
  rw [h, dAlembertian_comp_left _ (by fun_prop), dAlembertian_timeCoord_sq, Complex.ofRealCLM_apply]
  push_cast
  rfl

/-- `KG_m (t²) = -2 - m² t²` for `t²` as a complex-valued function. -/
example (m : ℝ) :
    kleinGordon m (fun p ↦ ((timeCoord p ^ 2 : ℝ) : ℂ)) =
      fun p ↦ -2 - m ^ 2 • ((timeCoord p ^ 2 : ℝ) : ℂ) := by
  funext p
  have h : (fun p ↦ ((timeCoord p ^ 2 : ℝ) : ℂ)) = Complex.ofRealCLM ∘ fun p ↦ timeCoord p ^ 2 :=
    rfl
  rw [h, kleinGordon_comp_left m _ (by fun_prop), kleinGordon_apply, dAlembertian_timeCoord_sq,
    map_sub, map_smul, Complex.ofRealCLM_apply, Complex.ofRealCLM_apply]
  push_cast
  rfl

/-- `□ (t² w) = -2 w` for a fixed vector `w` of any real normed space `F`. -/
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (w : F) :
    □ (fun p ↦ timeCoord p ^ 2 • w) = fun _ ↦ (-2 : ℝ) • w := by
  funext p
  have h : (fun p ↦ timeCoord p ^ 2 • w) =
      ContinuousLinearMap.toSpanSingleton ℝ w ∘ fun p ↦ timeCoord p ^ 2 :=
    rfl
  rw [h, dAlembertian_comp_left _ (by fun_prop), dAlembertian_timeCoord_sq,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- For `F = ℝ`, `□` is the original `∑ α, ∑ β, η α β * ∂[α] (∂[β] u) p`. -/
example (u : Spacetime → ℝ) (p : Spacetime) :
    □ u p = ∑ α, ∑ β, η α β * ∂[α] (∂[β] u) p :=
  rfl

/-- For `F = ℝ`, the Klein–Gordon operator is the original `□ u p - m ^ 2 * u p`. -/
example (m : ℝ) (u : Spacetime → ℝ) (p : Spacetime) :
    kleinGordon m u p = □ u p - m ^ 2 * u p :=
  rfl

/-- For `F = ℝ`, `rotation_eq`, `boost_eq` and `scaling_eq` give the formulas with products. -/
example (a b : Fin 3) (u : Spacetime → ℝ) (p : Spacetime) :
    rotation a b u p = spaceCoord a p * ∂ₓ[b] u p - spaceCoord b p * ∂ₓ[a] u p ∧
      boost a u p = timeCoord p * ∂ₓ[a] u p + spaceCoord a p * ∂ₜ u p ∧
      scaling u p = timeCoord p * ∂ₜ u p + ∑ c, spaceCoord c p * ∂ₓ[c] u p :=
  ⟨rotation_eq a b u p, boost_eq a u p, scaling_eq u p⟩

end VectorFieldMethod.Minkowski
