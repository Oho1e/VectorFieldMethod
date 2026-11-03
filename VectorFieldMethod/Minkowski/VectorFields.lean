/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.Derivative

/-!
# The Minkowski vector fields: rotations, boosts and scaling

Besides the four translations `∂_α` (`partialDeriv`), the vector field method uses

* the rotations `Ω_ab = x_a ∂_b - x_b ∂_a` (`rotation a b`), defined for all `a b : Fin 3`; since
  `Ω_ba = -Ω_ab` and `Ω_aa = 0`, only the three with `a < b` are independent;
* the Lorentz boosts `L_a = t ∂_a + x_a ∂_t` (`boost a`), three of them;
* the scaling field `S = t ∂_t + ∑ a, x_a ∂_a` (`scaling`).

This gives `4 + 3 + 3 + 1 = 11` vector fields. Each is `derivAlong` applied to a named component
field (`rotationField`, `boostField`, `scalingField`). Spatial indices are raised and lowered
without changing the value, `x_a = x^a`. Like `derivAlong`, the operators act on functions
`Spacetime → F` with values in an arbitrary real normed space `F`; the coefficients `t`, `x_a`
are real and act by scalar multiplication.

## Main statements

* `rotation_eq`, `boost_eq`, `scaling_eq`: the defining formulas in terms of `∂_t`, `∂_a`.
* Linearity (`*_smul`, `*_add`), smoothness (`contDiff_*`, `contDiff_infty_*`) and commutation
  with continuous linear maps (`*_clm_comp`).
* Values on the coordinates: `rotation_spaceCoord`, `boost_timeCoord`, `scaling_spaceCoord`, etc.
* `rotation_swap`: `Ω_ba = -Ω_ab`.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace VectorFieldMethod.Minkowski

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {u v : Spacetime → F} {p : Spacetime} {n : ℕ∞ω}

/-! ### Definitions -/

/-- The component field of the rotation `Ω_ab = x_a ∂_b - x_b ∂_a`:
`p ↦ (0, x_a e_b - x_b e_a)`. -/
def rotationField (a b : Fin 3) : Spacetime → Spacetime :=
  fun p ↦
    (0, spaceCoord a p • EuclideanSpace.single b 1 - spaceCoord b p • EuclideanSpace.single a 1)

/-- The rotation `Ω_ab u = x_a ∂_b u - x_b ∂_a u`, for `a b : Fin 3`. -/
def rotation (a b : Fin 3) : (Spacetime → F) → Spacetime → F :=
  derivAlong (rotationField a b)

/-- The component field of the boost `L_a = t ∂_a + x_a ∂_t`: `p ↦ (x_a, t e_a)`. -/
def boostField (a : Fin 3) : Spacetime → Spacetime :=
  fun p ↦ (spaceCoord a p, timeCoord p • EuclideanSpace.single a 1)

/-- The Lorentz boost `L_a u = t ∂_a u + x_a ∂_t u`, for `a : Fin 3`. -/
def boost (a : Fin 3) : (Spacetime → F) → Spacetime → F :=
  derivAlong (boostField a)

/-- The component field of the scaling field `S = t ∂_t + ∑ a, x_a ∂_a`: its components at
`p = (t, x)` are `(t, x)`, so it is the identity map `p ↦ p`. -/
def scalingField : Spacetime → Spacetime :=
  fun p ↦ p

/-- The scaling vector field `S u = t ∂_t u + ∑ a, x_a ∂_a u`. -/
def scaling : (Spacetime → F) → Spacetime → F :=
  derivAlong scalingField

theorem rotation_apply (a b : Fin 3) (u : Spacetime → F) (p : Spacetime) :
    rotation a b u p = fderiv ℝ u p (rotationField a b p) :=
  rfl

theorem boost_apply (a : Fin 3) (u : Spacetime → F) (p : Spacetime) :
    boost a u p = fderiv ℝ u p (boostField a p) :=
  rfl

theorem scaling_apply (u : Spacetime → F) (p : Spacetime) :
    scaling u p = fderiv ℝ u p p :=
  rfl

/-! ### The defining formulas -/

theorem rotationField_eq (a b : Fin 3) (p : Spacetime) :
    rotationField a b p = spaceCoord a p • spaceField b p - spaceCoord b p • spaceField a p := by
  ext <;> simp [rotationField, spaceField]

theorem boostField_eq (a : Fin 3) (p : Spacetime) :
    boostField a p = timeCoord p • spaceField a p + spaceCoord a p • timeField p := by
  ext <;> simp [boostField, spaceField, timeField]

theorem scalingField_eq (p : Spacetime) :
    scalingField p = timeCoord p • timeField p + ∑ a, spaceCoord a p • spaceField a p := by
  ext i
  · simp [scalingField, timeField, spaceField, timeCoord, Prod.fst_sum]
  · simp [scalingField, timeField, spaceField, spaceCoord, Prod.snd_sum, WithLp.ofLp_sum,
      Finset.sum_apply, Pi.single_apply, mul_ite]

/-- `Ω_ab u = x_a ∂_b u - x_b ∂_a u`. -/
theorem rotation_eq (a b : Fin 3) (u : Spacetime → F) (p : Spacetime) :
    rotation a b u p = spaceCoord a p • ∂ₓ[b] u p - spaceCoord b p • ∂ₓ[a] u p := by
  rw [rotation_apply, rotationField_eq, map_sub, map_smul, map_smul]
  rfl

/-- `L_a u = t ∂_a u + x_a ∂_t u`. -/
theorem boost_eq (a : Fin 3) (u : Spacetime → F) (p : Spacetime) :
    boost a u p = timeCoord p • ∂ₓ[a] u p + spaceCoord a p • ∂ₜ u p := by
  rw [boost_apply, boostField_eq, map_add, map_smul, map_smul]
  rfl

/-- `S u = t ∂_t u + ∑ a, x_a ∂_a u`. -/
theorem scaling_eq (u : Spacetime → F) (p : Spacetime) :
    scaling u p = timeCoord p • ∂ₜ u p + ∑ a, spaceCoord a p • ∂ₓ[a] u p := by
  rw [scaling, derivAlong_apply, scalingField_eq, map_add, map_smul, map_sum]
  simp only [map_smul]
  rfl

/-! ### Antisymmetry of the rotations -/

theorem rotationField_swap (a b : Fin 3) : rotationField b a = -rotationField a b := by
  funext p
  ext <;> simp [rotationField]

/-- `Ω_ba = -Ω_ab`. -/
theorem rotation_swap (a b : Fin 3) (u : Spacetime → F) : rotation b a u = -rotation a b u := by
  funext p
  rw [rotation_apply, rotationField_swap, Pi.neg_apply, map_neg]
  rfl

/-- `Ω_aa = 0`. -/
theorem rotation_self (a : Fin 3) (u : Spacetime → F) : rotation a a u = fun _ ↦ 0 := by
  funext p
  simp [rotation_apply, rotationField, Prod.mk_zero_zero]

/-! ### Linearity -/

theorem rotation_smul (a b : Fin 3) (c : ℝ) (u : Spacetime → F) :
    rotation a b (c • u) = c • rotation a b u :=
  derivAlong_smul _ c u

theorem boost_smul (a : Fin 3) (c : ℝ) (u : Spacetime → F) : boost a (c • u) = c • boost a u :=
  derivAlong_smul _ c u

theorem scaling_smul (c : ℝ) (u : Spacetime → F) : scaling (c • u) = c • scaling u :=
  derivAlong_smul _ c u

theorem rotation_add (a b : Fin 3) (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    rotation a b (u + v) p = rotation a b u p + rotation a b v p :=
  derivAlong_add _ hu hv

theorem boost_add (a : Fin 3) (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    boost a (u + v) p = boost a u p + boost a v p :=
  derivAlong_add _ hu hv

theorem scaling_add (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    scaling (u + v) p = scaling u p + scaling v p :=
  derivAlong_add _ hu hv

/-! ### Commutation with continuous linear maps -/

theorem rotation_clm_comp (a b : Fin 3) (T : F →L[ℝ] G) (hu : DifferentiableAt ℝ u p) :
    rotation a b (T ∘ u) p = T (rotation a b u p) :=
  derivAlong_clm_comp _ T hu

theorem boost_clm_comp (a : Fin 3) (T : F →L[ℝ] G) (hu : DifferentiableAt ℝ u p) :
    boost a (T ∘ u) p = T (boost a u p) :=
  derivAlong_clm_comp _ T hu

theorem scaling_clm_comp (T : F →L[ℝ] G) (hu : DifferentiableAt ℝ u p) :
    scaling (T ∘ u) p = T (scaling u p) :=
  derivAlong_clm_comp _ T hu

/-! ### Values on constants and coordinates -/

@[simp]
theorem rotation_const (a b : Fin 3) (c : F) : rotation a b (fun _ ↦ c) = fun _ ↦ 0 :=
  derivAlong_const _ c

@[simp]
theorem boost_const (a : Fin 3) (c : F) : boost a (fun _ ↦ c) = fun _ ↦ 0 :=
  derivAlong_const _ c

@[simp]
theorem scaling_const (c : F) : scaling (fun _ ↦ c) = fun _ ↦ 0 :=
  derivAlong_const _ c

/-- `Ω_ab t = 0`. -/
@[simp]
theorem rotation_timeCoord (a b : Fin 3) : rotation a b timeCoord = fun _ ↦ 0 := by
  rw [rotation, derivAlong_timeCoord]
  rfl

/-- `Ω_ab x_c = δ_bc x_a - δ_ac x_b`. -/
@[simp]
theorem rotation_spaceCoord (a b c : Fin 3) :
    rotation a b (spaceCoord c) = fun p ↦
      (if b = c then 1 else 0) * spaceCoord a p - (if a = c then 1 else 0) * spaceCoord b p := by
  rw [rotation, derivAlong_spaceCoord]
  funext p
  simp [rotationField, PiLp.single_apply, eq_comm, mul_comm]

/-- `L_a t = x_a`. -/
@[simp]
theorem boost_timeCoord (a : Fin 3) : boost a timeCoord = spaceCoord a := by
  rw [boost, derivAlong_timeCoord]
  rfl

/-- `L_a x_b = t δ_ab`. -/
@[simp]
theorem boost_spaceCoord (a b : Fin 3) :
    boost a (spaceCoord b) = fun p ↦ timeCoord p * if a = b then 1 else 0 := by
  rw [boost, derivAlong_spaceCoord]
  funext p
  simp [boostField, PiLp.single_apply, eq_comm]

/-- `S t = t`. -/
@[simp]
theorem scaling_timeCoord : scaling timeCoord = timeCoord := by
  rw [scaling, derivAlong_timeCoord]
  rfl

/-- `S x_a = x_a`. -/
@[simp]
theorem scaling_spaceCoord (a : Fin 3) : scaling (spaceCoord a) = spaceCoord a := by
  rw [scaling, derivAlong_spaceCoord]
  rfl

/-! ### Smoothness -/

theorem contDiff_rotationField (a b : Fin 3) : ContDiff ℝ n (rotationField a b) := by
  unfold rotationField
  fun_prop

theorem contDiff_boostField (a : Fin 3) : ContDiff ℝ n (boostField a) := by
  unfold boostField
  fun_prop

theorem contDiff_scalingField : ContDiff ℝ n scalingField :=
  contDiff_id

/-- If `u` is `C^{n+1}`, then `Ω_ab u` is `C^n`. -/
theorem contDiff_rotation (a b : Fin 3) (hu : ContDiff ℝ (n + 1) u) :
    ContDiff ℝ n (rotation a b u) :=
  contDiff_derivAlong (contDiff_rotationField a b) hu

/-- If `u` is `C^{n+1}`, then `L_a u` is `C^n`. -/
theorem contDiff_boost (a : Fin 3) (hu : ContDiff ℝ (n + 1) u) : ContDiff ℝ n (boost a u) :=
  contDiff_derivAlong (contDiff_boostField a) hu

/-- If `u` is `C^{n+1}`, then `S u` is `C^n`. -/
theorem contDiff_scaling (hu : ContDiff ℝ (n + 1) u) : ContDiff ℝ n (scaling u) :=
  contDiff_derivAlong contDiff_scalingField hu

theorem contDiff_infty_rotation (a b : Fin 3) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (rotation a b u) :=
  contDiff_rotation a b hu

theorem contDiff_infty_boost (a : Fin 3) (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (boost a u) :=
  contDiff_boost a hu

theorem contDiff_infty_scaling (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (scaling u) :=
  contDiff_scaling hu

end VectorFieldMethod.Minkowski
