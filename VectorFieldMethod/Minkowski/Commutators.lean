/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.VectorFields
public import Mathlib.Analysis.Calculus.VectorField

/-!
# Commutators of the Minkowski vector fields

For component fields `V W : Spacetime → Spacetime`, the commutator of the first-order operators
`derivAlong V` and `derivAlong W` is the first-order operator along the Lie bracket of the
component fields:
`V (W u) - W (V u) = [V, W] u`, where `[V, W] = lieBracket ℝ V W = DW · V - DV · W` is Mathlib's
`VectorField.lieBracket`. The component fields of the rotations, boosts and scaling are linear and
those of the translations are constant, so their Lie brackets are computed by linear algebra.

## Main statements

* `derivAlong_derivAlong_sub_derivAlong_derivAlong_apply`: `V (W u) - W (V u) = [V, W] u` at a
  point where `V` and `W` are differentiable and `u` is `C²`;
  `derivAlong_derivAlong_sub_derivAlong_derivAlong` is the identity of functions.
* Lie brackets of the component fields (`a, b, c, d : Fin 3`, `δ_ab = if a = b then 1 else 0`):
  `[∂_t, L_a] = ∂_a`, `[∂_b, L_a] = δ_ab ∂_t`, `[∂_t, Ω_ab] = 0`,
  `[∂_c, Ω_ab] = δ_ca ∂_b - δ_cb ∂_a`, `[∂_t, S] = ∂_t`, `[∂_a, S] = ∂_a`, `[L_a, L_b] = Ω_ab`,
  `[L_a, Ω_bc] = δ_ab L_c - δ_ac L_b`,
  `[Ω_ab, Ω_cd] = δ_bc Ω_ad - δ_ac Ω_bd - δ_bd Ω_ac + δ_ad Ω_bc`, `[S, L_a] = 0`, `[S, Ω_ab] = 0`
  (`lieBracket_timeField_boostField`, ..., `lieBracket_scalingField_rotationField`).
* The same relations for the operators acting on functions, at a point where `u` is `C²`
  (`boost_boost_sub_boost_boost_apply : L_a (L_b u) - L_b (L_a u) = Ω_ab u`, ...), and as
  identities of functions for `u` of class `C²` (`boost_boost_sub_boost_boost`, ...). The vanishing
  commutators are stated as commutation relations (`timeDeriv_rotation_comm_apply`,
  `scaling_boost_comm_apply`, `scaling_rotation_comm_apply`, ...).
* The brackets in the reverse order, such as `[L_a, ∂_t] = -∂_a` and `[S, ∂_α] = -∂_α`
  (`lieBracket_boostField_timeField`, ..., `lieBracket_scalingField_coordField`), from the
  antisymmetry of the Lie bracket.
* The same relations on an open set `U` on which `u` is `C²`, as equalities `Set.EqOn f g U`
  (names ending in `_of_contDiffOn`, for instance `boost_boost_sub_boost_boost_of_contDiffOn`).

## Implementation notes

The identity `V (W u) - W (V u) = [V, W] u` is Mathlib's `VectorField.fderiv_apply_lieBracket`: the
second-order terms `D²u(p) (V p) (W p)` and `D²u(p) (W p) (V p)` cancel by the symmetry of the
second derivative of a `C²` function. Since `fderiv` is `0` at points of non-differentiability,
the hypotheses cannot be dropped.

Mathlib's sign convention is `[V, W] = DW · V - DV · W`, so that `[V, W] u = V (W u) - W (V u)`.
In the relations above, the Kronecker delta `δ_ab` is the real number `if a = b then 1 else 0`,
acting on component fields and on values by scalar multiplication.
-/

@[expose] public noncomputable section

open VectorField
open scoped ContDiff

namespace VectorFieldMethod.Minkowski

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V W : Spacetime → Spacetime} {u : Spacetime → F} {p : Spacetime} {U : Set Spacetime}

/-! ### The commutator of two derivatives along vector fields -/

/-- `V (W u) - W (V u) = [V, W] u` at a point `p` where the component fields `V`, `W` are
differentiable and `u` is `C²`; here `[V, W] = lieBracket ℝ V W = DW · V - DV · W`. -/
theorem derivAlong_derivAlong_sub_derivAlong_derivAlong_apply (hV : DifferentiableAt ℝ V p)
    (hW : DifferentiableAt ℝ W p) (hu : ContDiffAt ℝ 2 u p) :
    derivAlong V (derivAlong W u) p - derivAlong W (derivAlong V u) p =
      derivAlong (lieBracket ℝ V W) u p := by
  rw [derivAlong_apply (lieBracket ℝ V W), fderiv_apply_lieBracket hu (by simp) hW hV]
  rfl

/-- `V (W u) - W (V u) = [V, W] u` for differentiable component fields `V`, `W` and `u` of class
`C²`. -/
theorem derivAlong_derivAlong_sub_derivAlong_derivAlong (hV : Differentiable ℝ V)
    (hW : Differentiable ℝ W) (hu : ContDiff ℝ 2 u) :
    derivAlong V (derivAlong W u) - derivAlong W (derivAlong V u) =
      derivAlong (lieBracket ℝ V W) u :=
  funext fun p ↦ derivAlong_derivAlong_sub_derivAlong_derivAlong_apply (hV p) (hW p) hu.contDiffAt

/-! ### Derivatives along combinations of component fields -/

/-- `(V + W) u = V u + W u`, without hypotheses. -/
theorem derivAlong_add_left (V W : Spacetime → Spacetime) (u : Spacetime → F) :
    derivAlong (V + W) u = derivAlong V u + derivAlong W u := by
  funext p
  simp [derivAlong_apply]

/-- `(V - W) u = V u - W u`, without hypotheses. -/
theorem derivAlong_sub_left (V W : Spacetime → Spacetime) (u : Spacetime → F) :
    derivAlong (V - W) u = derivAlong V u - derivAlong W u := by
  funext p
  simp [derivAlong_apply]

/-- `(c V) u = c (V u)` for `c : ℝ`, without hypotheses. -/
theorem derivAlong_smul_left (c : ℝ) (V : Spacetime → Spacetime) (u : Spacetime → F) :
    derivAlong (c • V) u = c • derivAlong V u := by
  funext p
  simp [derivAlong_apply]

/-- The derivative along the zero vector field vanishes. -/
theorem derivAlong_zero_left (u : Spacetime → F) :
    derivAlong (fun _ ↦ 0) u = fun _ ↦ 0 := by
  funext p
  simp [derivAlong_apply]

/-! ### Linear and constant component fields -/

/-- The component field of `Ω_ab` is linear. -/
theorem isLinearMap_rotationField (a b : Fin 3) : IsLinearMap ℝ (rotationField a b) where
  map_add x y := by
    refine Prod.ext (by simp [rotationField]) ?_
    simp only [rotationField, spaceCoord, Prod.snd_add, PiLp.add_apply, add_smul]
    abel
  map_smul c x := by
    refine Prod.ext (by simp [rotationField]) ?_
    simp only [rotationField, spaceCoord, Prod.smul_snd, PiLp.smul_apply, smul_eq_mul, smul_sub,
      smul_smul]

/-- The component field of `L_a` is linear. -/
theorem isLinearMap_boostField (a : Fin 3) : IsLinearMap ℝ (boostField a) where
  map_add x y := by
    refine Prod.ext ?_ ?_
    · simp [boostField, spaceCoord]
    · simp only [boostField, timeCoord, Prod.snd_add, Prod.fst_add, add_smul]
  map_smul c x := by
    refine Prod.ext ?_ ?_
    · simp [boostField, spaceCoord]
    · simp only [boostField, timeCoord, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_smul]

/-- The component field of `S` (the identity) is linear. -/
theorem isLinearMap_scalingField : IsLinearMap ℝ scalingField :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- A linear component field `V` is its own derivative at every point. -/
theorem hasFDerivAt_of_isLinearMap (hV : IsLinearMap ℝ V) (p : Spacetime) :
    HasFDerivAt V (LinearMap.toContinuousLinearMap (IsLinearMap.mk' V hV)) p :=
  (LinearMap.toContinuousLinearMap (IsLinearMap.mk' V hV)).hasFDerivAt

/-- The derivative of a linear component field `V` at any point is `V` itself. -/
theorem fderiv_apply_of_isLinearMap (hV : IsLinearMap ℝ V) (p v : Spacetime) :
    fderiv ℝ V p v = V v := by
  rw [(hasFDerivAt_of_isLinearMap hV p).fderiv]
  rfl

/-- The coordinate fields are constant: their derivative is `0`. -/
theorem hasFDerivAt_coordField (α : Fin 4) (p : Spacetime) :
    HasFDerivAt (coordField α) (0 : Spacetime →L[ℝ] Spacetime) p := by
  cases α using Fin.cases
  · exact hasFDerivAt_const _ p
  · exact hasFDerivAt_const _ p

theorem fderiv_timeField (p : Spacetime) : fderiv ℝ timeField p = 0 :=
  (hasFDerivAt_coordField 0 p).fderiv

theorem fderiv_spaceField (a : Fin 3) (p : Spacetime) : fderiv ℝ (spaceField a) p = 0 :=
  (hasFDerivAt_coordField a.succ p).fderiv

theorem fderiv_coordField (α : Fin 4) (p : Spacetime) : fderiv ℝ (coordField α) p = 0 :=
  (hasFDerivAt_coordField α p).fderiv

theorem differentiable_timeField : Differentiable ℝ timeField :=
  (contDiff_timeField (n := 1)).differentiable one_ne_zero

theorem differentiable_spaceField (a : Fin 3) : Differentiable ℝ (spaceField a) :=
  (contDiff_spaceField (n := 1) a).differentiable one_ne_zero

theorem differentiable_coordField (α : Fin 4) : Differentiable ℝ (coordField α) :=
  (contDiff_coordField (n := 1) α).differentiable one_ne_zero

theorem differentiable_rotationField (a b : Fin 3) : Differentiable ℝ (rotationField a b) :=
  (contDiff_rotationField (n := 1) a b).differentiable one_ne_zero

theorem differentiable_boostField (a : Fin 3) : Differentiable ℝ (boostField a) :=
  (contDiff_boostField (n := 1) a).differentiable one_ne_zero

theorem differentiable_scalingField : Differentiable ℝ scalingField :=
  (contDiff_scalingField (n := 1)).differentiable one_ne_zero

/-- The Lie bracket of two linear component fields: `[V, W] (p) = W (V p) - V (W p)`. -/
theorem lieBracket_apply_of_isLinearMap (hV : IsLinearMap ℝ V) (hW : IsLinearMap ℝ W) :
    lieBracket ℝ V W p = W (V p) - V (W p) := by
  rw [lieBracket, fderiv_apply_of_isLinearMap hV, fderiv_apply_of_isLinearMap hW]

/-- The Lie bracket of a component field `V` with `DV(p) = 0` (for instance a constant one) and a
linear component field `W`: `[V, W] (p) = W (V p)`. -/
theorem lieBracket_apply_of_fderiv_eq_zero (hV : fderiv ℝ V p = 0) (hW : IsLinearMap ℝ W) :
    lieBracket ℝ V W p = W (V p) := by
  rw [lieBracket, fderiv_apply_of_isLinearMap hW, hV, zero_apply, sub_zero]

/-! ### Lie brackets of the component fields -/

/-- `[∂_t, L_a] = ∂_a`. -/
theorem lieBracket_timeField_boostField (a : Fin 3) :
    lieBracket ℝ timeField (boostField a) = spaceField a := by
  funext p
  rw [lieBracket_apply_of_fderiv_eq_zero (fderiv_timeField p) (isLinearMap_boostField a)]
  refine Prod.ext ?_ ?_ <;> simp [boostField, timeField, spaceField, spaceCoord, timeCoord]

/-- `[∂_b, L_a] = δ_ab ∂_t`. -/
theorem lieBracket_spaceField_boostField (a b : Fin 3) :
    lieBracket ℝ (spaceField b) (boostField a) = (if a = b then (1 : ℝ) else 0) • timeField := by
  funext p
  rw [Pi.smul_apply, lieBracket_apply_of_fderiv_eq_zero (fderiv_spaceField b p)
    (isLinearMap_boostField a)]
  refine Prod.ext ?_ ?_
  · simp only [Prod.smul_fst]
    simp [boostField, timeField, spaceField, spaceCoord]
  · simp only [Prod.smul_snd]
    simp [boostField, timeField, spaceField, timeCoord]

/-- `[∂_t, Ω_ab] = 0`. -/
theorem lieBracket_timeField_rotationField (a b : Fin 3) :
    lieBracket ℝ timeField (rotationField a b) = fun _ ↦ 0 := by
  funext p
  rw [lieBracket_apply_of_fderiv_eq_zero (fderiv_timeField p) (isLinearMap_rotationField a b)]
  refine Prod.ext ?_ ?_ <;> simp [rotationField, timeField, spaceCoord]

/-- `[∂_c, Ω_ab] = δ_ca ∂_b - δ_cb ∂_a`. -/
theorem lieBracket_spaceField_rotationField (a b c : Fin 3) :
    lieBracket ℝ (spaceField c) (rotationField a b) =
      (if c = a then (1 : ℝ) else 0) • spaceField b -
        (if c = b then (1 : ℝ) else 0) • spaceField a := by
  funext p
  rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, lieBracket_apply_of_fderiv_eq_zero
    (fderiv_spaceField c p) (isLinearMap_rotationField a b)]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_sub, Prod.smul_fst]
    simp [rotationField, spaceField]
  · simp only [rotationField, spaceField, spaceCoord, Prod.snd_sub, Prod.smul_snd,
      PiLp.single_apply, @eq_comm (Fin 3) a c, @eq_comm (Fin 3) b c]

/-- `[∂_t, S] = ∂_t`. -/
theorem lieBracket_timeField_scalingField :
    lieBracket ℝ timeField scalingField = timeField := by
  funext p
  rw [lieBracket_apply_of_fderiv_eq_zero (fderiv_timeField p) isLinearMap_scalingField]
  rfl

/-- `[∂_a, S] = ∂_a`. -/
theorem lieBracket_spaceField_scalingField (a : Fin 3) :
    lieBracket ℝ (spaceField a) scalingField = spaceField a := by
  funext p
  rw [lieBracket_apply_of_fderiv_eq_zero (fderiv_spaceField a p) isLinearMap_scalingField]
  rfl

/-- `[∂_α, S] = ∂_α`. -/
theorem lieBracket_coordField_scalingField (α : Fin 4) :
    lieBracket ℝ (coordField α) scalingField = coordField α := by
  cases α using Fin.cases
  · exact lieBracket_timeField_scalingField
  · exact lieBracket_spaceField_scalingField _

/-- `[L_a, L_b] = Ω_ab`. -/
theorem lieBracket_boostField_boostField (a b : Fin 3) :
    lieBracket ℝ (boostField a) (boostField b) = rotationField a b := by
  funext p
  rw [lieBracket_apply_of_isLinearMap (isLinearMap_boostField a) (isLinearMap_boostField b)]
  refine Prod.ext ?_ ?_
  · simp only [boostField, rotationField, spaceCoord, timeCoord, Prod.fst_sub, PiLp.smul_apply,
      PiLp.single_apply, smul_eq_mul, @eq_comm (Fin 3) b a, sub_self]
  · simp only [boostField, rotationField, spaceCoord, timeCoord, Prod.snd_sub]

/-- `[L_a, Ω_bc] = δ_ab L_c - δ_ac L_b`. -/
theorem lieBracket_boostField_rotationField (a b c : Fin 3) :
    lieBracket ℝ (boostField a) (rotationField b c) =
      (if a = b then (1 : ℝ) else 0) • boostField c -
        (if a = c then (1 : ℝ) else 0) • boostField b := by
  funext p
  rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, lieBracket_apply_of_isLinearMap
    (isLinearMap_boostField a) (isLinearMap_rotationField b c)]
  refine Prod.ext ?_ ?_
  · simp only [boostField, rotationField, spaceCoord, timeCoord, Prod.fst_sub, Prod.smul_fst,
      PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
    ring
  · simp only [boostField, rotationField, spaceCoord, timeCoord, Prod.snd_sub, Prod.smul_snd,
      PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, @eq_comm (Fin 3) b a,
      @eq_comm (Fin 3) c a]
    module

/-- `[Ω_ab, Ω_cd] = δ_bc Ω_ad - δ_ac Ω_bd - δ_bd Ω_ac + δ_ad Ω_bc`. -/
theorem lieBracket_rotationField_rotationField (a b c d : Fin 3) :
    lieBracket ℝ (rotationField a b) (rotationField c d) =
      (if b = c then (1 : ℝ) else 0) • rotationField a d -
        (if a = c then (1 : ℝ) else 0) • rotationField b d -
        (if b = d then (1 : ℝ) else 0) • rotationField a c +
        (if a = d then (1 : ℝ) else 0) • rotationField b c := by
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [lieBracket_apply_of_isLinearMap (isLinearMap_rotationField a b)
    (isLinearMap_rotationField c d)]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sub, Prod.smul_fst]
    simp [rotationField]
  · simp only [rotationField, spaceCoord, Prod.snd_sub, Prod.snd_add, Prod.smul_snd,
      PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, @eq_comm (Fin 3) c b,
      @eq_comm (Fin 3) c a, @eq_comm (Fin 3) d b, @eq_comm (Fin 3) d a]
    module

/-- `[S, L_a] = 0`. -/
theorem lieBracket_scalingField_boostField (a : Fin 3) :
    lieBracket ℝ scalingField (boostField a) = fun _ ↦ 0 := by
  funext p
  rw [lieBracket_apply_of_isLinearMap isLinearMap_scalingField (isLinearMap_boostField a)]
  exact sub_self _

/-- `[S, Ω_ab] = 0`. -/
theorem lieBracket_scalingField_rotationField (a b : Fin 3) :
    lieBracket ℝ scalingField (rotationField a b) = fun _ ↦ 0 := by
  funext p
  rw [lieBracket_apply_of_isLinearMap isLinearMap_scalingField (isLinearMap_rotationField a b)]
  exact sub_self _

/-! ### Lie brackets in the reverse order

These follow from the brackets above by the antisymmetry `[V, W] = -[W, V]`
(Mathlib's `lieBracket_swap`). The brackets `[L_b, L_a]` and `[Ω_cd, Ω_ab]` are already covered by
`lieBracket_boostField_boostField` and `lieBracket_rotationField_rotationField` with the indices
exchanged. -/

/-- `[L_a, ∂_t] = -∂_a`. -/
theorem lieBracket_boostField_timeField (a : Fin 3) :
    lieBracket ℝ (boostField a) timeField = -spaceField a :=
  funext fun _ ↦ by rw [lieBracket_swap, lieBracket_timeField_boostField]; rfl

/-- `[L_a, ∂_b] = -δ_ab ∂_t`. -/
theorem lieBracket_boostField_spaceField (a b : Fin 3) :
    lieBracket ℝ (boostField a) (spaceField b) = -((if a = b then (1 : ℝ) else 0) • timeField) :=
  funext fun _ ↦ by rw [lieBracket_swap, lieBracket_spaceField_boostField]; rfl

/-- `[Ω_ab, ∂_t] = 0`. -/
theorem lieBracket_rotationField_timeField (a b : Fin 3) :
    lieBracket ℝ (rotationField a b) timeField = fun _ ↦ 0 :=
  funext fun _ ↦ by rw [lieBracket_swap, lieBracket_timeField_rotationField]; exact neg_zero

/-- `[Ω_ab, ∂_c] = -(δ_ca ∂_b - δ_cb ∂_a)`. -/
theorem lieBracket_rotationField_spaceField (a b c : Fin 3) :
    lieBracket ℝ (rotationField a b) (spaceField c) =
      -((if c = a then (1 : ℝ) else 0) • spaceField b -
        (if c = b then (1 : ℝ) else 0) • spaceField a) :=
  funext fun _ ↦ by rw [lieBracket_swap, lieBracket_spaceField_rotationField]; rfl

/-- `[S, ∂_t] = -∂_t`. -/
theorem lieBracket_scalingField_timeField : lieBracket ℝ scalingField timeField = -timeField :=
  funext fun _ ↦ by rw [lieBracket_swap, lieBracket_timeField_scalingField]; rfl

/-- `[S, ∂_a] = -∂_a`. -/
theorem lieBracket_scalingField_spaceField (a : Fin 3) :
    lieBracket ℝ scalingField (spaceField a) = -spaceField a :=
  funext fun _ ↦ by rw [lieBracket_swap, lieBracket_spaceField_scalingField]; rfl

/-- `[S, ∂_α] = -∂_α`. -/
theorem lieBracket_scalingField_coordField (α : Fin 4) :
    lieBracket ℝ scalingField (coordField α) = -coordField α :=
  funext fun _ ↦ by rw [lieBracket_swap, lieBracket_coordField_scalingField]; rfl

/-- `[Ω_bc, L_a] = -(δ_ab L_c - δ_ac L_b)`. -/
theorem lieBracket_rotationField_boostField (a b c : Fin 3) :
    lieBracket ℝ (rotationField b c) (boostField a) =
      -((if a = b then (1 : ℝ) else 0) • boostField c -
        (if a = c then (1 : ℝ) else 0) • boostField b) :=
  funext fun _ ↦ by rw [lieBracket_swap, lieBracket_boostField_rotationField]; rfl

/-- `[L_a, S] = 0`. -/
theorem lieBracket_boostField_scalingField (a : Fin 3) :
    lieBracket ℝ (boostField a) scalingField = fun _ ↦ 0 :=
  funext fun _ ↦ by rw [lieBracket_swap, lieBracket_scalingField_boostField]; exact neg_zero

/-- `[Ω_ab, S] = 0`. -/
theorem lieBracket_rotationField_scalingField (a b : Fin 3) :
    lieBracket ℝ (rotationField a b) scalingField = fun _ ↦ 0 :=
  funext fun _ ↦ by rw [lieBracket_swap, lieBracket_scalingField_rotationField]; exact neg_zero

/-! ### Commutators with the translations -/

/-- `[∂_t, L_a] u = ∂_a u` at a point where `u` is `C²`. -/
theorem timeDeriv_boost_sub_boost_timeDeriv_apply (a : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    ∂ₜ (boost a u) p - boost a (∂ₜ u) p = ∂ₓ[a] u p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply (differentiable_timeField p)
    (differentiable_boostField a p) hu
  rw [lieBracket_timeField_boostField] at h
  exact h

/-- `[∂_t, L_a] = ∂_a` on functions of class `C²`. -/
theorem timeDeriv_boost_sub_boost_timeDeriv (a : Fin 3) (hu : ContDiff ℝ 2 u) :
    ∂ₜ (boost a u) - boost a (∂ₜ u) = ∂ₓ[a] u :=
  funext fun _ ↦ timeDeriv_boost_sub_boost_timeDeriv_apply a hu.contDiffAt

/-- `[∂_b, L_a] u = δ_ab ∂_t u` at a point where `u` is `C²`. -/
theorem spaceDeriv_boost_sub_boost_spaceDeriv_apply (a b : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    ∂ₓ[b] (boost a u) p - boost a (∂ₓ[b] u) p = (if a = b then (1 : ℝ) else 0) • ∂ₜ u p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply
    (differentiable_spaceField b p) (differentiable_boostField a p) hu
  rw [lieBracket_spaceField_boostField, derivAlong_smul_left] at h
  exact h

/-- `[∂_b, L_a] = δ_ab ∂_t` on functions of class `C²`. -/
theorem spaceDeriv_boost_sub_boost_spaceDeriv (a b : Fin 3) (hu : ContDiff ℝ 2 u) :
    ∂ₓ[b] (boost a u) - boost a (∂ₓ[b] u) = (if a = b then (1 : ℝ) else 0) • ∂ₜ u :=
  funext fun _ ↦ spaceDeriv_boost_sub_boost_spaceDeriv_apply a b hu.contDiffAt

/-- `[∂_t, Ω_ab] u = 0` at a point where `u` is `C²`. -/
theorem timeDeriv_rotation_comm_apply (a b : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    ∂ₜ (rotation a b u) p = rotation a b (∂ₜ u) p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply (differentiable_timeField p)
    (differentiable_rotationField a b p) hu
  rw [lieBracket_timeField_rotationField, derivAlong_zero_left] at h
  exact sub_eq_zero.mp h

/-- `[∂_t, Ω_ab] = 0` on functions of class `C²`. -/
theorem timeDeriv_rotation_comm (a b : Fin 3) (hu : ContDiff ℝ 2 u) :
    ∂ₜ (rotation a b u) = rotation a b (∂ₜ u) :=
  funext fun _ ↦ timeDeriv_rotation_comm_apply a b hu.contDiffAt

/-- `[∂_c, Ω_ab] u = δ_ca ∂_b u - δ_cb ∂_a u` at a point where `u` is `C²`. -/
theorem spaceDeriv_rotation_sub_rotation_spaceDeriv_apply (a b c : Fin 3)
    (hu : ContDiffAt ℝ 2 u p) :
    ∂ₓ[c] (rotation a b u) p - rotation a b (∂ₓ[c] u) p =
      (if c = a then (1 : ℝ) else 0) • ∂ₓ[b] u p -
        (if c = b then (1 : ℝ) else 0) • ∂ₓ[a] u p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply
    (differentiable_spaceField c p) (differentiable_rotationField a b p) hu
  rw [lieBracket_spaceField_rotationField, derivAlong_sub_left, derivAlong_smul_left,
    derivAlong_smul_left] at h
  exact h

/-- `[∂_c, Ω_ab] = δ_ca ∂_b - δ_cb ∂_a` on functions of class `C²`. -/
theorem spaceDeriv_rotation_sub_rotation_spaceDeriv (a b c : Fin 3) (hu : ContDiff ℝ 2 u) :
    ∂ₓ[c] (rotation a b u) - rotation a b (∂ₓ[c] u) =
      (if c = a then (1 : ℝ) else 0) • ∂ₓ[b] u - (if c = b then (1 : ℝ) else 0) • ∂ₓ[a] u :=
  funext fun _ ↦ spaceDeriv_rotation_sub_rotation_spaceDeriv_apply a b c hu.contDiffAt

/-- `[∂_t, S] u = ∂_t u` at a point where `u` is `C²`. -/
theorem timeDeriv_scaling_sub_scaling_timeDeriv_apply (hu : ContDiffAt ℝ 2 u p) :
    ∂ₜ (scaling u) p - scaling (∂ₜ u) p = ∂ₜ u p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply (differentiable_timeField p)
    (differentiable_scalingField p) hu
  rw [lieBracket_timeField_scalingField] at h
  exact h

/-- `[∂_t, S] = ∂_t` on functions of class `C²`. -/
theorem timeDeriv_scaling_sub_scaling_timeDeriv (hu : ContDiff ℝ 2 u) :
    ∂ₜ (scaling u) - scaling (∂ₜ u) = ∂ₜ u :=
  funext fun _ ↦ timeDeriv_scaling_sub_scaling_timeDeriv_apply hu.contDiffAt

/-- `[∂_a, S] u = ∂_a u` at a point where `u` is `C²`. -/
theorem spaceDeriv_scaling_sub_scaling_spaceDeriv_apply (a : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    ∂ₓ[a] (scaling u) p - scaling (∂ₓ[a] u) p = ∂ₓ[a] u p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply
    (differentiable_spaceField a p) (differentiable_scalingField p) hu
  rw [lieBracket_spaceField_scalingField] at h
  exact h

/-- `[∂_a, S] = ∂_a` on functions of class `C²`. -/
theorem spaceDeriv_scaling_sub_scaling_spaceDeriv (a : Fin 3) (hu : ContDiff ℝ 2 u) :
    ∂ₓ[a] (scaling u) - scaling (∂ₓ[a] u) = ∂ₓ[a] u :=
  funext fun _ ↦ spaceDeriv_scaling_sub_scaling_spaceDeriv_apply a hu.contDiffAt

/-! ### Commutators of boosts, rotations and scaling -/

/-- `[L_a, L_b] u = Ω_ab u` at a point where `u` is `C²`. -/
theorem boost_boost_sub_boost_boost_apply (a b : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    boost a (boost b u) p - boost b (boost a u) p = rotation a b u p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply
    (differentiable_boostField a p) (differentiable_boostField b p) hu
  rw [lieBracket_boostField_boostField] at h
  exact h

/-- `[L_a, L_b] = Ω_ab` on functions of class `C²`. -/
theorem boost_boost_sub_boost_boost (a b : Fin 3) (hu : ContDiff ℝ 2 u) :
    boost a (boost b u) - boost b (boost a u) = rotation a b u :=
  funext fun _ ↦ boost_boost_sub_boost_boost_apply a b hu.contDiffAt

/-- `[L_a, Ω_bc] u = δ_ab L_c u - δ_ac L_b u` at a point where `u` is `C²`. -/
theorem boost_rotation_sub_rotation_boost_apply (a b c : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    boost a (rotation b c u) p - rotation b c (boost a u) p =
      (if a = b then (1 : ℝ) else 0) • boost c u p -
        (if a = c then (1 : ℝ) else 0) • boost b u p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply
    (differentiable_boostField a p) (differentiable_rotationField b c p) hu
  rw [lieBracket_boostField_rotationField, derivAlong_sub_left, derivAlong_smul_left,
    derivAlong_smul_left] at h
  exact h

/-- `[L_a, Ω_bc] = δ_ab L_c - δ_ac L_b` on functions of class `C²`. -/
theorem boost_rotation_sub_rotation_boost (a b c : Fin 3) (hu : ContDiff ℝ 2 u) :
    boost a (rotation b c u) - rotation b c (boost a u) =
      (if a = b then (1 : ℝ) else 0) • boost c u - (if a = c then (1 : ℝ) else 0) • boost b u :=
  funext fun _ ↦ boost_rotation_sub_rotation_boost_apply a b c hu.contDiffAt

/-- `[Ω_ab, Ω_cd] u = δ_bc Ω_ad u - δ_ac Ω_bd u - δ_bd Ω_ac u + δ_ad Ω_bc u` at a point where `u`
is `C²`. -/
theorem rotation_rotation_sub_rotation_rotation_apply (a b c d : Fin 3)
    (hu : ContDiffAt ℝ 2 u p) :
    rotation a b (rotation c d u) p - rotation c d (rotation a b u) p =
      (if b = c then (1 : ℝ) else 0) • rotation a d u p -
        (if a = c then (1 : ℝ) else 0) • rotation b d u p -
        (if b = d then (1 : ℝ) else 0) • rotation a c u p +
        (if a = d then (1 : ℝ) else 0) • rotation b c u p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply
    (differentiable_rotationField a b p) (differentiable_rotationField c d p) hu
  simp only [lieBracket_rotationField_rotationField, derivAlong_add_left, derivAlong_sub_left,
    derivAlong_smul_left] at h
  exact h

/-- `[Ω_ab, Ω_cd] = δ_bc Ω_ad - δ_ac Ω_bd - δ_bd Ω_ac + δ_ad Ω_bc` on functions of class `C²`. -/
theorem rotation_rotation_sub_rotation_rotation (a b c d : Fin 3) (hu : ContDiff ℝ 2 u) :
    rotation a b (rotation c d u) - rotation c d (rotation a b u) =
      (if b = c then (1 : ℝ) else 0) • rotation a d u -
        (if a = c then (1 : ℝ) else 0) • rotation b d u -
        (if b = d then (1 : ℝ) else 0) • rotation a c u +
        (if a = d then (1 : ℝ) else 0) • rotation b c u :=
  funext fun _ ↦ rotation_rotation_sub_rotation_rotation_apply a b c d hu.contDiffAt

/-- `[S, L_a] u = 0` at a point where `u` is `C²`. -/
theorem scaling_boost_comm_apply (a : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    scaling (boost a u) p = boost a (scaling u) p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply
    (differentiable_scalingField p) (differentiable_boostField a p) hu
  rw [lieBracket_scalingField_boostField, derivAlong_zero_left] at h
  exact sub_eq_zero.mp h

/-- `[S, L_a] = 0` on functions of class `C²`. -/
theorem scaling_boost_comm (a : Fin 3) (hu : ContDiff ℝ 2 u) :
    scaling (boost a u) = boost a (scaling u) :=
  funext fun _ ↦ scaling_boost_comm_apply a hu.contDiffAt

/-- `[S, Ω_ab] u = 0` at a point where `u` is `C²`. -/
theorem scaling_rotation_comm_apply (a b : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    scaling (rotation a b u) p = rotation a b (scaling u) p := by
  have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply
    (differentiable_scalingField p) (differentiable_rotationField a b p) hu
  rw [lieBracket_scalingField_rotationField, derivAlong_zero_left] at h
  exact sub_eq_zero.mp h

/-- `[S, Ω_ab] = 0` on functions of class `C²`. -/
theorem scaling_rotation_comm (a b : Fin 3) (hu : ContDiff ℝ 2 u) :
    scaling (rotation a b u) = rotation a b (scaling u) :=
  funext fun _ ↦ scaling_rotation_comm_apply a b hu.contDiffAt

/-! ### Commutation relations on open sets

If `u` is `C²` on an open set `U`, the commutation relations hold at every point of `U`: they are
stated as `Set.EqOn f g U`, that is, `f p = g p` for every `p ∈ U`. -/

/-- `V (W u) - W (V u) = [V, W] u` on an open set `U` on which the component fields `V`, `W` are
differentiable and `u` is `C²`. -/
theorem derivAlong_derivAlong_sub_derivAlong_derivAlong_of_contDiffOn (hU : IsOpen U)
    (hV : DifferentiableOn ℝ V U) (hW : DifferentiableOn ℝ W U) (hu : ContDiffOn ℝ 2 u U) :
    Set.EqOn (derivAlong V (derivAlong W u) - derivAlong W (derivAlong V u))
      (derivAlong (lieBracket ℝ V W) u) U := fun _ hp ↦
  derivAlong_derivAlong_sub_derivAlong_derivAlong_apply (hV.differentiableAt (hU.mem_nhds hp))
    (hW.differentiableAt (hU.mem_nhds hp)) (hu.contDiffAt (hU.mem_nhds hp))

/-- `[∂_t, L_a] = ∂_a` on an open set `U` on which `u` is `C²`. -/
theorem timeDeriv_boost_sub_boost_timeDeriv_of_contDiffOn (a : Fin 3) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) : Set.EqOn (∂ₜ (boost a u) - boost a (∂ₜ u)) (∂ₓ[a] u) U :=
  fun _ hp ↦ timeDeriv_boost_sub_boost_timeDeriv_apply a (hu.contDiffAt (hU.mem_nhds hp))

/-- `[∂_b, L_a] = δ_ab ∂_t` on an open set `U` on which `u` is `C²`. -/
theorem spaceDeriv_boost_sub_boost_spaceDeriv_of_contDiffOn (a b : Fin 3) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) :
    Set.EqOn (∂ₓ[b] (boost a u) - boost a (∂ₓ[b] u))
      ((if a = b then (1 : ℝ) else 0) • ∂ₜ u) U :=
  fun _ hp ↦ spaceDeriv_boost_sub_boost_spaceDeriv_apply a b (hu.contDiffAt (hU.mem_nhds hp))

/-- `[∂_t, Ω_ab] = 0` on an open set `U` on which `u` is `C²`. -/
theorem timeDeriv_rotation_comm_of_contDiffOn (a b : Fin 3) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) : Set.EqOn (∂ₜ (rotation a b u)) (rotation a b (∂ₜ u)) U :=
  fun _ hp ↦ timeDeriv_rotation_comm_apply a b (hu.contDiffAt (hU.mem_nhds hp))

/-- `[∂_c, Ω_ab] = δ_ca ∂_b - δ_cb ∂_a` on an open set `U` on which `u` is `C²`. -/
theorem spaceDeriv_rotation_sub_rotation_spaceDeriv_of_contDiffOn (a b c : Fin 3)
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) :
    Set.EqOn (∂ₓ[c] (rotation a b u) - rotation a b (∂ₓ[c] u))
      ((if c = a then (1 : ℝ) else 0) • ∂ₓ[b] u - (if c = b then (1 : ℝ) else 0) • ∂ₓ[a] u) U :=
  fun _ hp ↦
    spaceDeriv_rotation_sub_rotation_spaceDeriv_apply a b c (hu.contDiffAt (hU.mem_nhds hp))

/-- `[∂_t, S] = ∂_t` on an open set `U` on which `u` is `C²`. -/
theorem timeDeriv_scaling_sub_scaling_timeDeriv_of_contDiffOn (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) : Set.EqOn (∂ₜ (scaling u) - scaling (∂ₜ u)) (∂ₜ u) U :=
  fun _ hp ↦ timeDeriv_scaling_sub_scaling_timeDeriv_apply (hu.contDiffAt (hU.mem_nhds hp))

/-- `[∂_a, S] = ∂_a` on an open set `U` on which `u` is `C²`. -/
theorem spaceDeriv_scaling_sub_scaling_spaceDeriv_of_contDiffOn (a : Fin 3) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) :
    Set.EqOn (∂ₓ[a] (scaling u) - scaling (∂ₓ[a] u)) (∂ₓ[a] u) U :=
  fun _ hp ↦ spaceDeriv_scaling_sub_scaling_spaceDeriv_apply a (hu.contDiffAt (hU.mem_nhds hp))

/-- `[L_a, L_b] = Ω_ab` on an open set `U` on which `u` is `C²`. -/
theorem boost_boost_sub_boost_boost_of_contDiffOn (a b : Fin 3) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) :
    Set.EqOn (boost a (boost b u) - boost b (boost a u)) (rotation a b u) U :=
  fun _ hp ↦ boost_boost_sub_boost_boost_apply a b (hu.contDiffAt (hU.mem_nhds hp))

/-- `[L_a, Ω_bc] = δ_ab L_c - δ_ac L_b` on an open set `U` on which `u` is `C²`. -/
theorem boost_rotation_sub_rotation_boost_of_contDiffOn (a b c : Fin 3) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) :
    Set.EqOn (boost a (rotation b c u) - rotation b c (boost a u))
      ((if a = b then (1 : ℝ) else 0) • boost c u -
        (if a = c then (1 : ℝ) else 0) • boost b u) U :=
  fun _ hp ↦ boost_rotation_sub_rotation_boost_apply a b c (hu.contDiffAt (hU.mem_nhds hp))

/-- `[Ω_ab, Ω_cd] = δ_bc Ω_ad - δ_ac Ω_bd - δ_bd Ω_ac + δ_ad Ω_bc` on an open set `U` on which `u`
is `C²`. -/
theorem rotation_rotation_sub_rotation_rotation_of_contDiffOn (a b c d : Fin 3)
    (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) :
    Set.EqOn (rotation a b (rotation c d u) - rotation c d (rotation a b u))
      ((if b = c then (1 : ℝ) else 0) • rotation a d u -
        (if a = c then (1 : ℝ) else 0) • rotation b d u -
        (if b = d then (1 : ℝ) else 0) • rotation a c u +
        (if a = d then (1 : ℝ) else 0) • rotation b c u) U :=
  fun _ hp ↦
    rotation_rotation_sub_rotation_rotation_apply a b c d (hu.contDiffAt (hU.mem_nhds hp))

/-- `[S, L_a] = 0` on an open set `U` on which `u` is `C²`. -/
theorem scaling_boost_comm_of_contDiffOn (a : Fin 3) (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) :
    Set.EqOn (scaling (boost a u)) (boost a (scaling u)) U :=
  fun _ hp ↦ scaling_boost_comm_apply a (hu.contDiffAt (hU.mem_nhds hp))

/-- `[S, Ω_ab] = 0` on an open set `U` on which `u` is `C²`. -/
theorem scaling_rotation_comm_of_contDiffOn (a b : Fin 3) (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) : Set.EqOn (scaling (rotation a b u)) (rotation a b (scaling u)) U :=
  fun _ hp ↦ scaling_rotation_comm_apply a b (hu.contDiffAt (hU.mem_nhds hp))

/-! ### Sanity checks

The examples below check commutation relations on the coordinate functions, computing both sides
independently from the values of the vector fields on the coordinates (`boost_spaceCoord`,
`rotation_spaceCoord`, ...), without the theorems of this file. -/

/-- `[L_a, L_b] = Ω_ab` on the coordinate function `x_c`: both sides are `δ_bc x_a - δ_ac x_b`.
This checks the sign convention of `boost_boost_sub_boost_boost_apply`. -/
example (a b c : Fin 3) (p : Spacetime) :
    boost a (boost b (spaceCoord c)) p - boost b (boost a (spaceCoord c)) p =
      rotation a b (spaceCoord c) p := by
  have h (d e : Fin 3) :
      boost d (boost e (spaceCoord c)) = (if e = c then (1 : ℝ) else 0) • spaceCoord d := by
    have he : boost e (spaceCoord c) = (if e = c then (1 : ℝ) else 0) • timeCoord := by
      rw [boost_spaceCoord]
      funext q
      simp [mul_comm]
    rw [he, boost_smul, boost_timeCoord]
  rw [h, h, rotation_spaceCoord]
  simp

/-- `[∂_t, S] = ∂_t` on the coordinate function `t`: both sides are `1`. -/
example (p : Spacetime) :
    ∂ₜ (scaling timeCoord) p - scaling (∂ₜ timeCoord) p = 1 ∧ ∂ₜ timeCoord p = 1 := by
  simp

end VectorFieldMethod.Minkowski
