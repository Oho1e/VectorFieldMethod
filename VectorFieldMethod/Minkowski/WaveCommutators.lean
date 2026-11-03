/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.Commutators
public import VectorFieldMethod.Minkowski.Computations

/-!
# Commutators of the Minkowski vector fields with the wave and Klein–Gordon operators

The translations `∂_α`, the rotations `Ω_ab` and the boosts `L_a` commute with the wave operator
`□` and with the Klein–Gordon operator `KG_m u = □u - m² u`, and the scaling field satisfies
`[S, □] = -2 □` and `[S, KG_m] u = -2 □u`. Here `[X, Y] u = X (Y u) - Y (X u)`.

## Main statements

At a point `p` where `u` is `C³` (`ContDiffAt ℝ 3 u p`):

* `partialDeriv_dAlembertian_comm_apply`: `∂_α (□u) = □ (∂_α u)`;
* `rotation_dAlembertian_comm_apply`: `Ω_ab (□u) = □ (Ω_ab u)`;
* `boost_dAlembertian_comm_apply`: `L_a (□u) = □ (L_a u)`;
* `scaling_dAlembertian_sub_dAlembertian_scaling_apply`: `S (□u) - □ (S u) = -2 □u`;
* `partialDeriv_kleinGordon_comm_apply`, `rotation_kleinGordon_comm_apply`,
  `boost_kleinGordon_comm_apply`: the same commutation relations for `KG_m`;
* `scaling_kleinGordon_sub_kleinGordon_scaling_apply`: `S (KG_m u) - KG_m (S u) = -2 □u`.

The versions without the suffix `_apply` are the identities of functions for `u` of class `C³`.

All of them follow from `derivAlong_dAlembertian_sub_dAlembertian_derivAlong_apply`, the
commutator of `□` with the derivative along an affine component field `V` (one with a constant
derivative `A`):
`V (□u) - □ (V u) = -η^{αβ} (D²u(E_α, [∂_β, V]) + D²u([∂_α, V], E_β))`,
where `E_α` is the value of the constant field `∂_α` and `[∂_β, V] = A E_β` is constant.

## Implementation notes

For an affine `V`, the Lie bracket `[∂_β, V]` is a constant vector, so the general commutator
identity `derivAlong_derivAlong_sub_derivAlong_derivAlong_apply` gives
`V (∂_β u) = ∂_β (V u) - D u (A E_β)` near `p` (where `u` is `C²`), and, applied to `∂_β u` at `p`,
`V (∂_α ∂_β u) = ∂_α (V (∂_β u)) - D (∂_β u) (A E_α)`. Combining the two gives
`V (∂_α ∂_β u) = ∂_α ∂_β (V u) - D²u(E_α, A E_β) - D²u(A E_α, E_β)` at `p`, and the sum with the
coefficients `η^{αβ}` gives the general formula. For the Killing fields `∂_α`, `Ω_ab`, `L_a` the
right-hand side vanishes, the brackets `[∂_β, V]` being given by the Lie brackets of
`Commutators.lean`; for `S` the brackets are `[∂_β, S] = ∂_β`, which gives `-2 □u`.
-/

@[expose] public noncomputable section

open Filter VectorField
open scoped ContDiff Topology

namespace VectorFieldMethod.Minkowski

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : Spacetime → Spacetime} {u : Spacetime → F} {p : Spacetime}

/-! ### Preliminaries -/

/-- The second derivatives `∂_α ∂_β u` are differentiable at a point where `u` is `C³`. -/
theorem differentiableAt_partialDeriv_partialDeriv (α β : Fin 4) (hu : ContDiffAt ℝ 3 u p) :
    DifferentiableAt ℝ (∂[α] (∂[β] u)) p := by
  have h3 : ContDiffAt ℝ (1 + 1 + 1) u p := by
    norm_num
    exact hu
  exact (contDiffAt_partialDeriv α (contDiffAt_partialDeriv β h3)).differentiableAt one_ne_zero

theorem hasFDerivAt_dAlembertian (hu : ContDiffAt ℝ 3 u p) :
    HasFDerivAt (□ u) (∑ α, ∑ β, η α β • fderiv ℝ (∂[α] (∂[β] u)) p) p :=
  HasFDerivAt.fun_sum fun α _ ↦ HasFDerivAt.fun_sum fun β _ ↦
    (differentiableAt_partialDeriv_partialDeriv α β hu).hasFDerivAt.fun_const_smul (η α β)

/-- `□u` is differentiable at a point where `u` is `C³`. -/
theorem differentiableAt_dAlembertian (hu : ContDiffAt ℝ 3 u p) : DifferentiableAt ℝ (□ u) p :=
  (hasFDerivAt_dAlembertian hu).differentiableAt

/-- `V (□u) = η^{αβ} V (∂_α ∂_β u)` at a point where `u` is `C³`. -/
theorem derivAlong_dAlembertian_apply (V : Spacetime → Spacetime) (hu : ContDiffAt ℝ 3 u p) :
    derivAlong V (□ u) p = ∑ α, ∑ β, η α β • derivAlong V (∂[α] (∂[β] u)) p := by
  rw [derivAlong_eq_of_hasFDerivAt (hasFDerivAt_dAlembertian hu)]
  simp [derivAlong_apply]

/-- `V (KG_m u) = V (□u) - m² V u` at a point where `u` is `C³`. -/
theorem derivAlong_kleinGordon_apply (V : Spacetime → Spacetime) (m : ℝ)
    (hu : ContDiffAt ℝ 3 u p) :
    derivAlong V (kleinGordon m u) p = derivAlong V (□ u) p - m ^ 2 • derivAlong V u p := by
  have hd : HasFDerivAt (kleinGordon m u) (fderiv ℝ (□ u) p - m ^ 2 • fderiv ℝ u p) p :=
    (differentiableAt_dAlembertian hu).hasFDerivAt.sub
      ((hu.differentiableAt (by simp)).hasFDerivAt.const_smul (m ^ 2))
  rw [derivAlong_eq_of_hasFDerivAt hd]
  rfl

/-- The contraction of a family `X α β` with `η^{αβ}`:
`η^{αβ} X_{αβ} = -X_{00} + ∑ a, X_{aa}`. -/
theorem sum_minkowskiMetric_smul (X : Fin 4 → Fin 4 → F) :
    ∑ α, ∑ β, η α β • X α β = -X 0 0 + ∑ a : Fin 3, X a.succ a.succ := by
  simp only [Fin.sum_univ_succ (n := 3), minkowskiMetric_zero_zero, minkowskiMetric_zero_succ,
    minkowskiMetric_succ_zero, minkowskiMetric_succ_succ, zero_smul, Finset.sum_const_zero,
    add_zero, zero_add, ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    neg_one_smul]

/-! ### The commutator of `□` with the derivative along an affine component field -/

/-- The commutator of `□` with the derivative along a component field `V` with constant derivative
`A`, at a point where `u` is `C³`:
`V (□u) - □ (V u) = -η^{αβ} (D²u(p) (E_α, [∂_β, V](p)) + D²u(p) ([∂_α, V](p), E_β))`,
where `E_α = coordField α 0` is the value of the constant field `∂_α`. -/
theorem derivAlong_dAlembertian_sub_dAlembertian_derivAlong_apply
    {A : Spacetime →L[ℝ] Spacetime} (hV : ∀ q, HasFDerivAt V A q) (hu : ContDiffAt ℝ 3 u p) :
    derivAlong V (□ u) p - □ (derivAlong V u) p =
      -∑ α, ∑ β, η α β • (fderiv ℝ (fderiv ℝ u) p (coordField α 0)
          (lieBracket ℝ (coordField β) V p) +
        fderiv ℝ (fderiv ℝ u) p (lieBracket ℝ (coordField α) V p) (coordField β 0)) := by
  have hVc : ContDiff ℝ 2 V := by
    have h : ContDiff ℝ ((1 : ℕ) + 1) V := contDiff_succ_iff_hasFDerivAt.mpr
      ⟨fun _ ↦ A, contDiff_const, hV⟩
    norm_num at h
    exact h
  -- The Lie brackets `[∂_β, V] = A E_β` are constant.
  have hK (β : Fin 4) (q : Spacetime) :
      lieBracket ℝ (coordField β) V q = A (coordField β 0) := by
    rw [lieBracket, (hV q).fderiv, (hasFDerivAt_coordField β q).fderiv, zero_apply, sub_zero,
      coordField_eq_const]
  have hu3 : ContDiffAt ℝ (2 + 1) u p := by
    norm_num
    exact hu
  have hu2 : ContDiffAt ℝ 2 u p := hu.of_le (by norm_num)
  have hu2' : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 u q :=
    (hu.eventually (by simp)).mono fun q hq ↦ hq.of_le (by norm_num)
  have hB : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu2.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  have hVu : ContDiffAt ℝ (1 + 1) (derivAlong V u) p := by
    rw [one_add_one_eq_two]
    exact contDiffAt_derivAlong hVc.contDiffAt hu3
  -- `V (∂_α ∂_β u) = ∂_α ∂_β (V u) - D²u(E_α, A E_β) - D²u(A E_α, E_β)` at `p`.
  have key (α β : Fin 4) : derivAlong V (∂[α] (∂[β] u)) p =
      ∂[α] (∂[β] (derivAlong V u)) p -
        (fderiv ℝ (fderiv ℝ u) p (coordField α 0) (A (coordField β 0)) +
          fderiv ℝ (fderiv ℝ u) p (A (coordField α 0)) (coordField β 0)) := by
    -- `V (∂_β u) = ∂_β (V u) - D u (A E_β)` near `p`.
    have h1 : derivAlong V (∂[β] u) =ᶠ[𝓝 p]
        fun q ↦ ∂[β] (derivAlong V u) q - fderiv ℝ u q (A (coordField β 0)) := by
      filter_upwards [hu2'] with q hq
      have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply
        (differentiable_coordField β q) (hV q).differentiableAt hq
      rw [derivAlong_apply (lieBracket ℝ _ _), hK β q] at h
      rw [← h]
      exact (sub_sub_cancel _ _).symm
    -- `∂_α (V (∂_β u)) - V (∂_α ∂_β u) = D (∂_β u) (A E_α)` at `p`.
    have h2 : ∂[α] (derivAlong V (∂[β] u)) p - derivAlong V (∂[α] (∂[β] u)) p =
        fderiv ℝ (∂[β] u) p (A (coordField α 0)) := by
      have h := derivAlong_derivAlong_sub_derivAlong_derivAlong_apply
        (differentiable_coordField α p) (hV p).differentiableAt (contDiffAt_partialDeriv β hu3)
      rw [derivAlong_apply (lieBracket ℝ _ _), hK α p] at h
      exact h
    have h3 : ∂[α] (derivAlong V (∂[β] u)) p = ∂[α] (∂[β] (derivAlong V u)) p -
        fderiv ℝ (fderiv ℝ u) p (coordField α 0) (A (coordField β 0)) := by
      have hX : DifferentiableAt ℝ (∂[β] (derivAlong V u)) p :=
        (contDiffAt_partialDeriv β hVu).differentiableAt one_ne_zero
      have hY : DifferentiableAt ℝ (fun q ↦ fderiv ℝ u q (A (coordField β 0))) p :=
        hB.clm_apply (differentiableAt_const _)
      rw [partialDeriv, derivAlong_congr_of_eventuallyEq _ h1, derivAlong_apply,
        fderiv_fun_sub hX hY, sub_apply]
      congr 1
      exact (derivAlong_derivAlong_of_const (V := coordField α)
        (W := fun _ ↦ A (coordField β 0)) (fun _ ↦ rfl) hB).trans
        (by rw [coordField_eq_const α p])
    have h4 : fderiv ℝ (∂[β] u) p (A (coordField α 0)) =
        fderiv ℝ (fderiv ℝ u) p (A (coordField α 0)) (coordField β 0) :=
      derivAlong_derivAlong_of_const (V := fun _ ↦ A (coordField α 0)) (coordField_eq_const β) hB
    rw [h3, h4] at h2
    rw [← h2]
    abel
  rw [derivAlong_dAlembertian_apply V hu, dAlembertian_apply]
  simp only [key, smul_sub, Finset.sum_sub_distrib, hK _ p]
  abel

/-- The commutator of `KG_m` with the derivative along any component field `V` is its commutator
with `□`, at a point where `u` is `C³`. -/
theorem derivAlong_kleinGordon_sub_kleinGordon_derivAlong_apply (V : Spacetime → Spacetime)
    (m : ℝ) (hu : ContDiffAt ℝ 3 u p) :
    derivAlong V (kleinGordon m u) p - kleinGordon m (derivAlong V u) p =
      derivAlong V (□ u) p - □ (derivAlong V u) p := by
  rw [derivAlong_kleinGordon_apply V m hu, kleinGordon_apply]
  abel

/-! ### Commutators with the wave operator -/

/-- `[∂_α, □] u = 0`: `∂_α (□u) = □ (∂_α u)` at a point where `u` is `C³`. -/
theorem partialDeriv_dAlembertian_comm_apply (α : Fin 4) (hu : ContDiffAt ℝ 3 u p) :
    ∂[α] (□ u) p = □ (∂[α] u) p := by
  rw [← sub_eq_zero]
  refine (derivAlong_dAlembertian_sub_dAlembertian_derivAlong_apply
    (hasFDerivAt_coordField α) hu).trans ?_
  have h0 (β : Fin 4) : lieBracket ℝ (coordField β) (coordField α) p = 0 := by
    rw [lieBracket, fderiv_coordField, fderiv_coordField, zero_apply, zero_apply, sub_zero]
  simp [h0]

/-- `[∂_α, □] = 0` on functions of class `C³`. -/
theorem partialDeriv_dAlembertian_comm (α : Fin 4) (hu : ContDiff ℝ 3 u) :
    ∂[α] (□ u) = □ (∂[α] u) :=
  funext fun _ ↦ partialDeriv_dAlembertian_comm_apply α hu.contDiffAt

/-- `[Ω_ab, □] u = 0`: `Ω_ab (□u) = □ (Ω_ab u)` at a point where `u` is `C³`. -/
theorem rotation_dAlembertian_comm_apply (a b : Fin 3) (hu : ContDiffAt ℝ 3 u p) :
    rotation a b (□ u) p = □ (rotation a b u) p := by
  rw [← sub_eq_zero]
  refine (derivAlong_dAlembertian_sub_dAlembertian_derivAlong_apply
    (hasFDerivAt_of_isLinearMap (isLinearMap_rotationField a b)) hu).trans ?_
  rw [neg_eq_zero, sum_minkowskiMetric_smul]
  simp only [coordField_zero, coordField_succ, lieBracket_timeField_rotationField,
    lieBracket_spaceField_rotationField, Pi.sub_apply, Pi.smul_apply, map_sub, map_smul, map_zero,
    sub_apply, smul_apply, zero_apply]
  simp [spaceField, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- `[Ω_ab, □] = 0` on functions of class `C³`. -/
theorem rotation_dAlembertian_comm (a b : Fin 3) (hu : ContDiff ℝ 3 u) :
    rotation a b (□ u) = □ (rotation a b u) :=
  funext fun _ ↦ rotation_dAlembertian_comm_apply a b hu.contDiffAt

/-- `[L_a, □] u = 0`: `L_a (□u) = □ (L_a u)` at a point where `u` is `C³`. -/
theorem boost_dAlembertian_comm_apply (a : Fin 3) (hu : ContDiffAt ℝ 3 u p) :
    boost a (□ u) p = □ (boost a u) p := by
  rw [← sub_eq_zero]
  refine (derivAlong_dAlembertian_sub_dAlembertian_derivAlong_apply
    (hasFDerivAt_of_isLinearMap (isLinearMap_boostField a)) hu).trans ?_
  rw [neg_eq_zero, sum_minkowskiMetric_smul]
  simp only [coordField_zero, coordField_succ, lieBracket_timeField_boostField,
    lieBracket_spaceField_boostField, Pi.smul_apply, map_smul, smul_apply]
  simp [timeField, spaceField, Finset.sum_add_distrib]
  abel

/-- `[L_a, □] = 0` on functions of class `C³`. -/
theorem boost_dAlembertian_comm (a : Fin 3) (hu : ContDiff ℝ 3 u) :
    boost a (□ u) = □ (boost a u) :=
  funext fun _ ↦ boost_dAlembertian_comm_apply a hu.contDiffAt

/-- `[S, □] u = -2 □u`: `S (□u) - □ (S u) = -2 □u` at a point where `u` is `C³`. -/
theorem scaling_dAlembertian_sub_dAlembertian_scaling_apply (hu : ContDiffAt ℝ 3 u p) :
    scaling (□ u) p - □ (scaling u) p = (-2 : ℝ) • □ u p := by
  refine (derivAlong_dAlembertian_sub_dAlembertian_derivAlong_apply
    (hasFDerivAt_of_isLinearMap isLinearMap_scalingField) hu).trans ?_
  have hB : DifferentiableAt ℝ (fderiv ℝ u) p :=
    ((hu.of_le (by norm_num) : ContDiffAt ℝ 2 u p).fderiv_right (m := 1) le_rfl).differentiableAt
      one_ne_zero
  simp only [lieBracket_coordField_scalingField, coordField_eq_const _ p, dAlembertian_apply,
    partialDeriv_partialDeriv_apply _ _ hB]
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun β _ ↦ ?_
  module

/-- `[S, □] = -2 □` on functions of class `C³`. -/
theorem scaling_dAlembertian_sub_dAlembertian_scaling (hu : ContDiff ℝ 3 u) :
    scaling (□ u) - □ (scaling u) = (-2 : ℝ) • □ u :=
  funext fun _ ↦ scaling_dAlembertian_sub_dAlembertian_scaling_apply hu.contDiffAt

/-! ### Commutators with the Klein–Gordon operator -/

/-- `[∂_α, KG_m] u = 0`: `∂_α (KG_m u) = KG_m (∂_α u)` at a point where `u` is `C³`. -/
theorem partialDeriv_kleinGordon_comm_apply (α : Fin 4) (m : ℝ) (hu : ContDiffAt ℝ 3 u p) :
    ∂[α] (kleinGordon m u) p = kleinGordon m (∂[α] u) p := by
  rw [← sub_eq_zero]
  exact (derivAlong_kleinGordon_sub_kleinGordon_derivAlong_apply (coordField α) m hu).trans
    (sub_eq_zero.mpr (partialDeriv_dAlembertian_comm_apply α hu))

/-- `[∂_α, KG_m] = 0` on functions of class `C³`. -/
theorem partialDeriv_kleinGordon_comm (α : Fin 4) (m : ℝ) (hu : ContDiff ℝ 3 u) :
    ∂[α] (kleinGordon m u) = kleinGordon m (∂[α] u) :=
  funext fun _ ↦ partialDeriv_kleinGordon_comm_apply α m hu.contDiffAt

/-- `[Ω_ab, KG_m] u = 0`: `Ω_ab (KG_m u) = KG_m (Ω_ab u)` at a point where `u` is `C³`. -/
theorem rotation_kleinGordon_comm_apply (a b : Fin 3) (m : ℝ) (hu : ContDiffAt ℝ 3 u p) :
    rotation a b (kleinGordon m u) p = kleinGordon m (rotation a b u) p := by
  rw [← sub_eq_zero]
  exact (derivAlong_kleinGordon_sub_kleinGordon_derivAlong_apply (rotationField a b) m hu).trans
    (sub_eq_zero.mpr (rotation_dAlembertian_comm_apply a b hu))

/-- `[Ω_ab, KG_m] = 0` on functions of class `C³`. -/
theorem rotation_kleinGordon_comm (a b : Fin 3) (m : ℝ) (hu : ContDiff ℝ 3 u) :
    rotation a b (kleinGordon m u) = kleinGordon m (rotation a b u) :=
  funext fun _ ↦ rotation_kleinGordon_comm_apply a b m hu.contDiffAt

/-- `[L_a, KG_m] u = 0`: `L_a (KG_m u) = KG_m (L_a u)` at a point where `u` is `C³`. -/
theorem boost_kleinGordon_comm_apply (a : Fin 3) (m : ℝ) (hu : ContDiffAt ℝ 3 u p) :
    boost a (kleinGordon m u) p = kleinGordon m (boost a u) p := by
  rw [← sub_eq_zero]
  exact (derivAlong_kleinGordon_sub_kleinGordon_derivAlong_apply (boostField a) m hu).trans
    (sub_eq_zero.mpr (boost_dAlembertian_comm_apply a hu))

/-- `[L_a, KG_m] = 0` on functions of class `C³`. -/
theorem boost_kleinGordon_comm (a : Fin 3) (m : ℝ) (hu : ContDiff ℝ 3 u) :
    boost a (kleinGordon m u) = kleinGordon m (boost a u) :=
  funext fun _ ↦ boost_kleinGordon_comm_apply a m hu.contDiffAt

/-- `[S, KG_m] u = -2 □u`: `S (KG_m u) - KG_m (S u) = -2 □u` at a point where `u` is `C³`. -/
theorem scaling_kleinGordon_sub_kleinGordon_scaling_apply (m : ℝ) (hu : ContDiffAt ℝ 3 u p) :
    scaling (kleinGordon m u) p - kleinGordon m (scaling u) p = (-2 : ℝ) • □ u p :=
  (derivAlong_kleinGordon_sub_kleinGordon_derivAlong_apply scalingField m hu).trans
    (scaling_dAlembertian_sub_dAlembertian_scaling_apply hu)

/-- `[S, KG_m] u = -2 □u` on functions of class `C³`. -/
theorem scaling_kleinGordon_sub_kleinGordon_scaling (m : ℝ) (hu : ContDiff ℝ 3 u) :
    scaling (kleinGordon m u) - kleinGordon m (scaling u) = (-2 : ℝ) • □ u :=
  funext fun _ ↦ scaling_kleinGordon_sub_kleinGordon_scaling_apply m hu.contDiffAt

/-! ### Sanity checks

The first example checks `[S, □] = -2 □` on `u = t² - r²`, computing both sides independently from
`□(t² - r²) = -8` (`dAlembertian_timeCoord_sq_sub_radius_sq`) and `S(t² - r²) = 2 (t² - r²)`
(`scaling_timeCoord_sq_sub_radius_sq`): `S (□u) - □ (S u) = S(-8) - □(2u) = 0 + 16` and
`-2 □u = 16`. The second one applies `scaling_dAlembertian_sub_dAlembertian_scaling_apply` to the
same `u`, whose hypothesis `ContDiffAt ℝ 3 u p` holds since `u` is a polynomial. The last one
checks that the hypothesis of the general formula
`derivAlong_dAlembertian_sub_dAlembertian_derivAlong_apply` holds for the boost fields. -/

/-- `[S, □] = -2 □` on `u = t² - r²`: both sides equal `16`. -/
example (p : Spacetime) :
    scaling (□ fun q ↦ timeCoord q ^ 2 - radius q ^ 2) p -
        □ (scaling fun q ↦ timeCoord q ^ 2 - radius q ^ 2) p = 16 ∧
      (-2 : ℝ) • □ (fun q ↦ timeCoord q ^ 2 - radius q ^ 2) p = 16 := by
  have h : (fun p ↦ 2 * (timeCoord p ^ 2 - radius p ^ 2)) =
      (2 : ℝ) • fun p ↦ timeCoord p ^ 2 - radius p ^ 2 := rfl
  refine ⟨?_, ?_⟩
  · rw [dAlembertian_timeCoord_sq_sub_radius_sq, scaling_const, scaling_timeCoord_sq_sub_radius_sq,
      h, dAlembertian_smul, dAlembertian_timeCoord_sq_sub_radius_sq]
    norm_num
  · rw [dAlembertian_timeCoord_sq_sub_radius_sq]
    norm_num

/-- With `□(t² - r²) = -8`, the theorem `scaling_dAlembertian_sub_dAlembertian_scaling_apply`
gives `□ (S (t² - r²)) = -16`, in agreement with `S (t² - r²) = 2 (t² - r²)`. -/
example (p : Spacetime) : □ (scaling fun q ↦ timeCoord q ^ 2 - radius q ^ 2) p = -16 := by
  have hu : ContDiffAt ℝ 3 (fun q ↦ timeCoord q ^ 2 - radius q ^ 2) p := by
    simp_rw [radius_sq]
    fun_prop
  have h := scaling_dAlembertian_sub_dAlembertian_scaling_apply hu
  rw [dAlembertian_timeCoord_sq_sub_radius_sq, scaling_const] at h
  norm_num at h
  linarith

/-- The boost fields satisfy the hypothesis of the general formula
`derivAlong_dAlembertian_sub_dAlembertian_derivAlong_apply`: they have a constant derivative. -/
example (a : Fin 3) : ∃ A : Spacetime →L[ℝ] Spacetime, ∀ q, HasFDerivAt (boostField a) A q :=
  ⟨_, hasFDerivAt_of_isLinearMap (isLinearMap_boostField a)⟩

end VectorFieldMethod.Minkowski
