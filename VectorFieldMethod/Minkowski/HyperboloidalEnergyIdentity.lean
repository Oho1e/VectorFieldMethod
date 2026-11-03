/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.HyperboloidalEnergy
public import VectorFieldMethod.ForMathlib.MeasureTheory.Integral.DivergenceTheoremHyperboloid

/-!
# The hyperboloidal energy identity for the Klein–Gordon field

## Main statements

* `deriv_add_spatialDivergence_eq_spacetimeDiv`: the divergence of a vector field `J` on
  `Spacetime` (time first) agrees with the divergence `∂_t X₀ + div_x X` of the same field written
  in the coordinates `(x, t)` of the divergence theorems (time second).
* `measurePreserving_swap_spacetime`, `setIntegral_spacetime_eq_setIntegral_swap`: the coordinate
  swap `(x, t) ↦ (t, x)` is measure preserving, and the corresponding change of variables.
-/

@[expose] public noncomputable section

open Set Filter Function Topology MeasureTheory
open scoped RealInnerProductSpace

namespace VectorFieldMethod.Minkowski

/-! ### From `Spacetime` to the coordinates `(x, t)` of the divergence theorems -/

/-- The divergence of a vector field `J` with real components `J α` on `Spacetime`, written in the
coordinates `(x, t)` (time second) of the divergence theorems. Let `X₀ (x, t) = J 0 (t, x)` and
`X (x, t) = ∑ a, J (a + 1) (t, x) e_a`. If the components of `J` are differentiable at `(t, x)`,
then `∂_t X₀ + div_x X = ∂_α J^α` at `(x, t)`. -/
theorem deriv_add_spatialDivergence_eq_spacetimeDiv (J : Fin 4 → Spacetime → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} {t : ℝ} (hJ : ∀ α, DifferentiableAt ℝ (J α) (t, x)) :
    deriv (fun s ↦ J 0 (s, x)) t +
        spatialDivergence (fun q ↦ ∑ a, J a.succ (q.2, q.1) • EuclideanSpace.single a 1) (x, t) =
      spacetimeDiv J (t, x) := by
  -- the time derivative
  have h₀ : deriv (fun s ↦ J 0 (s, x)) t = ∂[0] (J 0) (t, x) := by
    have h : HasDerivAt (fun s : ℝ ↦ (s, x)) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact ((hJ 0).hasFDerivAt.comp_hasDerivAt t h).deriv
  -- the spatial divergence
  have hcomp (a : Fin 3) : (fun y : EuclideanSpace ℝ (Fin 3) ↦
      (∑ b : Fin 3, J b.succ (t, y) • EuclideanSpace.single b (1 : ℝ) :
        EuclideanSpace ℝ (Fin 3)) a) = fun y ↦ J a.succ (t, y) := by
    funext y
    simp [Pi.single_apply]
  have hdiff : DifferentiableAt ℝ
      (fun y : EuclideanSpace ℝ (Fin 3) ↦
        ∑ b : Fin 3, J b.succ (t, y) • EuclideanSpace.single b (1 : ℝ)) x := by
    refine DifferentiableAt.fun_sum fun (b : Fin 3) _ ↦ ?_
    have hb : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 3) ↦ J b.succ (t, y)) x :=
      (hJ b.succ).comp x (hasFDerivAt_prodMk_right t x).differentiableAt
    exact hb.smul_const _
  have h₁ : spatialDivergence
      (fun q : EuclideanSpace ℝ (Fin 3) × ℝ ↦
        ∑ a : Fin 3, J a.succ (q.2, q.1) • EuclideanSpace.single a (1 : ℝ)) (x, t) =
      ∑ a : Fin 3, ∂[a.succ] (J a.succ) (t, x) := by
    rw [spatialDivergence_euclideanSpace (p := (x, t)) hdiff]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [hcomp]
    have h : HasFDerivAt (fun y ↦ J a.succ (t, y))
        ((fderiv ℝ (J a.succ) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ _)) x :=
      (hJ a.succ).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    rw [h.fderiv]
    rfl
  rw [h₀, h₁, spacetimeDiv_apply, Fin.sum_univ_succ (n := 3)]

/-- The coordinate swap `(x, t) ↦ (t, x)` from `ℝ³ × ℝ`, the spacetime of the divergence theorems
(time second), to `Spacetime` (time first) is measure preserving for the Lebesgue measures. -/
theorem measurePreserving_swap_spacetime :
    MeasurePreserving (Prod.swap : EuclideanSpace ℝ (Fin 3) × ℝ → Spacetime)
      (volume.prod volume) volume :=
  Measure.measurePreserving_swap

/-- Change of variables `p = (x, t) ↦ (t, x)` between a set integral on `Spacetime` and the
corresponding set integral on `ℝ³ × ℝ`. -/
theorem setIntegral_spacetime_eq_setIntegral_swap {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (f : Spacetime → G) (s : Set Spacetime) :
    ∫ p in s, f p = ∫ q in Prod.swap ⁻¹' s, f q.swap ∂(volume.prod volume) :=
  (measurePreserving_swap_spacetime.setIntegral_preimage_emb
    MeasurableEquiv.prodComm.measurableEmbedding f s).symm

end VectorFieldMethod.Minkowski
