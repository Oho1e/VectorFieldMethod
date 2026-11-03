/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Analysis.HyperboloidalSobolev
public import VectorFieldMethod.Minkowski.VectorFields

/-!
# The Klainerman–Sobolev inequality on hyperboloids

For `s > 0` let `H_s = {(t, x) : t = √(s ^ 2 + ‖x‖ ^ 2)}` be the upper sheet of the hyperboloid
`t ^ 2 - ‖x‖ ^ 2 = s ^ 2`. The restriction of a real function `v` on spacetime to `H_s` is the
function `v|_{H_s} x = v (√(s ^ 2 + ‖x‖ ^ 2), x)` on `ℝ³` (`restrictHyperboloid s v`).

This file connects the weighted derivatives `Λ_a = φ_s ∂_a` on `ℝ³` of the analysis layer
(`EuclideanSobolev.hyperboloidalWeightedDeriv s a`, with `φ_s x = √(s ^ 2 + ‖x‖ ^ 2)`) with the
Lorentz boosts `L_a = t ∂_a + x_a ∂_t` (`boost a`), and deduces from the weighted inequality on
`ℝ³` (`EuclideanSobolev.exists_hyperboloidalSobolev`) the Klainerman–Sobolev inequality on
hyperboloids
`sup_{H_s} t ^ (3/2) |u| ≤ C ∑_{|J| ≤ 2} ‖L^J u‖_{L²_f(H_s)}`,
where `‖v‖_{L²_f(H_s)} = ‖v|_{H_s}‖_{L²(ℝ³)}` is the `L²` norm on `H_s` for the flat measure `dx`
and `C` is an absolute constant. See `docs/hyperboloidal-sobolev.md`.

## Main definitions

* `hyperboloidPoint s x`: the point `(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s` above `x ∈ ℝ³`.
* `restrictHyperboloid s v`: the restriction `x ↦ v (√(s ^ 2 + ‖x‖ ^ 2), x)` of `v` to `H_s`.

## Main statements

* `hyperboloidalWeightedDeriv_restrictHyperboloid_apply`: the restriction formula
  `Λ_a (v|_{H_s}) x = (L_a v)|_{H_s} x`, for `s ≠ 0` and `v` differentiable at the point
  `(√(s ^ 2 + ‖x‖ ^ 2), x)`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace VectorFieldMethod.Minkowski

open VectorFieldMethod.EuclideanSobolev

/-! ### Restriction to a hyperboloid -/

/-- The point `(√(s ^ 2 + ‖x‖ ^ 2), x)` of the hyperboloid `H_s = {t = √(s ^ 2 + ‖x‖ ^ 2)}`
above `x ∈ ℝ³`. -/
def hyperboloidPoint (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : Spacetime :=
  (√(s ^ 2 + ‖x‖ ^ 2), x)

/-- The restriction `v|_{H_s}` of `v : Spacetime → ℝ` to the hyperboloid
`H_s = {t = √(s ^ 2 + ‖x‖ ^ 2)}`, as a function on `ℝ³`:
`v|_{H_s} x = v (√(s ^ 2 + ‖x‖ ^ 2), x)`. -/
def restrictHyperboloid (s : ℝ) (v : Spacetime → ℝ) : EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x ↦ v (√(s ^ 2 + ‖x‖ ^ 2), x)

theorem restrictHyperboloid_apply (s : ℝ) (v : Spacetime → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    restrictHyperboloid s v x = v (√(s ^ 2 + ‖x‖ ^ 2), x) :=
  rfl

theorem restrictHyperboloid_eq_comp (s : ℝ) (v : Spacetime → ℝ) :
    restrictHyperboloid s v = v ∘ hyperboloidPoint s :=
  rfl

/-- `hyperboloidPoint s x` lies on the hyperboloid `H_s`. -/
theorem hyperboloidPoint_mem (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    hyperboloidPoint s x ∈ {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} :=
  rfl

/-- The derivative of `x ↦ (√(s ^ 2 + ‖x‖ ^ 2), x)`, for `s ≠ 0`. -/
theorem hasFDerivAt_hyperboloidPoint {s : ℝ} (hs : s ≠ 0) (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (hyperboloidPoint s)
      ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) ↦ √(s ^ 2 + ‖y‖ ^ 2)) x).prod
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)))) x :=
  ((contDiff_sqrt_sq_add_norm_sq hs).differentiable one_ne_zero x).hasFDerivAt.prodMk
    (hasFDerivAt_id x)

/-! ### The restriction formula -/

/-- The value of the boost field at the point `(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s`:
`(x_a, φ_s(x) e_a) = φ_s(x) (x_a / φ_s(x), e_a)`, for `φ_s(x) ≠ 0`. -/
theorem boostField_hyperboloidPoint {s : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hφ : √(s ^ 2 + ‖x‖ ^ 2) ≠ 0) (a : Fin 3) :
    boostField a (hyperboloidPoint s x) =
      √(s ^ 2 + ‖x‖ ^ 2) • (x a / √(s ^ 2 + ‖x‖ ^ 2), EuclideanSpace.single a (1 : ℝ)) := by
  rw [boostField, Prod.smul_mk, smul_eq_mul, mul_div_cancel₀ _ hφ]
  rfl

/-- **Restriction formula.** For `s ≠ 0` and `v` differentiable at the point
`(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s`, `Λ_a (v|_{H_s}) x = (L_a v)|_{H_s} x`. -/
theorem hyperboloidalWeightedDeriv_restrictHyperboloid_apply {s : ℝ} (hs : s ≠ 0) (a : Fin 3)
    {v : Spacetime → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hv : DifferentiableAt ℝ v (√(s ^ 2 + ‖x‖ ^ 2), x)) :
    hyperboloidalWeightedDeriv s a (restrictHyperboloid s v) x =
      restrictHyperboloid s (boost a v) x := by
  have hφ : √(s ^ 2 + ‖x‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hv' : HasFDerivAt v (fderiv ℝ v (hyperboloidPoint s x)) (hyperboloidPoint s x) :=
    hv.hasFDerivAt
  have h := hv'.comp x (hasFDerivAt_hyperboloidPoint hs x)
  rw [restrictHyperboloid_apply, show ((√(s ^ 2 + ‖x‖ ^ 2), x) : Spacetime) =
    hyperboloidPoint s x from rfl, boost_apply, boostField_hyperboloidPoint hφ,
    ContinuousLinearMap.map_smul, smul_eq_mul, hyperboloidalWeightedDeriv,
    restrictHyperboloid_eq_comp, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderiv_sqrt_sq_add_norm_sq_apply hs,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul]

/-! ### Sanity checks -/

/-- The two sides of the restriction formula for `v = t`, computed independently of it. Since
`t|_{H_s} = φ_s`, the left side is `Λ_a φ_s = φ_s ∂_a φ_s = x_a`; since `L_a t = x_a`, the right
side is `(L_a t)|_{H_s} = x_a`. -/
example {s : ℝ} (hs : s ≠ 0) (a : Fin 3) :
    hyperboloidalWeightedDeriv s a (fun x ↦ √(s ^ 2 + ‖x‖ ^ 2)) = (fun x ↦ x a) ∧
      restrictHyperboloid s (boost a timeCoord) = (fun x ↦ x a) := by
  refine ⟨funext fun x ↦ ?_, by rw [boost_timeCoord]; rfl⟩
  have hφ : √(s ^ 2 + ‖x‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [hyperboloidalWeightedDeriv, fderiv_sqrt_sq_add_norm_sq_apply hs,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, mul_div_cancel₀ _ hφ]

/-- The restriction formula applied to `v = t`, which is differentiable everywhere: since
`t|_{H_s} = φ_s` and `L_a t = x_a`, it gives `Λ_a φ_s = x_a` at every point. -/
example {s : ℝ} (hs : s ≠ 0) (a : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    hyperboloidalWeightedDeriv s a (fun y ↦ √(s ^ 2 + ‖y‖ ^ 2)) x = x a := by
  rw [show (fun y : EuclideanSpace ℝ (Fin 3) ↦ √(s ^ 2 + ‖y‖ ^ 2)) =
      restrictHyperboloid s timeCoord from rfl,
    hyperboloidalWeightedDeriv_restrictHyperboloid_apply hs a (differentiable_timeCoord _),
    boost_timeCoord]
  rfl

end VectorFieldMethod.Minkowski
