/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Minkowski spacetime: coordinates and metric

This file sets up the coordinate layer of Minkowski spacetime `ℝ^{1+3}`.

## Main definitions

* `Spacetime`: the type `ℝ × EuclideanSpace ℝ (Fin 3)` of points `p = (t, x)`.
* `timeCoord`, `spaceCoord a`, `radius`: the coordinate functions `t`, `x_a` and `r = |x|`.
* `minkowskiMetric`: the matrix `η_{αβ} = diag(-1, 1, 1, 1)` indexed by `Fin 4`.

## Conventions

* Signature `(-, +, +, +)`.
* Spacetime indices `α : Fin 4`: `0` is time, `Fin.succ a` is the spatial component `a : Fin 3`.
  The mathematical spatial indices `1, 2, 3` correspond to the Lean indices `0, 1, 2`.
* `η * η = 1`, so the inverse metric `η^{αβ}` has the same entries as `η_{αβ}`.
* The norm on `Spacetime` is the max norm of the product, `max |t| ‖x‖`, and `Spacetime` carries
  no inner product. `‖p‖` is therefore *not* a spacetime distance and is not used as one.

## Notation

`η` for `minkowskiMetric`, scoped in `VectorFieldMethod.Minkowski`.
-/

@[expose] public noncomputable section

namespace VectorFieldMethod.Minkowski

/-- Minkowski spacetime `ℝ^{1+3}`, modelled as `ℝ × ℝ³`: the first component of `p = (t, x)` is
the time `t`, the second component is the spatial point `x`.

The norm of this product type is the max norm `max |t| ‖x‖`, and there is no inner product;
`‖p‖` is not a spacetime distance. -/
abbrev Spacetime : Type := ℝ × EuclideanSpace ℝ (Fin 3)

/-! ### Coordinate functions -/

/-- The time coordinate `t` of `p = (t, x)`. -/
def timeCoord (p : Spacetime) : ℝ := p.1

/-- The spatial coordinate `x_a` of `p = (t, x)`, for `a : Fin 3`. The Lean index `a = 0, 1, 2`
corresponds to the mathematical index `1, 2, 3`. Spatial indices are raised and lowered without
changing the value: `x_a = x^a`. -/
def spaceCoord (a : Fin 3) (p : Spacetime) : ℝ := p.2 a

/-- The spatial radius `r = |x|` of `p = (t, x)`. It is not differentiable at `x = 0`; compute
with `r² = ∑ a, x_a²` (`radius_sq`) instead. -/
def radius (p : Spacetime) : ℝ := ‖p.2‖

theorem timeCoord_apply (p : Spacetime) : timeCoord p = p.1 := rfl

theorem spaceCoord_apply (a : Fin 3) (p : Spacetime) : spaceCoord a p = p.2 a := rfl

theorem radius_apply (p : Spacetime) : radius p = ‖p.2‖ := rfl

/-- `r² = ∑ a, x_a²`. -/
theorem radius_sq (p : Spacetime) : radius p ^ 2 = ∑ a, spaceCoord a p ^ 2 :=
  EuclideanSpace.real_norm_sq_eq p.2

/-- `r² = ∑ a, x_a²`, as an equality of functions. -/
theorem radius_sq_eq_sum : (fun p ↦ radius p ^ 2) = fun p ↦ ∑ a, spaceCoord a p ^ 2 :=
  funext radius_sq

/-! ### The Minkowski metric -/

/-- The Minkowski metric `η_{αβ} = diag(-1, 1, 1, 1)` in the signature `(-, +, +, +)`, indexed by
`α β : Fin 4` with `0` the time index. Since `η * η = 1` (`minkowskiMetric_mul_self`), the
inverse metric `η^{αβ}` has the same entries. -/
def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (Fin.cons (-1) fun _ ↦ 1)

@[inherit_doc] scoped notation "η" => minkowskiMetric

theorem minkowskiMetric_zero_zero : η 0 0 = -1 := rfl

theorem minkowskiMetric_zero_succ (b : Fin 3) : η 0 b.succ = 0 :=
  Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero b).symm

theorem minkowskiMetric_succ_zero (a : Fin 3) : η a.succ 0 = 0 :=
  Matrix.diagonal_apply_ne _ (Fin.succ_ne_zero a)

theorem minkowskiMetric_succ_succ (a b : Fin 3) : η a.succ b.succ = if a = b then 1 else 0 := by
  simp [minkowskiMetric, Matrix.diagonal_apply]

/-- `η` is symmetric. -/
theorem transpose_minkowskiMetric : Matrix.transpose η = η :=
  Matrix.diagonal_transpose _

/-- `η * η = 1`: the inverse metric `η^{αβ}` has the same entries as `η_{αβ}`. -/
theorem minkowskiMetric_mul_self : η * η = 1 := by
  rw [minkowskiMetric, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext α
  refine Fin.cases ?_ (fun a ↦ ?_) α <;> simp

/-- The inverse metric: `η⁻¹ = η`. -/
theorem inv_minkowskiMetric : η⁻¹ = η :=
  Matrix.inv_eq_left_inv minkowskiMetric_mul_self

end VectorFieldMethod.Minkowski
