/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.WaveOperator
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The energy-momentum tensor of the Klein–Gordon field

For a field `u : Spacetime → F` with values in a real inner product space `F` (real fields have
`F = ℝ`, complex fields `F = ℂ` with the real inner product `⟪z, w⟫ = Re (conj z * w)`) and a mass
`m : ℝ`, this file defines the energy-momentum tensor of the Klein–Gordon equation
`□u - m² u = 0`.

## Main definitions

* `energyMomentum m u α β`: the energy-momentum tensor
  `T_{αβ} = ⟪∂_α u, ∂_β u⟫ - ½ η_{αβ} (η^{γδ} ⟪∂_γ u, ∂_δ u⟫ + m² ‖u‖²)`.
* `spacetimeDiv J`: the spacetime divergence `∂_α J^α = ∑ α, ∂_α J^α` of a vector field with real
  components `J α : Spacetime → ℝ`.
* `energyCurrent m u α`: the energy current `P^α = -η^{αγ} T_{γ0}` associated with `∂_t`.

## Main statements

* `derivAlong_inner`, `derivAlong_norm_sq`: the Leibniz rules `V ⟪u, v⟫ = ⟪V u, v⟫ + ⟪u, V v⟫`
  and `V ‖u‖² = 2 ⟪u, V u⟫` at a point where `u` and `v` are differentiable.
* `energyMomentum_swap`: `T_{βα} = T_{αβ}`.

## Normalization

The tensor carries the factor `½`, so that the energy density is
`P^0 = T_{00} = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)`. Texts that define the energy density
without the factor `½`, as `‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²`, have a tensor, a current and an
energy that are twice the ones of this file; the identities of this file hold for them after
multiplying both sides by `2`.

## Conventions

Signature `(-, +, +, +)`. The inverse metric `η^{αβ}` has the same entries as `η_{αβ}`
(`inv_minkowskiMetric`), so both are written with `minkowskiMetric`. The Klein–Gordon operator is
`kleinGordon m u = □u - m² u` with `□ = -∂_t² + Δ`.
-/

@[expose] public noncomputable section

open Filter
open scoped RealInnerProductSpace Topology

namespace VectorFieldMethod.Minkowski

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {u v : Spacetime → F} {p : Spacetime}

/-! ### The Leibniz rule for the inner product -/

/-- The Leibniz rule `V ⟪u, v⟫ = ⟪V u, v⟫ + ⟪u, V v⟫` at a point where `u` and `v` are
differentiable. -/
theorem derivAlong_inner (V : Spacetime → Spacetime) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    derivAlong V (fun q ↦ ⟪u q, v q⟫) p = ⟪derivAlong V u p, v p⟫ + ⟪u p, derivAlong V v p⟫ := by
  rw [derivAlong_apply, derivAlong_apply, derivAlong_apply, fderiv_inner_apply ℝ hu hv]
  exact add_comm _ _

/-- The Leibniz rule `V ‖u‖² = 2 ⟪u, V u⟫` at a point where `u` is differentiable. -/
theorem derivAlong_norm_sq (V : Spacetime → Spacetime) (hu : DifferentiableAt ℝ u p) :
    derivAlong V (fun q ↦ ‖u q‖ ^ 2) p = 2 * ⟪u p, derivAlong V u p⟫ := by
  rw [derivAlong_eq_of_hasFDerivAt hu.hasFDerivAt.norm_sq, derivAlong_apply]
  simp

/-- `∂_α ⟪u, v⟫ = ⟪∂_α u, v⟫ + ⟪u, ∂_α v⟫` at a point where `u` and `v` are differentiable. -/
theorem partialDeriv_inner (α : Fin 4) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    ∂[α] (fun q ↦ ⟪u q, v q⟫) p = ⟪∂[α] u p, v p⟫ + ⟪u p, ∂[α] v p⟫ :=
  derivAlong_inner _ hu hv

/-- `∂_α ‖u‖² = 2 ⟪u, ∂_α u⟫` at a point where `u` is differentiable. -/
theorem partialDeriv_norm_sq (α : Fin 4) (hu : DifferentiableAt ℝ u p) :
    ∂[α] (fun q ↦ ‖u q‖ ^ 2) p = 2 * ⟪u p, ∂[α] u p⟫ :=
  derivAlong_norm_sq _ hu

/-! ### Definitions -/

/-- The energy-momentum tensor of the Klein–Gordon field `u` of mass `m`:
`T_{αβ} = ⟪∂_α u, ∂_β u⟫ - ½ η_{αβ} (η^{γδ} ⟪∂_γ u, ∂_δ u⟫ + m² ‖u‖²)`.

The coefficients `η_{αβ}` and `η^{γδ}` are both entries of `minkowskiMetric` (`η⁻¹ = η`). With the
factor `½`, the energy density is `T_{00} = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)`; texts whose
energy density has no factor `½` use `2 T_{αβ}`. -/
def energyMomentum (m : ℝ) (u : Spacetime → F) (α β : Fin 4) : Spacetime → ℝ :=
  fun p ↦ ⟪∂[α] u p, ∂[β] u p⟫ -
    1 / 2 * η α β * (∑ γ, ∑ δ, η γ δ * ⟪∂[γ] u p, ∂[δ] u p⟫ + m ^ 2 * ‖u p‖ ^ 2)

theorem energyMomentum_apply (m : ℝ) (u : Spacetime → F) (α β : Fin 4) (p : Spacetime) :
    energyMomentum m u α β p = ⟪∂[α] u p, ∂[β] u p⟫ -
      1 / 2 * η α β * (∑ γ, ∑ δ, η γ δ * ⟪∂[γ] u p, ∂[δ] u p⟫ + m ^ 2 * ‖u p‖ ^ 2) :=
  rfl

/-- The spacetime divergence `∂_α J^α = ∑ α, ∂_α J^α` of the vector field with real components
`J α : Spacetime → ℝ`. -/
def spacetimeDiv (J : Fin 4 → Spacetime → ℝ) : Spacetime → ℝ :=
  fun p ↦ ∑ α, ∂[α] (J α) p

theorem spacetimeDiv_apply (J : Fin 4 → Spacetime → ℝ) (p : Spacetime) :
    spacetimeDiv J p = ∑ α, ∂[α] (J α) p :=
  rfl

/-- The energy current `P^α = -η^{αγ} T_{γ0}` of the Klein–Gordon field `u`, associated with the
vector field `∂_t`. Its time component is the energy density
`P^0 = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)`. -/
def energyCurrent (m : ℝ) (u : Spacetime → F) (α : Fin 4) : Spacetime → ℝ :=
  fun p ↦ -∑ γ, η α γ * energyMomentum m u γ 0 p

theorem energyCurrent_apply (m : ℝ) (u : Spacetime → F) (α : Fin 4) (p : Spacetime) :
    energyCurrent m u α p = -∑ γ, η α γ * energyMomentum m u γ 0 p :=
  rfl

/-! ### Symmetry -/

/-- The energy-momentum tensor is symmetric: `T_{βα} = T_{αβ}`. -/
theorem energyMomentum_swap (m : ℝ) (u : Spacetime → F) (α β : Fin 4) :
    energyMomentum m u β α = energyMomentum m u α β := by
  funext p
  rw [energyMomentum_apply, energyMomentum_apply, real_inner_comm (∂[α] u p),
    Matrix.IsSymm.apply transpose_minkowskiMetric α β]

end VectorFieldMethod.Minkowski
