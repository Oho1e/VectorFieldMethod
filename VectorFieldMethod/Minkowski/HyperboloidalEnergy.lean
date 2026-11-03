/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.EnergyMomentum
public import VectorFieldMethod.Minkowski.VectorFields

/-!
# The semi-hyperboloidal frame and the hyperboloidal energy density

LeFloch–Ma's hyperboloidal foliation method works on the hyperboloids
`H_s = {t = √(s ^ 2 + ‖x‖ ^ 2)}` and replaces the spatial derivatives `∂_a` by the
*semi-hyperboloidal* derivatives `∂̲_a = ∂_a + (x_a / t) ∂_t`, which are tangent to the
hyperboloids.

## Main definitions

* `semiHyperboloidalDeriv a u`: the semi-hyperboloidal derivative
  `∂̲_a u = ∂_a u + (x_a / t) ∂_t u`, for `a : Fin 3`.

## Main statements

* `boost_eq_timeCoord_smul_semiHyperboloidalDeriv`: `L_a u = t ∂̲_a u` where `t ≠ 0`.
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace

namespace VectorFieldMethod.Minkowski

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {u : Spacetime → F} {p : Spacetime}

/-! ### The semi-hyperboloidal derivatives -/

/-- The semi-hyperboloidal derivative `∂̲_a u = ∂_a u + (x_a / t) ∂_t u`, for `a : Fin 3` (the
mathematical index is `a + 1`). At `t = 0` the coefficient `x_a / t` is the junk value `0`. -/
def semiHyperboloidalDeriv (a : Fin 3) (u : Spacetime → F) : Spacetime → F :=
  fun p ↦ ∂ₓ[a] u p + (spaceCoord a p / timeCoord p) • ∂ₜ u p

theorem semiHyperboloidalDeriv_apply (a : Fin 3) (u : Spacetime → F) (p : Spacetime) :
    semiHyperboloidalDeriv a u p = ∂ₓ[a] u p + (spaceCoord a p / timeCoord p) • ∂ₜ u p :=
  rfl

/-- The boost is `t` times the semi-hyperboloidal derivative: `L_a u = t ∂̲_a u` at a point where
`t ≠ 0`. -/
theorem boost_eq_timeCoord_smul_semiHyperboloidalDeriv (a : Fin 3) (u : Spacetime → F)
    (hp : timeCoord p ≠ 0) : boost a u p = timeCoord p • semiHyperboloidalDeriv a u p := by
  rw [boost_eq, semiHyperboloidalDeriv_apply, smul_add, smul_smul, mul_div_cancel₀ _ hp]

end VectorFieldMethod.Minkowski
