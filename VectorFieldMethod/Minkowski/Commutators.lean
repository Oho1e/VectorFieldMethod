/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.VectorFields
public import Mathlib.Analysis.Calculus.VectorField

/-!
# Commutators of derivatives along vector fields

For component fields `V W : Spacetime → Spacetime`, the commutator of the first-order operators
`derivAlong V` and `derivAlong W` is the first-order operator along the Lie bracket of the
component fields:
`V (W u) - W (V u) = [V, W] u`, where `[V, W] = lieBracket ℝ V W = DW · V - DV · W` is Mathlib's
`VectorField.lieBracket`.

## Main statements

* `derivAlong_derivAlong_sub_derivAlong_derivAlong_apply`: `V (W u) - W (V u) = [V, W] u` at a
  point where `V` and `W` are differentiable and `u` is `C²`.
* `derivAlong_derivAlong_sub_derivAlong_derivAlong`: the same identity of functions, for
  differentiable `V`, `W` and `u` of class `C²`.

## Implementation notes

The identity is Mathlib's `VectorField.fderiv_apply_lieBracket`: the second-order terms
`D²u(p) (V p) (W p)` and `D²u(p) (W p) (V p)` cancel by the symmetry of the second derivative of a
`C²` function. Since `fderiv` is `0` at points of non-differentiability, the hypotheses cannot be
dropped.
-/

@[expose] public noncomputable section

open VectorField
open scoped ContDiff

namespace VectorFieldMethod.Minkowski

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V W : Spacetime → Spacetime} {u : Spacetime → F} {p : Spacetime}

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

end VectorFieldMethod.Minkowski
