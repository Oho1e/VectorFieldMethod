/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Placeholder

This file only checks that the project builds against Mathlib.
It contains no mathematical content and will be removed once the
first real module is added.
-/

@[expose] public section

namespace VectorFieldMethod

/-- The ambient Euclidean space `ℝⁿ`, used here only as a smoke test of the
Mathlib import. -/
abbrev Placeholder (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

end VectorFieldMethod
