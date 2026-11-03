/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# A local Sobolev embedding `H² ⊂ L^∞` on balls of `ℝ³`

This file states the local Sobolev bound on balls of `ℝ³ = EuclideanSpace ℝ (Fin 3)`: there is an
absolute constant `C` such that for every ball `B = ball x₀ ρ` and every function `f` which is `C²`
on `B`,
`|f x₀| ≤ C (ρ ^ (-3/2) ‖f‖_{L²(B)} + ρ ^ (-1/2) ‖Df‖_{L²(B)} + ρ ^ (1/2) ‖D²f‖_{L²(B)})`.
The powers of `ρ` make the bound invariant under dilations. The `L²` norms are `eLpNorm`s, with
values in `ℝ≥0∞`; they may be infinite, in which case the bound holds trivially.

## Main definitions

* `LocalSobolevBound`: the statement of the bound, as a proposition.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace VectorFieldMethod.EuclideanSobolev

/-- **Local Sobolev bound on balls of `ℝ³`.** There is an absolute constant `C` such that for every
ball `B = ball x₀ ρ` and every `f : ℝ³ → ℝ` which is `C²` on `B`,
`|f x₀| ≤ C (ρ ^ (-3/2) ‖f‖_{L²(B)} + ρ ^ (-1/2) ‖Df‖_{L²(B)} + ρ ^ (1/2) ‖D²f‖_{L²(B)})`,
where `Df = fderiv ℝ f` and `D²f = iteratedFDeriv ℝ 2 f` carry their operator norms. -/
def LocalSobolevBound : Prop :=
  ∃ C : NNReal, ∀ (x₀ : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
    0 < ρ → ContDiffOn ℝ 2 f (Metric.ball x₀ ρ) →
    ENNReal.ofReal |f x₀| ≤ (C : ENNReal) *
      (ENNReal.ofReal (ρ ^ (-(3 / 2 : ℝ))) * eLpNorm f 2 (volume.restrict (Metric.ball x₀ ρ)) +
        ENNReal.ofReal (ρ ^ (-(1 / 2 : ℝ))) *
          eLpNorm (fderiv ℝ f) 2 (volume.restrict (Metric.ball x₀ ρ)) +
        ENNReal.ofReal (ρ ^ (1 / 2 : ℝ)) *
          eLpNorm (iteratedFDeriv ℝ 2 f) 2 (volume.restrict (Metric.ball x₀ ρ)))

end VectorFieldMethod.EuclideanSobolev
