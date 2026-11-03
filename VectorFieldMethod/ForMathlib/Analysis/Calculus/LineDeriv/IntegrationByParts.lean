/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.LinearAlgebra.Trace

/-!
# Integrals of derivatives of compactly supported functions

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`. We show that
the integral of a directional derivative of a compactly supported `C¹` function vanishes, and
deduce that so does the integral of the divergence `x ↦ tr (DV(x))` of a compactly supported `C¹`
vector field `V : E → E`. Both follow from the integration by parts formula
`integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`, applied with a constant function.

## Main statements

* `MeasureTheory.integral_fderiv_apply_eq_zero`: `∫ x, fderiv ℝ f x v ∂μ = 0`.
* `MeasureTheory.integral_trace_fderiv_eq_zero`: `∫ x, LinearMap.trace ℝ E (fderiv ℝ V x) ∂μ = 0`.
-/

@[expose] public noncomputable section

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The integral of a directional derivative of a compactly supported `C¹` function vanishes. -/
theorem integral_fderiv_apply_eq_zero {f : E → F} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (v : E) : ∫ x, fderiv ℝ f x v ∂μ = 0 := by
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := μ)
    (f := fun _ ↦ (1 : ℝ)) (g := f) (v := v) (by simp) ?_ ?_
    (fun x _ ↦ differentiableAt_const _) (fun x _ ↦ hf.differentiable one_ne_zero x)
  · simpa using h
  · simpa using ((hf.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport (hfc.fderiv_apply ℝ v)
  · simpa using hf.continuous.integrable_of_hasCompactSupport hfc

/-- The integral of the divergence `x ↦ tr (DV(x))` of a compactly supported `C¹` vector field
`V : E → E` vanishes. -/
theorem integral_trace_fderiv_eq_zero {V : E → E} (hV : ContDiff ℝ 1 V)
    (hVc : HasCompactSupport V) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ = 0 := by
  let T : (E →L[ℝ] E) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ))
  have hint : Integrable (fderiv ℝ V) μ :=
    (hV.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hVc.fderiv ℝ)
  have h0 : ∫ x, fderiv ℝ V x ∂μ = 0 := by
    ext v
    rw [ContinuousLinearMap.integral_apply hint v, integral_fderiv_apply_eq_zero hV hVc v]
    simp
  calc ∫ x, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ = ∫ x, T (fderiv ℝ V x) ∂μ := rfl
    _ = T (∫ x, fderiv ℝ V x ∂μ) := T.integral_comp_comm hint
    _ = 0 := by rw [h0, map_zero]

end MeasureTheory
