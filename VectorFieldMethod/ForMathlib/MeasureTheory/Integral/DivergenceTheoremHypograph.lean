/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.ForMathlib.Analysis.Calculus.SpatialDivergence
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The divergence theorem on the region below a graph

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, and equip
spacetime `E × ℝ` with the product measure `μ.prod volume`; time is the second coordinate. Let
`φ : E → ℝ` be a `C¹` function, and consider a compactly supported `C¹` vector field on spacetime
with time component `X₀ : E × ℝ → ℝ` and spatial component `X : E × ℝ → E`. The divergence theorem
on the region `{(x, t) | t ≤ φ x}` below the graph of `φ` (its *hypograph*) reads
```
∫_{t ≤ φ x} (∂ₜ X₀ + div_x X) d(μ × volume) = ∫_E (X₀ (x, φ x) - Dφ(x) (X (x, φ x))) dμ(x),
```
where `div_x X = spatialDivergence X`. The right-hand side is the flux of `(X₀, X)` through the
graph of `φ`, written in the parametrization `x ↦ (x, φ x)`: no normal vector and no surface
measure appear.

## Main statements

* `MeasureTheory.integral_fderiv_apply_eq_zero`: the integral of a directional derivative of a
  compactly supported `C¹` function vanishes.
* `MeasureTheory.integral_trace_fderiv_eq_zero`: the integral of the divergence of a compactly
  supported `C¹` vector field vanishes.
* `MeasureTheory.measurePreserving_shear`: the shear `(x, τ) ↦ (x, τ + φ x)` preserves
  `μ.prod volume`.

## Implementation notes

The proof uses the shear `S (x, τ) = (x, τ + φ x)`, which preserves `μ.prod volume` and maps the
lower half-space `{τ ≤ 0}` onto the hypograph of `φ`. Pulling back by `S`, the integrand becomes
`∂_τ Y₀ + div_x Y`, where `Y (x, τ) = X (x, τ + φ x)` and
`Y₀ (x, τ) = X₀ (x, τ + φ x) - Dφ(x) (X (x, τ + φ x))` (see `spatialDivergence_shear`). The time
part is handled for each `x` by the fundamental theorem of calculus on `(-∞, 0]`, and the space part
vanishes for each `τ` by `MeasureTheory.integral_trace_fderiv_eq_zero`. Since `∂_τ` never hits
`Dφ(x)`, the function `φ` only needs to be `C¹`, and no differentiation of integrals with variable
bounds is needed.
-/

@[expose] public noncomputable section

open Set Filter Function Topology

section CompactSupport

variable {α β M : Type*} [TopologicalSpace α] [TopologicalSpace β] [Zero M]

namespace HasCompactSupport

/-- A slice `a ↦ f (a, b)` of a function with compact support has compact support. -/
theorem comp_prodMkLeft [T1Space β] {f : α × β → M} (hf : HasCompactSupport f) (b : β) :
    HasCompactSupport fun a ↦ f (a, b) :=
  hf.comp_isClosedEmbedding
    (.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft b) (isClosedMap_prodMk_right b))

/-- A slice `b ↦ f (a, b)` of a function with compact support has compact support. -/
theorem comp_prodMkRight [T1Space α] {f : α × β → M} (hf : HasCompactSupport f) (a : α) :
    HasCompactSupport fun b ↦ f (a, b) :=
  hf.comp_isClosedEmbedding
    (.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight a) (isClosedMap_prodMk_left a))

end HasCompactSupport

end CompactSupport

namespace Homeomorph

variable {α : Type*} [TopologicalSpace α] {φ : α → ℝ}

/-- The shear `(x, τ) ↦ (x, τ + φ x)` of `α × ℝ` along a continuous function `φ : α → ℝ`, as a
homeomorphism. Its inverse is `(x, t) ↦ (x, t - φ x)`. -/
def shear (hφ : Continuous φ) : (α × ℝ) ≃ₜ (α × ℝ) where
  toFun q := (q.1, q.2 + φ q.1)
  invFun q := (q.1, q.2 - φ q.1)
  left_inv q := by simp
  right_inv q := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem shear_apply (hφ : Continuous φ) (q : α × ℝ) : shear hφ q = (q.1, q.2 + φ q.1) :=
  rfl

end Homeomorph

namespace MeasureTheory

section Fubini

variable {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SFinite μ] [SFinite ν] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : α × β → F}
  {s : Set (α × β)}

/-- **Fubini's theorem** on a measurable subset `s` of a product: the integral over `s` is the
iterated integral over the slices of `s`. -/
theorem setIntegral_prod_eq_integral_setIntegral (hs : MeasurableSet s)
    (hf : IntegrableOn f s (μ.prod ν)) :
    ∫ z in s, f z ∂μ.prod ν = ∫ x, ∫ y in Prod.mk x ⁻¹' s, f (x, y) ∂ν ∂μ := by
  rw [← integral_indicator hs, integral_prod _ ((integrable_indicator_iff hs).2 hf)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [← integral_indicator (measurable_prodMk_left hs)]
  rfl

omit [SFinite μ] in
/-- The iterated integral over the slices of a measurable subset `s` of a product is integrable. -/
theorem integrable_setIntegral_prod (hs : MeasurableSet s) (hf : IntegrableOn f s (μ.prod ν)) :
    Integrable (fun x ↦ ∫ y in Prod.mk x ⁻¹' s, f (x, y) ∂ν) μ := by
  refine ((integrable_indicator_iff hs).2 hf).integral_prod_left.congr
    (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [← integral_indicator (measurable_prodMk_left hs)]
  rfl

end Fubini

section Shear

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ] {φ : α → ℝ}

/-- The shear `(x, τ) ↦ (x, τ + φ x)` along a measurable function `φ` preserves the product
measure `μ.prod volume`. -/
theorem measurePreserving_shear (hφ : Measurable φ) :
    MeasurePreserving (fun q : α × ℝ ↦ (q.1, q.2 + φ q.1)) (μ.prod volume) (μ.prod volume) :=
  (MeasurePreserving.id μ).skew_product (g := fun x τ ↦ τ + φ x)
    (measurable_snd.add (hφ.comp measurable_fst))
    (ae_of_all _ fun x ↦ map_add_right_eq_self volume (φ x))

end Shear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

section DivergenceFree

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

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

end DivergenceFree

end MeasureTheory
