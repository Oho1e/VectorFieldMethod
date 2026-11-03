/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini's theorem on a measurable subset of a product

For a measurable set `s ⊆ α × β` and a function `f` integrable on `s`, the integral of `f` over `s`
is the iterated integral of `f` over the slices `Prod.mk x ⁻¹' s` of `s`. This generalizes
`MeasureTheory.setIntegral_prod`, which is the case of a rectangle `s ×ˢ t`.

## Main statements

* `MeasureTheory.setIntegral_prod_eq_integral_setIntegral`: Fubini's theorem on a measurable subset
  of a product.
* `MeasureTheory.IntegrableOn.setIntegral_prod_left`: the inner integral is integrable.
-/

@[expose] public noncomputable section

open Set Filter

namespace MeasureTheory

variable {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [SFinite ν] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : α × β → F} {s : Set (α × β)}

/-- **Fubini's theorem** on a measurable subset `s` of a product: the integral over `s` is the
iterated integral over the slices of `s`. -/
theorem setIntegral_prod_eq_integral_setIntegral [SFinite μ] (hs : MeasurableSet s)
    (hf : IntegrableOn f s (μ.prod ν)) :
    ∫ z in s, f z ∂μ.prod ν = ∫ x, ∫ y in Prod.mk x ⁻¹' s, f (x, y) ∂ν ∂μ := by
  rw [← integral_indicator hs, integral_prod _ ((integrable_indicator_iff hs).2 hf)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [← integral_indicator (measurable_prodMk_left hs)]
  rfl

/-- The inner integral in `MeasureTheory.setIntegral_prod_eq_integral_setIntegral` is an
integrable function. -/
theorem IntegrableOn.setIntegral_prod_left (hf : IntegrableOn f s (μ.prod ν))
    (hs : MeasurableSet s) : Integrable (fun x ↦ ∫ y in Prod.mk x ⁻¹' s, f (x, y) ∂ν) μ := by
  refine ((integrable_indicator_iff hs).2 hf).integral_prod_left.congr
    (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [← integral_indicator (measurable_prodMk_left hs)]
  rfl

end MeasureTheory
