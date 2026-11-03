/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.ForMathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import VectorFieldMethod.ForMathlib.Analysis.Calculus.SpatialDivergence
public import VectorFieldMethod.ForMathlib.MeasureTheory.Integral.Prod
public import VectorFieldMethod.ForMathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.Gradient.Basic

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

* `MeasureTheory.integral_divergence_hypograph`: the divergence theorem on the hypograph of a `C¹`
  function, for a compactly supported `C¹` vector field.
* `MeasureTheory.integral_setIntegral_Iic_divergence`: the same statement as an iterated integral.
* `MeasureTheory.integral_intervalIntegral_divergence`: the divergence theorem between the graphs
  of two `C¹` functions `φ₁, φ₂`, in any order, with an oriented inner integral
  `∫ t in φ₁ x..φ₂ x`.
* `MeasureTheory.integral_divergence_region_between_cc`,
  `MeasureTheory.integral_divergence_regionBetween`: if `φ₁ ≤ φ₂`, the same statement as a set
  integral over the closed, respectively open, region between the graphs.
* `MeasureTheory.integral_divergence_hypograph_gradient`: inner product space version, with the
  flux written using `∇ φ`.
* `MeasureTheory.integral_divergence_hypograph_swap`: version on `ℝ × E`, time first.
* `Homeomorph.shear`, `MeasureTheory.measurePreserving_shear`: the shear `(x, τ) ↦ (x, τ + φ x)`
  is a homeomorphism if `φ` is continuous, and preserves `μ.prod volume` if `φ` is measurable.

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

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {φ : E → ℝ} {X₀ : E × ℝ → ℝ} {X : E × ℝ → E}

/-- **Divergence theorem on the region below a graph.** Let `φ : E → ℝ` be `C¹`, and let
`X₀ : E × ℝ → ℝ` and `X : E × ℝ → E` be compactly supported `C¹` functions, the time and space
components of a vector field on spacetime `E × ℝ`. Then the integral of its divergence
`∂ₜ X₀ + div_x X` over the hypograph `{(x, t) | t ≤ φ x}` equals the flux
`∫ x, X₀ (x, φ x) - Dφ(x) (X (x, φ x)) ∂μ` through the graph of `φ`. -/
theorem integral_divergence_hypograph (hφ : ContDiff ℝ 1 φ) (hX₀ : ContDiff ℝ 1 X₀)
    (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ p in {p : E × ℝ | p.2 ≤ φ p.1},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      ∫ x, (X₀ (x, φ x) - fderiv ℝ φ x (X (x, φ x))) ∂μ := by
  set S := Homeomorph.shear hφ.continuous with hS
  -- the time derivatives of the components, the sheared spatial component, and the time part of
  -- the pulled back integrand
  set T₀ : E × ℝ → ℝ := fun p ↦ deriv (fun t ↦ X₀ (p.1, t)) p.2 with hT₀
  set T : E × ℝ → E := fun p ↦ deriv (fun t ↦ X (p.1, t)) p.2 with hT
  set Y : E × ℝ → E := fun q ↦ X (q.1, q.2 + φ q.1) with hY
  set G : E × ℝ → ℝ := fun q ↦ T₀ (S q) - fderiv ℝ φ q.1 (T (S q)) with hG
  have hYd : ContDiff ℝ 1 Y :=
    hX.comp (contDiff_fst.prodMk (contDiff_snd.add (hφ.comp contDiff_fst)))
  have hYc : HasCompactSupport Y := hXc.comp_homeomorph S
  have hGc : Continuous G :=
    (hX₀.continuous_deriv_comp_prodMk_right.comp S.continuous).sub
      (((hφ.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply
        (hX.continuous_deriv_comp_prodMk_right.comp S.continuous))
  have hGs : HasCompactSupport G := by
    refine (hX₀c.deriv_comp_prodMk_right.comp_homeomorph S).sub
      ((hXc.deriv_comp_prodMk_right.comp_homeomorph S).mono fun q hq ↦ ?_)
    contrapose hq
    simp only [mem_support, not_not, comp_apply] at hq ⊢
    have hq' : T (S q) = 0 := hq
    rw [hq', map_zero]
  have hGi : Integrable G (μ.prod volume) := hGc.integrable_of_hasCompactSupport hGs
  have hYi : Integrable (spatialDivergence Y) (μ.prod volume) :=
    hYd.continuous_spatialDivergence.integrable_of_hasCompactSupport hYc.spatialDivergence
  -- change of variables along the shear, which maps the lower half-space onto the hypograph
  have hpre : (fun q : E × ℝ ↦ (q.1, q.2 + φ q.1)) ⁻¹' {p : E × ℝ | p.2 ≤ φ p.1} =
      univ ×ˢ Iic 0 := by
    ext q
    simp
  rw [← (measurePreserving_shear hφ.continuous.measurable).setIntegral_preimage_emb
    S.measurableEmbedding, hpre]
  -- the pulled back integrand splits into a time part and a space part
  have hpt : ∀ q : E × ℝ, T₀ (S q) + spatialDivergence X (S q) = G q + spatialDivergence Y q := by
    rintro ⟨x, τ⟩
    have h := spatialDivergence_shear (hφ.differentiable one_ne_zero x)
      (hX.differentiable one_ne_zero (x, τ + φ x))
    simp only [hG, hY, hT₀, hT, hS, Homeomorph.shear_apply] at h ⊢
    rw [h]
    ring
  -- the time part: the fundamental theorem of calculus in `τ`, for each `x`
  have h₂ : ∫ q in univ ×ˢ Iic (0 : ℝ), G q ∂μ.prod volume =
      ∫ x, (X₀ (x, φ x) - fderiv ℝ φ x (X (x, φ x))) ∂μ := by
    rw [setIntegral_prod _ hGi.integrableOn, Measure.restrict_univ]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    set g : ℝ → ℝ := fun τ ↦ X₀ (x, τ + φ x) - fderiv ℝ φ x (X (x, τ + φ x)) with hg
    have hxt : ContDiff ℝ 1 fun τ : ℝ ↦ (x, τ + φ x) :=
      contDiff_const.prodMk (contDiff_id.add contDiff_const)
    have hgd : ContDiff ℝ 1 g :=
      (hX₀.comp hxt).sub ((fderiv ℝ φ x).contDiff.comp (hX.comp hxt))
    have hgc : HasCompactSupport g := by
      have h : HasCompactSupport fun p : E × ℝ ↦ X₀ p - fderiv ℝ φ x (X p) :=
        hX₀c.sub (hXc.comp_left (g := fderiv ℝ φ x) (map_zero _))
      exact (h.comp_homeomorph S).comp_prodMkRight x
    have hg' : ∀ τ, deriv g τ = G (x, τ) := by
      intro τ
      have h₀ : HasDerivAt (fun τ ↦ X₀ (x, τ + φ x)) (T₀ (x, τ + φ x)) τ :=
        ((hX₀.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero
          (τ + φ x)).hasDerivAt.comp_add_const τ (φ x)
      have h₁ : HasDerivAt (fun τ ↦ X (x, τ + φ x)) (T (x, τ + φ x)) τ :=
        ((hX.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero
          (τ + φ x)).hasDerivAt.comp_add_const τ (φ x)
      exact (h₀.sub ((fderiv ℝ φ x).hasFDerivAt.comp_hasDerivAt τ h₁)).deriv
    simp_rw [← hg']
    rw [hgc.integral_Iic_deriv_eq hgd 0]
    simp [hg]
  -- the space part: for each `τ`, the divergence of the compactly supported field `Y (·, τ)`
  -- integrates to zero
  have h₃ : ∫ q in univ ×ˢ Iic (0 : ℝ), spatialDivergence Y q ∂μ.prod volume = 0 := by
    have hYi' : Integrable (spatialDivergence Y) (μ.prod (volume.restrict (Iic 0))) := by
      have h := hYi.integrableOn (s := univ ×ˢ Iic (0 : ℝ))
      rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
    rw [← Measure.prod_restrict, Measure.restrict_univ, integral_prod_symm _ hYi']
    refine integral_eq_zero_of_ae (Eventually.of_forall fun τ ↦ ?_)
    exact integral_trace_fderiv_eq_zero (μ := μ) (V := fun y ↦ Y (y, τ))
      (hYd.comp (contDiff_id.prodMk contDiff_const)) (hYc.comp_prodMkLeft τ)
  calc _ = ∫ q in univ ×ˢ Iic (0 : ℝ), (G q + spatialDivergence Y q) ∂μ.prod volume :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = _ := by rw [integral_add hGi.integrableOn hYi.integrableOn, h₂, h₃, add_zero]

/-- The divergence `∂ₜ X₀ + div_x X` of a compactly supported `C¹` vector field on spacetime is
integrable. -/
theorem integrable_deriv_add_spatialDivergence (hX₀ : ContDiff ℝ 1 X₀)
    (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    Integrable (fun p : E × ℝ ↦ deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p)
      (μ.prod volume) :=
  (hX₀.continuous_deriv_comp_prodMk_right.add hX.continuous_spatialDivergence)
    |>.integrable_of_hasCompactSupport
      (hX₀c.deriv_comp_prodMk_right.add hXc.spatialDivergence)

/-- **Divergence theorem on the region below a graph**, as an iterated integral: the integral
over `t ≤ φ x` is computed first. -/
theorem integral_setIntegral_Iic_divergence (hφ : ContDiff ℝ 1 φ) (hX₀ : ContDiff ℝ 1 X₀)
    (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ x, (∫ t in Iic (φ x), (deriv (fun s ↦ X₀ (x, s)) t + spatialDivergence X (x, t))) ∂μ =
      ∫ x, (X₀ (x, φ x) - fderiv ℝ φ x (X (x, φ x))) ∂μ := by
  have hs : MeasurableSet {p : E × ℝ | p.2 ≤ φ p.1} :=
    measurableSet_le measurable_snd (hφ.continuous.measurable.comp measurable_fst)
  rw [← integral_divergence_hypograph hφ hX₀ hX₀c hX hXc,
    setIntegral_prod_eq_integral_setIntegral hs
      (integrable_deriv_add_spatialDivergence hX₀ hX₀c hX hXc).integrableOn]
  rfl

/-- The inner integral in `MeasureTheory.integral_setIntegral_Iic_divergence` is an integrable
function of `x`. -/
theorem integrable_setIntegral_Iic_divergence (hφ : Continuous φ) (hX₀ : ContDiff ℝ 1 X₀)
    (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    Integrable (fun x ↦
      ∫ t in Iic (φ x), (deriv (fun s ↦ X₀ (x, s)) t + spatialDivergence X (x, t))) μ :=
  (integrable_deriv_add_spatialDivergence hX₀ hX₀c hX hXc).integrableOn.setIntegral_prod_left
    (measurableSet_le measurable_snd (hφ.measurable.comp measurable_fst))

variable {φ₁ φ₂ : E → ℝ}

/-- **Divergence theorem between two graphs.** For `C¹` functions `φ₁ φ₂ : E → ℝ` (in any order)
and a compactly supported `C¹` vector field `(X₀, X)` on spacetime, the integral over `x` of the
oriented integral `∫ t in φ₁ x..φ₂ x` of the divergence `∂ₜ X₀ + div_x X` is the difference of the
fluxes through the graphs of `φ₂` and `φ₁`. -/
theorem integral_intervalIntegral_divergence (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂)
    (hX₀ : ContDiff ℝ 1 X₀) (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) :
    ∫ x, (∫ t in φ₁ x..φ₂ x, (deriv (fun s ↦ X₀ (x, s)) t + spatialDivergence X (x, t))) ∂μ =
      (∫ x, (X₀ (x, φ₂ x) - fderiv ℝ φ₂ x (X (x, φ₂ x))) ∂μ) -
        ∫ x, (X₀ (x, φ₁ x) - fderiv ℝ φ₁ x (X (x, φ₁ x))) ∂μ := by
  have hint : ∀ (x : E) (a : ℝ), IntegrableOn
      (fun t ↦ deriv (fun s ↦ X₀ (x, s)) t + spatialDivergence X (x, t)) (Iic a) := fun x a ↦
    ((hX₀.continuous_deriv_comp_prodMk_right.add hX.continuous_spatialDivergence).comp
        (Continuous.prodMk_right x)).integrable_of_hasCompactSupport
      ((hX₀c.deriv_comp_prodMk_right.add hXc.spatialDivergence).comp_prodMkRight x)
      |>.integrableOn
  have h : ∀ x : E, ∫ t in φ₁ x..φ₂ x, (deriv (fun s ↦ X₀ (x, s)) t + spatialDivergence X (x, t)) =
      (∫ t in Iic (φ₂ x), (deriv (fun s ↦ X₀ (x, s)) t + spatialDivergence X (x, t))) -
        ∫ t in Iic (φ₁ x), (deriv (fun s ↦ X₀ (x, s)) t + spatialDivergence X (x, t)) :=
    fun x ↦ (intervalIntegral.integral_Iic_sub_Iic (hint x _) (hint x _)).symm
  simp_rw [h]
  rw [integral_sub (integrable_setIntegral_Iic_divergence hφ₂.continuous hX₀ hX₀c hX hXc)
      (integrable_setIntegral_Iic_divergence hφ₁.continuous hX₀ hX₀c hX hXc),
    integral_setIntegral_Iic_divergence hφ₂ hX₀ hX₀c hX hXc,
    integral_setIntegral_Iic_divergence hφ₁ hX₀ hX₀c hX hXc]

/-- **Divergence theorem on the closed region between two graphs.** If `φ₁ ≤ φ₂` are `C¹`, the
integral of the divergence `∂ₜ X₀ + div_x X` of a compactly supported `C¹` vector field over
`{(x, t) | φ₁ x ≤ t ≤ φ₂ x}` is the difference of the fluxes through the graphs of `φ₂` and
`φ₁`. -/
theorem integral_divergence_region_between_cc (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂)
    (hφ : φ₁ ≤ φ₂) (hX₀ : ContDiff ℝ 1 X₀) (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) :
    ∫ p in {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      (∫ x, (X₀ (x, φ₂ x) - fderiv ℝ φ₂ x (X (x, φ₂ x))) ∂μ) -
        ∫ x, (X₀ (x, φ₁ x) - fderiv ℝ φ₁ x (X (x, φ₁ x))) ∂μ := by
  have hs : MeasurableSet {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)} :=
    (measurableSet_le (hφ₁.continuous.measurable.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hφ₂.continuous.measurable.comp measurable_fst))
  rw [setIntegral_prod_eq_integral_setIntegral hs
      (integrable_deriv_add_spatialDivergence hX₀ hX₀c hX hXc).integrableOn,
    ← integral_intervalIntegral_divergence hφ₁ hφ₂ hX₀ hX₀c hX hXc]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [intervalIntegral.integral_of_le (hφ x), ← integral_Icc_eq_integral_Ioc]
  rfl

/-- **Divergence theorem on the open region between two graphs**, stated with `regionBetween`.
If `φ₁ ≤ φ₂` are `C¹`, the integral of the divergence `∂ₜ X₀ + div_x X` of a compactly supported
`C¹` vector field over `regionBetween φ₁ φ₂ univ = {(x, t) | φ₁ x < t < φ₂ x}` is the difference of
the fluxes through the graphs of `φ₂` and `φ₁`. -/
theorem integral_divergence_regionBetween (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂)
    (hφ : φ₁ ≤ φ₂) (hX₀ : ContDiff ℝ 1 X₀) (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) :
    ∫ p in regionBetween φ₁ φ₂ univ,
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      (∫ x, (X₀ (x, φ₂ x) - fderiv ℝ φ₂ x (X (x, φ₂ x))) ∂μ) -
        ∫ x, (X₀ (x, φ₁ x) - fderiv ℝ φ₁ x (X (x, φ₁ x))) ∂μ := by
  rw [setIntegral_prod_eq_integral_setIntegral
      (measurableSet_regionBetween hφ₁.continuous.measurable hφ₂.continuous.measurable
        MeasurableSet.univ)
      (integrable_deriv_add_spatialDivergence hX₀ hX₀c hX hXc).integrableOn,
    ← integral_intervalIntegral_divergence hφ₁ hφ₂ hX₀ hX₀c hX hXc]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  have hx : Prod.mk x ⁻¹' regionBetween φ₁ φ₂ univ = Ioo (φ₁ x) (φ₂ x) := by
    ext t
    simp [regionBetween]
  dsimp only
  rw [hx, intervalIntegral.integral_of_le (hφ x), integral_Ioc_eq_integral_Ioo]

/-- **Divergence theorem on the region below a graph, time first.** The version of
`MeasureTheory.integral_divergence_hypograph` on spacetime `ℝ × E`, with time as the first
coordinate and the measure `volume.prod μ`. The spatial divergence of `X : ℝ × E → E` at
`(t, x)` is the trace of the derivative at `x` of `y ↦ X (t, y)`. -/
theorem integral_divergence_hypograph_swap {X₀ : ℝ × E → ℝ} {X : ℝ × E → E}
    (hφ : ContDiff ℝ 1 φ) (hX₀ : ContDiff ℝ 1 X₀) (hX₀c : HasCompactSupport X₀)
    (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ p in {p : ℝ × E | p.1 ≤ φ p.2},
        (deriv (fun t ↦ X₀ (t, p.2)) p.1 +
          LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ X (p.1, y)) p.2 : E →ₗ[ℝ] E)) ∂volume.prod μ =
      ∫ x, (X₀ (φ x, x) - fderiv ℝ φ x (X (φ x, x))) ∂μ := by
  rw [← (Measure.measurePreserving_swap (μ := μ) (ν := volume)).setIntegral_preimage_emb
    MeasurableEquiv.prodComm.measurableEmbedding]
  exact integral_divergence_hypograph (X₀ := X₀ ∘ Prod.swap) (X := X ∘ Prod.swap) hφ
    (hX₀.comp (contDiff_snd.prodMk contDiff_fst)) (hX₀c.comp_homeomorph (Homeomorph.prodComm E ℝ))
    (hX.comp (contDiff_snd.prodMk contDiff_fst)) (hXc.comp_homeomorph (Homeomorph.prodComm E ℝ))

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {φ : E → ℝ} {X₀ : E × ℝ → ℝ} {X : E × ℝ → E}

open scoped RealInnerProductSpace Gradient

/-- **Divergence theorem on the region below a graph**, inner product space version: the flux
through the graph of `φ` is `∫ x, X₀ (x, φ x) - ⟪∇ φ x, X (x, φ x)⟫ ∂μ`. -/
theorem integral_divergence_hypograph_gradient (hφ : ContDiff ℝ 1 φ) (hX₀ : ContDiff ℝ 1 X₀)
    (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ p in {p : E × ℝ | p.2 ≤ φ p.1},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      ∫ x, (X₀ (x, φ x) - ⟪∇ φ x, X (x, φ x)⟫) ∂μ := by
  simp_rw [inner_gradient_left]
  exact integral_divergence_hypograph hφ hX₀ hX₀c hX hXc

end InnerProductSpace

end MeasureTheory
