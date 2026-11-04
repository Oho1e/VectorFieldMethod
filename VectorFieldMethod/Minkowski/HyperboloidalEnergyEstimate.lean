/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.HyperboloidalEnergyIdentity
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The hyperboloidal energy estimate for the Klein–Gordon field

This file works towards the energy estimate of LeFloch–Ma's hyperboloidal foliation method,
`E_m(s, u)^{1/2} ≤ E_m(s₀, u)^{1/2} + ∫_{s₀}^{s} ‖KG_m u‖_{L²_f(H_{s'})} ds'`, on top of the energy
identity `hyperboloidalEnergy_sub_hyperboloidalEnergy` of `HyperboloidalEnergyIdentity.lean`.

Write `φ_s(x) = √(s ^ 2 + ‖x‖ ^ 2)`, so that the hyperboloid `H_s` is the graph `t = φ_s(x)`, and
`D = regionBetweenHyperboloids s₁ s₂` for the closed region between `H_{s₁}` and `H_{s₂}`.

## Main statements

* `map_withDensity_eq_restrict_regionBetweenHyperboloids`: for `0 < s₁ ≤ s₂`, the map
  `(s, x) ↦ (φ_s(x), x)` sends the measure `(s / φ_s(x)) ds dx` on `[s₁, s₂] × ℝ³` to Lebesgue
  measure on `D`. This is the change of variables `t = φ_s(x)`, `dt = (s / φ_s(x)) ds` at fixed `x`.
* `setIntegral_regionBetweenHyperboloids_eq` (integrable functions) and
  `setLIntegral_regionBetweenHyperboloids_eq` (nonnegative measurable functions): the foliation
  formula `∫_D g dt dx = ∫_{s₁}^{s₂} ∫_{ℝ³} g(φ_s(x), x) (s / φ_s(x)) dx ds`.

## Implementation notes

The foliation formula is not deduced from the multidimensional change of variables formula. At
fixed `x`, the map `s ↦ φ_s(x)` is a `C¹` increasing bijection from `[s₁, s₂]` onto the segment
`[φ_{s₁}(x), φ_{s₂}(x)]` of `D` above `x`, with derivative `s / φ_s(x)`, and the one-dimensional
change of variables (`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`) is combined with
Tonelli's theorem. This proves the identity of measures above on measurable sets; the integral
formulas follow from it.
-/

@[expose] public noncomputable section

open Set Filter Function Topology MeasureTheory
open scoped RealInnerProductSpace NNReal ENNReal

namespace VectorFieldMethod.Minkowski

/-! ### The foliation by hyperboloids -/

/-- The derivative of `σ ↦ √(σ ^ 2 + c)` at a point where `s ^ 2 + c > 0` is `s / √(s ^ 2 + c)`. -/
theorem hasDerivAt_sqrt_sq_add {s c : ℝ} (h : 0 < s ^ 2 + c) :
    HasDerivAt (fun σ : ℝ ↦ √(σ ^ 2 + c)) (s / √(s ^ 2 + c)) s := by
  have h1 : HasDerivAt (fun σ : ℝ ↦ σ ^ 2 + c) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const c
  convert h1.sqrt h.ne' using 1
  field_simp

/-- For `c ≥ 0`, the function `σ ↦ √(σ ^ 2 + c)` is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_sqrt_sq_add {c : ℝ} (hc : 0 ≤ c) :
    StrictMonoOn (fun σ : ℝ ↦ √(σ ^ 2 + c)) (Ici 0) := fun σ₁ h₁ σ₂ _ h ↦
  Real.sqrt_lt_sqrt (by positivity) (by nlinarith [mem_Ici.1 h₁])

/-- For `0 ≤ s₁ ≤ s₂` and `c ≥ 0`, the function `σ ↦ √(σ ^ 2 + c)` maps `[s₁, s₂]` onto
`[√(s₁ ^ 2 + c), √(s₂ ^ 2 + c)]`. -/
theorem image_sqrt_sq_add_Icc {s₁ s₂ c : ℝ} (hs₁ : 0 ≤ s₁) (hs₁₂ : s₁ ≤ s₂) (hc : 0 ≤ c) :
    (fun σ : ℝ ↦ √(σ ^ 2 + c)) '' Icc s₁ s₂ = Icc √(s₁ ^ 2 + c) √(s₂ ^ 2 + c) :=
  (by fun_prop : Continuous fun σ : ℝ ↦ √(σ ^ 2 + c)).continuousOn.image_Icc_of_monotoneOn
    hs₁₂ ((strictMonoOn_sqrt_sq_add hc).monotoneOn.mono fun _ h ↦ mem_Ici.2 (hs₁.trans h.1))

/-- **The foliation of the region between two hyperboloids, as an identity of measures.** Let
`0 < s₁ ≤ s₂`. The map `(s, x) ↦ (√(s ^ 2 + ‖x‖ ^ 2), x)` sends the measure
`(s / √(s ^ 2 + ‖x‖ ^ 2)) ds dx` on `[s₁, s₂] × ℝ³` to Lebesgue measure on the region `D` between
the hyperboloids `H_{s₁}` and `H_{s₂}`.

At fixed `x`, `s ↦ √(s ^ 2 + ‖x‖ ^ 2)` is an increasing bijection from `[s₁, s₂]` onto the segment
of `D` above `x`, with derivative `s / √(s ^ 2 + ‖x‖ ^ 2)`; the identity is the one-dimensional
change of variables combined with Tonelli's theorem. -/
theorem map_withDensity_eq_restrict_regionBetweenHyperboloids {s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ ≤ s₂) :
    Measure.map (fun q : ℝ × EuclideanSpace ℝ (Fin 3) ↦ ((√(q.1 ^ 2 + ‖q.2‖ ^ 2), q.2) : Spacetime))
        (((volume.restrict (Icc s₁ s₂)).prod volume).withDensity
          fun q ↦ ENNReal.ofReal (q.1 / √(q.1 ^ 2 + ‖q.2‖ ^ 2))) =
      volume.restrict (regionBetweenHyperboloids s₁ s₂) := by
  set Ψ : ℝ × EuclideanSpace ℝ (Fin 3) → Spacetime := fun q ↦ (√(q.1 ^ 2 + ‖q.2‖ ^ 2), q.2)
    with hΨdef
  have hΨ : Measurable Ψ := by fun_prop
  set ρ : ℝ × EuclideanSpace ℝ (Fin 3) → ℝ≥0∞ :=
    fun q ↦ ENNReal.ofReal (q.1 / √(q.1 ^ 2 + ‖q.2‖ ^ 2)) with hρdef
  have hρ : Measurable ρ := by fun_prop
  ext N hN
  have hD := (isClosed_regionBetweenHyperboloids s₁ s₂).measurableSet
  -- both sides as iterated integrals, the inner one in `s`, respectively in `t`
  rw [Measure.map_apply hΨ hN, withDensity_apply _ (hΨ hN), Measure.restrict_apply hN,
    ← lintegral_indicator (hΨ hN), lintegral_prod_symm _ (hρ.indicator (hΨ hN)).aemeasurable,
    Measure.volume_eq_prod, Measure.prod_apply_symm (hN.inter hD)]
  refine lintegral_congr fun x ↦ ?_
  -- at fixed `x`: the change of variables `t = √(s ^ 2 + ‖x‖ ^ 2)`
  have hc : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
  have hmeasN : MeasurableSet ((fun t : ℝ ↦ ((t, x) : Spacetime)) ⁻¹' N) :=
    measurable_prodMk_right hN
  have hderiv (s : ℝ) (hs : s ∈ Icc s₁ s₂) :
      HasDerivWithinAt (fun σ : ℝ ↦ √(σ ^ 2 + ‖x‖ ^ 2)) (s / √(s ^ 2 + ‖x‖ ^ 2)) (Icc s₁ s₂) s :=
    (hasDerivAt_sqrt_sq_add (by nlinarith [hs₁.trans_le hs.1])).hasDerivWithinAt
  have hinj : InjOn (fun σ : ℝ ↦ √(σ ^ 2 + ‖x‖ ^ 2)) (Icc s₁ s₂) :=
    ((strictMonoOn_sqrt_sq_add hc).mono fun _ h ↦ mem_Ici.2 (hs₁.le.trans h.1)).injOn
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc hderiv hinj
    (((fun t : ℝ ↦ ((t, x) : Spacetime)) ⁻¹' N).indicator 1)
  rw [image_sqrt_sq_add_Icc hs₁.le hs₁₂ hc, lintegral_indicator_one hmeasN,
    Measure.restrict_apply hmeasN] at key
  have hslice : (fun t : ℝ ↦ ((t, x) : Spacetime)) ⁻¹' (N ∩ regionBetweenHyperboloids s₁ s₂) =
      (fun t : ℝ ↦ ((t, x) : Spacetime)) ⁻¹' N ∩ Icc √(s₁ ^ 2 + ‖x‖ ^ 2) √(s₂ ^ 2 + ‖x‖ ^ 2) := by
    ext t
    simp only [mem_preimage, mem_inter_iff, mem_regionBetweenHyperboloids, mem_Icc]
  rw [hslice, key]
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs ↦ ?_
  have hφ : 0 < √(s ^ 2 + ‖x‖ ^ 2) := Real.sqrt_pos.2 (by nlinarith [hs₁.trans_le hs.1])
  by_cases hmem : ((√(s ^ 2 + ‖x‖ ^ 2), x) : Spacetime) ∈ N
  · have h1 : (s, x) ∈ Ψ ⁻¹' N := hmem
    have h2 : √(s ^ 2 + ‖x‖ ^ 2) ∈ (fun t : ℝ ↦ ((t, x) : Spacetime)) ⁻¹' N := hmem
    rw [indicator_of_mem h1, indicator_of_mem h2, Pi.one_apply, mul_one,
      abs_of_pos (div_pos (hs₁.trans_le hs.1) hφ)]
  · have h1 : (s, x) ∉ Ψ ⁻¹' N := hmem
    have h2 : √(s ^ 2 + ‖x‖ ^ 2) ∉ (fun t : ℝ ↦ ((t, x) : Spacetime)) ⁻¹' N := hmem
    rw [indicator_of_notMem h1, indicator_of_notMem h2, mul_zero]

/-- **The foliation formula for nonnegative functions.** For `0 < s₁ ≤ s₂` and a measurable
`g : Spacetime → ℝ≥0∞`,
`∫_D g dt dx = ∫_{s₁}^{s₂} ∫_{ℝ³} (s / √(s ^ 2 + ‖x‖ ^ 2)) g(√(s ^ 2 + ‖x‖ ^ 2), x) dx ds`,
where `D` is the region between the hyperboloids `H_{s₁}` and `H_{s₂}`. -/
theorem setLIntegral_regionBetweenHyperboloids_eq {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂)
    {g : Spacetime → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p in regionBetweenHyperboloids s₁ s₂, g p =
      ∫⁻ s in Icc s₁ s₂, ∫⁻ x : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (s / √(s ^ 2 + ‖x‖ ^ 2)) * g (√(s ^ 2 + ‖x‖ ^ 2), x) := by
  have hΨ : Measurable fun q : ℝ × EuclideanSpace ℝ (Fin 3) ↦
      ((√(q.1 ^ 2 + ‖q.2‖ ^ 2), q.2) : Spacetime) := by fun_prop
  have hρ : Measurable fun q : ℝ × EuclideanSpace ℝ (Fin 3) ↦
      ENNReal.ofReal (q.1 / √(q.1 ^ 2 + ‖q.2‖ ^ 2)) := by fun_prop
  rw [← map_withDensity_eq_restrict_regionBetweenHyperboloids hs₁ hs₁₂, lintegral_map hg hΨ,
    lintegral_withDensity_eq_lintegral_mul _ hρ
      (g := fun q ↦ g (√(q.1 ^ 2 + ‖q.2‖ ^ 2), q.2)) (hg.comp hΨ)]
  exact lintegral_prod _ (hρ.mul (hg.comp hΨ)).aemeasurable

/-- **The foliation formula.** For `0 < s₁ ≤ s₂` and `g : Spacetime → ℝ` integrable on the region
`D` between the hyperboloids `H_{s₁}` and `H_{s₂}`,
`∫_D g dt dx = ∫_{s₁}^{s₂} ∫_{ℝ³} (s / √(s ^ 2 + ‖x‖ ^ 2)) g(√(s ^ 2 + ‖x‖ ^ 2), x) dx ds`.

This is the change of variables `t = √(s ^ 2 + ‖x‖ ^ 2)`, `dt = (s / t) ds` at fixed `x`, combined
with Fubini's theorem (`map_withDensity_eq_restrict_regionBetweenHyperboloids`). -/
theorem setIntegral_regionBetweenHyperboloids_eq {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂)
    {g : Spacetime → ℝ} (hg : IntegrableOn g (regionBetweenHyperboloids s₁ s₂)) :
    ∫ p in regionBetweenHyperboloids s₁ s₂, g p =
      ∫ s in Icc s₁ s₂, ∫ x : EuclideanSpace ℝ (Fin 3),
        s / √(s ^ 2 + ‖x‖ ^ 2) * g (√(s ^ 2 + ‖x‖ ^ 2), x) := by
  set Ψ : ℝ × EuclideanSpace ℝ (Fin 3) → Spacetime := fun q ↦ (√(q.1 ^ 2 + ‖q.2‖ ^ 2), q.2)
    with hΨdef
  have hΨ : Measurable Ψ := by fun_prop
  set ρ : ℝ × EuclideanSpace ℝ (Fin 3) → ℝ≥0 :=
    fun q ↦ Real.toNNReal (q.1 / √(q.1 ^ 2 + ‖q.2‖ ^ 2)) with hρdef
  have hρ : Measurable ρ := by fun_prop
  set ν := ((volume.restrict (Icc s₁ s₂)).prod (volume : Measure (EuclideanSpace ℝ (Fin 3))))
    with hνdef
  have hmap : Measure.map Ψ (ν.withDensity fun q ↦ (ρ q : ℝ≥0∞)) =
      volume.restrict (regionBetweenHyperboloids s₁ s₂) :=
    map_withDensity_eq_restrict_regionBetweenHyperboloids hs₁ hs₁₂
  have hg' : Integrable g (Measure.map Ψ (ν.withDensity fun q ↦ (ρ q : ℝ≥0∞))) := by
    rw [hmap]; exact hg
  have hint : Integrable (fun q ↦ ρ q • g (Ψ q)) ν :=
    (integrable_withDensity_iff_integrable_smul hρ).1
      ((integrable_map_measure hg'.aestronglyMeasurable hΨ.aemeasurable).1 hg')
  calc ∫ p in regionBetweenHyperboloids s₁ s₂, g p
      = ∫ p, g p ∂(Measure.map Ψ (ν.withDensity fun q ↦ (ρ q : ℝ≥0∞))) := by rw [hmap]
    _ = ∫ q, g (Ψ q) ∂(ν.withDensity fun q ↦ (ρ q : ℝ≥0∞)) :=
      integral_map hΨ.aemeasurable hg'.aestronglyMeasurable
    _ = ∫ q, ρ q • g (Ψ q) ∂ν := integral_withDensity_eq_integral_smul hρ _
    _ = ∫ s in Icc s₁ s₂, ∫ x : EuclideanSpace ℝ (Fin 3), ρ (s, x) • g (Ψ (s, x)) :=
      integral_prod _ hint
    _ = _ := by
      refine setIntegral_congr_fun measurableSet_Icc fun s hs ↦ integral_congr_ae
        (ae_of_all _ fun x ↦ ?_)
      have hφ : 0 < √(s ^ 2 + ‖x‖ ^ 2) := Real.sqrt_pos.2 (by nlinarith [hs₁.trans_le hs.1])
      simp only [hρdef, hΨdef, NNReal.smul_def, smul_eq_mul,
        Real.coe_toNNReal _ (div_pos (hs₁.trans_le hs.1) hφ).le]

/-! ### Sanity checks

The examples below use a smooth bump function `u : Spacetime → ℝ` centered at `(t, x) = (4, 0)`,
equal to `1` on the closed ball of radius `1 / 4` and vanishing outside the open ball of radius
`1 / 2`, for the max norm `max |t - 4| ‖x‖` of `Spacetime` (the function of the sanity checks of
`HyperboloidalEnergyIdentity.lean`, which is private there). -/

section SanityChecks

/-- A smooth bump function on `Spacetime` centered at `(t, x) = (4, 0)`, equal to `1` on the
closed ball of radius `1 / 4` and vanishing outside the open ball of radius `1 / 2`. -/
private def estimateBump : ContDiffBump ((4 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The foliation formula applies to the bump function between the hyperboloids `H_2` and `H_4`:
the bump function is continuous with compact support, hence integrable on the region between
them. -/
example : ∫ p in regionBetweenHyperboloids 2 4, (estimateBump : Spacetime → ℝ) p =
    ∫ s in Icc (2 : ℝ) 4, ∫ x : EuclideanSpace ℝ (Fin 3),
      s / √(s ^ 2 + ‖x‖ ^ 2) * (estimateBump : Spacetime → ℝ) (√(s ^ 2 + ‖x‖ ^ 2), x) :=
  setIntegral_regionBetweenHyperboloids_eq (by norm_num) (by norm_num)
    (estimateBump.continuous.integrable_of_hasCompactSupport
      estimateBump.hasCompactSupport).integrableOn

end SanityChecks

end VectorFieldMethod.Minkowski
