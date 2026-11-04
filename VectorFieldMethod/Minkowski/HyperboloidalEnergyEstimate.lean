/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Analysis.SqrtGronwall
public import VectorFieldMethod.Minkowski.HyperboloidalEnergyIdentity
public import VectorFieldMethod.Minkowski.KlainermanSobolev
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The hyperboloidal energy estimate for the Klein–Gordon field

This file proves the energy estimate of LeFloch–Ma's hyperboloidal foliation method: for a field
`u` of class `C²` near the part `D ∩ K` of the region `D` between the hyperboloids `H_{s₀}` and
`H_S` inside the cone `K = {‖x‖ ≤ t - 1}`, and with `D ∩ supp u ⊆ K`,
`E_m(s, u)^{1/2} ≤ E_m(s₀, u)^{1/2} + ∫_{s₀}^{s} ‖KG_m u‖_{L²_f(H_{s'})} ds'` for `s ∈ [s₀, S]`.
Here `E_m(s, u) = hyperboloidalEnergy m s u`, `KG_m u = □u - m² u = kleinGordon m u`, and
`‖f‖_{L²_f(H_s)} = (∫_{ℝ³} ‖f(φ_s(x), x)‖² dx)^{1/2}` is the `L²` norm on `H_s` for the flat
measure `dx` (`eLpNorm (restrictHyperboloid s f) 2 volume`). The estimate is deduced from the
energy identity `hyperboloidalEnergy_sub_hyperboloidalEnergy` of `HyperboloidalEnergyIdentity.lean`.

Write `φ_s(x) = √(s ^ 2 + ‖x‖ ^ 2)`, so that the hyperboloid `H_s` is the graph `t = φ_s(x)`, and
`D = regionBetweenHyperboloids s₁ s₂` for the closed region between `H_{s₁}` and `H_{s₂}`.

## Main statements

* `map_withDensity_eq_restrict_regionBetweenHyperboloids`: for `0 < s₁ ≤ s₂`, the map
  `(s, x) ↦ (φ_s(x), x)` sends the measure `(s / φ_s(x)) ds dx` on `[s₁, s₂] × ℝ³` to Lebesgue
  measure on `D`. This is the change of variables `t = φ_s(x)`, `dt = (s / φ_s(x)) ds` at fixed `x`.
* `setIntegral_regionBetweenHyperboloids_eq` (integrable functions) and
  `setLIntegral_regionBetweenHyperboloids_eq` (nonnegative measurable functions): the foliation
  formula `∫_D g dt dx = ∫_{s₁}^{s₂} ∫_{ℝ³} g(φ_s(x), x) (s / φ_s(x)) dx ds`.
* `hyperboloidalEnergy_sub_hyperboloidalEnergy_of_le`: if the hypotheses of the energy identity
  hold on the region between `H_{s₀}` and `H_S`, they hold between any two intermediate
  hyperboloids `H_{s₁}`, `H_{s₂}` (`regionBetweenHyperboloids_inter_cone_subset_of_le`,
  `regionBetweenHyperboloids_inter_tsupport_subset_of_le`), and the energy identity holds there.
* `sq_div_mul_norm_timeDeriv_sq_le_hyperboloidalEnergyDensity`: on `H_s`,
  `(s / t)² ‖∂_t u‖² ≤ e_m[u]`.
* `abs_integral_mul_inner_timeDeriv_le`: by Cauchy–Schwarz,
  `|∫_{ℝ³} (s / t) ⟪f, ∂_t u⟫(φ_s(x), x) dx| ≤ ‖f‖_{L²_f(H_s)} E_m(s, u)^{1/2}`.
* `continuousOn_integral_hyperboloid`, `continuousOn_hyperboloidalEnergy`: under the hypotheses of
  the energy identity on the region between `H_{s₀}` and `H_S`, `s ↦ E_m(s, u)` (and
  `s ↦ ‖KG_m u‖_{L²_f(H_s)}`) is continuous on `[s₀, S]`.
* `hyperboloidalEnergy_le_add_two_mul_integral`: under the same hypotheses, for `s ∈ [s₀, S]`,
  `E_m(s, u) ≤ E_m(s₀, u) + 2 ∫_{s₀}^{s} ‖KG_m u‖_{L²_f(H_{s'})} E_m(s', u)^{1/2} ds'`.
* `ofReal_sqrt_hyperboloidalEnergy_le`: **the energy estimate**, in `ℝ≥0∞`;
  `sqrt_hyperboloidalEnergy_le_add_integral` is the same estimate in `ℝ`, and
  `lintegral_eLpNorm_restrictHyperboloid_kleinGordon_lt_top` states that its right-hand side is
  finite.

## Implementation notes

The foliation formula is not deduced from the multidimensional change of variables formula. At
fixed `x`, the map `s ↦ φ_s(x)` is a `C¹` increasing bijection from `[s₁, s₂]` onto the segment
`[φ_{s₁}(x), φ_{s₂}(x)]` of `D` above `x`, with derivative `s / φ_s(x)`, and the one-dimensional
change of variables (`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`) is combined with
Tonelli's theorem. This proves the identity of measures above on measurable sets; the integral
formulas follow from it.

The energy estimate follows from the integral inequality by the square-root Grönwall inequality
`VectorFieldMethod.Analysis.sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral`.

## Notation and conventions

LeFloch–Ma (*The hyperboloidal foliation method*, arXiv:1411.4910) write `E_{m,c}(s, u)` for the
energy of a field of mass `c`, which is `hyperboloidalEnergy c s u` here, and their Klein–Gordon
operator is `-(□u - c² u)`; since only its norm enters, the estimate reads the same with their
operator.
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

/-! ### Subregions -/

/-- For `0 ≤ s₀ ≤ s₁ ≤ s₂ ≤ S`, the region between the hyperboloids `H_{s₁}` and `H_{s₂}` lies in
the region between `H_{s₀}` and `H_S`. -/
theorem regionBetweenHyperboloids_subset {s₀ s₁ s₂ S : ℝ} (hs₀ : 0 ≤ s₀) (h₀₁ : s₀ ≤ s₁)
    (h₁₂ : s₁ ≤ s₂) (h₂S : s₂ ≤ S) :
    regionBetweenHyperboloids s₁ s₂ ⊆ regionBetweenHyperboloids s₀ S := fun p hp ↦
  mem_regionBetweenHyperboloids.2
    ⟨(Real.sqrt_le_sqrt (by nlinarith)).trans (mem_regionBetweenHyperboloids.1 hp).1,
      (mem_regionBetweenHyperboloids.1 hp).2.trans (Real.sqrt_le_sqrt (by nlinarith))⟩

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {u : Spacetime → F}

/-- The hypothesis `D ∩ K ⊆ U` of the energy identity passes from the region `D` between `H_{s₀}`
and `H_S` to the region between `H_{s₁}` and `H_{s₂}`, for `0 ≤ s₀ ≤ s₁ ≤ s₂ ≤ S`. -/
theorem regionBetweenHyperboloids_inter_cone_subset_of_le {s₀ s₁ s₂ S : ℝ} (hs₀ : 0 ≤ s₀)
    (h₀₁ : s₀ ≤ s₁) (h₁₂ : s₁ ≤ s₂) (h₂S : s₂ ≤ S) {U : Set Spacetime}
    (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U) :
    regionBetweenHyperboloids s₁ s₂ ∩ cone ⊆ U :=
  (inter_subset_inter_left _ (regionBetweenHyperboloids_subset hs₀ h₀₁ h₁₂ h₂S)).trans hDU

omit [InnerProductSpace ℝ F] in
/-- The support hypothesis `D ∩ supp u ⊆ K` of the energy identity passes from the region `D`
between `H_{s₀}` and `H_S` to the region between `H_{s₁}` and `H_{s₂}`, for
`0 ≤ s₀ ≤ s₁ ≤ s₂ ≤ S`. -/
theorem regionBetweenHyperboloids_inter_tsupport_subset_of_le {s₀ s₁ s₂ S : ℝ} (hs₀ : 0 ≤ s₀)
    (h₀₁ : s₀ ≤ s₁) (h₁₂ : s₁ ≤ s₂) (h₂S : s₂ ≤ S)
    (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone) :
    regionBetweenHyperboloids s₁ s₂ ∩ tsupport u ⊆ cone :=
  (inter_subset_inter_left _ (regionBetweenHyperboloids_subset hs₀ h₀₁ h₁₂ h₂S)).trans hsupp

/-- **The energy identity between two intermediate hyperboloids.** Let `0 < s₀`, let `D` be the
region between `H_{s₀}` and `H_S`, `K` the cone, `U` an open set containing `D ∩ K`, and `u` of
class `C²` on `U` with `D ∩ supp u ⊆ K`. Then for `s₀ ≤ s₁ < s₂ ≤ S`,
`E_m(s₂, u) - E_m(s₁, u) = -2 ∫_{D(s₁, s₂)} ⟪KG_m u, ∂_t u⟫`, where `D(s₁, s₂)` is the region
between `H_{s₁}` and `H_{s₂}`. For `s₁ = s₀` this is `E_m(s, u) - E_m(s₀, u)`. -/
theorem hyperboloidalEnergy_sub_hyperboloidalEnergy_of_le (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s₁ s₂ : ℝ} (h₀₁ : s₀ ≤ s₁) (h₁₂ : s₁ < s₂) (h₂S : s₂ ≤ S) :
    hyperboloidalEnergy m s₂ u - hyperboloidalEnergy m s₁ u =
      -2 * ∫ p in regionBetweenHyperboloids s₁ s₂, ⟪kleinGordon m u p, ∂ₜ u p⟫ :=
  hyperboloidalEnergy_sub_hyperboloidalEnergy m (hs₀.trans_le h₀₁) h₁₂ hU
    (regionBetweenHyperboloids_inter_cone_subset_of_le hs₀.le h₀₁ h₁₂.le h₂S hDU) hu
    (regionBetweenHyperboloids_inter_tsupport_subset_of_le hs₀.le h₀₁ h₁₂.le h₂S hsupp)

/-! ### Cauchy–Schwarz on a hyperboloid -/

/-- On the hyperboloid `H_s` (`s ≠ 0`), at the point `(t, x)` with `t = √(s ^ 2 + ‖x‖ ^ 2)`:
`(s / t)² ‖∂_t u‖² ≤ e_m[u]`. This follows from the form
`e_m[u] = ∑ a, ‖∂̲_a u‖² + (s² / t²) ‖∂_t u‖² + m² ‖u‖²` of the energy density on `H_s`. -/
theorem sq_div_mul_norm_timeDeriv_sq_le_hyperboloidalEnergyDensity (m : ℝ) (u : Spacetime → F)
    {s : ℝ} (hs : s ≠ 0) (x : EuclideanSpace ℝ (Fin 3)) :
    (s / √(s ^ 2 + ‖x‖ ^ 2)) ^ 2 * ‖∂ₜ u (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2 ≤
      hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x) := by
  rw [hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv_of_hyperboloid m u hs x, div_pow]
  have h1 : 0 ≤ ∑ a, ‖semiHyperboloidalDeriv a u (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2 :=
    Finset.sum_nonneg fun a _ ↦ sq_nonneg _
  have h2 : 0 ≤ m ^ 2 * ‖u (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2 := by positivity
  linarith

/-- **Cauchy–Schwarz on a hyperboloid.** Let `s ≠ 0`, `t = √(s ^ 2 + ‖x‖ ^ 2)`, and
`f : Spacetime → F` with `f|_{H_s}` square integrable. If `∂_t u|_{H_s}` is (a.e. strongly)
measurable and the energy density `e_m[u]` is integrable on `H_s`, then
`|∫_{ℝ³} (s / t) ⟪f, ∂_t u⟫(t, x) dx| ≤ ‖f‖_{L²_f(H_s)} E_m(s, u)^{1/2}`, where
`‖f‖_{L²_f(H_s)} = (∫_{ℝ³} ‖f(t, x)‖² dx)^{1/2}` is the `L²` norm on `H_s` for the flat
measure `dx`.

The proof is Cauchy–Schwarz (Hölder with `p = q = 2`) for `f` and `(s / t) ∂_t u` on `H_s`,
together with `(s / t)² ‖∂_t u‖² ≤ e_m[u]`. -/
theorem abs_integral_mul_inner_timeDeriv_le (m : ℝ) {s : ℝ} (hs : s ≠ 0) {f : Spacetime → F}
    (hf : MemLp (restrictHyperboloid s f) 2 volume)
    (hu : AEStronglyMeasurable (restrictHyperboloid s (∂ₜ u)) volume)
    (he : Integrable fun x : EuclideanSpace ℝ (Fin 3) ↦
      hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x)) :
    |∫ x : EuclideanSpace ℝ (Fin 3),
        s / √(s ^ 2 + ‖x‖ ^ 2) * ⟪f (√(s ^ 2 + ‖x‖ ^ 2), x), ∂ₜ u (√(s ^ 2 + ‖x‖ ^ 2), x)⟫| ≤
      (eLpNorm (restrictHyperboloid s f) 2 volume).toReal * √(hyperboloidalEnergy m s u) := by
  -- `G x = (s / t) ∂_t u (t, x)` on `H_s`, with `‖G‖² ≤ e_m[u]`
  set G : EuclideanSpace ℝ (Fin 3) → F :=
    fun x ↦ (s / √(s ^ 2 + ‖x‖ ^ 2)) • ∂ₜ u (√(s ^ 2 + ‖x‖ ^ 2), x) with hGdef
  have hGm : AEStronglyMeasurable G volume :=
    (continuous_const.div (by fun_prop) fun x ↦ (Real.sqrt_pos.2 (by positivity)).ne' :
      Continuous fun x : EuclideanSpace ℝ (Fin 3) ↦
        s / √(s ^ 2 + ‖x‖ ^ 2)).aestronglyMeasurable.smul hu
  have hGe (x : EuclideanSpace ℝ (Fin 3)) :
      ‖G x‖ ^ 2 ≤ hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x) := by
    rw [hGdef, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact sq_div_mul_norm_timeDeriv_sq_le_hyperboloidalEnergyDensity m u hs x
  have hG2 : Integrable fun x ↦ ‖G x‖ ^ 2 :=
    he.mono' (hGm.norm.pow 2) (ae_of_all _ fun x ↦ by
      rw [Real.norm_of_nonneg (by positivity)]; exact hGe x)
  have hG : MemLp G 2 volume := (memLp_two_iff_integrable_sq_norm hGm).2 hG2
  -- Cauchy–Schwarz pointwise, then Hölder
  have hpt (x : EuclideanSpace ℝ (Fin 3)) :
      |s / √(s ^ 2 + ‖x‖ ^ 2) * ⟪f (√(s ^ 2 + ‖x‖ ^ 2), x), ∂ₜ u (√(s ^ 2 + ‖x‖ ^ 2), x)⟫| ≤
        ‖restrictHyperboloid s f x‖ * ‖G x‖ := by
    rw [← real_inner_smul_right]
    exact abs_real_inner_le_norm _ _
  have hprod : Integrable fun x ↦ ‖restrictHyperboloid s f x‖ * ‖G x‖ :=
    hf.norm.integrable_mul hG.norm
  have hHolder := integral_mul_norm_le_Lp_mul_Lq (μ := volume) Real.HolderConjugate.two_two
    (f := restrictHyperboloid s f) (g := G) (by simpa using hf) (by simpa using hG)
  have hf' : (eLpNorm (restrictHyperboloid s f) 2 volume).toReal =
      (∫ x, ‖restrictHyperboloid s f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
  have hG' : (∫ x, ‖G x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ √(hyperboloidalEnergy m s u) := by
    rw [Real.sqrt_eq_rpow, hyperboloidalEnergy_apply]
    refine Real.rpow_le_rpow (integral_nonneg fun x ↦ by positivity) ?_ (by norm_num)
    simp only [Real.rpow_two]
    exact integral_mono hG2 he hGe
  calc _ ≤ ∫ x, |s / √(s ^ 2 + ‖x‖ ^ 2) *
          ⟪f (√(s ^ 2 + ‖x‖ ^ 2), x), ∂ₜ u (√(s ^ 2 + ‖x‖ ^ 2), x)⟫| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, ‖restrictHyperboloid s f x‖ * ‖G x‖ :=
        integral_mono_of_nonneg (ae_of_all _ fun x ↦ abs_nonneg _) hprod (ae_of_all _ hpt)
    _ ≤ _ := hHolder
    _ ≤ _ := by
        rw [← hf']
        exact mul_le_mul_of_nonneg_left hG' ENNReal.toReal_nonneg

/-! ### Continuity in `s` of integrals over the hyperboloids -/

/-- For `0 ≤ s₁ ≤ s ≤ s₂`, the point `(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s` lies in the region between
`H_{s₁}` and `H_{s₂}`. -/
theorem mem_regionBetweenHyperboloids_of_mem_Icc {s₁ s₂ s : ℝ} (hs₁ : 0 ≤ s₁)
    (hs : s ∈ Icc s₁ s₂) (x : EuclideanSpace ℝ (Fin 3)) :
    ((√(s ^ 2 + ‖x‖ ^ 2), x) : Spacetime) ∈ regionBetweenHyperboloids s₁ s₂ :=
  mem_regionBetweenHyperboloids.2
    ⟨Real.sqrt_le_sqrt (by nlinarith [hs.1]), Real.sqrt_le_sqrt (by nlinarith [hs.1, hs.2])⟩

/-- A point `(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s` in the cone `‖x‖ ≤ t - 1` satisfies `‖x‖ ≤ s ^ 2`
(indeed `(‖x‖ + 1) ^ 2 ≤ s ^ 2 + ‖x‖ ^ 2`, that is `2 ‖x‖ + 1 ≤ s ^ 2`). -/
theorem norm_le_sq_of_mem_cone {s : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (h : ((√(s ^ 2 + ‖x‖ ^ 2), x) : Spacetime) ∈ cone) : ‖x‖ ≤ s ^ 2 := by
  have hK : ‖x‖ ≤ √(s ^ 2 + ‖x‖ ^ 2) - 1 := h
  have h₁ := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ ‖x‖ + 1)
    (by linarith : ‖x‖ + 1 ≤ √(s ^ 2 + ‖x‖ ^ 2))
  have h₂ := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ s ^ 2 + ‖x‖ ^ 2)
  nlinarith [norm_nonneg x]

/-- **Continuity of integrals over the hyperboloids.** Let `0 ≤ s₁`, `D` the region between
`H_{s₁}` and `H_{s₂}`, and `f : Spacetime → ℝ` continuous at every point of `D` and vanishing at
the points of `D` outside the cone `K`. Then `s ↦ ∫_{ℝ³} f(√(s ^ 2 + ‖x‖ ^ 2), x) dx` is continuous
on `[s₁, s₂]`.

The integrand is continuous in `(s, x)` on `[s₁, s₂] × ℝ³` and vanishes for `‖x‖ > s₂ ^ 2`
(`norm_le_sq_of_mem_cone`), so this is continuity of a parametric integral with uniformly compact
support (`continuousOn_integral_of_compact_support`). -/
theorem continuousOn_integral_hyperboloid {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) {f : Spacetime → ℝ}
    (hf : ∀ p ∈ regionBetweenHyperboloids s₁ s₂, ContinuousAt f p)
    (hfK : ∀ p ∈ regionBetweenHyperboloids s₁ s₂, p ∉ cone → f p = 0) :
    ContinuousOn (fun s ↦ ∫ x : EuclideanSpace ℝ (Fin 3), f (√(s ^ 2 + ‖x‖ ^ 2), x))
      (Icc s₁ s₂) := by
  have hΨ : Continuous fun q : ℝ × EuclideanSpace ℝ (Fin 3) ↦
      ((√(q.1 ^ 2 + ‖q.2‖ ^ 2), q.2) : Spacetime) := by fun_prop
  refine continuousOn_integral_of_compact_support
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (s₂ ^ 2)) ?_ ?_
  · rintro ⟨s, x⟩ ⟨hs, -⟩
    exact ((hf _ (mem_regionBetweenHyperboloids_of_mem_Icc hs₁ hs x)).comp
      (x := (s, x)) hΨ.continuousAt).continuousWithinAt
  · intro s x hs hx
    refine hfK _ (mem_regionBetweenHyperboloids_of_mem_Icc hs₁ hs x) fun hK ↦ hx ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_sq_of_mem_cone hK).trans (by nlinarith [hs.1, hs.2])

/-- **Continuity of the energy.** Let `0 < s₀`, `D` the region between `H_{s₀}` and `H_S`, `K` the
cone, `U` an open set containing `D ∩ K`, and `u` of class `C²` on `U` with `D ∩ supp u ⊆ K`. Then
`s ↦ E_m(s, u)` is continuous on `[s₀, S]`. -/
theorem continuousOn_hyperboloidalEnergy (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone) :
    ContinuousOn (fun s ↦ hyperboloidalEnergy m s u) (Icc s₀ S) := by
  refine continuousOn_integral_hyperboloid (f := hyperboloidalEnergyDensity m u) hs₀.le
    (fun p hp ↦ ?_) fun p hp hK ↦ ?_
  · have hp' := contDiffAt_of_inter_tsupport_subset hU hDU hu hsupp hp
    have h1 : √(s₀ ^ 2 + ‖p.2‖ ^ 2) ≤ p.1 := (mem_regionBetweenHyperboloids.1 hp).1
    have h2 : 0 < √(s₀ ^ 2 + ‖p.2‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
    exact continuousAt_hyperboloidalEnergyDensity m (hp'.of_le one_le_two) (h2.trans_le h1).ne'
  · by_contra hne
    exact hK (hsupp ⟨hp, support_hyperboloidalEnergyDensity_subset m u hne⟩)

omit [InnerProductSpace ℝ F] in
/-- If `f` is continuous at every point of the region between `H_{s₀}` and `H_S` (`0 ≤ s₀`), its
restriction to `H_s` is continuous for every `s ∈ [s₀, S]`. -/
theorem continuous_restrictHyperboloid_of_continuousAt {s₀ S s : ℝ} (hs₀ : 0 ≤ s₀)
    (hs : s ∈ Icc s₀ S) {f : Spacetime → F}
    (hf : ∀ p ∈ regionBetweenHyperboloids s₀ S, ContinuousAt f p) :
    Continuous (restrictHyperboloid s f) :=
  continuous_iff_continuousAt.2 fun x ↦
    ContinuousAt.comp (g := f) (f := fun y : EuclideanSpace ℝ (Fin 3) ↦
        ((√(s ^ 2 + ‖y‖ ^ 2), y) : Spacetime))
      (hf _ (mem_regionBetweenHyperboloids_of_mem_Icc hs₀ hs x))
      (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin 3) ↦
        ((√(s ^ 2 + ‖y‖ ^ 2), y) : Spacetime)).continuousAt

omit [InnerProductSpace ℝ F] in
/-- If `f` vanishes at the points of the region between `H_{s₀}` and `H_S` (`0 ≤ s₀`) outside the
cone, its restriction to `H_s` has compact support for every `s ∈ [s₀, S]`. -/
theorem hasCompactSupport_restrictHyperboloid_of_eq_zero {s₀ S s : ℝ} (hs₀ : 0 ≤ s₀)
    (hs : s ∈ Icc s₀ S) {f : Spacetime → F}
    (hfK : ∀ p ∈ regionBetweenHyperboloids s₀ S, p ∉ cone → f p = 0) :
    HasCompactSupport (restrictHyperboloid s f) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (S ^ 2)) fun x hx ↦ ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hS
  refine hx (hfK _ (mem_regionBetweenHyperboloids_of_mem_Icc hs₀ hs x) fun hK ↦ hS ?_)
  exact (norm_le_sq_of_mem_cone hK).trans (by nlinarith [hs.1, hs.2])

/-- Under the hypotheses of the energy identity on the region between `H_{s₀}` and `H_S`,
`KG_m u|_{H_s}` is square integrable for every `s ∈ [s₀, S]`: it is continuous with compact
support. -/
theorem memLp_restrictHyperboloid_kleinGordon (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s : ℝ} (hs : s ∈ Icc s₀ S) :
    MemLp (restrictHyperboloid s (kleinGordon m u)) 2 volume :=
  (continuous_restrictHyperboloid_of_continuousAt hs₀.le hs fun _ hp ↦
      continuousAt_kleinGordon m (contDiffAt_of_inter_tsupport_subset hU hDU hu hsupp hp)
    ).memLp_of_hasCompactSupport
    (hasCompactSupport_restrictHyperboloid_of_eq_zero hs₀.le hs fun _ hp hK ↦
      kleinGordon_of_notMem_tsupport m fun h ↦ hK (hsupp ⟨hp, h⟩))

/-- Under the hypotheses of the energy identity on the region between `H_{s₀}` and `H_S`,
`∂_t u|_{H_s}` is continuous for every `s ∈ [s₀, S]`. -/
theorem continuous_restrictHyperboloid_timeDeriv {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s : ℝ} (hs : s ∈ Icc s₀ S) :
    Continuous (restrictHyperboloid s (∂ₜ u)) :=
  continuous_restrictHyperboloid_of_continuousAt hs₀.le hs fun p hp ↦ by
    have hp' := contDiffAt_of_inter_tsupport_subset hU hDU hu hsupp hp
    have hu' : ContDiffAt ℝ (0 + 1) u p := by rw [zero_add]; exact hp'.of_le one_le_two
    exact (contDiffAt_partialDeriv 0 hu').continuousAt

omit [InnerProductSpace ℝ F] in
/-- For `f|_{H_s}` square integrable,
`‖f‖_{L²_f(H_s)} = (∫_{ℝ³} ‖f(√(s ^ 2 + ‖x‖ ^ 2), x)‖² dx)^{1/2}`. -/
theorem toReal_eLpNorm_restrictHyperboloid_eq_sqrt {s : ℝ} {f : Spacetime → F}
    (hf : MemLp (restrictHyperboloid s f) 2 volume) :
    (eLpNorm (restrictHyperboloid s f) 2 volume).toReal =
      √(∫ x : EuclideanSpace ℝ (Fin 3), ‖f (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  norm_num
  rfl

/-- Under the hypotheses of the energy identity on the region between `H_{s₀}` and `H_S`,
`s ↦ ‖KG_m u‖_{L²_f(H_s)}` is continuous on `[s₀, S]`. -/
theorem continuousOn_toReal_eLpNorm_restrictHyperboloid_kleinGordon (m : ℝ) {s₀ S : ℝ}
    (hs₀ : 0 < s₀) {U : Set Spacetime} (hU : IsOpen U)
    (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone) :
    ContinuousOn (fun s ↦ (eLpNorm (restrictHyperboloid s (kleinGordon m u)) 2 volume).toReal)
      (Icc s₀ S) := by
  have h := (continuousOn_integral_hyperboloid (f := fun p ↦ ‖kleinGordon m u p‖ ^ 2) hs₀.le
    (fun p hp ↦ ((continuousAt_kleinGordon m
      (contDiffAt_of_inter_tsupport_subset hU hDU hu hsupp hp)).norm.pow 2))
    fun _ hp hK ↦ by
      rw [kleinGordon_of_notMem_tsupport m fun h ↦ hK (hsupp ⟨hp, h⟩), norm_zero,
        zero_pow two_ne_zero]).sqrt
  exact h.congr fun s hs ↦ toReal_eLpNorm_restrictHyperboloid_eq_sqrt
    (memLp_restrictHyperboloid_kleinGordon m hs₀ hU hDU hu hsupp hs)


/-! ### The integral inequality -/

/-- **The integral inequality for the energy.** Let `0 < s₀`, `D` the region between `H_{s₀}` and
`H_S`, `K` the cone, `U` an open set containing `D ∩ K`, and `u` of class `C²` on `U` with
`D ∩ supp u ⊆ K`. Then for `s ∈ [s₀, S]`,
`E_m(s, u) ≤ E_m(s₀, u) + 2 ∫_{s₀}^{s} ‖KG_m u‖_{L²_f(H_{s'})} E_m(s', u)^{1/2} ds'`.

By the energy identity and the foliation formula,
`E_m(s, u) - E_m(s₀, u) = -2 ∫_{s₀}^{s} ∫_{ℝ³} (s' / t) ⟪KG_m u, ∂_t u⟫(t, x) dx ds'` with
`t = √(s' ^ 2 + ‖x‖ ^ 2)`, and the inner integral is bounded by Cauchy–Schwarz
(`abs_integral_mul_inner_timeDeriv_le`). The norms `‖KG_m u‖_{L²_f(H_{s'})}` are finite
(`memLp_restrictHyperboloid_kleinGordon`), and the integrand on the right is continuous in `s'`. -/
theorem hyperboloidalEnergy_le_add_two_mul_integral (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s : ℝ} (hs : s ∈ Icc s₀ S) :
    hyperboloidalEnergy m s u ≤ hyperboloidalEnergy m s₀ u +
      2 * ∫ s' in s₀..s, (eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume).toReal *
        √(hyperboloidalEnergy m s' u) := by
  rcases hs.1.eq_or_lt with h | h
  · subst h; simp
  have hsub : Icc s₀ s ⊆ Icc s₀ S := Icc_subset_Icc le_rfl hs.2
  -- the right-hand side integrand is continuous, hence integrable
  have hGcont : ContinuousOn (fun s' ↦
      (eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume).toReal *
        √(hyperboloidalEnergy m s' u)) (Icc s₀ S) :=
    (continuousOn_toReal_eLpNorm_restrictHyperboloid_kleinGordon m hs₀ hU hDU hu hsupp).mul
      (continuousOn_hyperboloidalEnergy m hs₀ hU hDU hu hsupp).sqrt
  have hGint := (hGcont.mono hsub).integrableOn_Icc (μ := volume)
  -- the pointwise bound on each hyperboloid
  have hpt (s' : ℝ) (hs' : s' ∈ Icc s₀ s) :
      -∫ x : EuclideanSpace ℝ (Fin 3), s' / √(s' ^ 2 + ‖x‖ ^ 2) *
          ⟪kleinGordon m u (√(s' ^ 2 + ‖x‖ ^ 2), x), ∂ₜ u (√(s' ^ 2 + ‖x‖ ^ 2), x)⟫ ≤
        (eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume).toReal *
          √(hyperboloidalEnergy m s' u) :=
    (neg_le_abs _).trans (abs_integral_mul_inner_timeDeriv_le m (hs₀.trans_le hs'.1).ne'
      (memLp_restrictHyperboloid_kleinGordon m hs₀ hU hDU hu hsupp (hsub hs'))
      (continuous_restrictHyperboloid_timeDeriv hs₀ hU hDU hu hsupp
        (hsub hs')).aestronglyMeasurable
      (integrable_hyperboloidalEnergyDensity m hs₀ (hsub hs') hU hDU hu hsupp))
  have hle : -∫ s' in Icc s₀ s, ∫ x : EuclideanSpace ℝ (Fin 3), s' / √(s' ^ 2 + ‖x‖ ^ 2) *
        ⟪kleinGordon m u (√(s' ^ 2 + ‖x‖ ^ 2), x), ∂ₜ u (√(s' ^ 2 + ‖x‖ ^ 2), x)⟫ ≤
      ∫ s' in Icc s₀ s, (eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume).toReal *
        √(hyperboloidalEnergy m s' u) := by
    rw [← integral_neg]
    by_cases hint : IntegrableOn (fun s' ↦ -∫ x : EuclideanSpace ℝ (Fin 3),
        s' / √(s' ^ 2 + ‖x‖ ^ 2) *
          ⟪kleinGordon m u (√(s' ^ 2 + ‖x‖ ^ 2), x), ∂ₜ u (√(s' ^ 2 + ‖x‖ ^ 2), x)⟫) (Icc s₀ s)
    · exact setIntegral_mono_on hint hGint measurableSet_Icc hpt
    · rw [integral_undef hint]
      exact setIntegral_nonneg measurableSet_Icc fun s' _ ↦
        mul_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)
  -- the energy identity on `[s₀, s]` and the foliation formula
  have hid := hyperboloidalEnergy_sub_hyperboloidalEnergy_of_le m hs₀ hU hDU hu hsupp le_rfl h hs.2
  have hfol := setIntegral_regionBetweenHyperboloids_eq hs₀ h.le
    (integrableOn_inner_kleinGordon_timeDeriv m hU
      (regionBetweenHyperboloids_inter_cone_subset_of_le hs₀.le le_rfl h.le hs.2 hDU) hu
      (regionBetweenHyperboloids_inter_tsupport_subset_of_le hs₀.le le_rfl h.le hs.2 hsupp))
  rw [intervalIntegral.integral_of_le h.le, ← integral_Icc_eq_integral_Ioc]
  linarith

/-! ### The energy estimate -/

/-- **The hyperboloidal energy estimate, real form.** Under the hypotheses of the energy identity
on the region between `H_{s₀}` and `H_S` (`0 < s₀`, `U` open, `D ∩ K ⊆ U`, `u` of class `C²` on
`U`, `D ∩ supp u ⊆ K`), for `s ∈ [s₀, S]`,
`E_m(s, u)^{1/2} ≤ E_m(s₀, u)^{1/2} + ∫_{s₀}^{s} ‖KG_m u‖_{L²_f(H_{s'})} ds'`.

The norms `‖KG_m u‖_{L²_f(H_{s'})}` are finite (`memLp_restrictHyperboloid_kleinGordon`), so
`toReal` loses nothing here. This is the square-root Grönwall inequality
(`VectorFieldMethod.Analysis.sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral`) applied to the
integral inequality `hyperboloidalEnergy_le_add_two_mul_integral`, with `s ↦ E_m(s, u)`
continuous (`continuousOn_hyperboloidalEnergy`). -/
theorem sqrt_hyperboloidalEnergy_le_add_integral (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s : ℝ} (hs : s ∈ Icc s₀ S) :
    √(hyperboloidalEnergy m s u) ≤ √(hyperboloidalEnergy m s₀ u) +
      ∫ s' in s₀..s, (eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume).toReal :=
  VectorFieldMethod.Analysis.sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral
    (E := fun s ↦ hyperboloidalEnergy m s u)
    (continuousOn_hyperboloidalEnergy m hs₀ hU hDU hu hsupp)
    ((continuousOn_toReal_eLpNorm_restrictHyperboloid_kleinGordon m hs₀ hU hDU hu
      hsupp).integrableOn_Icc)
    (fun _ _ ↦ ENNReal.toReal_nonneg)
    (fun _ hs' ↦ hyperboloidalEnergy_le_add_two_mul_integral m hs₀ hU hDU hu hsupp hs') hs

/-- Under the hypotheses of the energy estimate, its right-hand side is finite: for `s ≤ S`,
`∫_{[s₀, s]} ‖KG_m u‖_{L²_f(H_{s'})} ds' < ∞`, since `s' ↦ ‖KG_m u‖_{L²_f(H_{s'})}` is finite and
continuous on `[s₀, S]`. -/
theorem lintegral_eLpNorm_restrictHyperboloid_kleinGordon_lt_top (m : ℝ) {s₀ S : ℝ}
    (hs₀ : 0 < s₀) {U : Set Spacetime} (hU : IsOpen U)
    (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone) {s : ℝ} (hs : s ≤ S) :
    ∫⁻ s' in Icc s₀ s, eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume < ∞ := by
  have hsub : Icc s₀ s ⊆ Icc s₀ S := Icc_subset_Icc le_rfl hs
  rw [setLIntegral_congr_fun measurableSet_Icc fun s' hs' ↦ (ENNReal.ofReal_toReal
      (memLp_restrictHyperboloid_kleinGordon m hs₀ hU hDU hu hsupp
        (hsub hs')).eLpNorm_ne_top).symm,
    ← ofReal_integral_eq_lintegral_ofReal
      (((continuousOn_toReal_eLpNorm_restrictHyperboloid_kleinGordon m hs₀ hU hDU hu
        hsupp).mono hsub).integrableOn_Icc)
      (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)]
  exact ENNReal.ofReal_lt_top

/-- **The hyperboloidal energy estimate.** Let `0 < s₀`, `D` the region between the hyperboloids
`H_{s₀}` and `H_S`, `K = {‖x‖ ≤ t - 1}` the cone, `U` an open set containing `D ∩ K`, and `u` of
class `C²` on `U` with `D ∩ supp u ⊆ K`. Then for `s ∈ [s₀, S]`,
`E_m(s, u)^{1/2} ≤ E_m(s₀, u)^{1/2} + ∫_{s₀}^{s} ‖KG_m u‖_{L²_f(H_{s'})} ds'`,
where `‖f‖_{L²_f(H_{s'})} = (∫_{ℝ³} ‖f(√(s' ^ 2 + ‖x‖ ^ 2), x)‖² dx)^{1/2}` is the `L²` norm on
`H_{s'}` for the flat measure `dx` and `KG_m u = □u - m² u`.

The inequality is stated in `ℝ≥0∞`, where the integral of the `L²` norms always makes sense; no
integrability is assumed. Under the hypotheses its right-hand side is finite
(`lintegral_eLpNorm_restrictHyperboloid_kleinGordon_lt_top`). -/
theorem ofReal_sqrt_hyperboloidalEnergy_le (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s : ℝ} (hs : s ∈ Icc s₀ S) :
    ENNReal.ofReal √(hyperboloidalEnergy m s u) ≤ ENNReal.ofReal √(hyperboloidalEnergy m s₀ u) +
      ∫⁻ s' in Icc s₀ s, eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume := by
  have h := sqrt_hyperboloidalEnergy_le_add_integral m hs₀ hU hDU hu hsupp hs
  have hGint : IntegrableOn
      (fun s' ↦ (eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume).toReal)
      (Icc s₀ s) :=
    ((continuousOn_toReal_eLpNorm_restrictHyperboloid_kleinGordon m hs₀ hU hDU hu hsupp).mono
      (Icc_subset_Icc le_rfl hs.2)).integrableOn_Icc
  rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc] at h
  calc ENNReal.ofReal √(hyperboloidalEnergy m s u)
      ≤ ENNReal.ofReal (√(hyperboloidalEnergy m s₀ u) + ∫ s' in Icc s₀ s,
          (eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume).toReal) :=
        ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal √(hyperboloidalEnergy m s₀ u) + ∫⁻ s' in Icc s₀ s,
          ENNReal.ofReal (eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume).toReal := by
        rw [ENNReal.ofReal_add (Real.sqrt_nonneg _)
            (setIntegral_nonneg measurableSet_Icc fun _ _ ↦ ENNReal.toReal_nonneg),
          ofReal_integral_eq_lintegral_ofReal hGint (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg)]
    _ ≤ _ := by
        gcongr with s'
        exact ENNReal.ofReal_toReal_le

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

/-- The points `(t, x)` of the closed support of the bump function satisfy `|t - 4| ≤ 1 / 2` and
`‖x‖ ≤ 1 / 2`. -/
private theorem mem_tsupport_estimateBump {t : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (h : ((t, x) : Spacetime) ∈ tsupport (estimateBump : Spacetime → ℝ)) :
    -(1 / 2) ≤ t - 4 ∧ t - 4 ≤ 1 / 2 ∧ ‖x‖ ≤ 1 / 2 := by
  rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq,
    dist_zero_right] at h
  have hr : estimateBump.rOut = 1 / 2 := rfl
  rw [hr, abs_le] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The closed support of the bump function lies in the cone `‖x‖ ≤ t - 1`, since `t ≥ 7 / 2`
there. -/
private theorem tsupport_estimateBump_subset : tsupport (estimateBump : Spacetime → ℝ) ⊆ cone := by
  intro p hp
  obtain ⟨h₁, -, h₃⟩ := mem_tsupport_estimateBump (t := p.1) (x := p.2) hp
  rw [mem_cone]
  linarith

/-- The energy identity between intermediate hyperboloids applies to the bump function, with the
hypotheses stated on the region between `H_2` and `H_5` (`U` the whole spacetime), between `H_3`
and `H_4`. -/
example (m : ℝ) :
    hyperboloidalEnergy m 4 (estimateBump : Spacetime → ℝ) -
        hyperboloidalEnergy m 3 (estimateBump : Spacetime → ℝ) =
      -2 * ∫ p in regionBetweenHyperboloids 3 4,
        ⟪kleinGordon m (estimateBump : Spacetime → ℝ) p, ∂ₜ (estimateBump : Spacetime → ℝ) p⟫ :=
  hyperboloidalEnergy_sub_hyperboloidalEnergy_of_le m (s₀ := 2) (S := 5) (by norm_num)
    isOpen_univ (subset_univ _) estimateBump.contDiff.contDiffOn
    (inter_subset_right.trans tsupport_estimateBump_subset) (by norm_num) (by norm_num)
    (by norm_num)

/-- The Cauchy–Schwarz bound on a hyperboloid applies with `f = u =` the bump function on `H_4`:
`f|_{H_4}` is continuous with compact support, `∂_t u|_{H_4}` is continuous, and the energy
density of `u` on `H_4` is integrable. -/
example (m : ℝ) :
    |∫ x : EuclideanSpace ℝ (Fin 3), 4 / √(4 ^ 2 + ‖x‖ ^ 2) *
        ⟪(estimateBump : Spacetime → ℝ) (√(4 ^ 2 + ‖x‖ ^ 2), x),
          ∂ₜ (estimateBump : Spacetime → ℝ) (√(4 ^ 2 + ‖x‖ ^ 2), x)⟫| ≤
      (eLpNorm (restrictHyperboloid 4 (estimateBump : Spacetime → ℝ)) 2 volume).toReal *
        √(hyperboloidalEnergy m 4 (estimateBump : Spacetime → ℝ)) :=
  abs_integral_mul_inner_timeDeriv_le m (by norm_num)
    ((continuous_restrictHyperboloid 4 estimateBump.continuous).memLp_of_hasCompactSupport
      (hasCompactSupport_restrictHyperboloid 4 estimateBump.hasCompactSupport))
    (continuous_restrictHyperboloid 4
      (contDiff_infty_timeDeriv estimateBump.contDiff).continuous).aestronglyMeasurable
    (integrable_hyperboloidalEnergyDensity m (s₁ := 2) (s₂ := 4) (by norm_num)
      ⟨by norm_num, le_rfl⟩ isOpen_univ (subset_univ _) estimateBump.contDiff.contDiffOn
      (inter_subset_right.trans tsupport_estimateBump_subset))

/-- Continuity of integrals over the hyperboloids applies to the bump function itself on
`[2, 5]`: it is continuous, and it vanishes outside the cone. -/
example : ContinuousOn (fun s ↦ ∫ x : EuclideanSpace ℝ (Fin 3),
    (estimateBump : Spacetime → ℝ) (√(s ^ 2 + ‖x‖ ^ 2), x)) (Icc 2 5) :=
  continuousOn_integral_hyperboloid (by norm_num) (fun _ _ ↦ estimateBump.continuous.continuousAt)
    fun _ _ hK ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hK (tsupport_estimateBump_subset h)

/-- The energy of the bump function is continuous in `s` on `[2, 5]`. -/
example (m : ℝ) :
    ContinuousOn (fun s ↦ hyperboloidalEnergy m s (estimateBump : Spacetime → ℝ)) (Icc 2 5) :=
  continuousOn_hyperboloidalEnergy m (by norm_num) isOpen_univ (subset_univ _)
    estimateBump.contDiff.contDiffOn (inter_subset_right.trans tsupport_estimateBump_subset)

/-- The integral inequality for the bump function, with the hypotheses on the region between
`H_2` and `H_5` and `s = 4`. -/
example (m : ℝ) :
    hyperboloidalEnergy m 4 (estimateBump : Spacetime → ℝ) ≤
      hyperboloidalEnergy m 2 (estimateBump : Spacetime → ℝ) +
        2 * ∫ s' in (2 : ℝ)..4, (eLpNorm (restrictHyperboloid s'
          (kleinGordon m (estimateBump : Spacetime → ℝ))) 2 volume).toReal *
            √(hyperboloidalEnergy m s' (estimateBump : Spacetime → ℝ)) :=
  hyperboloidalEnergy_le_add_two_mul_integral m (S := 5) (by norm_num) isOpen_univ
    (subset_univ _) estimateBump.contDiff.contDiffOn
    (inter_subset_right.trans tsupport_estimateBump_subset) ⟨by norm_num, by norm_num⟩

/-- The energy estimate applies to the bump function, with the hypotheses on the region between
`H_2` and `H_5` (`U` the whole spacetime) and `s = 4`. -/
example (m : ℝ) :
    ENNReal.ofReal √(hyperboloidalEnergy m 4 (estimateBump : Spacetime → ℝ)) ≤
      ENNReal.ofReal √(hyperboloidalEnergy m 2 (estimateBump : Spacetime → ℝ)) +
        ∫⁻ s' in Icc (2 : ℝ) 4, eLpNorm (restrictHyperboloid s'
          (kleinGordon m (estimateBump : Spacetime → ℝ))) 2 volume :=
  ofReal_sqrt_hyperboloidalEnergy_le m (S := 5) (by norm_num) isOpen_univ (subset_univ _)
    estimateBump.contDiff.contDiffOn (inter_subset_right.trans tsupport_estimateBump_subset)
    ⟨by norm_num, by norm_num⟩

/-- The bump function equals `1` at the points `(t, x)` with `|t - 4| ≤ 1 / 4` and
`‖x‖ ≤ 1 / 4`. -/
private theorem estimateBump_eq_one {t : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (h₁ : -(1 / 4) ≤ t - 4) (h₂ : t - 4 ≤ 1 / 4) (h₃ : ‖x‖ ≤ 1 / 4) :
    (estimateBump : Spacetime → ℝ) (t, x) = 1 := by
  refine estimateBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right]
  have hr : estimateBump.rIn = 1 / 4 := rfl
  rw [hr, abs_le]
  exact ⟨⟨h₁, h₂⟩, h₃⟩

/-- For `m ≠ 0` the energy estimate for the bump function between `H_2` and `H_4` is a genuine
inequality between finite, nonzero quantities. The energy on `H_2` vanishes, since the closed
support of `u` does not meet `H_2`; the energy on `H_4` is positive, since the energy density is
nonnegative and at least `m² > 0` where `u = 1`; and the right-hand side is finite. So the
estimate gives `0 < E_m(4, u)^{1/2} ≤ ∫_2^4 ‖KG_m u‖_{L²_f(H_{s'})} ds' < ∞`. -/
example (m : ℝ) (hm : m ≠ 0) :
    hyperboloidalEnergy m 2 (estimateBump : Spacetime → ℝ) = 0 ∧
      0 < ENNReal.ofReal √(hyperboloidalEnergy m 4 (estimateBump : Spacetime → ℝ)) ∧
      ENNReal.ofReal √(hyperboloidalEnergy m 4 (estimateBump : Spacetime → ℝ)) ≤
        ∫⁻ s' in Icc (2 : ℝ) 4, eLpNorm (restrictHyperboloid s'
          (kleinGordon m (estimateBump : Spacetime → ℝ))) 2 volume ∧
      ∫⁻ s' in Icc (2 : ℝ) 4, eLpNorm (restrictHyperboloid s'
          (kleinGordon m (estimateBump : Spacetime → ℝ))) 2 volume < ∞ := by
  -- the hyperboloid `H_2` does not meet the closed support of `u`
  have h2 : hyperboloidalEnergy m 2 (estimateBump : Spacetime → ℝ) = 0 := by
    have h0 (x : EuclideanSpace ℝ (Fin 3)) :
        hyperboloidalEnergyDensity m (estimateBump : Spacetime → ℝ) (√(2 ^ 2 + ‖x‖ ^ 2), x) =
          0 := by
      by_contra hne
      obtain ⟨h₁, -, h₃⟩ :=
        mem_tsupport_estimateBump (support_hyperboloidalEnergyDensity_subset m _ hne)
      have h₂ := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 ^ 2 + ‖x‖ ^ 2)
      have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
      generalize √(2 ^ 2 + ‖x‖ ^ 2) = T at h₁ h₂
      nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 7 / 2)
        (by linarith : (7 : ℝ) / 2 ≤ T), mul_self_le_mul_self hx0 h₃]
    simp only [hyperboloidalEnergy_apply, h0, integral_zero]
  -- the energy density on `H_4` is nonnegative, integrable, and positive near `x = 0`
  have h4 : 0 < hyperboloidalEnergy m 4 (estimateBump : Spacetime → ℝ) := by
    have hnonneg : 0 ≤ fun x : EuclideanSpace ℝ (Fin 3) ↦
        hyperboloidalEnergyDensity m (estimateBump : Spacetime → ℝ) (√(4 ^ 2 + ‖x‖ ^ 2), x) :=
      fun x ↦ hyperboloidalEnergyDensity_nonneg m _
        ((Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg 4))).trans (le_abs_self _))
        (Real.sqrt_pos.2 (by positivity)).ne'
    have hint := integrable_hyperboloidalEnergyDensity m (s₁ := 2) (s₂ := 4) (s := 4)
      (by norm_num) ⟨by norm_num, le_rfl⟩ isOpen_univ (subset_univ _)
      estimateBump.contDiff.contDiffOn (inter_subset_right.trans tsupport_estimateBump_subset)
    have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4) ⊆ support fun x ↦
        hyperboloidalEnergyDensity m (estimateBump : Spacetime → ℝ) (√(4 ^ 2 + ‖x‖ ^ 2), x) := by
      intro x hx
      rw [Metric.mem_ball, dist_zero_right] at hx
      have h₄ : (4 : ℝ) ≤ √(4 ^ 2 + ‖x‖ ^ 2) :=
        Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg x])
      have h₄' : √(4 ^ 2 + ‖x‖ ^ 2) ≤ 4 + 1 / 4 := by
        calc √(4 ^ 2 + ‖x‖ ^ 2) ≤ √((4 + 1 / 4) ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith [norm_nonneg x])
          _ = 4 + 1 / 4 := Real.sqrt_sq (by norm_num)
      have hu1 : (estimateBump : Spacetime → ℝ) (√(4 ^ 2 + ‖x‖ ^ 2), x) = 1 := by
        generalize √(4 ^ 2 + ‖x‖ ^ 2) = T at h₄ h₄' ⊢
        exact estimateBump_eq_one (by linarith) (by linarith) hx.le
      rw [Function.mem_support,
        hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv_of_hyperboloid m _
          (by norm_num : (4 : ℝ) ≠ 0), hu1, norm_one, one_pow, mul_one]
      positivity
    rw [hyperboloidalEnergy_apply, integral_pos_iff_support_of_nonneg hnonneg hint]
    exact (Metric.measure_ball_pos volume 0 (by norm_num)).trans_le (measure_mono hball)
  -- the energy estimate between `H_2` and `H_4`, and the finiteness of its right-hand side
  have hest := ofReal_sqrt_hyperboloidalEnergy_le m (s₀ := 2) (S := 5) (by norm_num) isOpen_univ
    (subset_univ _) estimateBump.contDiff.contDiffOn
    (inter_subset_right.trans tsupport_estimateBump_subset) (s := 4) ⟨by norm_num, by norm_num⟩
  rw [h2, Real.sqrt_zero, ENNReal.ofReal_zero, zero_add] at hest
  exact ⟨h2, ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 h4), hest,
    lintegral_eLpNorm_restrictHyperboloid_kleinGordon_lt_top m (s₀ := 2) (S := 5) (by norm_num)
      isOpen_univ (subset_univ _) estimateBump.contDiff.contDiffOn
      (inter_subset_right.trans tsupport_estimateBump_subset) (by norm_num)⟩

end SanityChecks

end VectorFieldMethod.Minkowski
