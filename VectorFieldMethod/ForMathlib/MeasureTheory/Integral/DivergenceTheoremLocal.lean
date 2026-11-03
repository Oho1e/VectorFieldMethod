/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.ForMathlib.Geometry.Manifold.PartitionOfUnity
public import VectorFieldMethod.ForMathlib.MeasureTheory.Integral.DivergenceTheoremHypograph

/-!
# The divergence theorem between two graphs, for locally defined vector fields

The divergence theorems between two graphs `MeasureTheory.integral_intervalIntegral_divergence`
and `MeasureTheory.integral_divergence_region_between_cc` assume that the vector field `(X₀, X)` on
spacetime `E × ℝ` is `C¹` and compactly supported. Here we only assume that it is `C¹` on an open
set `U` containing the closed region `D` between the graphs of two `C¹` functions
`φ₁, φ₂ : E → ℝ`, and that `D ∩ (tsupport X₀ ∪ tsupport X)` is compact. The proof multiplies
`X₀` and `X` by smooth cutoff functions which are equal to `1` near
`D ∩ (tsupport X₀ ∪ tsupport X)` and supported in `U`
(`ContDiffOn.exists_contDiff_hasCompactSupport_eventuallyEq`), and applies the compactly supported
case.

## Main statements

* `deriv_add_spatialDivergence_congr`: two vector fields which coincide near `p` have the same
  divergence at `p`.
* `exists_contDiff_hasCompactSupport_eventuallyEq_of_contDiffOn`: localization of a vector field
  near a set `D`.
* `MeasureTheory.integral_intervalIntegral_divergence_of_contDiffOn`: the divergence theorem
  between two graphs, in any order, as an iterated integral.
* `MeasureTheory.integral_divergence_region_between_cc_of_contDiffOn`: the divergence theorem on
  the closed region between two graphs `φ₁ ≤ φ₂`, as a set integral.
-/

@[expose] public noncomputable section

open Set Filter Function Topology

section Localization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {X₀ : E × ℝ → ℝ} {X : E × ℝ → E}

/-- Two vector fields on spacetime which coincide near `p` have the same divergence at `p`. -/
theorem deriv_add_spatialDivergence_congr {Y₀ : E × ℝ → ℝ} {Y : E × ℝ → E} {p : E × ℝ}
    (h₀ : Y₀ =ᶠ[𝓝 p] X₀) (h : Y =ᶠ[𝓝 p] X) :
    deriv (fun t ↦ Y₀ (p.1, t)) p.2 + spatialDivergence Y p =
      deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p := by
  have h₀' : (fun t ↦ Y₀ (p.1, t)) =ᶠ[𝓝 p.2] fun t ↦ X₀ (p.1, t) :=
    h₀.comp_tendsto (Continuous.tendsto' (by fun_prop) p.2 p rfl)
  rw [h.spatialDivergence_eq, h₀'.deriv_eq]

variable [FiniteDimensional ℝ E]

/-- Localization: given a set `D` contained in an open set `U` on which the components `X₀`, `X`
are `C¹`, such that `D ∩ (tsupport X₀ ∪ tsupport X)` is compact, there is a compactly supported
`C¹` vector field `(Y₀, Y)` which coincides with `(X₀, X)` near every point of `D`. -/
theorem exists_contDiff_hasCompactSupport_eventuallyEq_of_contDiffOn {U D : Set (E × ℝ)}
    (hU : IsOpen U) (hDU : D ⊆ U) (hX₀ : ContDiffOn ℝ 1 X₀ U) (hX : ContDiffOn ℝ 1 X U)
    (hK : IsCompact (D ∩ (tsupport X₀ ∪ tsupport X))) :
    ∃ Y₀ : E × ℝ → ℝ, ∃ Y : E × ℝ → E, ContDiff ℝ 1 Y₀ ∧ HasCompactSupport Y₀ ∧
      ContDiff ℝ 1 Y ∧ HasCompactSupport Y ∧ ∀ p ∈ D, Y₀ =ᶠ[𝓝 p] X₀ ∧ Y =ᶠ[𝓝 p] X := by
  have hKU : D ∩ (tsupport X₀ ∪ tsupport X) ⊆ U := inter_subset_left.trans hDU
  obtain ⟨Y₀, hY₀, hY₀c, hY₀e⟩ := hX₀.exists_contDiff_hasCompactSupport_eventuallyEq hU hK hKU
  obtain ⟨Y, hY, hYc, hYe⟩ := hX.exists_contDiff_hasCompactSupport_eventuallyEq hU hK hKU
  refine ⟨Y₀, Y, hY₀, hY₀c, hY, hYc, fun p hp ↦ ⟨hY₀e p ?_, hYe p ?_⟩⟩
  · by_cases h : p ∈ tsupport X₀ ∪ tsupport X
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr fun h' ↦ h (Or.inl h')
  · by_cases h : p ∈ tsupport X₀ ∪ tsupport X
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr fun h' ↦ h (Or.inr h')

end Localization

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {φ₁ φ₂ : E → ℝ} {X₀ : E × ℝ → ℝ} {X : E × ℝ → E}

/-- **Divergence theorem between two graphs, for a locally defined vector field.** Let
`φ₁ φ₂ : E → ℝ` be `C¹` (in any order), and let `D = {(x, t) | t ∈ [[φ₁ x, φ₂ x]]}` be the closed
region between their graphs. If `D` is contained in an open set `U` on which `X₀` and `X` are
`C¹`, and `D ∩ (tsupport X₀ ∪ tsupport X)` is compact, then the conclusion of
`MeasureTheory.integral_intervalIntegral_divergence` holds. -/
theorem integral_intervalIntegral_divergence_of_contDiffOn {U : Set (E × ℝ)} (hU : IsOpen U)
    (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂)
    (hDU : {p : E × ℝ | p.2 ∈ uIcc (φ₁ p.1) (φ₂ p.1)} ⊆ U)
    (hX₀ : ContDiffOn ℝ 1 X₀ U) (hX : ContDiffOn ℝ 1 X U)
    (hK : IsCompact ({p : E × ℝ | p.2 ∈ uIcc (φ₁ p.1) (φ₂ p.1)} ∩ (tsupport X₀ ∪ tsupport X))) :
    ∫ x, (∫ t in φ₁ x..φ₂ x, (deriv (fun s ↦ X₀ (x, s)) t + spatialDivergence X (x, t))) ∂μ =
      (∫ x, (X₀ (x, φ₂ x) - fderiv ℝ φ₂ x (X (x, φ₂ x))) ∂μ) -
        ∫ x, (X₀ (x, φ₁ x) - fderiv ℝ φ₁ x (X (x, φ₁ x))) ∂μ := by
  obtain ⟨Y₀, Y, hY₀, hY₀c, hY, hYc, hD⟩ :=
    exists_contDiff_hasCompactSupport_eventuallyEq_of_contDiffOn hU hDU hX₀ hX hK
  have h₁ : ∀ x, (x, φ₁ x) ∈ {p : E × ℝ | p.2 ∈ uIcc (φ₁ p.1) (φ₂ p.1)} :=
    fun _ ↦ left_mem_uIcc
  have h₂ : ∀ x, (x, φ₂ x) ∈ {p : E × ℝ | p.2 ∈ uIcc (φ₁ p.1) (φ₂ p.1)} :=
    fun _ ↦ right_mem_uIcc
  calc _ = ∫ x, (∫ t in φ₁ x..φ₂ x, (deriv (fun s ↦ Y₀ (x, s)) t + spatialDivergence Y (x, t)))
          ∂μ :=
        integral_congr_ae (Eventually.of_forall fun x ↦ intervalIntegral.integral_congr
          fun t ht ↦ (deriv_add_spatialDivergence_congr (hD (x, t) ht).1 (hD (x, t) ht).2).symm)
    _ = _ := integral_intervalIntegral_divergence hφ₁ hφ₂ hY₀ hY₀c hY hYc
    _ = _ := by
      congr 1 <;> refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      · simp only [(hD _ (h₂ x)).1.eq_of_nhds, (hD _ (h₂ x)).2.eq_of_nhds]
      · simp only [(hD _ (h₁ x)).1.eq_of_nhds, (hD _ (h₁ x)).2.eq_of_nhds]

/-- **Divergence theorem on the closed region between two graphs, for a locally defined vector
field.** Let `φ₁ ≤ φ₂` be `C¹`, and let `D = {(x, t) | φ₁ x ≤ t ≤ φ₂ x}`. If `D` is contained in
an open set `U` on which `X₀` and `X` are `C¹`, and `D ∩ (tsupport X₀ ∪ tsupport X)` is compact,
then the conclusion of `MeasureTheory.integral_divergence_region_between_cc` holds. -/
theorem integral_divergence_region_between_cc_of_contDiffOn {U : Set (E × ℝ)} (hU : IsOpen U)
    (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂) (hφ : φ₁ ≤ φ₂)
    (hDU : {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)} ⊆ U)
    (hX₀ : ContDiffOn ℝ 1 X₀ U) (hX : ContDiffOn ℝ 1 X U)
    (hK : IsCompact ({p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)} ∩ (tsupport X₀ ∪ tsupport X))) :
    ∫ p in {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      (∫ x, (X₀ (x, φ₂ x) - fderiv ℝ φ₂ x (X (x, φ₂ x))) ∂μ) -
        ∫ x, (X₀ (x, φ₁ x) - fderiv ℝ φ₁ x (X (x, φ₁ x))) ∂μ := by
  obtain ⟨Y₀, Y, hY₀, hY₀c, hY, hYc, hD⟩ :=
    exists_contDiff_hasCompactSupport_eventuallyEq_of_contDiffOn hU hDU hX₀ hX hK
  have hs : MeasurableSet {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)} :=
    (measurableSet_le (hφ₁.continuous.measurable.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hφ₂.continuous.measurable.comp measurable_fst))
  have h₁ : ∀ x, (x, φ₁ x) ∈ {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)} :=
    fun x ↦ left_mem_Icc.2 (hφ x)
  have h₂ : ∀ x, (x, φ₂ x) ∈ {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)} :=
    fun x ↦ right_mem_Icc.2 (hφ x)
  calc _ = ∫ p in {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)},
          (deriv (fun t ↦ Y₀ (p.1, t)) p.2 + spatialDivergence Y p) ∂μ.prod volume :=
        setIntegral_congr_fun hs fun p hp ↦
          (deriv_add_spatialDivergence_congr (hD p hp).1 (hD p hp).2).symm
    _ = _ := integral_divergence_region_between_cc hφ₁ hφ₂ hφ hY₀ hY₀c hY hYc
    _ = _ := by
      congr 1 <;> refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      · simp only [(hD _ (h₂ x)).1.eq_of_nhds, (hD _ (h₂ x)).2.eq_of_nhds]
      · simp only [(hD _ (h₁ x)).1.eq_of_nhds, (hD _ (h₁ x)).2.eq_of_nhds]

end MeasureTheory
