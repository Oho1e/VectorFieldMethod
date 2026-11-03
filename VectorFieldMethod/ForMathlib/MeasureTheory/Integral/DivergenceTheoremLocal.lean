/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.ForMathlib.Geometry.Manifold.PartitionOfUnity
public import VectorFieldMethod.ForMathlib.MeasureTheory.Integral.DivergenceTheoremHypograph

import Mathlib.Analysis.Calculus.BumpFunction.Normed

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
  refine ⟨Y₀, Y, hY₀, hY₀c, hY, hYc, fun p hp ↦ ?_⟩
  by_cases h : p ∈ tsupport X₀ ∪ tsupport X
  · exact ⟨hY₀e p (.inl ⟨hp, h⟩), hYe p (.inl ⟨hp, h⟩)⟩
  · exact ⟨hY₀e p (.inr fun h' ↦ h (.inl h')), hYe p (.inr fun h' ↦ h (.inr h'))⟩

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

/-! ### Sanity checks

Both theorems of this file have hypotheses beyond regularity: the region `D` between the graphs
lies in the open set `U`, and `D ∩ (tsupport X₀ ∪ tsupport X)` is compact. Each is applied below to
the same explicit vector field, which is not compactly supported, so that the corresponding
theorems of `DivergenceTheoremHypograph.lean` do not apply to it. The data are as follows.

* `E = ℝ` with Lebesgue measure, `X = 0`, `U = ℝ × ℝ`, `φ₁ = -1` and `φ₂ = 0`, so that `D` is the
  strip `ℝ × [-1, 0]`.
* `X₀ (x, t) = ψ x * (t + 2)`, where `ψ` is a smooth bump function on `ℝ` that equals `1` on
  `[-1 / 4, 1 / 4]` and vanishes outside `(-1 / 2, 1 / 2)`.

The support of `X₀` lies in `[-1 / 2, 1 / 2] × ℝ`, so its intersection with `D` is compact.
Neither identity is a trivial `0 = 0`. Since `∂ₜ X₀ (x, t) = ψ x` and `X = 0`, the left-hand sides
equal `∫ x, ψ x`. The right-hand sides equal `∫ x, 2 * ψ x - ∫ x, ψ x = ∫ x, ψ x`, which is
positive because `ψ` is continuous, nonnegative and equal to `1` near `0`; the last example proves
this. -/

section SanityChecks

open MeasureTheory

/-- A smooth bump function on `ℝ` centered at `0`: it equals `1` on `[-1 / 4, 1 / 4]` and vanishes
outside `(-1 / 2, 1 / 2)`. -/
private def sanityBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The time component `(x, t) ↦ ψ x * (t + 2)` of the vector field of the sanity checks: it is
smooth, but not compactly supported. -/
private def sanityX₀ (p : ℝ × ℝ) : ℝ :=
  sanityBump p.1 * (p.2 + 2)

private theorem contDiff_sanityX₀ : ContDiff ℝ 1 sanityX₀ :=
  ((sanityBump.contDiff (n := 1)).comp contDiff_fst).mul (contDiff_snd.add contDiff_const)

/-- The part of the strip `ℝ × [-1, 0]` in the support of the field is compact. -/
private theorem isCompact_sanity :
    IsCompact ({p : ℝ × ℝ | p.2 ∈ Icc (-1) 0} ∩
      (tsupport sanityX₀ ∪ tsupport fun _ : ℝ × ℝ ↦ (0 : ℝ))) := by
  refine (IsCompact.prod (isCompact_closedBall (0 : ℝ) (1 / 2))
    (isCompact_Icc (a := (-1 : ℝ)) (b := 0))).of_isClosed_subset
    ((isClosed_Icc.preimage continuous_snd).inter
      ((isClosed_tsupport _).union (isClosed_tsupport _))) ?_
  rintro p ⟨hp₂, hp⟩
  refine ⟨?_, hp₂⟩
  have hsub : tsupport sanityX₀ ⊆ {q : ℝ × ℝ | q.1 ∈ Metric.closedBall 0 (1 / 2)} := by
    refine closure_minimal (fun q hq ↦ ?_) (Metric.isClosed_closedBall.preimage continuous_fst)
    have h : sanityBump q.1 * (q.2 + 2) ≠ 0 := hq
    have h' : q.1 ∈ tsupport sanityBump := subset_tsupport _ (left_ne_zero_of_mul h)
    rwa [sanityBump.tsupport_eq] at h'
  rcases hp with hp | hp
  · exact hsub hp
  · simp at hp

/-- `MeasureTheory.integral_intervalIntegral_divergence_of_contDiffOn` with `φ₁ = -1`, `φ₂ = 0`,
`U = ℝ × ℝ`, `X₀ (x, t) = ψ x * (t + 2)` and `X = 0`: both sides equal `∫ x, ψ x`. -/
example :
    ∫ x, (∫ t in (-1 : ℝ)..0, (deriv (fun s ↦ sanityX₀ (x, s)) t +
        spatialDivergence (fun _ ↦ (0 : ℝ)) (x, t))) =
      (∫ x, (sanityX₀ (x, 0) - fderiv ℝ (fun _ ↦ (0 : ℝ)) x 0)) -
        ∫ x, (sanityX₀ (x, -1) - fderiv ℝ (fun _ ↦ (-1 : ℝ)) x 0) := by
  have hK := isCompact_sanity
  rw [← Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hK
  exact integral_intervalIntegral_divergence_of_contDiffOn (φ₁ := fun _ ↦ -1) (φ₂ := fun _ ↦ 0)
    (X := fun _ ↦ 0) isOpen_univ contDiff_const contDiff_const (subset_univ _)
    contDiff_sanityX₀.contDiffOn contDiffOn_const hK

/-- `MeasureTheory.integral_divergence_region_between_cc_of_contDiffOn` with `φ₁ = -1 ≤ φ₂ = 0`,
`U = ℝ × ℝ`, `X₀ (x, t) = ψ x * (t + 2)` and `X = 0`: both sides equal `∫ x, ψ x`. -/
example :
    ∫ p in {p : ℝ × ℝ | p.2 ∈ Icc (-1) 0},
        (deriv (fun t ↦ sanityX₀ (p.1, t)) p.2 + spatialDivergence (fun _ ↦ (0 : ℝ)) p)
          ∂volume.prod volume =
      (∫ x, (sanityX₀ (x, 0) - fderiv ℝ (fun _ ↦ (0 : ℝ)) x 0)) -
        ∫ x, (sanityX₀ (x, -1) - fderiv ℝ (fun _ ↦ (-1 : ℝ)) x 0) :=
  integral_divergence_region_between_cc_of_contDiffOn (φ₁ := fun _ ↦ -1) (φ₂ := fun _ ↦ 0)
    (X := fun _ ↦ 0) isOpen_univ contDiff_const contDiff_const (fun _ ↦ by norm_num)
    (subset_univ _) contDiff_sanityX₀.contDiffOn contDiffOn_const isCompact_sanity

/-- The common right-hand side of the two examples above is positive, so that neither identity is a
trivial `0 = 0`: it equals `∫ x, 2 * ψ x - ∫ x, ψ x = ∫ x, ψ x > 0`. -/
example :
    0 < (∫ x, (sanityX₀ (x, 0) - fderiv ℝ (fun _ ↦ (0 : ℝ)) x 0)) -
      ∫ x, (sanityX₀ (x, -1) - fderiv ℝ (fun _ ↦ (-1 : ℝ)) x 0) := by
  have h := sanityBump.integral_pos (μ := volume)
  simp only [sanityX₀, fderiv_const_apply, zero_apply, sub_zero, integral_mul_const]
  norm_num
  linarith

end SanityChecks
