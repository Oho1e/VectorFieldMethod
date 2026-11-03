/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.ForMathlib.MeasureTheory.Integral.DivergenceTheoremHypograph
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The divergence theorem between two graphs, for locally defined vector fields

The divergence theorems of `Mathlib.MeasureTheory.Integral.DivergenceTheoremHypograph` (in this
project, `VectorFieldMethod.ForMathlib.MeasureTheory.Integral.DivergenceTheoremHypograph`) assume
that the vector field `(X₀, X)` on spacetime `E × ℝ` is `C¹` and compactly supported. Here we only
assume that it is `C¹` on an open set `U` containing the closed region `D` between the graphs of two
`C¹` functions `φ₁, φ₂ : E → ℝ`, and that `D ∩ (tsupport X₀ ∪ tsupport X)` is compact. The proof
multiplies `(X₀, X)` by a smooth cutoff function which is equal to `1` near
`D ∩ (tsupport X₀ ∪ tsupport X)` and supported in `U`, and applies the compactly supported case.

## Main statements

* `ContDiffOn.exists_contDiff_hasCompactSupport_eventuallyEq`: a function which is `C¹` on an open
  set `U` coincides near a compact set `K ⊆ U`, and near every point outside its support, with a
  compactly supported `C¹` function.
* `MeasureTheory.integral_intervalIntegral_divergence_of_contDiffOn`: the divergence theorem
  between two graphs, in any order, as an iterated integral.
* `MeasureTheory.integral_divergence_region_between_cc_of_contDiffOn`: the divergence theorem on
  the closed region between two graphs `φ₁ ≤ φ₂`, as a set integral.
-/

@[expose] public noncomputable section

open Set Filter Function Topology

section Cutoff

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function which is `C¹` on an open set `U` coincides, near every point of a compact set
`K ⊆ U` and near every point outside its support, with a compactly supported `C¹` function. -/
theorem ContDiffOn.exists_contDiff_hasCompactSupport_eventuallyEq {f : G → F} {U K : Set G}
    (hf : ContDiffOn ℝ 1 f U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g : G → F, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧
      ∀ x, x ∈ K ∨ x ∉ tsupport f → g =ᶠ[𝓝 x] f := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨L', hL'c, hLL', hL'U⟩ := exists_compact_between hLc hU hLU
  obtain ⟨χ, hχd, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) isOpen_interior hLc.isClosed hLL'
  have hχt : tsupport χ ⊆ L' := closure_minimal (hχs ▸ interior_subset) hL'c.isClosed
  refine ⟨χ • f, contDiff_iff_contDiffAt.2 fun x ↦ ?_, ?_, ?_⟩
  · by_cases hx : x ∈ U
    · exact hχd.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have h : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hx (hL'U (hχt h))
      exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
        (h.mono fun y hy ↦ by simp [hy])
  · exact HasCompactSupport.of_support_subset_isCompact hL'c
      ((support_smul_subset_left χ f).trans (subset_tsupport χ |>.trans hχt))
  · rintro x (hx | hx)
    · filter_upwards [isOpen_interior.mem_nhds (hKL hx)] with y hy
      simp [(hχ1 y).1 (interior_subset hy)]
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]

end Cutoff

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
