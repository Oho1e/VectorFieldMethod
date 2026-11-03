/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.ForMathlib.MeasureTheory.Integral.DivergenceTheoremLocal
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The divergence theorem between two hyperboloids

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`. For
`0 < s₁ < s₂`, consider the region between the hyperboloids `t = √(sᵢ ^ 2 + ‖x‖ ^ 2)` in spacetime
`E × ℝ`, and a `C¹` vector field `(X₀, X)` on `E × ℝ` supported in `{(x, t) | ‖x‖ ≤ t - 1}`, a
typical situation for solutions of wave equations with compactly supported initial data. The
vector field is not assumed to be compactly supported, but its support meets the region between the
hyperboloids in a compact set, so the localized divergence theorem
`MeasureTheory.integral_divergence_region_between_cc_of_contDiffOn` applies. Since
`D(√(s ^ 2 + ‖·‖ ^ 2))(x) v = ⟪x, v⟫ / √(s ^ 2 + ‖x‖ ^ 2)`, the flux through the hyperboloid
`t = φ x` is `∫ x, X₀ (x, φ x) - ⟪x, X (x, φ x)⟫ / φ x ∂μ`.

## Main statements

* `fderiv_sqrt_sq_add_norm_sq_apply`: the derivative of `x ↦ √(s ^ 2 + ‖x‖ ^ 2)`.
* `MeasureTheory.integral_divergence_between_hyperboloids`: the divergence theorem between two
  hyperboloids, with explicit fluxes.
-/

@[expose] public noncomputable section

open Set Filter Function Topology

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The function `x ↦ √(s ^ 2 + ‖x‖ ^ 2)`, whose graph is the hyperboloid `t ^ 2 - ‖x‖ ^ 2 = s ^ 2`,
`t > 0`, is `C¹` if `s ≠ 0`. -/
theorem contDiff_sqrt_sq_add_norm_sq {s : ℝ} (hs : s ≠ 0) :
    ContDiff ℝ 1 fun x : E ↦ √(s ^ 2 + ‖x‖ ^ 2) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun x ↦ by positivity

/-- The derivative of `x ↦ √(s ^ 2 + ‖x‖ ^ 2)` at `x` maps `v` to `⟪x, v⟫ / √(s ^ 2 + ‖x‖ ^ 2)`. -/
theorem fderiv_sqrt_sq_add_norm_sq_apply {s : ℝ} (hs : s ≠ 0) (x v : E) :
    fderiv ℝ (fun y : E ↦ √(s ^ 2 + ‖y‖ ^ 2)) x v = ⟪x, v⟫ / √(s ^ 2 + ‖x‖ ^ 2) := by
  have hpos : s ^ 2 + ‖x‖ ^ 2 ≠ 0 := by positivity
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add (s ^ 2)).sqrt hpos
  rw [h.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  field_simp

namespace MeasureTheory

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {X₀ : E × ℝ → ℝ} {X : E × ℝ → E}

/-- **Divergence theorem between two hyperboloids.** Let `0 < s₁ < s₂`, and let
`(X₀, X)` be a `C¹` vector field on spacetime `E × ℝ` supported in the region `‖x‖ ≤ t - 1`.
Then the integral of its divergence `∂ₜ X₀ + div_x X` over the region between the hyperboloids
`t = √(s₁ ^ 2 + ‖x‖ ^ 2)` and `t = √(s₂ ^ 2 + ‖x‖ ^ 2)` is the difference of the fluxes
`∫ x, X₀ (x, φᵢ x) - ⟪x, X (x, φᵢ x)⟫ / φᵢ x ∂μ` through the two hyperboloids, where
`φᵢ x = √(sᵢ ^ 2 + ‖x‖ ^ 2)`. -/
theorem integral_divergence_between_hyperboloids {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂)
    (hX₀ : ContDiff ℝ 1 X₀) (hX : ContDiff ℝ 1 X)
    (hX₀s : support X₀ ⊆ {p | ‖p.1‖ ≤ p.2 - 1}) (hXs : support X ⊆ {p | ‖p.1‖ ≤ p.2 - 1}) :
    ∫ p in {p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      (∫ x, (X₀ (x, √(s₂ ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, X (x, √(s₂ ^ 2 + ‖x‖ ^ 2))⟫ / √(s₂ ^ 2 + ‖x‖ ^ 2)) ∂μ) -
        ∫ x, (X₀ (x, √(s₁ ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, X (x, √(s₁ ^ 2 + ‖x‖ ^ 2))⟫ / √(s₁ ^ 2 + ‖x‖ ^ 2)) ∂μ := by
  have hs₂ : 0 < s₂ := hs₁.trans hs₁₂
  have hφ : (fun x : E ↦ √(s₁ ^ 2 + ‖x‖ ^ 2)) ≤ fun x ↦ √(s₂ ^ 2 + ‖x‖ ^ 2) :=
    fun x ↦ Real.sqrt_le_sqrt (by nlinarith)
  -- the supports lie in the closed set `{‖x‖ ≤ t - 1}`
  have hC : IsClosed {p : E × ℝ | ‖p.1‖ ≤ p.2 - 1} := isClosed_le (by fun_prop) (by fun_prop)
  have hsupp : tsupport X₀ ∪ tsupport X ⊆ {p : E × ℝ | ‖p.1‖ ≤ p.2 - 1} :=
    union_subset (closure_minimal hX₀s hC) (closure_minimal hXs hC)
  -- the part of the support between the hyperboloids is compact
  have hK : IsCompact ({p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)} ∩
      (tsupport X₀ ∪ tsupport X)) := by
    refine Metric.isCompact_of_isClosed_isBounded
      (((isClosed_le (by fun_prop) (by fun_prop)).inter
        (isClosed_le (by fun_prop) (by fun_prop))).inter
        ((isClosed_tsupport _).union (isClosed_tsupport _)))
      (isBounded_iff_forall_norm_le.2 ⟨s₂ + s₂ ^ 2, fun p hp ↦ ?_⟩)
    obtain ⟨⟨-, hp₂⟩, hpC⟩ := hp
    have h₁ : ‖p.1‖ ≤ p.2 - 1 := hsupp hpC
    have ht : 0 ≤ p.2 := by linarith [norm_nonneg p.1]
    have h₂ : p.2 ^ 2 ≤ s₂ ^ 2 + ‖p.1‖ ^ 2 := (Real.le_sqrt ht (by positivity)).1 hp₂
    have h₃ : ‖p.1‖ ≤ s₂ ^ 2 := by
      have h : ‖p.1‖ + 1 ≤ p.2 := by linarith
      nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ ‖p.1‖ + 1) h]
    have h₄ : p.2 ≤ s₂ + s₂ ^ 2 := by
      have h : s₂ ^ 2 + ‖p.1‖ ^ 2 ≤ (s₂ + s₂ ^ 2) ^ 2 := by
        nlinarith [mul_self_le_mul_self (norm_nonneg p.1) h₃, pow_pos hs₂ 3]
      calc p.2 ≤ √(s₂ ^ 2 + ‖p.1‖ ^ 2) := hp₂
        _ ≤ √((s₂ + s₂ ^ 2) ^ 2) := Real.sqrt_le_sqrt h
        _ = s₂ + s₂ ^ 2 := Real.sqrt_sq (by positivity)
    refine norm_prod_le_iff.2 ⟨by nlinarith, ?_⟩
    rwa [Real.norm_of_nonneg ht]
  refine (integral_divergence_region_between_cc_of_contDiffOn (μ := μ) isOpen_univ
    (contDiff_sqrt_sq_add_norm_sq hs₁.ne') (contDiff_sqrt_sq_add_norm_sq hs₂.ne') hφ
    (subset_univ _) hX₀.contDiffOn hX.contDiffOn hK).trans ?_
  congr 1 <;> refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  · simp only [fderiv_sqrt_sq_add_norm_sq_apply hs₂.ne']
  · simp only [fderiv_sqrt_sq_add_norm_sq_apply hs₁.ne']

end MeasureTheory
