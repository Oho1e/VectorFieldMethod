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
`0 < s₁ < s₂`, let `D` be the closed region between the hyperboloids `t = √(s₁ ^ 2 + ‖x‖ ^ 2)` and
`t = √(s₂ ^ 2 + ‖x‖ ^ 2)` in spacetime `E × ℝ`, and let `C = {(x, t) | ‖x‖ ≤ t - 1}` be the closed
solid cone. Since `D(√(s ^ 2 + ‖·‖ ^ 2))(x) v = ⟪x, v⟫ / √(s ^ 2 + ‖x‖ ^ 2)`, the flux of a vector
field `(X₀, X)` through the hyperboloid `t = φ x` is `∫ x, X₀ (x, φ x) - ⟪x, X (x, φ x)⟫ / φ x ∂μ`.
We prove the divergence theorem on `D` with these explicit fluxes, in two versions.

* In the localized version, `X₀` and `X` are only assumed to be `C¹` on an open set `U ⊇ D`, and
  only the points of `D` in their supports are assumed to lie in the cone:
  `D ∩ (tsupport X₀ ∪ tsupport X) ⊆ C`. The values of the field outside `U` play no role.
* In the global version, `X₀` and `X` are `C¹` on all of `E × ℝ` and their supports lie in `C`
  everywhere. Since `‖x‖ ≤ t - 1` forces `t ≥ 1`, this global support condition implies that the
  field vanishes identically for `t < 1`. The global version is deduced from the localized one.

In neither version is the field assumed to be compactly supported. Instead, `D ∩ C` is compact,
hence so is `D ∩ (tsupport X₀ ∪ tsupport X)`, and the localized divergence theorem
`MeasureTheory.integral_divergence_region_between_cc_of_contDiffOn` applies.

A point `(x, t)` of `D ∩ C` satisfies `(‖x‖ + 1) ^ 2 ≤ t ^ 2 ≤ s₂ ^ 2 + ‖x‖ ^ 2`, that is,
`2 * ‖x‖ + 1 ≤ s₂ ^ 2`. So the cone meets `D` only if `s₂ ≥ 1`, and only at `(0, 1)` if `s₂ = 1`.
Hence, for `s₂ ≤ 1`, the field vanishes on `D` and both sides of the identity are `0`: the theorems
have content only for `s₂ > 1`.

## Main statements

* `fderiv_sqrt_sq_add_norm_sq_apply`: the derivative of `x ↦ √(s ^ 2 + ‖x‖ ^ 2)`.
* `MeasureTheory.integral_divergence_between_hyperboloids_of_contDiffOn`: the divergence theorem
  between two hyperboloids for a vector field that is `C¹` near `D` and supported in the cone on
  `D`.
* `MeasureTheory.integral_divergence_between_hyperboloids`: the global version, for a vector field
  that is `C¹` on `E × ℝ` and supported in the cone.

The file ends with a sanity check: the localized version applied to a nonzero vector field.
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

/-- The part of the closed region between the hyperboloids `t = √(s₁ ^ 2 + ‖x‖ ^ 2)` and
`t = √(s₂ ^ 2 + ‖x‖ ^ 2)` which lies in the cone `‖x‖ ≤ t - 1` is compact. -/
theorem isCompact_region_between_hyperboloids_inter_cone [FiniteDimensional ℝ E] (s₁ s₂ : ℝ) :
    IsCompact ({p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)} ∩
      {p | ‖p.1‖ ≤ p.2 - 1}) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (((isClosed_le (by fun_prop) (by fun_prop)).inter
      (isClosed_le (by fun_prop) (by fun_prop))).inter (isClosed_le (by fun_prop) (by fun_prop)))
    (isBounded_iff_forall_norm_le.2 ⟨s₂ ^ 2 + s₂ ^ 4 + 1, fun p hp ↦ ?_⟩)
  obtain ⟨⟨-, hp₂⟩, h₁⟩ := hp
  have h₁ : ‖p.1‖ ≤ p.2 - 1 := h₁
  have ht : 0 ≤ p.2 := by linarith [norm_nonneg p.1]
  have h₂ : p.2 ^ 2 ≤ s₂ ^ 2 + ‖p.1‖ ^ 2 := (Real.le_sqrt ht (by positivity)).1 hp₂
  have h₃ : ‖p.1‖ ≤ s₂ ^ 2 := by
    have h : ‖p.1‖ + 1 ≤ p.2 := by linarith
    nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ ‖p.1‖ + 1) h]
  have h₄ : ‖p.1‖ ^ 2 ≤ s₂ ^ 4 := by
    nlinarith [mul_self_le_mul_self (norm_nonneg p.1) h₃]
  refine norm_prod_le_iff.2 ⟨by nlinarith, ?_⟩
  rw [Real.norm_of_nonneg ht]
  nlinarith [sq_nonneg (p.2 - 1)]

namespace MeasureTheory

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {X₀ : E × ℝ → ℝ} {X : E × ℝ → E}

/-- **Divergence theorem between two hyperboloids, for a locally defined vector field.** Let
`0 < s₁ < s₂` and let `D` be the closed region between the hyperboloids `t = √(s₁ ^ 2 + ‖x‖ ^ 2)`
and `t = √(s₂ ^ 2 + ‖x‖ ^ 2)`. Let `X₀` and `X` be `C¹` on an open set `U ⊇ D`, and assume that the
points of `D` in their supports lie in the cone `‖x‖ ≤ t - 1`:
`D ∩ (tsupport X₀ ∪ tsupport X) ⊆ {p | ‖p.1‖ ≤ p.2 - 1}`. Then the integral of the divergence
`∂ₜ X₀ + div_x X` over `D` is the difference of the fluxes
`∫ x, X₀ (x, φᵢ x) - ⟪x, X (x, φᵢ x)⟫ / φᵢ x ∂μ` through the two hyperboloids, where
`φᵢ x = √(sᵢ ^ 2 + ‖x‖ ^ 2)`.

The values of the field outside `U` play no role, and the support condition only concerns points of
`D`; the field is not assumed to be compactly supported. The cone meets `D` only if `s₂ ≥ 1`, and
only at `(0, 1)` if `s₂ = 1`, so for `s₂ ≤ 1` the field vanishes on `D` and both sides are `0`: the
statement has content only for `s₂ > 1`. -/
theorem integral_divergence_between_hyperboloids_of_contDiffOn {s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) {U : Set (E × ℝ)} (hU : IsOpen U)
    (hDU : {p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)} ⊆ U)
    (hX₀ : ContDiffOn ℝ 1 X₀ U) (hX : ContDiffOn ℝ 1 X U)
    (hsupp : {p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)} ∩
      (tsupport X₀ ∪ tsupport X) ⊆ {p | ‖p.1‖ ≤ p.2 - 1}) :
    ∫ p in {p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      (∫ x, (X₀ (x, √(s₂ ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, X (x, √(s₂ ^ 2 + ‖x‖ ^ 2))⟫ / √(s₂ ^ 2 + ‖x‖ ^ 2)) ∂μ) -
        ∫ x, (X₀ (x, √(s₁ ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, X (x, √(s₁ ^ 2 + ‖x‖ ^ 2))⟫ / √(s₁ ^ 2 + ‖x‖ ^ 2)) ∂μ := by
  have hs₂ : 0 < s₂ := hs₁.trans hs₁₂
  have hφ : (fun x : E ↦ √(s₁ ^ 2 + ‖x‖ ^ 2)) ≤ fun x ↦ √(s₂ ^ 2 + ‖x‖ ^ 2) :=
    fun x ↦ Real.sqrt_le_sqrt (by nlinarith)
  -- the part of the support of the field in the region between the hyperboloids is compact
  have hK : IsCompact ({p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)} ∩
      (tsupport X₀ ∪ tsupport X)) :=
    (isCompact_region_between_hyperboloids_inter_cone s₁ s₂).of_isClosed_subset
      (((isClosed_le (by fun_prop) (by fun_prop)).inter
        (isClosed_le (by fun_prop) (by fun_prop))).inter
        ((isClosed_tsupport _).union (isClosed_tsupport _)))
      fun p hp ↦ ⟨hp.1, hsupp hp⟩
  refine (integral_divergence_region_between_cc_of_contDiffOn (μ := μ) hU
    (contDiff_sqrt_sq_add_norm_sq hs₁.ne') (contDiff_sqrt_sq_add_norm_sq hs₂.ne') hφ
    hDU hX₀ hX hK).trans ?_
  congr 1 <;> refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  · simp only [fderiv_sqrt_sq_add_norm_sq_apply hs₂.ne']
  · simp only [fderiv_sqrt_sq_add_norm_sq_apply hs₁.ne']

/-- **Divergence theorem between two hyperboloids, global version.** Let `0 < s₁ < s₂`, and let
`(X₀, X)` be a `C¹` vector field on all of spacetime `E × ℝ` whose support lies in the cone
`‖x‖ ≤ t - 1`. Then the integral of its divergence `∂ₜ X₀ + div_x X` over the closed region
between the hyperboloids `t = √(s₁ ^ 2 + ‖x‖ ^ 2)` and `t = √(s₂ ^ 2 + ‖x‖ ^ 2)` is the
difference of the fluxes `∫ x, X₀ (x, φᵢ x) - ⟪x, X (x, φᵢ x)⟫ / φᵢ x ∂μ` through the two
hyperboloids, where `φᵢ x = √(sᵢ ^ 2 + ‖x‖ ^ 2)`.

The support condition is imposed on all of `E × ℝ`. Since `‖x‖ ≤ t - 1` forces `t ≥ 1`, it implies
that `X₀` and `X` vanish identically for `t < 1`; for instance, it excludes every solution of a
wave equation that does not vanish at some time `t < 1`. A field that is `C¹` near the region
between the hyperboloids and satisfies the cone condition only there is covered by
`MeasureTheory.integral_divergence_between_hyperboloids_of_contDiffOn`, from which this version is
deduced. As there, the statement has content only for `s₂ > 1`. -/
theorem integral_divergence_between_hyperboloids {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂)
    (hX₀ : ContDiff ℝ 1 X₀) (hX : ContDiff ℝ 1 X)
    (hX₀s : support X₀ ⊆ {p | ‖p.1‖ ≤ p.2 - 1}) (hXs : support X ⊆ {p | ‖p.1‖ ≤ p.2 - 1}) :
    ∫ p in {p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      (∫ x, (X₀ (x, √(s₂ ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, X (x, √(s₂ ^ 2 + ‖x‖ ^ 2))⟫ / √(s₂ ^ 2 + ‖x‖ ^ 2)) ∂μ) -
        ∫ x, (X₀ (x, √(s₁ ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, X (x, √(s₁ ^ 2 + ‖x‖ ^ 2))⟫ / √(s₁ ^ 2 + ‖x‖ ^ 2)) ∂μ := by
  have hC : IsClosed {p : E × ℝ | ‖p.1‖ ≤ p.2 - 1} := isClosed_le (by fun_prop) (by fun_prop)
  exact integral_divergence_between_hyperboloids_of_contDiffOn hs₁ hs₁₂ isOpen_univ
    (subset_univ _) hX₀.contDiffOn hX.contDiffOn
    (inter_subset_right.trans (union_subset (closure_minimal hX₀s hC) (closure_minimal hXs hC)))

end MeasureTheory

/-! ### Sanity checks

The hypotheses of `MeasureTheory.integral_divergence_between_hyperboloids_of_contDiffOn` are
satisfied by a nonzero vector field: on `EuclideanSpace ℝ (Fin 3) × ℝ`, take for `X₀` a smooth
bump function centered at `(0, 3)` with outer radius `1 / 2`, and `X = 0`. Its support lies in
`{‖x‖ ≤ 1 / 2, t ≥ 5 / 2}`, hence in the cone `‖x‖ ≤ t - 1`. -/

section SanityChecks

open MeasureTheory

/-- A smooth bump function on `EuclideanSpace ℝ (Fin 3) × ℝ` centered at `(0, 3)`: it equals `1` on
the closed ball of radius `1 / 4` and vanishes outside the open ball of radius `1 / 2` (balls for
the max norm of the product, so the support lies in `{‖x‖ ≤ 1 / 2, |t - 3| ≤ 1 / 2}`). -/
private def sanityBump : ContDiffBump ((0 : EuclideanSpace ℝ (Fin 3)), (3 : ℝ)) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The bump function is not zero: it equals `1` at its center. -/
example : sanityBump ((0 : EuclideanSpace ℝ (Fin 3)), (3 : ℝ)) = 1 :=
  sanityBump.one_of_mem_closedBall (Metric.mem_closedBall_self sanityBump.rIn_pos.le)

/-- The localized divergence theorem between the hyperboloids `s₁ = 2` and `s₂ = 4`, applied to
`X₀ = sanityBump`, `X = 0` and `U = {t > 0}`. -/
example :
    ∫ p in {p : EuclideanSpace ℝ (Fin 3) × ℝ |
        p.2 ∈ Icc √(2 ^ 2 + ‖p.1‖ ^ 2) √(4 ^ 2 + ‖p.1‖ ^ 2)},
        (deriv (fun t ↦ sanityBump (p.1, t)) p.2 +
          spatialDivergence (fun _ ↦ (0 : EuclideanSpace ℝ (Fin 3))) p) ∂volume.prod volume =
      (∫ x, (sanityBump (x, √(4 ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, (0 : EuclideanSpace ℝ (Fin 3))⟫ / √(4 ^ 2 + ‖x‖ ^ 2))) -
        ∫ x, (sanityBump (x, √(2 ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, (0 : EuclideanSpace ℝ (Fin 3))⟫ / √(2 ^ 2 + ‖x‖ ^ 2)) := by
  refine integral_divergence_between_hyperboloids_of_contDiffOn (μ := volume)
    (X₀ := sanityBump) (X := fun _ ↦ 0) (U := {p | 0 < p.2}) (by norm_num) (by norm_num)
    (isOpen_lt continuous_const continuous_snd) ?_ (sanityBump.contDiff (n := 1)).contDiffOn
    contDiffOn_const ?_
  · -- the region between the hyperboloids lies in `{t > 0}`
    exact fun p hp ↦ (Real.sqrt_pos.2 (by positivity)).trans_le hp.1
  · -- the support of the field lies in the cone
    rintro p ⟨-, hp⟩
    have hp' : p ∈ tsupport sanityBump := by simpa using hp
    rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, Prod.dist_eq, max_le_iff,
      dist_zero_right, Real.dist_eq, abs_le] at hp'
    obtain ⟨h₁, h₂, -⟩ := hp'
    have hr : sanityBump.rOut = 1 / 2 := rfl
    rw [hr] at h₁ h₂
    change ‖p.1‖ ≤ p.2 - 1
    linarith

end SanityChecks
