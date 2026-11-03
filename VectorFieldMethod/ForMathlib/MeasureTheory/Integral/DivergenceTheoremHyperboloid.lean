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

* In the localized version, only the behaviour of the field near `D` matters. The points of `D` in
  the supports of `X₀` and `X` are assumed to lie in the cone, `D ∩ (tsupport X₀ ∪ tsupport X) ⊆ C`,
  that is, the field vanishes near every point of `D` outside `C`; and `X₀`, `X` are assumed to be
  `C¹` on an open set `U ⊇ D ∩ C`. For instance, a field that is only defined, and `C¹`, on an open
  time slab containing `D ∩ C`, and is extended by zero outside it, can be used if it is supported
  in `C` on the slab.
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

* `contDiff_sqrt_sq_add_norm_sq`: the function `x ↦ √(s ^ 2 + ‖x‖ ^ 2)` is `C¹` for `s ≠ 0`.
* `fderiv_sqrt_sq_add_norm_sq_apply`: the derivative of `x ↦ √(s ^ 2 + ‖x‖ ^ 2)`.
* `isCompact_region_between_hyperboloids_inter_cone`: `D ∩ C` is compact.
* `MeasureTheory.integral_divergence_between_hyperboloids_of_contDiffOn`: the divergence theorem
  between two hyperboloids for a vector field that is `C¹` near `D ∩ C` and vanishes near the other
  points of `D`.
* `MeasureTheory.integral_divergence_between_hyperboloids`: the global version, for a vector field
  that is `C¹` on `E × ℝ` and supported in the cone.

The file ends with sanity checks, three `example`s about one explicit vector field, for which both
sides of the identity of the localized version are nonzero and the global version does not apply.
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
and `t = √(s₂ ^ 2 + ‖x‖ ^ 2)`, and `C = {p | ‖p.1‖ ≤ p.2 - 1}` the cone `‖x‖ ≤ t - 1`. Assume that
the points of `D` in the supports of `X₀` and `X` lie in `C`,
`D ∩ (tsupport X₀ ∪ tsupport X) ⊆ C`, and that `X₀` and `X` are `C¹` on an open set `U` containing
`D ∩ C`. Then the integral of the divergence `∂ₜ X₀ + div_x X` over `D` is the difference of the
fluxes `∫ x, X₀ (x, φᵢ x) - ⟪x, X (x, φᵢ x)⟫ / φᵢ x ∂μ` through the two hyperboloids, where
`φᵢ x = √(sᵢ ^ 2 + ‖x‖ ^ 2)`.

Only the behaviour of the field near `D` matters: by the support condition, it vanishes near every
point of `D` outside `C`, and it has to be `C¹` near `D ∩ C`. It is not assumed to be compactly
supported, nor to be differentiable away from `U`. The cone meets `D` only if `s₂ ≥ 1`, and only at
`(0, 1)` if `s₂ = 1`, so for `s₂ ≤ 1` the field vanishes on `D` and both sides are `0`: the
statement has content only for `s₂ > 1`. -/
theorem integral_divergence_between_hyperboloids_of_contDiffOn {s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) {U : Set (E × ℝ)} (hU : IsOpen U)
    (hDU : {p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)} ∩
      {p | ‖p.1‖ ≤ p.2 - 1} ⊆ U)
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
  -- enlarge `U` by the open set where the field vanishes: the result contains the whole region
  -- between the hyperboloids, and the field is `C¹` on it
  set V := (tsupport X₀ ∪ tsupport X)ᶜ
  have hVo : IsOpen V := ((isClosed_tsupport _).union (isClosed_tsupport _)).isOpen_compl
  have hDU' : {p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)} ⊆ U ∪ V := by
    intro p hp
    by_cases h : p ∈ tsupport X₀ ∪ tsupport X
    · exact Or.inl (hDU ⟨hp, hsupp ⟨hp, h⟩⟩)
    · exact Or.inr h
  have hX₀' : ContDiffOn ℝ 1 X₀ (U ∪ V) := by
    rintro p (hp | hp)
    · exact (hX₀.contDiffAt (hU.mem_nhds hp)).contDiffWithinAt
    · exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hp (Or.inl h))).contDiffWithinAt
  have hX' : ContDiffOn ℝ 1 X (U ∪ V) := by
    rintro p (hp | hp)
    · exact (hX.contDiffAt (hU.mem_nhds hp)).contDiffWithinAt
    · exact ((contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hp (Or.inr h))).contDiffWithinAt
  -- the part of the support of the field in the region between the hyperboloids is compact
  have hK : IsCompact ({p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)} ∩
      (tsupport X₀ ∪ tsupport X)) :=
    (isCompact_region_between_hyperboloids_inter_cone s₁ s₂).of_isClosed_subset
      (((isClosed_le (by fun_prop) (by fun_prop)).inter
        (isClosed_le (by fun_prop) (by fun_prop))).inter
        ((isClosed_tsupport _).union (isClosed_tsupport _)))
      fun p hp ↦ ⟨hp.1, hsupp hp⟩
  refine (integral_divergence_region_between_cc_of_contDiffOn (μ := μ) (hU.union hVo)
    (contDiff_sqrt_sq_add_norm_sq hs₁.ne') (contDiff_sqrt_sq_add_norm_sq hs₂.ne') hφ
    hDU' hX₀' hX' hK).trans ?_
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
wave equation that does not vanish at some time `t < 1`. A field that satisfies the cone condition
only on the region between the hyperboloids, and is `C¹` only near the part of that region in the
cone, is covered by `MeasureTheory.integral_divergence_between_hyperboloids_of_contDiffOn`, from
which this version is deduced. As there, the statement has content only for `s₂ > 1`. -/
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

The following vector field on `EuclideanSpace ℝ (Fin 3) × ℝ` satisfies the hypotheses of
`MeasureTheory.integral_divergence_between_hyperboloids_of_contDiffOn` for the hyperboloids
`s₁ = 2`, `s₂ = 4`, with `U` the whole space and `X = 0`, but not those of the global version, and
both sides of the identity are nonzero. Its time component `X₀` is the sum of two smooth bump
functions with `rIn = 1 / 4` and `rOut = 1 / 2` (balls for the max norm of the product):

* `sanityBumpUpper`, centered at `(0, 4)`, which straddles the upper hyperboloid
  `t = √(4 ^ 2 + ‖x‖ ^ 2)` and is supported in `{‖x‖ ≤ 1 / 2, t ≥ 7 / 2}`, inside the cone
  `‖x‖ ≤ t - 1`;
* `sanityBumpOrigin`, centered at `(0, 0)`, which is not supported in the cone, so the global
  version does not apply to `X₀`; but the region `D` between the hyperboloids lies in `{t ≥ 2}` and
  does not meet its support, and the support condition of the localized version is only checked on
  `D`.

The lower flux is `0`, since neither bump meets the lower hyperboloid `t = √(2 ^ 2 + ‖x‖ ^ 2)`. The
upper flux is positive: for `‖x‖ < 1 / 4` one has `4 ≤ √(4 ^ 2 + ‖x‖ ^ 2) ≤ 4 + 1 / 4`, so the
integrand `X₀ (x, √(4 ^ 2 + ‖x‖ ^ 2))` equals `1` there; since it is nonnegative, the upper flux is
at least the volume of the ball of radius `1 / 4`. The three examples below prove that `X₀` is not
supported in the cone, apply the localized version, and prove that the right-hand side of its
conclusion is positive. -/

section SanityChecks

open MeasureTheory

/-- A smooth bump function on `EuclideanSpace ℝ (Fin 3) × ℝ` centered at `(0, 4)`, a point of the
hyperboloid `t = √(4 ^ 2 + ‖x‖ ^ 2)`: it equals `1` on the closed ball of radius `1 / 4` and
vanishes outside the open ball of radius `1 / 2` (balls for the max norm of the product). -/
private def sanityBumpUpper : ContDiffBump ((0 : EuclideanSpace ℝ (Fin 3)), (4 : ℝ)) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The same bump function, centered at `(0, 0)`, a point outside the cone `‖x‖ ≤ t - 1`. -/
private def sanityBumpOrigin : ContDiffBump ((0 : EuclideanSpace ℝ (Fin 3)), (0 : ℝ)) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The time component of the vector field of the sanity checks. -/
private def sanityX₀ (p : EuclideanSpace ℝ (Fin 3) × ℝ) : ℝ :=
  sanityBumpUpper p + sanityBumpOrigin p

private theorem dist_zero_prod (p : EuclideanSpace ℝ (Fin 3) × ℝ) (c : ℝ) :
    dist p ((0 : EuclideanSpace ℝ (Fin 3)), c) = max ‖p.1‖ |p.2 - c| := by
  rw [Prod.dist_eq, dist_zero_right, Real.dist_eq]

private theorem sanityBumpOrigin_eq_zero {p : EuclideanSpace ℝ (Fin 3) × ℝ} (hp : 1 / 2 ≤ p.2) :
    sanityBumpOrigin p = 0 :=
  sanityBumpOrigin.zero_of_le_dist <| by
    rw [dist_zero_prod, sub_zero]
    exact le_max_of_le_right (hp.trans (le_abs_self _))

private theorem sanityBumpUpper_eq_zero {p : EuclideanSpace ℝ (Fin 3) × ℝ}
    (hp : 1 / 2 ≤ ‖p.1‖ ∨ 1 / 2 ≤ |p.2 - 4|) : sanityBumpUpper p = 0 :=
  sanityBumpUpper.zero_of_le_dist <| by
    rw [dist_zero_prod]
    exact le_max_iff.2 hp

/-- `X₀` is not supported in the cone `‖x‖ ≤ t - 1`, so the global version
`MeasureTheory.integral_divergence_between_hyperboloids` does not apply to it. -/
example : ¬ support sanityX₀ ⊆ {p | ‖p.1‖ ≤ p.2 - 1} := by
  intro h
  have h₁ : sanityBumpUpper ((0 : EuclideanSpace ℝ (Fin 3)), (0 : ℝ)) = 0 :=
    sanityBumpUpper_eq_zero (Or.inr (by norm_num))
  have h₂ : sanityBumpOrigin ((0 : EuclideanSpace ℝ (Fin 3)), (0 : ℝ)) = 1 :=
    sanityBumpOrigin.one_of_mem_closedBall (Metric.mem_closedBall_self sanityBumpOrigin.rIn_pos.le)
  have h₀ : ((0 : EuclideanSpace ℝ (Fin 3)), (0 : ℝ)) ∈ support sanityX₀ := by
    rw [Function.mem_support, sanityX₀, h₁, h₂]
    norm_num
  have h₀' := h h₀
  norm_num at h₀'

/-- The localized divergence theorem between the hyperboloids `s₁ = 2` and `s₂ = 4`, applied to
`X₀ = sanityX₀`, `X = 0` and `U` the whole space. -/
example :
    ∫ p in {p : EuclideanSpace ℝ (Fin 3) × ℝ |
        p.2 ∈ Icc √(2 ^ 2 + ‖p.1‖ ^ 2) √(4 ^ 2 + ‖p.1‖ ^ 2)},
        (deriv (fun t ↦ sanityX₀ (p.1, t)) p.2 +
          spatialDivergence (fun _ ↦ (0 : EuclideanSpace ℝ (Fin 3))) p) ∂volume.prod volume =
      (∫ x, (sanityX₀ (x, √(4 ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, (0 : EuclideanSpace ℝ (Fin 3))⟫ / √(4 ^ 2 + ‖x‖ ^ 2))) -
        ∫ x, (sanityX₀ (x, √(2 ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, (0 : EuclideanSpace ℝ (Fin 3))⟫ / √(2 ^ 2 + ‖x‖ ^ 2)) := by
  refine integral_divergence_between_hyperboloids_of_contDiffOn (μ := volume)
    (X₀ := sanityX₀) (X := fun _ ↦ 0) (U := univ) (by norm_num) (by norm_num) isOpen_univ
    (subset_univ _)
    ((sanityBumpUpper.contDiff (n := 1)).add (sanityBumpOrigin.contDiff (n := 1))).contDiffOn
    contDiffOn_const ?_
  -- on the region between the hyperboloids, the support of the field lies in the cone
  rintro p ⟨hpD, hp⟩
  have ht : 2 ≤ p.2 :=
    ((Real.le_sqrt' (by norm_num)).2 (by nlinarith [norm_nonneg p.1])).trans hpD.1
  have hp₁ : p ∈ tsupport sanityX₀ := by simpa using hp
  have hp' : p ∈ tsupport sanityBumpUpper ∪ tsupport sanityBumpOrigin :=
    tsupport_add (⇑sanityBumpUpper) (⇑sanityBumpOrigin) hp₁
  rcases hp' with hp' | hp'
  · rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, dist_zero_prod, max_le_iff] at hp'
    obtain ⟨h₁, -⟩ := hp'
    change ‖p.1‖ ≤ p.2 - 1
    have hr : sanityBumpUpper.rOut = 1 / 2 := rfl
    linarith
  · rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, dist_zero_prod, max_le_iff, sub_zero,
      abs_le] at hp'
    have hr : sanityBumpOrigin.rOut = 1 / 2 := rfl
    linarith [hp'.2.2]

/-- The right-hand side of the previous example is positive: the lower flux vanishes, and the
integrand of the upper flux is nonnegative and equal to `1` for `‖x‖ < 1 / 4`. -/
example :
    0 < (∫ x, (sanityX₀ (x, √(4 ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, (0 : EuclideanSpace ℝ (Fin 3))⟫ / √(4 ^ 2 + ‖x‖ ^ 2))) -
        ∫ x, (sanityX₀ (x, √(2 ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, (0 : EuclideanSpace ℝ (Fin 3))⟫ / √(2 ^ 2 + ‖x‖ ^ 2)) := by
  simp only [inner_zero_right, zero_div, sub_zero]
  -- the lower flux vanishes
  have hlow (x : EuclideanSpace ℝ (Fin 3)) : sanityX₀ (x, √(2 ^ 2 + ‖x‖ ^ 2)) = 0 := by
    have h₂ : (2 : ℝ) ≤ √(2 ^ 2 + ‖x‖ ^ 2) :=
      (Real.le_sqrt' (by norm_num)).2 (by nlinarith [norm_nonneg x])
    have hb : sanityBumpUpper (x, √(2 ^ 2 + ‖x‖ ^ 2)) = 0 := by
      refine sanityBumpUpper_eq_zero ?_
      by_cases hx : 1 / 2 ≤ ‖x‖
      · exact Or.inl hx
      · refine Or.inr ?_
        have h₇ : √(2 ^ 2 + ‖x‖ ^ 2) ≤ 7 / 2 := by
          calc √(2 ^ 2 + ‖x‖ ^ 2) ≤ √((7 / 2) ^ 2) :=
                Real.sqrt_le_sqrt (by nlinarith [norm_nonneg x])
            _ = 7 / 2 := Real.sqrt_sq (by norm_num)
        change 1 / 2 ≤ |√(2 ^ 2 + ‖x‖ ^ 2) - 4|
        rw [abs_sub_comm, abs_of_pos (sub_pos.2 (h₇.trans_lt (by norm_num)))]
        exact le_sub_comm.2 (h₇.trans (by norm_num))
    have h' : (1 : ℝ) / 2 ≤ √(2 ^ 2 + ‖x‖ ^ 2) := (by norm_num : (1 : ℝ) / 2 ≤ 2).trans h₂
    rw [sanityX₀, hb, sanityBumpOrigin_eq_zero h', add_zero]
  simp only [hlow, integral_zero, sub_zero]
  -- the upper flux is positive
  set f : EuclideanSpace ℝ (Fin 3) → ℝ := fun x ↦ sanityX₀ (x, √(4 ^ 2 + ‖x‖ ^ 2)) with hf
  have h₄ (x : EuclideanSpace ℝ (Fin 3)) : (4 : ℝ) ≤ √(4 ^ 2 + ‖x‖ ^ 2) :=
    (Real.le_sqrt' (by norm_num)).2 (by nlinarith [norm_nonneg x])
  have horig (x : EuclideanSpace ℝ (Fin 3)) :
      sanityBumpOrigin (x, √(4 ^ 2 + ‖x‖ ^ 2)) = 0 := by
    have h' : (1 : ℝ) / 2 ≤ √(4 ^ 2 + ‖x‖ ^ 2) := (by norm_num : (1 : ℝ) / 2 ≤ 4).trans (h₄ x)
    exact sanityBumpOrigin_eq_zero h'
  have hnonneg : 0 ≤ f := fun x ↦ add_nonneg sanityBumpUpper.nonneg sanityBumpOrigin.nonneg
  have hsupp : support f ⊆ Metric.closedBall 0 (1 / 2) := by
    intro x hx
    by_contra h
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at h
    have h' : (1 : ℝ) / 2 ≤ ‖(x, √(4 ^ 2 + ‖x‖ ^ 2)).1‖ := h.le
    refine hx ?_
    change sanityX₀ (x, √(4 ^ 2 + ‖x‖ ^ 2)) = 0
    rw [sanityX₀, sanityBumpUpper_eq_zero (Or.inl h'), horig x, add_zero]
  have hint : Integrable f :=
    ((sanityBumpUpper.continuous.comp (by fun_prop)).add
      (sanityBumpOrigin.continuous.comp (by fun_prop))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) hsupp)
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4) ⊆ support f := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    have h₄' : √(4 ^ 2 + ‖x‖ ^ 2) ≤ 4 + 1 / 4 := by
      calc √(4 ^ 2 + ‖x‖ ^ 2) ≤ √((4 + 1 / 4) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith [norm_nonneg x])
        _ = 4 + 1 / 4 := Real.sqrt_sq (by norm_num)
    have hb : sanityBumpUpper (x, √(4 ^ 2 + ‖x‖ ^ 2)) = 1 := by
      refine sanityBumpUpper.one_of_mem_closedBall ?_
      rw [Metric.mem_closedBall, dist_zero_prod]
      have hr : sanityBumpUpper.rIn = 1 / 4 := rfl
      rw [hr]
      refine max_le hx.le ?_
      change |√(4 ^ 2 + ‖x‖ ^ 2) - 4| ≤ 1 / 4
      rw [abs_of_nonneg (by linarith [h₄ x] : (0 : ℝ) ≤ √(4 ^ 2 + ‖x‖ ^ 2) - 4)]
      linarith
    change sanityX₀ (x, √(4 ^ 2 + ‖x‖ ^ 2)) ≠ 0
    rw [sanityX₀, hb, horig x]
    norm_num
  rw [integral_pos_iff_support_of_nonneg hnonneg hint]
  exact (Metric.measure_ball_pos volume 0 (by norm_num)).trans_le (measure_mono hball)

end SanityChecks
