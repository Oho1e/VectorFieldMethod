/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# A local Sobolev embedding `H² ⊂ L^∞` on balls of `ℝ³`

This file states the local Sobolev bound on balls of `ℝ³ = EuclideanSpace ℝ (Fin 3)`: there is an
absolute constant `C` such that for every ball `B = ball x₀ ρ` and every function `f` which is `C²`
on `B`,
`|f x₀| ≤ C (ρ ^ (-3/2) ‖f‖_{L²(B)} + ρ ^ (-1/2) ‖Df‖_{L²(B)} + ρ ^ (1/2) ‖D²f‖_{L²(B)})`.
The powers of `ρ` make the bound invariant under dilations. The `L²` norms are `eLpNorm`s, with
values in `ℝ≥0∞`; they may be infinite, in which case the bound holds trivially.

## Main definitions

* `LocalSobolevBound`: the statement of the bound, as a proposition.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace VectorFieldMethod.EuclideanSobolev

/-- **Local Sobolev bound on balls of `ℝ³`.** There is an absolute constant `C` such that for every
ball `B = ball x₀ ρ` and every `f : ℝ³ → ℝ` which is `C²` on `B`,
`|f x₀| ≤ C (ρ ^ (-3/2) ‖f‖_{L²(B)} + ρ ^ (-1/2) ‖Df‖_{L²(B)} + ρ ^ (1/2) ‖D²f‖_{L²(B)})`,
where `Df = fderiv ℝ f` and `D²f = iteratedFDeriv ℝ 2 f` carry their operator norms. -/
def LocalSobolevBound : Prop :=
  ∃ C : NNReal, ∀ (x₀ : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
    0 < ρ → ContDiffOn ℝ 2 f (Metric.ball x₀ ρ) →
    ENNReal.ofReal |f x₀| ≤ (C : ENNReal) *
      (ENNReal.ofReal (ρ ^ (-(3 / 2 : ℝ))) * eLpNorm f 2 (volume.restrict (Metric.ball x₀ ρ)) +
        ENNReal.ofReal (ρ ^ (-(1 / 2 : ℝ))) *
          eLpNorm (fderiv ℝ f) 2 (volume.restrict (Metric.ball x₀ ρ)) +
        ENNReal.ofReal (ρ ^ (1 / 2 : ℝ)) *
          eLpNorm (iteratedFDeriv ℝ 2 f) 2 (volume.restrict (Metric.ball x₀ ρ)))

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ### Step 1: Taylor's formula along a segment -/

section Segment

variable {x₀ y : ℝ³} {ρ : ℝ} {f : ℝ³ → ℝ}

/-- The segment from the center `x₀` to a point `y` of `ball x₀ ρ` lies in the ball. -/
theorem add_smul_sub_mem_ball (hy : y ∈ Metric.ball x₀ ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x₀ + t • (y - x₀) ∈ Metric.ball x₀ ρ := by
  rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
  calc t * ‖y - x₀‖ ≤ 1 * ‖y - x₀‖ := by gcongr; exact ht.2
    _ < ρ := by rwa [one_mul]

/-- **Taylor's formula along a segment.** If `f` is `C²` on `ball x₀ ρ` and `y` lies in the ball,
then `f x₀ = f y - Df(y)(y - x₀) + ∫₀¹ t D²f(x₀ + t (y - x₀))(y - x₀, y - x₀) dt`. -/
theorem eq_sub_add_integral_of_contDiffOn_ball (hf : ContDiffOn ℝ 2 f (Metric.ball x₀ ρ))
    (hy : y ∈ Metric.ball x₀ ρ) :
    f x₀ = f y - fderiv ℝ f y (y - x₀) +
      ∫ t in (0 : ℝ)..1, t * fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀)) (y - x₀) (y - x₀) := by
  have hcd : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 2 f (x₀ + t • (y - x₀)) := fun t ht ↦
    hf.contDiffAt (Metric.isOpen_ball.mem_nhds (add_smul_sub_mem_ball hy ht))
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ x₀ + t • (y - x₀)) (y - x₀) t := fun t ↦ by
    simpa using ((hasDerivAt_id t).smul_const (y - x₀)).const_add x₀
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t ↦ t * fderiv ℝ f (x₀ + t • (y - x₀)) (y - x₀) - f (x₀ + t • (y - x₀)))
        (t * fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀)) (y - x₀) (y - x₀)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 : HasFDerivAt f (fderiv ℝ f (x₀ + t • (y - x₀))) (x₀ + t • (y - x₀)) :=
      ((hcd t ht).differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀)))
        (x₀ + t • (y - x₀)) :=
      (((hcd t ht).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasFDerivAt
    have h3 := (h2.comp_hasDerivAt t (hγ t)).clm_apply (hasDerivAt_const t (y - x₀))
    have h4 := ((hasDerivAt_id t).mul h3).sub (h1.comp_hasDerivAt t (hγ t))
    exact h4.congr_deriv (by simp)
  have hint : IntervalIntegrable
      (fun t ↦ t * fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀)) (y - x₀) (y - x₀)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    have hc : ContinuousAt (fderiv ℝ (fderiv ℝ f)) (x₀ + t • (y - x₀)) :=
      (((hcd t ht).fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0)
        (by norm_num)).continuousAt
    exact continuousAt_id.mul
      (((hc.comp (f := fun t : ℝ ↦ x₀ + t • (y - x₀)) (hγ t).continuousAt).clm_apply
        continuousAt_const).clm_apply continuousAt_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp
  ring

/-- **Step 1.** Pointwise bound along a segment: for `y ∈ ball x₀ ρ`,
`|f x₀| ≤ |f y| + ρ ‖Df(y)‖ + ∫₀¹ t ρ ^ 2 ‖D²f(x₀ + t (y - x₀))‖ dt`. -/
theorem enorm_le_of_contDiffOn_ball (hf : ContDiffOn ℝ 2 f (Metric.ball x₀ ρ))
    (hy : y ∈ Metric.ball x₀ ρ) :
    ‖f x₀‖ₑ ≤ ‖f y‖ₑ + ENNReal.ofReal ρ * ‖fderiv ℝ f y‖ₑ +
      ∫⁻ t in Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (t * ρ ^ 2) * ‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ₑ := by
  have hyx : ‖y - x₀‖ ≤ ρ := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hy.le
  rw [eq_sub_add_integral_of_contDiffOn_ball hf hy, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_add_le _ _).trans (add_le_add (enorm_sub_le.trans (add_le_add le_rfl ?_)) ?_)
  · calc ‖fderiv ℝ f y (y - x₀)‖ₑ ≤ ‖fderiv ℝ f y‖ₑ * ‖y - x₀‖ₑ :=
          ContinuousLinearMap.le_opENorm _ _
      _ ≤ ‖fderiv ℝ f y‖ₑ * ENNReal.ofReal ρ := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal hyx
      _ = ENNReal.ofReal ρ * ‖fderiv ℝ f y‖ₑ := mul_comm _ _
  · refine (enorm_integral_le_lintegral_enorm _).trans
      (setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_)
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by nlinarith [ht.1])]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [norm_mul, Real.norm_of_nonneg ht.1.le]
    have ht0 := ht.1.le
    have hρ : 0 ≤ ρ := (norm_nonneg _).trans hyx
    calc t * ‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀)) (y - x₀) (y - x₀)‖
        ≤ t * (‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ * ‖y - x₀‖ * ‖y - x₀‖) := by
          gcongr
          exact (fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))).le_opNorm₂ (y - x₀) (y - x₀)
      _ ≤ t * (‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ * ρ * ρ) := by
          gcongr
      _ = t * ρ ^ 2 * ‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ := by ring

/-! ### Step 2: averaging over the ball -/

/-- Cauchy–Schwarz against the constant function `1`: `∫ ‖g‖ ≤ ‖g‖_{L²} μ(univ) ^ (1/2)`. -/
theorem lintegral_enorm_le_eLpNorm_mul_measure_univ {F : Type*} [NormedAddCommGroup F]
    {μ : Measure ℝ³} {g : ℝ³ → F} (hg : AEStronglyMeasurable g μ) :
    ∫⁻ y, ‖g y‖ₑ ∂μ ≤ eLpNorm g 2 μ * μ Set.univ ^ (1 / 2 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hg
  rw [eLpNorm_one_eq_lintegral_enorm hg] at h
  convert h using 3
  norm_num

/-- **Step 2.** Averaging the pointwise bound of step 1 over `y ∈ ball x₀ ρ`. -/
theorem measure_ball_mul_enorm_le (hf : ContDiffOn ℝ 2 f (Metric.ball x₀ ρ)) :
    volume (Metric.ball x₀ ρ) * ‖f x₀‖ₑ ≤
      (∫⁻ y in Metric.ball x₀ ρ, ‖f y‖ₑ) +
        ENNReal.ofReal ρ * (∫⁻ y in Metric.ball x₀ ρ, ‖fderiv ℝ f y‖ₑ) +
        ∫⁻ y in Metric.ball x₀ ρ, ∫⁻ t in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (t * ρ ^ 2) * ‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ₑ := by
  have h1 : AEMeasurable (fun y ↦ ‖f y‖ₑ) (volume.restrict (Metric.ball x₀ ρ)) :=
    (hf.continuousOn.aestronglyMeasurable measurableSet_ball).enorm
  have h2 : Measurable (fun y ↦ ENNReal.ofReal ρ * ‖fderiv ℝ f y‖ₑ) :=
    (measurable_fderiv ℝ f).enorm.const_mul _
  have h12 : AEMeasurable (fun y ↦ ‖f y‖ₑ + ENNReal.ofReal ρ * ‖fderiv ℝ f y‖ₑ)
      (volume.restrict (Metric.ball x₀ ρ)) :=
    h1.add h2.aemeasurable
  calc volume (Metric.ball x₀ ρ) * ‖f x₀‖ₑ = ∫⁻ _ in Metric.ball x₀ ρ, ‖f x₀‖ₑ := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ y in Metric.ball x₀ ρ, (‖f y‖ₑ + ENNReal.ofReal ρ * ‖fderiv ℝ f y‖ₑ +
          ∫⁻ t in Set.Ioc (0 : ℝ) 1,
            ENNReal.ofReal (t * ρ ^ 2) * ‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ₑ) :=
        setLIntegral_mono' measurableSet_ball fun y hy ↦ enorm_le_of_contDiffOn_ball hf hy
    _ = _ := by
        rw [lintegral_add_left' h12, lintegral_add_left' h1,
          lintegral_const_mul _ (measurable_fderiv ℝ f).enorm]

end Segment

end VectorFieldMethod.EuclideanSobolev
