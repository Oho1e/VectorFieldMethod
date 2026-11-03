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
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# A local Sobolev embedding `H² ⊂ L^∞` on balls of `ℝ³`

This file proves the local Sobolev bound on balls of `ℝ³ = EuclideanSpace ℝ (Fin 3)`: there is an
absolute constant `C` such that for every ball `B = ball x₀ ρ` and every function `f` which is `C²`
on `B`,
`|f x₀| ≤ C (ρ ^ (-3/2) ‖f‖_{L²(B)} + ρ ^ (-1/2) ‖Df‖_{L²(B)} + ρ ^ (1/2) ‖D²f‖_{L²(B)})`,
where `Df = fderiv ℝ f` and `D²f = iteratedFDeriv ℝ 2 f` carry their operator norms. The powers of
`ρ` make the bound invariant under dilations. The `L²` norms are `eLpNorm`s, with values in `ℝ≥0∞`;
they may be infinite, in which case the bound holds trivially. Only the values of `f` on the open
ball enter, so `f` is only assumed to be `C²` there.

## Proof

The proof averages Taylor's formula along the segments issued from `x₀`; it uses neither polar
coordinates nor cut-off functions. Write `|B|` for the volume of `B`.

1. For `y ∈ B`, Taylor's formula along the segment from `x₀` to `y`
   (`eq_sub_add_integral_of_contDiffOn_ball`) gives
   `|f x₀| ≤ |f y| + ρ ‖Df(y)‖ + ρ ^ 2 ∫₀¹ t ‖D²f(x₀ + t (y - x₀))‖ dt`
   (`enorm_le_of_contDiffOn_ball`).
2. Integrating over `y ∈ B` (`measure_ball_mul_enorm_le`), the Cauchy–Schwarz inequality
   `∫_B ‖g‖ ≤ |B| ^ (1/2) ‖g‖_{L²(B)}` bounds the first two terms of `|B| |f x₀|` by
   `|B| ^ (1/2) (‖f‖_{L²(B)} + ρ ‖Df‖_{L²(B)})`.
3. In the last term, exchange the two integrals (Tonelli). For fixed `t ∈ (0, 1]`, the homothety
   `y ↦ x₀ + t (y - x₀)` maps `B` into itself and multiplies volumes by `t ^ 3`, so the
   Cauchy–Schwarz inequality gives
   `∫_B ‖D²f(x₀ + t (y - x₀))‖ dy ≤ t ^ (-3/2) |B| ^ (1/2) ‖D²f‖_{L²(B)}`
   (`eLpNorm_comp_homothety_le`). Since `∫₀¹ t · t ^ (-3/2) dt = 2`, the last term is at most
   `2 ρ ^ 2 |B| ^ (1/2) ‖D²f‖_{L²(B)}` (`lintegral_ball_lintegral_Ioc_le`).
4. Dividing by `|B| = ρ ^ 3 |ball 0 1|` gives the bound with `C = 2 |ball 0 1| ^ (-1/2)`.

## Main definitions

* `LocalSobolevBound`: the statement of the bound, as a proposition.

## Main statements

* `exists_abs_le_eLpNorm_ball`: the local Sobolev bound (Theorem 1).
* `localSobolevBound_holds`: the same statement, as a proof of `LocalSobolevBound`.

## Notation

`ℝ³` is local notation for `EuclideanSpace ℝ (Fin 3)`.
-/

@[expose] public noncomputable section

open MeasureTheory

open scoped ENNReal

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
  exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans_lt hy

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
  simp only [map_sub, one_smul, add_sub_cancel, one_mul, zero_smul, add_zero, zero_mul, zero_sub,
    sub_neg_eq_add]
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

/-! ### Step 3: the second-order term -/

/-- `∫₀¹ t ^ (-1/2) dt = 2`. -/
theorem lintegral_Ioc_rpow_neg_one_half :
    ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) = ENNReal.ofReal 2 := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hint)]
  · rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl (by norm_num))]
    norm_num
  · exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht ↦ Real.rpow_nonneg ht.1.le _)

/-- **Change of variables under a homothety.** For `0 < t ≤ 1`, the homothety
`y ↦ x₀ + t (y - x₀)` maps `ball x₀ ρ` into itself and multiplies volumes by `t ^ 3`, so
`∫_{ball x₀ ρ} H(x₀ + t (y - x₀)) dy ≤ t ^ (-3) ∫_{ball x₀ ρ} H`. -/
theorem setLIntegral_ball_comp_homothety_le {H : ℝ³ → ℝ≥0∞} (hH : Measurable H) (x₀ : ℝ³)
    (ρ : ℝ) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ∫⁻ y in Metric.ball x₀ ρ, H (x₀ + t • (y - x₀)) ≤
      ENNReal.ofReal (t ^ (-3 : ℝ)) * ∫⁻ z in Metric.ball x₀ ρ, H z := by
  set K := (Metric.ball x₀ ρ).indicator H with hKdef
  have hK : Measurable K := hH.indicator measurableSet_ball
  have hdet : ENNReal.ofReal |(t ^ Module.finrank ℝ ℝ³)⁻¹| = ENNReal.ofReal (t ^ (-3 : ℝ)) := by
    rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos ht.1 3)),
      Real.rpow_neg ht.1.le]
    norm_num
  calc ∫⁻ y in Metric.ball x₀ ρ, H (x₀ + t • (y - x₀))
      = ∫⁻ y, (Metric.ball x₀ ρ).indicator (fun y ↦ H (x₀ + t • (y - x₀))) y :=
        (lintegral_indicator measurableSet_ball _).symm
    _ ≤ ∫⁻ y, K (x₀ + t • (y - x₀)) := by
        refine lintegral_mono fun y ↦ ?_
        by_cases hy : y ∈ Metric.ball x₀ ρ
        · rw [Set.indicator_of_mem hy, hKdef,
            Set.indicator_of_mem (add_smul_sub_mem_ball hy ⟨ht.1.le, ht.2⟩)]
        · rw [Set.indicator_of_notMem hy]
          exact zero_le
    _ = ∫⁻ h, K (x₀ + t • h) := lintegral_sub_right_eq_self (fun h ↦ K (x₀ + t • h)) x₀
    _ = ENNReal.ofReal (t ^ (-3 : ℝ)) * ∫⁻ z, K (x₀ + z) := by
        rw [← lintegral_map (f := fun z ↦ K (x₀ + z)) (hK.comp (measurable_const_add x₀))
          (measurable_const_smul t), Measure.map_addHaar_smul volume ht.1.ne',
          lintegral_smul_measure, hdet, smul_eq_mul]
    _ = ENNReal.ofReal (t ^ (-3 : ℝ)) * ∫⁻ z in Metric.ball x₀ ρ, H z := by
        rw [lintegral_add_left_eq_self K x₀, lintegral_indicator measurableSet_ball]

/-- The `L²` norm of `y ↦ D²f(x₀ + t (y - x₀))` on `ball x₀ ρ` is at most `t ^ (-3/2)` times
the `L²` norm of `D²f` on the same ball, for `0 < t ≤ 1`. -/
theorem eLpNorm_comp_homothety_le (x₀ : ℝ³) (ρ : ℝ) (f : ℝ³ → ℝ) {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    eLpNorm (fun y ↦ fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))) 2
        (volume.restrict (Metric.ball x₀ ρ)) ≤
      ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) *
        eLpNorm (fderiv ℝ (fderiv ℝ f)) 2 (volume.restrict (Metric.ball x₀ ρ)) := by
  have hG : Measurable (fderiv ℝ (fderiv ℝ f)) := measurable_fderiv ℝ _
  have hGt : Measurable (fun y ↦ fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))) :=
    hG.comp (by fun_prop)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hGt.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hG.aestronglyMeasurable, ENNReal.toReal_ofNat]
  calc (∫⁻ y in Metric.ball x₀ ρ, ‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ₑ ^ (2 : ℝ)) ^
        (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (t ^ (-3 : ℝ)) *
          ∫⁻ z in Metric.ball x₀ ρ, ‖fderiv ℝ (fderiv ℝ f) z‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        gcongr
        exact setLIntegral_ball_comp_homothety_le (hG.enorm.pow_const _) x₀ ρ ht
    _ = ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) *
          (∫⁻ z in Metric.ball x₀ ρ, ‖fderiv ℝ (fderiv ℝ f) z‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.1.le _) (by norm_num),
          ← Real.rpow_mul ht.1.le]
        norm_num

/-- **Step 3.** The second-order term of step 2 is bounded by
`2 ρ ^ 2 ‖D²f‖_{L²(ball x₀ ρ)} vol(ball x₀ ρ) ^ (1/2)`. -/
theorem lintegral_ball_lintegral_Ioc_le (x₀ : ℝ³) (ρ : ℝ) (f : ℝ³ → ℝ) :
    ∫⁻ y in Metric.ball x₀ ρ, ∫⁻ t in Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (t * ρ ^ 2) * ‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ₑ ≤
      ENNReal.ofReal (2 * ρ ^ 2) *
        eLpNorm (fderiv ℝ (fderiv ℝ f)) 2 (volume.restrict (Metric.ball x₀ ρ)) *
        volume (Metric.ball x₀ ρ) ^ (1 / 2 : ℝ) := by
  have hG : Measurable (fderiv ℝ (fderiv ℝ f)) := measurable_fderiv ℝ _
  set K := eLpNorm (fderiv ℝ (fderiv ℝ f)) 2 (volume.restrict (Metric.ball x₀ ρ)) *
    volume (Metric.ball x₀ ρ) ^ (1 / 2 : ℝ) with hK
  have hmeas : Measurable (Function.uncurry fun (y : ℝ³) (t : ℝ) ↦
      ENNReal.ofReal (t * ρ ^ 2) * ‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ₑ) := by
    have h1 : Measurable (fun p : ℝ³ × ℝ ↦ x₀ + p.2 • (p.1 - x₀)) := by fun_prop
    exact (by fun_prop : Measurable fun p : ℝ³ × ℝ ↦ ENNReal.ofReal (p.2 * ρ ^ 2)).mul
      (hG.comp h1).enorm
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ t in Set.Ioc (0 : ℝ) 1, ∫⁻ y in Metric.ball x₀ ρ,
        ENNReal.ofReal (t * ρ ^ 2) * ‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ₑ
      ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (ρ ^ 2) * K * ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) := by
        refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
        have hGt : Measurable (fun y ↦ fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))) :=
          hG.comp (by fun_prop)
        have hpow : t * t ^ (-(3 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
          rw [show (-(1 / 2 : ℝ)) = 1 + -(3 / 2 : ℝ) by norm_num, Real.rpow_add ht.1,
            Real.rpow_one]
        rw [lintegral_const_mul _ hGt.enorm]
        calc ENNReal.ofReal (t * ρ ^ 2) *
              ∫⁻ y in Metric.ball x₀ ρ, ‖fderiv ℝ (fderiv ℝ f) (x₀ + t • (y - x₀))‖ₑ
            ≤ ENNReal.ofReal (t * ρ ^ 2) * (ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) * K) := by
              gcongr
              refine (lintegral_enorm_le_eLpNorm_mul_measure_univ
                hGt.aestronglyMeasurable).trans ?_
              rw [Measure.restrict_apply_univ, hK, ← mul_assoc]
              gcongr
              exact eLpNorm_comp_homothety_le x₀ ρ f ht
          _ = ENNReal.ofReal (ρ ^ 2) * K * ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) := by
              rw [← hpow, ENNReal.ofReal_mul ht.1.le, ENNReal.ofReal_mul ht.1.le]
              ring
    _ = ENNReal.ofReal (ρ ^ 2) * K * ENNReal.ofReal 2 := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_Ioc_rpow_neg_one_half]
    _ = ENNReal.ofReal (2 * ρ ^ 2) * K := by
        rw [ENNReal.ofReal_mul zero_le_two]
        ring
    _ = _ := by rw [hK, mul_assoc]

/-! ### Step 4: conclusion -/

/-- On a ball where `f` is `C²`, the `L²` norms of `fderiv ℝ (fderiv ℝ f)` and
`iteratedFDeriv ℝ 2 f` agree, since the two second derivatives have the same norm at every
point. -/
theorem eLpNorm_fderiv_fderiv_eq_of_contDiffOn {x₀ : ℝ³} {ρ : ℝ} {f : ℝ³ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Metric.ball x₀ ρ)) :
    eLpNorm (fderiv ℝ (fderiv ℝ f)) 2 (volume.restrict (Metric.ball x₀ ρ)) =
      eLpNorm (iteratedFDeriv ℝ 2 f) 2 (volume.restrict (Metric.ball x₀ ρ)) := by
  have h2 : AEStronglyMeasurable (iteratedFDeriv ℝ 2 f) (volume.restrict (Metric.ball x₀ ρ)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_ball
    exact (hf.continuousOn_iteratedFDerivWithin (m := 2) le_rfl
      Metric.isOpen_ball.uniqueDiffOn).congr
        (iteratedFDerivWithin_of_isOpen 2 Metric.isOpen_ball).symm
  refine eLpNorm_congr_norm_ae (measurable_fderiv ℝ _).aestronglyMeasurable h2
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]

/-- **Theorem 1 (local embedding `H² ⊂ L^∞` on balls of `ℝ³`).** There is an absolute constant
`C` such that for every ball `B = ball x₀ ρ` of `ℝ³` and every function `f` which is `C²` on `B`,
`|f x₀| ≤ C (ρ ^ (-3/2) ‖f‖_{L²(B)} + ρ ^ (-1/2) ‖Df‖_{L²(B)} + ρ ^ (1/2) ‖D²f‖_{L²(B)})`. -/
theorem exists_abs_le_eLpNorm_ball :
    ∃ C : NNReal, ∀ (x₀ : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
      0 < ρ → ContDiffOn ℝ 2 f (Metric.ball x₀ ρ) →
      ENNReal.ofReal |f x₀| ≤ (C : ENNReal) *
        (ENNReal.ofReal (ρ ^ (-(3 / 2 : ℝ))) * eLpNorm f 2 (volume.restrict (Metric.ball x₀ ρ)) +
          ENNReal.ofReal (ρ ^ (-(1 / 2 : ℝ))) *
            eLpNorm (fderiv ℝ f) 2 (volume.restrict (Metric.ball x₀ ρ)) +
          ENNReal.ofReal (ρ ^ (1 / 2 : ℝ)) *
            eLpNorm (iteratedFDeriv ℝ 2 f) 2 (volume.restrict (Metric.ball x₀ ρ))) := by
  set c₁ := (volume (Metric.ball (0 : ℝ³) 1)).toReal with hc₁
  have hc₁pos : 0 < c₁ :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  refine ⟨Real.toNNReal (2 * c₁ ^ (-(1 / 2 : ℝ))), fun x₀ ρ f hρ hf ↦ ?_⟩
  set μB := volume.restrict (Metric.ball x₀ ρ)
  set A := eLpNorm f 2 μB
  set B := eLpNorm (fderiv ℝ f) 2 μB
  set D := eLpNorm (iteratedFDeriv ℝ 2 f) 2 μB
  set w := ρ ^ (3 / 2 : ℝ) * c₁ ^ (1 / 2 : ℝ) with hw
  have hwpos : 0 < w := by positivity
  have hww : w * w = ρ ^ 3 * c₁ := by
    calc w * w = ρ ^ (3 / 2 + 3 / 2 : ℝ) * c₁ ^ (1 / 2 + 1 / 2 : ℝ) := by
          rw [Real.rpow_add hρ, Real.rpow_add hc₁pos, hw]
          ring
      _ = ρ ^ 3 * c₁ := by norm_num
  have hV : volume (Metric.ball x₀ ρ) = ENNReal.ofReal (w * w) := by
    rw [Measure.addHaar_ball volume x₀ hρ.le, finrank_euclideanSpace_fin, hww,
      ENNReal.ofReal_mul (by positivity), hc₁, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  have hVhalf : volume (Metric.ball x₀ ρ) ^ (1 / 2 : ℝ) = ENNReal.ofReal w := by
    rw [hV, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_mul_self hwpos.le]
  have hI1 : ∫⁻ y in Metric.ball x₀ ρ, ‖f y‖ₑ ≤ A * ENNReal.ofReal w := by
    have := lintegral_enorm_le_eLpNorm_mul_measure_univ (μ := μB)
      (hf.continuousOn.aestronglyMeasurable measurableSet_ball)
    rwa [Measure.restrict_apply_univ, hVhalf] at this
  have hI2 : ∫⁻ y in Metric.ball x₀ ρ, ‖fderiv ℝ f y‖ₑ ≤ B * ENNReal.ofReal w := by
    have := lintegral_enorm_le_eLpNorm_mul_measure_univ (μ := μB)
      (measurable_fderiv ℝ f).aestronglyMeasurable
    rwa [Measure.restrict_apply_univ, hVhalf] at this
  have hI3 := lintegral_ball_lintegral_Ioc_le x₀ ρ f
  rw [hVhalf, eLpNorm_fderiv_fderiv_eq_of_contDiffOn hf] at hI3
  have hmain : ENNReal.ofReal w * (ENNReal.ofReal w * ‖f x₀‖ₑ) ≤
      ENNReal.ofReal w * (A + ENNReal.ofReal ρ * B + ENNReal.ofReal (2 * ρ ^ 2) * D) := by
    calc ENNReal.ofReal w * (ENNReal.ofReal w * ‖f x₀‖ₑ)
        = volume (Metric.ball x₀ ρ) * ‖f x₀‖ₑ := by
          rw [hV, ENNReal.ofReal_mul hwpos.le, mul_assoc]
      _ ≤ _ := measure_ball_mul_enorm_le hf
      _ ≤ A * ENNReal.ofReal w + ENNReal.ofReal ρ * (B * ENNReal.ofReal w) +
            ENNReal.ofReal (2 * ρ ^ 2) * D * ENNReal.ofReal w := by
          gcongr
      _ = _ := by ring
  have hmain' := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hwpos).ne'
    ENNReal.ofReal_ne_top).mp hmain
  have hκ : w⁻¹ = c₁ ^ (-(1 / 2 : ℝ)) * ρ ^ (-(3 / 2 : ℝ)) := by
    rw [hw, mul_inv, Real.rpow_neg hρ.le, Real.rpow_neg hc₁pos.le]
    ring
  have e1 : w⁻¹ ≤ 2 * c₁ ^ (-(1 / 2 : ℝ)) * ρ ^ (-(3 / 2 : ℝ)) := by
    have : 0 ≤ c₁ ^ (-(1 / 2 : ℝ)) * ρ ^ (-(3 / 2 : ℝ)) := by positivity
    rw [hκ]
    linarith
  have e2 : w⁻¹ * ρ ≤ 2 * c₁ ^ (-(1 / 2 : ℝ)) * ρ ^ (-(1 / 2 : ℝ)) := by
    have h1 : ρ ^ (-(3 / 2 : ℝ)) * ρ = ρ ^ (-(1 / 2 : ℝ)) := by
      rw [show (-(1 / 2 : ℝ)) = -(3 / 2 : ℝ) + 1 by norm_num, Real.rpow_add hρ, Real.rpow_one]
    have h2 : 0 ≤ c₁ ^ (-(1 / 2 : ℝ)) * ρ ^ (-(1 / 2 : ℝ)) := by positivity
    rw [hκ, mul_assoc, h1]
    linarith
  have e3 : w⁻¹ * (2 * ρ ^ 2) = 2 * c₁ ^ (-(1 / 2 : ℝ)) * ρ ^ (1 / 2 : ℝ) := by
    have h1 : ρ ^ (-(3 / 2 : ℝ)) * ρ ^ 2 = ρ ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hρ]
      norm_num
    rw [hκ, ← h1]
    ring
  have hw0 : 0 ≤ w⁻¹ := inv_nonneg.mpr hwpos.le
  rw [← Real.enorm_eq_ofReal_abs]
  calc ‖f x₀‖ₑ = ENNReal.ofReal w⁻¹ * (ENNReal.ofReal w * ‖f x₀‖ₑ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hw0, inv_mul_cancel₀ hwpos.ne', ENNReal.ofReal_one,
          one_mul]
    _ ≤ ENNReal.ofReal w⁻¹ * (A + ENNReal.ofReal ρ * B + ENNReal.ofReal (2 * ρ ^ 2) * D) := by
        gcongr
    _ = ENNReal.ofReal w⁻¹ * A + ENNReal.ofReal (w⁻¹ * ρ) * B +
          ENNReal.ofReal (w⁻¹ * (2 * ρ ^ 2)) * D := by
        rw [ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul hw0]
        ring
    _ ≤ ENNReal.ofReal (2 * c₁ ^ (-(1 / 2 : ℝ)) * ρ ^ (-(3 / 2 : ℝ))) * A +
          ENNReal.ofReal (2 * c₁ ^ (-(1 / 2 : ℝ)) * ρ ^ (-(1 / 2 : ℝ))) * B +
          ENNReal.ofReal (2 * c₁ ^ (-(1 / 2 : ℝ)) * ρ ^ (1 / 2 : ℝ)) * D := by
        rw [e3]
        gcongr
    _ = _ := by
        have hC0 : 0 ≤ 2 * c₁ ^ (-(1 / 2 : ℝ)) := by positivity
        simp only [ENNReal.ofReal_mul hC0]
        rw [show ((Real.toNNReal (2 * c₁ ^ (-(1 / 2 : ℝ))) : ℝ≥0∞)) =
          ENNReal.ofReal (2 * c₁ ^ (-(1 / 2 : ℝ))) from rfl]
        ring

/-- Theorem 1, in the form of the proposition `LocalSobolevBound`. -/
theorem localSobolevBound_holds : LocalSobolevBound := exists_abs_le_eLpNorm_ball

end VectorFieldMethod.EuclideanSobolev
