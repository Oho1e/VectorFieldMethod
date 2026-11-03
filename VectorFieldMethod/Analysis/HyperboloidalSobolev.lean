/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Analysis.LocalSobolev
public import VectorFieldMethod.ForMathlib.MeasureTheory.Integral.DivergenceTheoremHyperboloid
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# The hyperboloidal Sobolev inequality on `ℝ³`

For `s > 0` let `φ_s x = √(s ^ 2 + ‖x‖ ^ 2)`, and for `a : Fin 3` let `Λ_a w = φ_s ∂_a w`
(`hyperboloidalWeightedDeriv s a w`), where `∂_a w x = fderiv ℝ w x (EuclideanSpace.single a 1)`.
This file proves the weighted inequality
`φ_s(x₀) ^ (3/2) |w x₀| ≤ C (‖w‖ + ∑ a, ‖Λ_a w‖ + ∑ a, ∑ b, ‖Λ_a Λ_b w‖)`
for every `C²` function `w : ℝ³ → ℝ` and every `x₀`, with `L²` norms over `ℝ³`, and with an absolute
constant `C` (independent of `s`, `w` and `x₀`). This is the `ℝ³` form of the Klainerman–Sobolev
inequality on the hyperboloid `t = √(s ^ 2 + ‖x‖ ^ 2)`; see `docs/hyperboloidal-sobolev.md`. It is
first derived from the local Sobolev bound `LocalSobolevBound` on balls of `ℝ³`, as an implication,
and then combined with `localSobolevBound_holds`.

## Proof

Let `φ₀ = φ_s x₀` and `ρ = φ₀ / 3`, and apply the local bound on `B = ball x₀ ρ`.

* `φ_s` is `1`-Lipschitz, so `φ₀ ≤ (3/2) φ_s x` on `B` (`sqrt_sq_add_norm_sq_le_of_mem_ball`).
* `‖Dw x‖ ≤ ∑ a, |∂_a w x|` and `‖D²w x‖ ≤ ∑ a, ∑ b, |∂_a ∂_b w x|`
  (`norm_le_sum_norm_apply_single`), hence `φ₀ ‖Dw x‖ ≤ (3/2) ∑ a, |Λ_a w x|` on `B`.
* `Λ_a Λ_b w = φ_s ^ 2 ∂_a ∂_b w + x_a ∂_b w`
  (`hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_apply`) and `|x_a| ≤ φ_s`, hence
  `φ₀ ^ 2 ‖D²w x‖ ≤ (9/4) ∑ a, ∑ b, (|Λ_a Λ_b w x| + |Λ_b w x|)` on `B`.
* Multiplying the local bound by `φ₀ ^ (3/2)`, the three coefficients become `3 ^ (3/2)`,
  `√3 φ₀` and `φ₀ ^ 2 / √3`, and the two previous bounds absorb the powers of `φ₀`.

The bound is first obtained with `L²` norms on `B` (the local version), and the global version
follows by monotonicity of `eLpNorm` in the measure.

## Main definitions

* `hyperboloidalWeightedDeriv s a w`: the weighted derivative `Λ_a w = φ_s ∂_a w`.

## Main statements

* `exists_hyperboloidalSobolev_ball_of_localSobolevBound`: the local bound implies the weighted
  inequality with `L²` norms on `ball x₀ (φ_s(x₀) / 3)`.
* `exists_hyperboloidalSobolev_of_localSobolevBound`: the local bound implies the weighted
  inequality with `L²` norms on `ℝ³`.
* `exists_hyperboloidalSobolev_ball`: the weighted inequality with `L²` norms on
  `ball x₀ (φ_s(x₀) / 3)` (local version of Theorem 2).
* `exists_hyperboloidalSobolev`: the weighted inequality with `L²` norms on `ℝ³` (Theorem 2).

Both unconditional statements combine the reductions with `localSobolevBound_holds`.

## Notation

`ℝ³` is local notation for `EuclideanSpace ℝ (Fin 3)`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace VectorFieldMethod.EuclideanSobolev

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The hyperboloidal weighted derivative `Λ_a w = φ_s ∂_a w` on `ℝ³`, where
`φ_s x = √(s ^ 2 + ‖x‖ ^ 2)` and `∂_a w x = fderiv ℝ w x (EuclideanSpace.single a 1)`. If
`w x = u (√(s ^ 2 + ‖x‖ ^ 2), x)` is the restriction of a spacetime function `u` to the hyperboloid
`t = φ_s x`, then `Λ_a w` is the restriction of the boost `L_a u = t ∂_a u + x_a ∂_t u`. -/
def hyperboloidalWeightedDeriv (s : ℝ) (a : Fin 3) (w : EuclideanSpace ℝ (Fin 3) → ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x ↦ √(s ^ 2 + ‖x‖ ^ 2) * fderiv ℝ w x (EuclideanSpace.single a 1)

/-- `Λ_a w` is measurable for every function `w`. -/
theorem measurable_hyperboloidalWeightedDeriv (s : ℝ) (a : Fin 3) (w : ℝ³ → ℝ) :
    Measurable (hyperboloidalWeightedDeriv s a w) :=
  (by fun_prop : Measurable fun x : ℝ³ ↦ √(s ^ 2 + ‖x‖ ^ 2)).mul
    (measurable_fderiv_apply_const ℝ w _)

/-! ### Elementary bounds -/

/-- Expansion of a vector of `ℝ³` in the standard basis. -/
theorem sum_apply_smul_single (v : ℝ³) : ∑ a, v a • EuclideanSpace.single a (1 : ℝ) = v := by
  simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v

/-- The operator norm of a linear map on `ℝ³` is at most the sum of the norms of its values on the
standard basis. -/
theorem norm_le_sum_norm_apply_single {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℝ³ →L[ℝ] F) : ‖L‖ ≤ ∑ a, ‖L (EuclideanSpace.single a 1)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun a _ ↦ norm_nonneg _) fun v ↦ ?_
  calc ‖L v‖ = ‖∑ a, v a • L (EuclideanSpace.single a 1)‖ := by
        conv_lhs => rw [← sum_apply_smul_single v]
        simp only [map_sum, map_smul]
    _ ≤ ∑ a, ‖v a • L (EuclideanSpace.single a 1)‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖v‖ * ‖L (EuclideanSpace.single a 1)‖ := by
        gcongr with a
        rw [norm_smul]
        gcongr
        exact PiLp.norm_apply_le v a
    _ = (∑ a, ‖L (EuclideanSpace.single a 1)‖) * ‖v‖ := by
        rw [Finset.sum_mul]
        simp only [mul_comm]

/-- The weight `φ_s x = √(s ^ 2 + ‖x‖ ^ 2)` is `1`-Lipschitz: `φ_s x₀ ≤ φ_s x + ‖x - x₀‖`. -/
theorem sqrt_sq_add_norm_sq_le_add (s : ℝ) (x x₀ : ℝ³) :
    √(s ^ 2 + ‖x₀‖ ^ 2) ≤ √(s ^ 2 + ‖x‖ ^ 2) + ‖x - x₀‖ := by
  have h1 : ‖x‖ ≤ √(s ^ 2 + ‖x‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s])
  have h2 : ‖x₀‖ ≤ ‖x‖ + ‖x - x₀‖ := by
    have := norm_sub_norm_le x₀ x
    rw [norm_sub_rev] at this
    linarith
  have h3 := Real.sq_sqrt (show 0 ≤ s ^ 2 + ‖x‖ ^ 2 by positivity)
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg x, norm_nonneg x₀, norm_nonneg (x - x₀),
    Real.sqrt_nonneg (s ^ 2 + ‖x‖ ^ 2)]

/-- On the ball `ball x₀ (φ_s x₀ / 3)`, the weight is comparable to its value at the center:
`φ_s x₀ ≤ (3/2) φ_s x`. -/
theorem sqrt_sq_add_norm_sq_le_of_mem_ball (s : ℝ) {x x₀ : ℝ³}
    (hx : x ∈ Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3)) :
    √(s ^ 2 + ‖x₀‖ ^ 2) ≤ 3 / 2 * √(s ^ 2 + ‖x‖ ^ 2) := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have := sqrt_sq_add_norm_sq_le_add s x x₀
  linarith

/-- `Λ_a Λ_b w = φ_s ^ 2 ∂_a ∂_b w + x_a ∂_b w` for `C²` functions `w`, where
`∂_a ∂_b w x = fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)`
(the outer derivative is in the direction `a`). -/
theorem hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_apply {s : ℝ} (hs : s ≠ 0)
    {w : ℝ³ → ℝ} (hw : ContDiff ℝ 2 w) (a b : Fin 3) (x : ℝ³) :
    hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w) x =
      (s ^ 2 + ‖x‖ ^ 2) *
          fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) +
        x a * fderiv ℝ w x (EuclideanSpace.single b 1) := by
  have hφ : DifferentiableAt ℝ (fun y : ℝ³ ↦ √(s ^ 2 + ‖y‖ ^ 2)) x :=
    (contDiff_sqrt_sq_add_norm_sq hs).differentiable one_ne_zero x
  have hDw : Differentiable ℝ (fderiv ℝ w) :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hg : DifferentiableAt ℝ (fun y ↦ fderiv ℝ w y (EuclideanSpace.single b 1)) x :=
    (hDw x).clm_apply (differentiableAt_const _)
  have hpos : 0 < √(s ^ 2 + ‖x‖ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hΛ : hyperboloidalWeightedDeriv s b w =
      fun y ↦ √(s ^ 2 + ‖y‖ ^ 2) * fderiv ℝ w y (EuclideanSpace.single b 1) := rfl
  rw [hyperboloidalWeightedDeriv, hΛ, fderiv_fun_mul hφ hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_clm_apply (hDw x) (differentiableAt_const _), fderiv_sqrt_sq_add_norm_sq_apply hs]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-- Pointwise bound of the first derivative by the weighted derivatives: if
`c ≤ (3/2) φ_s x`, then `c ‖Dw x‖ ≤ (3/2) ∑ a, |Λ_a w x|`. -/
theorem mul_norm_fderiv_le {s c : ℝ} (w : ℝ³ → ℝ) (x : ℝ³)
    (hcx : c ≤ 3 / 2 * √(s ^ 2 + ‖x‖ ^ 2)) :
    c * ‖fderiv ℝ w x‖ ≤ 3 / 2 * ∑ a, ‖hyperboloidalWeightedDeriv s a w x‖ := by
  have h1 := norm_le_sum_norm_apply_single (fderiv ℝ w x)
  calc c * ‖fderiv ℝ w x‖
      ≤ (3 / 2 * √(s ^ 2 + ‖x‖ ^ 2)) * ∑ a, ‖fderiv ℝ w x (EuclideanSpace.single a 1)‖ := by
        gcongr
    _ = 3 / 2 * ∑ a, ‖hyperboloidalWeightedDeriv s a w x‖ := by
        rw [mul_assoc, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        simp only [hyperboloidalWeightedDeriv, norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- Pointwise bound of the second derivative by the weighted derivatives: if `0 ≤ c` and
`c ≤ (3/2) φ_s x`, then `c ^ 2 ‖D²w x‖ ≤ (9/4) ∑ a, ∑ b, (|Λ_a Λ_b w x| + |Λ_b w x|)`. -/
theorem sq_mul_norm_iteratedFDeriv_le {s c : ℝ} (hs : s ≠ 0) {w : ℝ³ → ℝ} (hw : ContDiff ℝ 2 w)
    (x : ℝ³) (hc : 0 ≤ c) (hcx : c ≤ 3 / 2 * √(s ^ 2 + ‖x‖ ^ 2)) :
    c ^ 2 * ‖iteratedFDeriv ℝ 2 w x‖ ≤
      9 / 4 * ∑ a, ∑ b, (‖hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w) x‖ +
        ‖hyperboloidalWeightedDeriv s b w x‖) := by
  have hnorm : ‖iteratedFDeriv ℝ 2 w x‖ = ‖fderiv ℝ (fderiv ℝ w) x‖ := by
    rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  have hφsq := Real.sq_sqrt (show 0 ≤ s ^ 2 + ‖x‖ ^ 2 by positivity)
  have h1 : ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ ∑ a, ∑ b,
      ‖fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)‖ :=
    (norm_le_sum_norm_apply_single _).trans
      (Finset.sum_le_sum fun a _ ↦ norm_le_sum_norm_apply_single _)
  have h3 : ∀ a b, (s ^ 2 + ‖x‖ ^ 2) *
      ‖fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)‖ ≤
      ‖hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w) x‖ +
        ‖hyperboloidalWeightedDeriv s b w x‖ := by
    intro a b
    have hid := hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_apply hs hw a b x
    have hxa : |x a| ≤ √(s ^ 2 + ‖x‖ ^ 2) :=
      (Real.norm_eq_abs (x a) ▸ PiLp.norm_apply_le x a).trans
        (Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s]))
    have hΛb : ‖hyperboloidalWeightedDeriv s b w x‖ =
        √(s ^ 2 + ‖x‖ ^ 2) * |fderiv ℝ w x (EuclideanSpace.single b 1)| := by
      rw [hyperboloidalWeightedDeriv, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hΛb, Real.norm_eq_abs, Real.norm_eq_abs]
    calc (s ^ 2 + ‖x‖ ^ 2) *
          |fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)|
        = |hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w) x -
            x a * fderiv ℝ w x (EuclideanSpace.single b 1)| := by
          rw [hid, add_sub_cancel_right, abs_mul,
            abs_of_nonneg (show 0 ≤ s ^ 2 + ‖x‖ ^ 2 by positivity)]
      _ ≤ |hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w) x| +
            |x a * fderiv ℝ w x (EuclideanSpace.single b 1)| := abs_sub _ _
      _ ≤ _ := by
          rw [abs_mul]
          gcongr
  calc c ^ 2 * ‖iteratedFDeriv ℝ 2 w x‖
      ≤ (9 / 4 * (s ^ 2 + ‖x‖ ^ 2)) * ∑ a, ∑ b,
          ‖fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)‖ := by
        rw [hnorm]
        gcongr
        rw [← hφsq]
        nlinarith
    _ = 9 / 4 * ∑ a, ∑ b, (s ^ 2 + ‖x‖ ^ 2) *
          ‖fderiv ℝ (fderiv ℝ w) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)‖ := by
        simp only [Finset.mul_sum, mul_assoc]
    _ ≤ _ := by
        gcongr with a _ b _
        exact h3 a b

/-- The triangle inequality in `L²` for a finite sum of functions, written pointwise. -/
theorem eLpNorm_fun_sum_le {ι : Type*} (t : Finset ι) (g : ι → ℝ³ → ℝ) (μ : Measure ℝ³) :
    eLpNorm (fun x ↦ ∑ i ∈ t, g i x) 2 μ ≤ ∑ i ∈ t, eLpNorm (g i) 2 μ := by
  have : (fun x ↦ ∑ i ∈ t, g i x) = ∑ i ∈ t, g i := by
    ext x
    simp only [Finset.sum_apply]
  rw [this]
  exact eLpNorm_sum_le (by norm_num)

/-- `L²` bound of the first derivative on a set where `c ≤ (3/2) φ_s`. -/
theorem ofReal_mul_eLpNorm_fderiv_le {s c : ℝ} (hc : 0 ≤ c) (w : ℝ³ → ℝ) {t : Set ℝ³}
    (ht : MeasurableSet t) (hct : ∀ x ∈ t, c ≤ 3 / 2 * √(s ^ 2 + ‖x‖ ^ 2)) :
    ENNReal.ofReal c * eLpNorm (fderiv ℝ w) 2 (volume.restrict t) ≤
      2 * ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2 (volume.restrict t) := by
  rw [← Real.enorm_eq_ofReal hc, ← eLpNorm_const_smul]
  calc eLpNorm (c • fderiv ℝ w) 2 (volume.restrict t)
      ≤ eLpNorm ((2 : ℝ) • fun x ↦ ∑ a, ‖hyperboloidalWeightedDeriv s a w x‖) 2
          (volume.restrict t) := by
        refine eLpNorm_mono_ae ((measurable_fderiv ℝ w).const_smul c).aestronglyMeasurable ?_
        refine ae_restrict_of_forall_mem ht fun x hx ↦ ?_
        have h1 := mul_norm_fderiv_le w x (hct x hx)
        have h2 : 0 ≤ ∑ a, ‖hyperboloidalWeightedDeriv s a w x‖ :=
          Finset.sum_nonneg fun a _ ↦ norm_nonneg _
        rw [Pi.smul_apply, Pi.smul_apply, norm_smul, norm_smul, Real.norm_of_nonneg hc,
          Real.norm_of_nonneg h2, Real.norm_of_nonneg zero_le_two]
        linarith
    _ = 2 * eLpNorm (fun x ↦ ∑ a, ‖hyperboloidalWeightedDeriv s a w x‖) 2 (volume.restrict t) := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal zero_le_two, ENNReal.ofReal_ofNat]
    _ ≤ 2 * ∑ a, eLpNorm (fun x ↦ ‖hyperboloidalWeightedDeriv s a w x‖) 2 (volume.restrict t) := by
        gcongr
        exact eLpNorm_fun_sum_le _ _ _
    _ = 2 * ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2 (volume.restrict t) := by
        congr 1
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        exact eLpNorm_norm _ (measurable_hyperboloidalWeightedDeriv s a w).aestronglyMeasurable

/-- `L²` bound of the second derivative on a set where `0 ≤ c ≤ (3/2) φ_s`. -/
theorem ofReal_sq_mul_eLpNorm_iteratedFDeriv_le {s c : ℝ} (hs : s ≠ 0) (hc : 0 ≤ c)
    {w : ℝ³ → ℝ} (hw : ContDiff ℝ 2 w) {t : Set ℝ³} (ht : MeasurableSet t)
    (hct : ∀ x ∈ t, c ≤ 3 / 2 * √(s ^ 2 + ‖x‖ ^ 2)) :
    ENNReal.ofReal (c ^ 2) * eLpNorm (iteratedFDeriv ℝ 2 w) 2 (volume.restrict t) ≤
      3 * (∑ a, ∑ b, eLpNorm (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w)) 2
          (volume.restrict t) +
        3 * ∑ b, eLpNorm (hyperboloidalWeightedDeriv s b w) 2 (volume.restrict t)) := by
  set μ := volume.restrict t
  have hmeas : AEStronglyMeasurable (iteratedFDeriv ℝ 2 w) μ :=
    (hw.continuous_iteratedFDeriv (m := 2) le_rfl).aestronglyMeasurable
  set G : ℝ³ → ℝ := fun x ↦
    ∑ a, ∑ b, ‖hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w) x‖ +
      3 * ∑ b, ‖hyperboloidalWeightedDeriv s b w x‖ with hG
  have hG0 : ∀ x, 0 ≤ G x := fun x ↦ by positivity
  rw [← Real.enorm_eq_ofReal (by positivity), ← eLpNorm_const_smul]
  calc eLpNorm (c ^ 2 • iteratedFDeriv ℝ 2 w) 2 μ ≤ eLpNorm ((3 : ℝ) • G) 2 μ := by
        refine eLpNorm_mono_ae (hmeas.const_smul _) ?_
        refine ae_restrict_of_forall_mem ht fun x hx ↦ ?_
        have h1 := sq_mul_norm_iteratedFDeriv_le hs hw x hc (hct x hx)
        have h2 : ∑ a, ∑ b,
            (‖hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w) x‖ +
              ‖hyperboloidalWeightedDeriv s b w x‖) = G x := by
          simp only [hG, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
        rw [h2] at h1
        rw [Pi.smul_apply, Pi.smul_apply, norm_smul, norm_smul, Real.norm_of_nonneg (by positivity),
          Real.norm_of_nonneg (hG0 x), Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
        linarith [hG0 x]
    _ = 3 * eLpNorm G 2 μ := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ _ := by
        gcongr
        calc eLpNorm G 2 μ ≤ eLpNorm (fun x ↦ ∑ a, ∑ b,
              ‖hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w) x‖) 2 μ +
              eLpNorm ((3 : ℝ) • fun x ↦ ∑ b, ‖hyperboloidalWeightedDeriv s b w x‖) 2 μ :=
            eLpNorm_add_le (by norm_num)
          _ ≤ ∑ a, ∑ b, eLpNorm
                (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w)) 2 μ +
              3 * ∑ b, eLpNorm (hyperboloidalWeightedDeriv s b w) 2 μ := by
            rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num), ENNReal.ofReal_ofNat]
            gcongr
            · refine (eLpNorm_fun_sum_le _ _ _).trans (Finset.sum_le_sum fun a _ ↦ ?_)
              refine (eLpNorm_fun_sum_le _ _ _).trans_eq (Finset.sum_congr rfl fun b _ ↦ ?_)
              exact eLpNorm_norm _
                (measurable_hyperboloidalWeightedDeriv _ _ _).aestronglyMeasurable
            · refine (eLpNorm_fun_sum_le _ _ _).trans_eq (Finset.sum_congr rfl fun b _ ↦ ?_)
              exact eLpNorm_norm _
                (measurable_hyperboloidalWeightedDeriv _ _ _).aestronglyMeasurable

/-! ### The reduction -/

/-- Power bookkeeping for the coefficients of the local bound on a ball of radius `ρ = φ₀ / 3`. -/
theorem three_mul_rpow_mul_rpow {ρ : ℝ} (hρ : 0 < ρ) (e : ℝ) :
    (3 * ρ) ^ (3 / 2 : ℝ) * ρ ^ e = 3 ^ (3 / 2 : ℝ) * ρ ^ (3 / 2 + e) := by
  rw [Real.mul_rpow (by norm_num) hρ.le, mul_assoc, ← Real.rpow_add hρ]

/-- A crude bound `3 ^ (3/2) ≤ 9`. -/
theorem three_rpow_le_nine : (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 9 := by
  calc (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 9 := by
        rw [Real.rpow_two]
        norm_num

/-- **Local hyperboloidal Sobolev inequality, from the local Sobolev bound.** If
`LocalSobolevBound` holds, there is an absolute constant `C` such that for all `s > 0`, all `C²`
functions `w : ℝ³ → ℝ` and all `x₀`, with `φ₀ = √(s ^ 2 + ‖x₀‖ ^ 2)` and `L²` norms on
`ball x₀ (φ₀ / 3)`,
`φ₀ ^ (3/2) |w x₀| ≤ C (‖w‖ + ∑ a, ‖Λ_a w‖ + ∑ a, ∑ b, ‖Λ_a Λ_b w‖)`. -/
theorem exists_hyperboloidalSobolev_ball_of_localSobolevBound (h : LocalSobolevBound) :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 w →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |w x₀|) ≤ (C : ENNReal) *
        (eLpNorm w 2 (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3))) +
          ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2
            (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3))) +
          ∑ a, ∑ b, eLpNorm (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w)) 2
            (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3)))) := by
  obtain ⟨C₁, hC₁⟩ := h
  refine ⟨15 * C₁, fun s hs w hw x₀ ↦ ?_⟩
  set φ₀ := √(s ^ 2 + ‖x₀‖ ^ 2) with hφ₀
  have hφ₀pos : 0 < φ₀ := Real.sqrt_pos.mpr (by positivity)
  set ρ := φ₀ / 3 with hρ
  have hρpos : 0 < ρ := by positivity
  have hφ₀ρ : φ₀ = 3 * ρ := by
    rw [hρ]
    ring
  set μ := volume.restrict (Metric.ball x₀ ρ) with hμ
  set P := eLpNorm w 2 μ
  set Y := eLpNorm (fderiv ℝ w) 2 μ
  set Z := eLpNorm (iteratedFDeriv ℝ 2 w) 2 μ
  set Q := ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2 μ
  set R := ∑ a, ∑ b,
    eLpNorm (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w)) 2 μ
  have hct : ∀ x ∈ Metric.ball x₀ ρ, φ₀ ≤ 3 / 2 * √(s ^ 2 + ‖x‖ ^ 2) :=
    fun x hx ↦ sqrt_sq_add_norm_sq_le_of_mem_ball s hx
  have hY : ENNReal.ofReal φ₀ * Y ≤ 2 * Q :=
    ofReal_mul_eLpNorm_fderiv_le hφ₀pos.le w Metric.isOpen_ball.measurableSet hct
  have hZ : ENNReal.ofReal (φ₀ ^ 2) * Z ≤ 3 * (R + 3 * Q) :=
    ofReal_sq_mul_eLpNorm_iteratedFDeriv_le hs.ne' hφ₀pos.le hw
      Metric.isOpen_ball.measurableSet hct
  have key := hC₁ x₀ ρ w hρpos hw.contDiffOn
  have c1 : φ₀ ^ (3 / 2 : ℝ) * ρ ^ (-(3 / 2 : ℝ)) ≤ 9 := by
    rw [hφ₀ρ, three_mul_rpow_mul_rpow hρpos, show (3 / 2 : ℝ) + -(3 / 2) = 0 by norm_num,
      Real.rpow_zero, mul_one]
    exact three_rpow_le_nine
  have c2 : φ₀ ^ (3 / 2 : ℝ) * ρ ^ (-(1 / 2 : ℝ)) ≤ 3 * φ₀ := by
    rw [hφ₀ρ, three_mul_rpow_mul_rpow hρpos, show (3 / 2 : ℝ) + -(1 / 2) = 1 by norm_num,
      Real.rpow_one]
    nlinarith [three_rpow_le_nine]
  have c3 : φ₀ ^ (3 / 2 : ℝ) * ρ ^ (1 / 2 : ℝ) ≤ φ₀ ^ 2 := by
    rw [hφ₀ρ, three_mul_rpow_mul_rpow hρpos, show (3 / 2 : ℝ) + 1 / 2 = 2 by norm_num,
      Real.rpow_two]
    nlinarith [three_rpow_le_nine, sq_nonneg ρ]
  have hpow : 0 ≤ φ₀ ^ (3 / 2 : ℝ) := by positivity
  calc ENNReal.ofReal (φ₀ ^ (3 / 2 : ℝ) * |w x₀|)
      = ENNReal.ofReal (φ₀ ^ (3 / 2 : ℝ)) * ENNReal.ofReal |w x₀| := ENNReal.ofReal_mul hpow
    _ ≤ ENNReal.ofReal (φ₀ ^ (3 / 2 : ℝ)) * (C₁ * (ENNReal.ofReal (ρ ^ (-(3 / 2 : ℝ))) * P +
          ENNReal.ofReal (ρ ^ (-(1 / 2 : ℝ))) * Y + ENNReal.ofReal (ρ ^ (1 / 2 : ℝ)) * Z)) := by
        gcongr
    _ = C₁ * (ENNReal.ofReal (φ₀ ^ (3 / 2 : ℝ) * ρ ^ (-(3 / 2 : ℝ))) * P +
          ENNReal.ofReal (φ₀ ^ (3 / 2 : ℝ) * ρ ^ (-(1 / 2 : ℝ))) * Y +
          ENNReal.ofReal (φ₀ ^ (3 / 2 : ℝ) * ρ ^ (1 / 2 : ℝ)) * Z) := by
        rw [ENNReal.ofReal_mul hpow, ENNReal.ofReal_mul hpow, ENNReal.ofReal_mul hpow]
        ring
    _ ≤ C₁ * (ENNReal.ofReal 9 * P + ENNReal.ofReal (3 * φ₀) * Y +
          ENNReal.ofReal (φ₀ ^ 2) * Z) := by
        gcongr
    _ = C₁ * (9 * P + 3 * (ENNReal.ofReal φ₀ * Y) + ENNReal.ofReal (φ₀ ^ 2) * Z) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
        ring
    _ ≤ C₁ * (9 * P + 3 * (2 * Q) + 3 * (R + 3 * Q)) := by gcongr
    _ = C₁ * (9 * P + 15 * Q + 3 * R) := by ring
    _ ≤ C₁ * (15 * P + 15 * Q + 15 * R) := by gcongr <;> norm_num
    _ = ((15 * C₁ : NNReal) : ENNReal) * (P + Q + R) := by
        push_cast
        ring

/-- **Hyperboloidal Sobolev inequality, from the local Sobolev bound.** If `LocalSobolevBound`
holds, there is an absolute constant `C` such that for all `s > 0`, all `C²` functions
`w : ℝ³ → ℝ` and all `x₀`, with `L²` norms on `ℝ³`,
`√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3/2) |w x₀| ≤ C (‖w‖ + ∑ a, ‖Λ_a w‖ + ∑ a, ∑ b, ‖Λ_a Λ_b w‖)`. -/
theorem exists_hyperboloidalSobolev_of_localSobolevBound (h : LocalSobolevBound) :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 w →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |w x₀|) ≤ (C : ENNReal) *
        (eLpNorm w 2 volume + ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2 volume +
          ∑ a, ∑ b, eLpNorm (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w))
            2 volume) := by
  obtain ⟨C, hC⟩ := exists_hyperboloidalSobolev_ball_of_localSobolevBound h
  refine ⟨C, fun s hs w hw x₀ ↦ (hC s hs w hw x₀).trans ?_⟩
  have hle : volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3)) ≤ volume :=
    Measure.restrict_le_self
  gcongr

/-! ### The hyperboloidal Sobolev inequality -/

/-- **Theorem 2, local version.** There is an absolute constant `C` such that for all `s > 0`, all
`C²` functions `w : ℝ³ → ℝ` and all `x₀`, with `φ₀ = √(s ^ 2 + ‖x₀‖ ^ 2)` and `L²` norms on
`ball x₀ (φ₀ / 3)`,
`φ₀ ^ (3/2) |w x₀| ≤ C (‖w‖ + ∑ a, ‖Λ_a w‖ + ∑ a, ∑ b, ‖Λ_a Λ_b w‖)`. -/
theorem exists_hyperboloidalSobolev_ball :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 w →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |w x₀|) ≤ (C : ENNReal) *
        (eLpNorm w 2 (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3))) +
          ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2
            (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3))) +
          ∑ a, ∑ b, eLpNorm (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w)) 2
            (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3)))) :=
  exists_hyperboloidalSobolev_ball_of_localSobolevBound localSobolevBound_holds

/-- **Theorem 2 (hyperboloidal Sobolev inequality on `ℝ³`).** There is an absolute constant `C`
such that for all `s > 0`, all `C²` functions `w : ℝ³ → ℝ` and all `x₀`, with `L²` norms on `ℝ³`,
`√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3/2) |w x₀| ≤ C (‖w‖ + ∑ a, ‖Λ_a w‖ + ∑ a, ∑ b, ‖Λ_a Λ_b w‖)`. -/
theorem exists_hyperboloidalSobolev :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 w →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |w x₀|) ≤ (C : ENNReal) *
        (eLpNorm w 2 volume + ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2 volume +
          ∑ a, ∑ b, eLpNorm (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w))
            2 volume) :=
  exists_hyperboloidalSobolev_of_localSobolevBound localSobolevBound_holds

end VectorFieldMethod.EuclideanSobolev
