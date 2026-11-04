/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.IntermediateValue

/-!
# A square-root Grönwall inequality

Let `E` be continuous on `[a, b]`, `g ≥ 0` integrable on `[a, b]`, and assume that
`E(s) ≤ A + 2 ∫_a^s g E^{1/2}` for all `s ∈ [a, b]`. Then `E(s)^{1/2} ≤ A^{1/2} + ∫_a^s g` for all
`s ∈ [a, b]`. This is the form of Grönwall's lemma used to close energy estimates: if
`E' ≤ 2 g E^{1/2}`, then `(E^{1/2})' ≤ g`.

## Main statements

* `sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral`: the inequality above.
* `sqrt_add_two_mul_integral_le_of_pos`: the main step, for `A > 0`: with
  `Φ(s) = A + 2 ∫_a^s g E^{1/2}`, `Φ(s)^{1/2} ≤ A^{1/2} + ∫_a^s g`.

## Implementation notes

`g` is only assumed integrable, so `Φ` need not be differentiable everywhere, and the proof does
not differentiate. Write `R = Φ^{1/2}` and `G(s) = ∫_a^s g`. Since `E ≤ Φ` and `Φ` is
nondecreasing, `Φ(z) - Φ(x) ≤ 2 R(z) (G(z) - G(x))` for `a ≤ x ≤ z ≤ b`, which gives
`2 A^{1/2} ((R(z) - R(x)) - (G(z) - G(x))) ≤ (R(z) - R(x)) (G(z) - G(x))`: the increments of
`R - G` are of second order. By continuous induction
(`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`), using only the continuity of `G`, one gets
`R - A^{1/2} - G ≤ ε (R - A^{1/2})` on `[a, b]` for every `ε > 0`. The case `A ≤ 0` follows by
applying the case `A > 0` to `max A 0 + δ²` and letting `δ → 0`.

The hypotheses `E ≥ 0` and `A ≥ 0` of the usual statement are not needed: `Real.sqrt` is `0` on
negative numbers, and the statement remains true without them.
-/

@[expose] public noncomputable section

open Set Filter Topology MeasureTheory

namespace VectorFieldMethod.Analysis

variable {a b A : ℝ} {E g : ℝ → ℝ}

/-- **Square-root Grönwall inequality, main step.** Let `A > 0`, `E` continuous on `[a, b]`, and
`g ≥ 0` integrable on `[a, b]`, with `E(s) ≤ Φ(s) = A + 2 ∫_a^s g E^{1/2}` on `[a, b]`. Then
`Φ(s)^{1/2} ≤ A^{1/2} + ∫_a^s g` for `s ∈ [a, b]`. -/
theorem sqrt_add_two_mul_integral_le_of_pos (hA : 0 < A) (hE : ContinuousOn E (Icc a b))
    (hg : IntegrableOn g (Icc a b)) (hg0 : ∀ s ∈ Icc a b, 0 ≤ g s)
    (h : ∀ s ∈ Icc a b, E s ≤ A + 2 * ∫ τ in a..s, g τ * √(E τ)) {s : ℝ} (hs : s ∈ Icc a b) :
    √(A + 2 * ∫ τ in a..s, g τ * √(E τ)) ≤ √A + ∫ τ in a..s, g τ := by
  have hab : a ≤ b := hs.1.trans hs.2
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  set Φ : ℝ → ℝ := fun s ↦ A + 2 * ∫ τ in a..s, g τ * √(E τ) with hΦdef
  set G : ℝ → ℝ := fun s ↦ ∫ τ in a..s, g τ with hGdef
  change √(Φ s) ≤ √A + G s
  -- integrability
  have hint : IntegrableOn (fun τ ↦ g τ * √(E τ)) (Icc a b) :=
    hg.mul_continuousOn hE.sqrt isCompact_Icc
  have hii (x z : ℝ) (hx : x ∈ Icc a b) (hz : z ∈ Icc a b) :
      IntervalIntegrable (fun τ ↦ g τ * √(E τ)) volume x z :=
    (hint.mono_set (uIcc_subset_Icc hx hz)).intervalIntegrable
  have hgi (x z : ℝ) (hx : x ∈ Icc a b) (hz : z ∈ Icc a b) : IntervalIntegrable g volume x z :=
    (hg.mono_set (uIcc_subset_Icc hx hz)).intervalIntegrable
  -- increments of `Φ` and `G`
  have hΦsub (x z : ℝ) (hx : x ∈ Icc a b) (hz : z ∈ Icc a b) :
      Φ z - Φ x = 2 * ∫ τ in x..z, g τ * √(E τ) := by
    simp only [hΦdef]
    rw [← intervalIntegral.integral_interval_sub_left (hii a z ha hz) (hii a x ha hx)]
    ring
  have hGsub (x z : ℝ) (hx : x ∈ Icc a b) (hz : z ∈ Icc a b) :
      G z - G x = ∫ τ in x..z, g τ :=
    intervalIntegral.integral_interval_sub_left (hgi a z ha hz) (hgi a x ha hx)
  have hΦmono (x z : ℝ) (hx : x ∈ Icc a b) (hz : z ∈ Icc a b) (hxz : x ≤ z) : Φ x ≤ Φ z := by
    have h0 : 0 ≤ ∫ τ in x..z, g τ * √(E τ) :=
      intervalIntegral.integral_nonneg hxz fun τ hτ ↦
        mul_nonneg (hg0 τ ⟨hx.1.trans hτ.1, hτ.2.trans hz.2⟩) (Real.sqrt_nonneg _)
    linarith [hΦsub x z hx hz]
  have hGmono (x z : ℝ) (hx : x ∈ Icc a b) (hz : z ∈ Icc a b) (hxz : x ≤ z) : G x ≤ G z := by
    have h0 : 0 ≤ ∫ τ in x..z, g τ :=
      intervalIntegral.integral_nonneg hxz fun τ hτ ↦ hg0 τ ⟨hx.1.trans hτ.1, hτ.2.trans hz.2⟩
    linarith [hGsub x z hx hz]
  have hΦa : Φ a = A := by simp [hΦdef]
  have hGa : G a = 0 := by simp [hGdef]
  have hΦA (x : ℝ) (hx : x ∈ Icc a b) : A ≤ Φ x := hΦa ▸ hΦmono a x ha hx hx.1
  -- the increment of `Φ` on `[x, z]` is at most `2 √(Φ z) (G z - G x)`
  have hstep (x z : ℝ) (hx : x ∈ Icc a b) (hz : z ∈ Icc a b) (hxz : x ≤ z) :
      Φ z - Φ x ≤ 2 * (√(Φ z) * (G z - G x)) := by
    have hmono : ∫ τ in x..z, g τ * √(E τ) ≤ ∫ τ in x..z, g τ * √(Φ z) :=
      intervalIntegral.integral_mono_on hxz (hii x z hx hz) ((hgi x z hx hz).mul_const _)
        fun τ hτ ↦ by
          have hτ' : τ ∈ Icc a b := ⟨hx.1.trans hτ.1, hτ.2.trans hz.2⟩
          exact mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt ((h τ hτ').trans (hΦmono τ z hτ' hz hτ.2))) (hg0 τ hτ')
    rw [intervalIntegral.integral_mul_const] at hmono
    rw [hΦsub x z hx hz, hGsub x z hx hz]
    linarith
  -- continuity
  have hΦc : ContinuousOn Φ (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := a) (b := b)
      (by rwa [uIcc_of_le hab] : IntegrableOn (fun τ ↦ g τ * √(E τ)) (uIcc a b))
    rw [uIcc_of_le hab] at this
    exact continuousOn_const.add (continuousOn_const.mul this)
  have hGc : ContinuousOn G (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := a) (b := b)
      (by rwa [uIcc_of_le hab] : IntegrableOn g (uIcc a b))
    rwa [uIcc_of_le hab] at this
  have hsA : 0 < √A := Real.sqrt_pos.2 hA
  -- continuous induction: for every `ε > 0`, `√Φ - √A - G ≤ ε (√Φ - √A)` on `[a, b]`
  have key (ε : ℝ) (hε : 0 < ε) :
      Icc a b ⊆ {x | √(Φ x) - √A - G x ≤ ε * (√(Φ x) - √A)} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_ ?_
    · have hc : ContinuousOn (fun x ↦ ε * (√(Φ x) - √A) - (√(Φ x) - √A - G x)) (Icc a b) :=
        (continuousOn_const.mul (hΦc.sqrt.sub continuousOn_const)).sub
          ((hΦc.sqrt.sub continuousOn_const).sub hGc)
      convert hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0 : ℝ)))
        using 1
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Ici, sub_nonneg]
      tauto
    · simp [hΦa, hGa]
    · rintro y ⟨hyS, hya, hyb⟩
      have hyI : y ∈ Icc a b := ⟨hya, hyb.le⟩
      have hGt : Tendsto G (𝓝[>] y) (𝓝 (G y)) := by
        rw [← nhdsWithin_Ioo_eq_nhdsGT hyb]
        exact (hGc y hyI).mono fun z hz ↦ ⟨hya.trans hz.1.le, hz.2.le⟩
      have hδ : 0 < 2 * √A * ε := by positivity
      filter_upwards [hGt (Iio_mem_nhds (by linarith : G y < G y + 2 * √A * ε)),
        Ioo_mem_nhdsGT hyb] with z hz1 hz2
      have hzI : z ∈ Icc a b := ⟨hya.trans hz2.1.le, hz2.2.le⟩
      have hst := hstep y z hyI hzI hz2.1.le
      have hR₁ : √A ≤ √(Φ y) := Real.sqrt_le_sqrt (hΦA y hyI)
      have hR₁₂ : √(Φ y) ≤ √(Φ z) := Real.sqrt_le_sqrt (hΦmono y z hyI hzI hz2.1.le)
      have hGyz : G y ≤ G z := hGmono y z hyI hzI hz2.1.le
      have hsq₁ : √(Φ y) ^ 2 = Φ y := Real.sq_sqrt (hA.le.trans (hΦA y hyI))
      have hsq₂ : √(Φ z) ^ 2 = Φ z := Real.sq_sqrt (hA.le.trans (hΦA z hzI))
      have hyS' : √(Φ y) - √A - G y ≤ ε * (√(Φ y) - √A) := hyS
      have hz1' : G z < G y + 2 * √A * ε := hz1
      -- the increment of `√Φ - G` on `[y, z]` is at most `ε` times the increment of `√Φ`
      have hQ : (√(Φ z) - √(Φ y)) - (G z - G y) ≤ ε * (√(Φ z) - √(Φ y)) := by
        by_contra hQ
        rw [not_le] at hQ
        have e1 : (√(Φ z) - √(Φ y) - (G z - G y)) * (√(Φ z) + √(Φ y)) ≤
            (√(Φ z) - √(Φ y)) * (G z - G y) := by nlinarith
        have e2 : (√(Φ z) - √(Φ y) - (G z - G y)) * (2 * √A) ≤
            (√(Φ z) - √(Φ y) - (G z - G y)) * (√(Φ z) + √(Φ y)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
        have e3 : (√(Φ z) - √(Φ y)) * (G z - G y) ≤ (√(Φ z) - √(Φ y)) * (2 * √A * ε) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        nlinarith
      change √(Φ z) - √A - G z ≤ ε * (√(Φ z) - √A)
      linarith
  -- conclusion
  have hfin (ε : ℝ) (hε : 0 < ε) : √(Φ s) - √A - G s ≤ ε * (√(Φ s) - √A) := key ε hε hs
  by_contra hcon
  rw [not_le] at hcon
  have hX : 0 < √(Φ s) - √A - G s := by linarith
  have hY : 0 ≤ √(Φ s) - √A := sub_nonneg.2 (Real.sqrt_le_sqrt (hΦA s hs))
  have h1 := hfin ((√(Φ s) - √A - G s) / (√(Φ s) - √A + 1)) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h1
  nlinarith

/-- **Square-root Grönwall inequality.** Let `E` be continuous on `[a, b]` and `g ≥ 0` integrable
on `[a, b]`. If `E(s) ≤ A + 2 ∫_a^s g E^{1/2}` for all `s ∈ [a, b]`, then
`E(s)^{1/2} ≤ A^{1/2} + ∫_a^s g` for all `s ∈ [a, b]`.

The usual hypotheses `E ≥ 0` and `A ≥ 0` are not needed, since `√x = 0` for `x < 0`. -/
theorem sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral (hE : ContinuousOn E (Icc a b))
    (hg : IntegrableOn g (Icc a b)) (hg0 : ∀ s ∈ Icc a b, 0 ≤ g s)
    (h : ∀ s ∈ Icc a b, E s ≤ A + 2 * ∫ τ in a..s, g τ * √(E τ)) {s : ℝ} (hs : s ∈ Icc a b) :
    √(E s) ≤ √A + ∫ τ in a..s, g τ := by
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  have hA' : 0 < max A 0 + δ ^ 2 := by positivity
  have h' (s : ℝ) (hs : s ∈ Icc a b) :
      E s ≤ (max A 0 + δ ^ 2) + 2 * ∫ τ in a..s, g τ * √(E τ) :=
    (h s hs).trans (by nlinarith [le_max_left A 0])
  have key := sqrt_add_two_mul_integral_le_of_pos hA' hE hg hg0 h' hs
  have hE' := Real.sqrt_le_sqrt (h' s hs)
  have hmax : √(max A 0) = √A := by
    rcases le_total A 0 with hA | hA
    · rw [max_eq_right hA, Real.sqrt_zero, Real.sqrt_eq_zero_of_nonpos hA]
    · rw [max_eq_left hA]
  have hsqrt : √(max A 0 + δ ^ 2) ≤ √A + δ := by
    rw [← hmax]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt (le_max_right A 0), Real.sqrt_nonneg (max A 0)]
  linarith

/-! ### Sanity checks -/

/-- `E(s) = s²`, `g = 1` and `A = 0` on `[0, 1]`: the hypothesis of
`sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral` holds, with equality
`s² = 2 ∫_0^s √(τ²) dτ`, and the conclusion `√(s²) ≤ √0 + ∫_0^s 1 = s` is an equality as well:
the inequality is sharp. -/
example {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : √(s ^ 2) ≤ √0 + ∫ _ in (0 : ℝ)..s, (1 : ℝ) := by
  refine sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral (E := fun τ ↦ τ ^ 2)
    (g := fun _ ↦ 1) (by fun_prop) (integrableOn_const (by simp))
    (fun _ _ ↦ zero_le_one) (fun t ht ↦ ?_) hs
  have hcongr : ∫ τ in (0 : ℝ)..t, (1 : ℝ) * √(τ ^ 2) = ∫ τ in (0 : ℝ)..t, τ :=
    intervalIntegral.integral_congr fun τ hτ ↦ by
      rw [uIcc_of_le ht.1] at hτ
      simp [Real.sqrt_sq hτ.1]
  simp only [hcongr, integral_id]
  linarith

/-- `E(s) = (1 + s)²`, `g = 1` and `A = 1` on `[0, 1]`: the hypothesis of
`sqrt_add_two_mul_integral_le_of_pos` holds with equality,
`(1 + s)² = 1 + 2 ∫_0^s ((1 + τ)²)^{1/2} dτ`, and its conclusion is an equality as well: both sides
are `1 + s`. The example proves the two equalities and applies the theorem. -/
example {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (1 + s) ^ 2 = 1 + 2 * ∫ τ in (0 : ℝ)..s, (1 : ℝ) * √((1 + τ) ^ 2) ∧
      √(1 + 2 * ∫ τ in (0 : ℝ)..s, (1 : ℝ) * √((1 + τ) ^ 2)) =
        √1 + ∫ _ in (0 : ℝ)..s, (1 : ℝ) ∧
      √(1 + 2 * ∫ τ in (0 : ℝ)..s, (1 : ℝ) * √((1 + τ) ^ 2)) ≤
        √1 + ∫ _ in (0 : ℝ)..s, (1 : ℝ) := by
  -- `∫_0^t ((1 + τ)²)^{1/2} dτ = ∫_0^t (1 + τ) dτ = t + t² / 2` for `t ≥ 0`
  have hint (t : ℝ) (ht : 0 ≤ t) :
      ∫ τ in (0 : ℝ)..t, (1 : ℝ) * √((1 + τ) ^ 2) = t + t ^ 2 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun τ ↦ 1 + τ) fun τ hτ ↦ by
      rw [uIcc_of_le ht] at hτ
      simp [Real.sqrt_sq (by linarith [hτ.1] : (0 : ℝ) ≤ 1 + τ)]]
    rw [intervalIntegral.integral_add intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
    simp
  have hsq (t : ℝ) (ht : 0 ≤ t) : √(1 + 2 * (t + t ^ 2 / 2)) = 1 + t := by
    rw [show 1 + 2 * (t + t ^ 2 / 2) = (1 + t) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  refine ⟨by rw [hint s hs.1]; ring, ?_, sqrt_add_two_mul_integral_le_of_pos
    (E := fun τ ↦ (1 + τ) ^ 2) (g := fun _ ↦ 1) one_pos (by fun_prop)
    (integrableOn_const (by simp)) (fun _ _ ↦ zero_le_one) (fun t ht ↦ ?_) hs⟩
  · rw [hint s hs.1, hsq s hs.1, Real.sqrt_one, integral_one]
    ring
  · rw [hint t ht.1]
    nlinarith

/-- `E(s) = 2 s - 1`, `g = 1` and `A = 1` on `[0, 1]`: `E` takes negative values (`E(0) = -1`), so
the usual hypothesis `E ≥ 0` fails, but the hypothesis of
`sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral` holds, since
`E(s) ≤ 1 ≤ 1 + 2 ∫_0^s √(2 τ - 1) dτ`, and the theorem gives `√(2 s - 1) ≤ 1 + s`. This shows the
gain from dropping the hypothesis `E ≥ 0`. -/
example : (∃ s ∈ Icc (0 : ℝ) 1, 2 * s - 1 < 0) ∧
    ∀ s ∈ Icc (0 : ℝ) 1, √(2 * s - 1) ≤ √1 + ∫ _ in (0 : ℝ)..s, (1 : ℝ) :=
  ⟨⟨0, ⟨le_rfl, zero_le_one⟩, by norm_num⟩, fun _ hs ↦
    sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral (E := fun τ ↦ 2 * τ - 1)
      (g := fun _ ↦ 1) (by fun_prop) (integrableOn_const (by simp)) (fun _ _ ↦ zero_le_one)
      (fun t ht ↦ by
        have h0 : 0 ≤ ∫ τ in (0 : ℝ)..t, (1 : ℝ) * √(2 * τ - 1) :=
          intervalIntegral.integral_nonneg ht.1 fun τ _ ↦ by positivity
        linarith [ht.2]) hs⟩

end VectorFieldMethod.Analysis
