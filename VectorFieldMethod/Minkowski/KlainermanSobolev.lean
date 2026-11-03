/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Analysis.HyperboloidalSobolev
public import VectorFieldMethod.Minkowski.VectorFields

/-!
# The Klainerman–Sobolev inequality on hyperboloids

For `s > 0` let `H_s = {(t, x) : t = √(s ^ 2 + ‖x‖ ^ 2)}` be the upper sheet of the hyperboloid
`t ^ 2 - ‖x‖ ^ 2 = s ^ 2`. The restriction of a real function `v` on spacetime to `H_s` is the
function `v|_{H_s} x = v (√(s ^ 2 + ‖x‖ ^ 2), x)` on `ℝ³` (`restrictHyperboloid s v`).

This file connects the weighted derivatives `Λ_a = φ_s ∂_a` on `ℝ³` of the analysis layer
(`EuclideanSobolev.hyperboloidalWeightedDeriv s a`, with `φ_s x = √(s ^ 2 + ‖x‖ ^ 2)`) with the
Lorentz boosts `L_a = t ∂_a + x_a ∂_t` (`boost a`), and deduces from the weighted inequality on
`ℝ³` (`EuclideanSobolev.exists_hyperboloidalSobolev`) the Klainerman–Sobolev inequality on
hyperboloids
`sup_{H_s} t ^ (3/2) |u| ≤ C ∑_{|J| ≤ 2} ‖L^J u‖_{L²_f(H_s)}`,
where `‖v‖_{L²_f(H_s)} = ‖v|_{H_s}‖_{L²(ℝ³)}` is the `L²` norm on `H_s` for the flat measure `dx`
and `C` is an absolute constant. See `docs/hyperboloidal-sobolev.md`.

## Main definitions

* `hyperboloidPoint s x`: the point `(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s` above `x ∈ ℝ³`.
* `restrictHyperboloid s v`: the restriction `x ↦ v (√(s ^ 2 + ‖x‖ ^ 2), x)` of `v` to `H_s`.

## Main statements

* `hyperboloidalWeightedDeriv_restrictHyperboloid_apply`: the restriction formula
  `Λ_a (v|_{H_s}) x = (L_a v)|_{H_s} x`, for `s ≠ 0` and `v` differentiable at the point
  `(√(s ^ 2 + ‖x‖ ^ 2), x)`.
* `hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid`: the second-order
  formula `Λ_a Λ_b (u|_{H_s}) = (L_a L_b u)|_{H_s}` on `ℝ³`, for `s ≠ 0` and `u` of class `C²` on
  an open set containing `H_s`.
* `contDiff_restrictHyperboloid`: under the same hypotheses, `u|_{H_s}` is `C²` on `ℝ³` (more
  generally `C^n` if `u` is `C^n` near `H_s`).
* `exists_klainermanSobolev_hyperboloid`: the Klainerman–Sobolev inequality on `H_s`, with an
  absolute constant `C` (independent of `s`, `u` and the point) and `L²` norms on `H_s` for the
  flat measure `dx`. It is `EuclideanSobolev.exists_hyperboloidalSobolev` applied to
  `w = u|_{H_s}`, whose weighted derivatives are rewritten with the two restriction formulas.
* `eLpNorm_restrictHyperboloid_lt_top`: the restriction to `H_s` of a continuous function with
  compact support is square integrable. The sanity checks use it to show that the right-hand side
  of the inequality is finite for a smooth bump function.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace VectorFieldMethod.Minkowski

open VectorFieldMethod.EuclideanSobolev

/-! ### Restriction to a hyperboloid -/

/-- The point `(√(s ^ 2 + ‖x‖ ^ 2), x)` of the hyperboloid `H_s = {t = √(s ^ 2 + ‖x‖ ^ 2)}`
above `x ∈ ℝ³`. -/
def hyperboloidPoint (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : Spacetime :=
  (√(s ^ 2 + ‖x‖ ^ 2), x)

/-- The restriction `v|_{H_s}` of `v : Spacetime → ℝ` to the hyperboloid
`H_s = {t = √(s ^ 2 + ‖x‖ ^ 2)}`, as a function on `ℝ³`:
`v|_{H_s} x = v (√(s ^ 2 + ‖x‖ ^ 2), x)`. -/
def restrictHyperboloid (s : ℝ) (v : Spacetime → ℝ) : EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x ↦ v (√(s ^ 2 + ‖x‖ ^ 2), x)

theorem restrictHyperboloid_apply (s : ℝ) (v : Spacetime → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    restrictHyperboloid s v x = v (√(s ^ 2 + ‖x‖ ^ 2), x) :=
  rfl

theorem restrictHyperboloid_eq_comp (s : ℝ) (v : Spacetime → ℝ) :
    restrictHyperboloid s v = v ∘ hyperboloidPoint s :=
  rfl

/-- `hyperboloidPoint s x` lies on the hyperboloid `H_s`. -/
theorem hyperboloidPoint_mem (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    hyperboloidPoint s x ∈ {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} :=
  rfl

/-- The derivative of `x ↦ (√(s ^ 2 + ‖x‖ ^ 2), x)`, for `s ≠ 0`. -/
theorem hasFDerivAt_hyperboloidPoint {s : ℝ} (hs : s ≠ 0) (x : EuclideanSpace ℝ (Fin 3)) :
    HasFDerivAt (hyperboloidPoint s)
      ((fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) ↦ √(s ^ 2 + ‖y‖ ^ 2)) x).prod
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)))) x :=
  ((contDiff_sqrt_sq_add_norm_sq hs).differentiable one_ne_zero x).hasFDerivAt.prodMk
    (hasFDerivAt_id x)

/-! ### The restriction formula -/

/-- The value of the boost field at the point `(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s`:
`(x_a, φ_s(x) e_a) = φ_s(x) (x_a / φ_s(x), e_a)`, for `φ_s(x) ≠ 0`. -/
theorem boostField_hyperboloidPoint {s : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hφ : √(s ^ 2 + ‖x‖ ^ 2) ≠ 0) (a : Fin 3) :
    boostField a (hyperboloidPoint s x) =
      √(s ^ 2 + ‖x‖ ^ 2) • (x a / √(s ^ 2 + ‖x‖ ^ 2), EuclideanSpace.single a (1 : ℝ)) := by
  rw [boostField, Prod.smul_mk, smul_eq_mul, mul_div_cancel₀ _ hφ]
  rfl

/-- **Restriction formula.** For `s ≠ 0` and `v` differentiable at the point
`(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s`, `Λ_a (v|_{H_s}) x = (L_a v)|_{H_s} x`. -/
theorem hyperboloidalWeightedDeriv_restrictHyperboloid_apply {s : ℝ} (hs : s ≠ 0) (a : Fin 3)
    {v : Spacetime → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hv : DifferentiableAt ℝ v (√(s ^ 2 + ‖x‖ ^ 2), x)) :
    hyperboloidalWeightedDeriv s a (restrictHyperboloid s v) x =
      restrictHyperboloid s (boost a v) x := by
  have hφ : √(s ^ 2 + ‖x‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hv' : HasFDerivAt v (fderiv ℝ v (hyperboloidPoint s x)) (hyperboloidPoint s x) :=
    hv.hasFDerivAt
  have h := hv'.comp x (hasFDerivAt_hyperboloidPoint hs x)
  rw [restrictHyperboloid_apply, show ((√(s ^ 2 + ‖x‖ ^ 2), x) : Spacetime) =
    hyperboloidPoint s x from rfl, boost_apply, boostField_hyperboloidPoint hφ,
    ContinuousLinearMap.map_smul, smul_eq_mul, hyperboloidalWeightedDeriv,
    restrictHyperboloid_eq_comp, h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, fderiv_sqrt_sq_add_norm_sq_apply hs,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul]

/-- **Restriction formula, as functions.** For `s ≠ 0` and `v` differentiable at every point
`(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s`, `Λ_a (v|_{H_s}) = (L_a v)|_{H_s}`. -/
theorem hyperboloidalWeightedDeriv_restrictHyperboloid {s : ℝ} (hs : s ≠ 0) (a : Fin 3)
    {v : Spacetime → ℝ}
    (hv : ∀ x : EuclideanSpace ℝ (Fin 3), DifferentiableAt ℝ v (√(s ^ 2 + ‖x‖ ^ 2), x)) :
    hyperboloidalWeightedDeriv s a (restrictHyperboloid s v) =
      restrictHyperboloid s (boost a v) :=
  funext fun x ↦ hyperboloidalWeightedDeriv_restrictHyperboloid_apply hs a (hv x)

/-- A function of class `C^n` on an open set containing `H_s` is `C^n` at every point
`(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s`. -/
theorem contDiffAt_of_contDiffOn_of_hyperboloid_subset {s : ℝ} {n : ℕ∞ω} {u : Spacetime → ℝ}
    {U : Set Spacetime} (hU : IsOpen U)
    (hHU : {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} ⊆ U) (hu : ContDiffOn ℝ n u U)
    (x : EuclideanSpace ℝ (Fin 3)) : ContDiffAt ℝ n u (√(s ^ 2 + ‖x‖ ^ 2), x) :=
  hu.contDiffAt (hU.mem_nhds (hHU (hyperboloidPoint_mem s x)))

/-- **Restriction formula on `H_s`.** For `s ≠ 0` and `u` differentiable on an open set `U`
containing `H_s`, `Λ_a (u|_{H_s}) = (L_a u)|_{H_s}` as functions on `ℝ³`. -/
theorem hyperboloidalWeightedDeriv_restrictHyperboloid_of_differentiableOn {s : ℝ}
    (hs : s ≠ 0) {u : Spacetime → ℝ} {U : Set Spacetime} (hU : IsOpen U)
    (hHU : {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} ⊆ U) (hu : DifferentiableOn ℝ u U)
    (a : Fin 3) :
    hyperboloidalWeightedDeriv s a (restrictHyperboloid s u) =
      restrictHyperboloid s (boost a u) :=
  hyperboloidalWeightedDeriv_restrictHyperboloid hs a fun x ↦
    hu.differentiableAt (hU.mem_nhds (hHU (hyperboloidPoint_mem s x)))

/-- **Second-order restriction formula.** For `s ≠ 0` and `u` of class `C²` on an open set `U`
containing `H_s`, `Λ_a Λ_b (u|_{H_s}) = (L_a L_b u)|_{H_s}` as functions on `ℝ³`, with the indices
in the same order. -/
theorem hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid {s : ℝ}
    (hs : s ≠ 0) {u : Spacetime → ℝ} {U : Set Spacetime} (hU : IsOpen U)
    (hHU : {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (a b : Fin 3) :
    hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b (restrictHyperboloid s u)) =
      restrictHyperboloid s (boost a (boost b u)) := by
  have hP := contDiffAt_of_contDiffOn_of_hyperboloid_subset hU hHU hu
  rw [hyperboloidalWeightedDeriv_restrictHyperboloid_of_differentiableOn hs hU hHU
      (hu.differentiableOn two_ne_zero) b,
    hyperboloidalWeightedDeriv_restrictHyperboloid (v := boost b u) hs a fun x ↦
      (contDiffAt_derivAlong (n := 1) (contDiff_boostField b).contDiffAt
        (hP x)).differentiableAt one_ne_zero]

/-! ### Regularity of the restriction -/

/-- The map `x ↦ (√(s ^ 2 + ‖x‖ ^ 2), x)` is smooth for `s ≠ 0`. -/
theorem contDiff_hyperboloidPoint {s : ℝ} (hs : s ≠ 0) {n : ℕ∞ω} :
    ContDiff ℝ n (hyperboloidPoint s) :=
  ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt fun x ↦ by positivity).prodMk contDiff_id

/-- **Regularity of the restriction.** For `s ≠ 0` and `u` of class `C^n` on an open set `U`
containing `H_s`, the restriction `u|_{H_s}` is `C^n` on `ℝ³`; in particular it is `C²` if `u` is
`C²` on `U`. -/
theorem contDiff_restrictHyperboloid {s : ℝ} (hs : s ≠ 0) {n : ℕ∞ω} {u : Spacetime → ℝ}
    {U : Set Spacetime} (hU : IsOpen U)
    (hHU : {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} ⊆ U) (hu : ContDiffOn ℝ n u U) :
    ContDiff ℝ n (restrictHyperboloid s u) :=
  contDiff_iff_contDiffAt.mpr fun x ↦
    ContDiffAt.comp (f := hyperboloidPoint s) x
      (contDiffAt_of_contDiffOn_of_hyperboloid_subset hU hHU hu x)
      (contDiff_hyperboloidPoint hs).contDiffAt

/-! ### The Klainerman–Sobolev inequality on hyperboloids -/

/-- **Klainerman–Sobolev inequality on hyperboloids.** There is an absolute constant `C` such that
for all `s > 0`, every `u` of class `C²` on an open set `U` containing
`H_s = {t = √(s ^ 2 + ‖x‖ ^ 2)}` and every point `(t₀, x₀) = (√(s ^ 2 + ‖x₀‖ ^ 2), x₀)` of `H_s`,
`t₀ ^ (3/2) |u (t₀, x₀)| ≤ C ∑_{|J| ≤ 2} ‖L^J u‖_{L²_f(H_s)}`, where
`‖v‖_{L²_f(H_s)} = ‖v|_{H_s}‖_{L²(ℝ³)}` is the `L²` norm on `H_s` for the flat measure `dx`, and
`L^J` runs over `1`, the three boosts `L_a` and the nine products `L_a L_b`. -/
theorem exists_klainermanSobolev_hyperboloid :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ (u : Spacetime → ℝ) (U : Set Spacetime), IsOpen U →
      {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} ⊆ U → ContDiffOn ℝ 2 u U →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |u (√(s ^ 2 + ‖x₀‖ ^ 2), x₀)|) ≤
        (C : ENNReal) *
          (eLpNorm (restrictHyperboloid s u) 2 volume +
            ∑ a, eLpNorm (restrictHyperboloid s (boost a u)) 2 volume +
            ∑ a, ∑ b, eLpNorm (restrictHyperboloid s (boost a (boost b u))) 2 volume) := by
  obtain ⟨C, hC⟩ := exists_hyperboloidalSobolev
  refine ⟨C, fun s hs u U hU hHU hu x₀ ↦ ?_⟩
  have h := hC s hs (restrictHyperboloid s u) (contDiff_restrictHyperboloid hs.ne' hU hHU hu) x₀
  simp only [hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid hs.ne' hU
    hHU hu] at h
  simp only [hyperboloidalWeightedDeriv_restrictHyperboloid_of_differentiableOn hs.ne' hU hHU
    (hu.differentiableOn two_ne_zero)] at h
  exact h

/-! ### Restrictions of compactly supported functions -/

/-- The restriction of a continuous function to `H_s` is continuous. -/
theorem continuous_restrictHyperboloid (s : ℝ) {v : Spacetime → ℝ} (hv : Continuous v) :
    Continuous (restrictHyperboloid s v) :=
  hv.comp ((continuous_const.add (continuous_norm.pow 2)).sqrt.prodMk continuous_id)

/-- The restriction to `H_s` of a function with compact support has compact support. -/
theorem hasCompactSupport_restrictHyperboloid (s : ℝ) {v : Spacetime → ℝ}
    (hv : HasCompactSupport v) : HasCompactSupport (restrictHyperboloid s v) :=
  HasCompactSupport.intro (hv.isCompact.image continuous_snd) fun x hx ↦
    image_eq_zero_of_notMem_tsupport (f := v) (x := (√(s ^ 2 + ‖x‖ ^ 2), x)) fun h ↦
      hx ⟨_, h, rfl⟩

/-- The restriction to `H_s` of a continuous function with compact support is square
integrable on `ℝ³`. -/
theorem eLpNorm_restrictHyperboloid_lt_top (s : ℝ) {v : Spacetime → ℝ} (hv : Continuous v)
    (hvs : HasCompactSupport v) : eLpNorm (restrictHyperboloid s v) 2 volume < ⊤ :=
  ((continuous_restrictHyperboloid s hv).memLp_of_hasCompactSupport
    (hasCompactSupport_restrictHyperboloid s hvs)).eLpNorm_lt_top

/-- The derivative along a vector field of a function with compact support has compact
support. -/
theorem hasCompactSupport_derivAlong {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : Spacetime → Spacetime) {u : Spacetime → F} (hu : HasCompactSupport u) :
    HasCompactSupport (derivAlong V u) :=
  (hu.fderiv (𝕜 := ℝ)).mono fun p hp h ↦ hp (by rw [derivAlong_apply, h]; rfl)

/-! ### Sanity checks -/

/-- The hypotheses of `exists_klainermanSobolev_hyperboloid` hold for `u = t`, which is smooth on
the whole spacetime `U = Set.univ`. (Here `t|_{H_s} = √(s ^ 2 + ‖x‖ ^ 2)` is not square
integrable on `ℝ³`, so the right-hand side is `∞`.) -/
example : ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ x₀ : EuclideanSpace ℝ (Fin 3),
    ENNReal.ofReal
        (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |timeCoord (√(s ^ 2 + ‖x₀‖ ^ 2), x₀)|) ≤
      (C : ENNReal) *
        (eLpNorm (restrictHyperboloid s timeCoord) 2 volume +
          ∑ a, eLpNorm (restrictHyperboloid s (boost a timeCoord)) 2 volume +
          ∑ a, ∑ b, eLpNorm (restrictHyperboloid s (boost a (boost b timeCoord))) 2 volume) := by
  obtain ⟨C, hC⟩ := exists_klainermanSobolev_hyperboloid
  exact ⟨C, fun s hs x₀ ↦ hC s hs timeCoord Set.univ isOpen_univ (Set.subset_univ _)
    contDiff_timeCoord.contDiffOn x₀⟩

/-- The hypotheses of `exists_klainermanSobolev_hyperboloid` with an open set `U` smaller than the
whole spacetime: `u = 1/t` is smooth on the half-space `U = {t > 0}`, which contains `H_s` for
every `s > 0`, and is singular at `t = 0`. -/
example : ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ x₀ : EuclideanSpace ℝ (Fin 3),
    ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |(√(s ^ 2 + ‖x₀‖ ^ 2))⁻¹|) ≤
      (C : ENNReal) *
        (eLpNorm (restrictHyperboloid s fun p ↦ (timeCoord p)⁻¹) 2 volume +
          ∑ a, eLpNorm (restrictHyperboloid s (boost a fun p ↦ (timeCoord p)⁻¹)) 2 volume +
          ∑ a, ∑ b, eLpNorm
            (restrictHyperboloid s (boost a (boost b fun p ↦ (timeCoord p)⁻¹))) 2 volume) := by
  obtain ⟨C, hC⟩ := exists_klainermanSobolev_hyperboloid
  refine ⟨C, fun s hs x₀ ↦ hC s hs (fun p ↦ (timeCoord p)⁻¹) {p | 0 < timeCoord p}
    (isOpen_lt continuous_const differentiable_timeCoord.continuous) (fun p hp ↦ ?_)
    (contDiff_timeCoord.contDiffOn.inv fun p hp ↦ hp.ne') x₀⟩
  have hp' : p.1 = √(s ^ 2 + ‖p.2‖ ^ 2) := hp
  change 0 < p.1
  rw [hp']
  positivity

/-- A case where the inequality of `exists_klainermanSobolev_hyperboloid` is not trivial: for a
smooth bump function `u` on spacetime, equal to `1` on the closed unit ball (for the max norm) and
with compact support, the left side at the point `(1, 0)` of `H_1` (`s = 1`, `x₀ = 0`) is `1`,
and the right side is finite, since the thirteen functions `(L^J u)|_{H_1}` are continuous with
compact support. -/
example : ∃ u : Spacetime → ℝ, ContDiff ℝ ∞ u ∧
    ENNReal.ofReal (√(1 ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2) ^ (3 / 2 : ℝ) *
      |u (√(1 ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2), 0)|) = 1 ∧
    eLpNorm (restrictHyperboloid 1 u) 2 volume +
        ∑ a, eLpNorm (restrictHyperboloid 1 (boost a u)) 2 volume +
        ∑ a, ∑ b, eLpNorm (restrictHyperboloid 1 (boost a (boost b u))) 2 volume < ⊤ := by
  let f : ContDiffBump (0 : Spacetime) := ⟨1, 2, one_pos, one_lt_two⟩
  have hf : ContDiff ℝ ∞ f := f.contDiff
  have hcs : HasCompactSupport f := f.hasCompactSupport
  have h1 : ∀ b, ContDiff ℝ ∞ (boost b f) := fun b ↦ contDiff_infty_boost b hf
  have h2 : ∀ a b, ContDiff ℝ ∞ (boost a (boost b f)) := fun a b ↦ contDiff_infty_boost a (h1 b)
  have hφ : √(1 ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2) = 1 := by simp
  refine ⟨f, hf, ?_, ?_⟩
  · have hmem : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) ∈ Metric.closedBall 0 f.rIn := by
      change dist _ _ ≤ 1
      simp [Prod.norm_def]
    rw [hφ, f.one_of_mem_closedBall hmem]
    simp
  · simp only [ENNReal.add_lt_top, ENNReal.sum_lt_top, Finset.mem_univ, forall_const]
    exact ⟨⟨eLpNorm_restrictHyperboloid_lt_top 1 hf.continuous hcs, fun a ↦
      eLpNorm_restrictHyperboloid_lt_top 1 (h1 a).continuous (hasCompactSupport_derivAlong _ hcs)⟩,
      fun a b ↦ eLpNorm_restrictHyperboloid_lt_top 1 (h2 a b).continuous
        (hasCompactSupport_derivAlong _ (hasCompactSupport_derivAlong _ hcs))⟩

/-- The two sides of the restriction formula for `v = t`, computed independently of it. Since
`t|_{H_s} = φ_s`, the left side is `Λ_a φ_s = φ_s ∂_a φ_s = x_a`; since `L_a t = x_a`, the right
side is `(L_a t)|_{H_s} = x_a`. -/
example {s : ℝ} (hs : s ≠ 0) (a : Fin 3) :
    hyperboloidalWeightedDeriv s a (fun x ↦ √(s ^ 2 + ‖x‖ ^ 2)) = (fun x ↦ x a) ∧
      restrictHyperboloid s (boost a timeCoord) = (fun x ↦ x a) := by
  refine ⟨funext fun x ↦ ?_, by rw [boost_timeCoord]; rfl⟩
  have hφ : √(s ^ 2 + ‖x‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [hyperboloidalWeightedDeriv, fderiv_sqrt_sq_add_norm_sq_apply hs,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, mul_div_cancel₀ _ hφ]

/-- The restriction formula applied to `v = t`, which is differentiable everywhere: since
`t|_{H_s} = φ_s` and `L_a t = x_a`, it gives `Λ_a φ_s = x_a` at every point. -/
example {s : ℝ} (hs : s ≠ 0) (a : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    hyperboloidalWeightedDeriv s a (fun y ↦ √(s ^ 2 + ‖y‖ ^ 2)) x = x a := by
  rw [show (fun y : EuclideanSpace ℝ (Fin 3) ↦ √(s ^ 2 + ‖y‖ ^ 2)) =
      restrictHyperboloid s timeCoord from rfl,
    hyperboloidalWeightedDeriv_restrictHyperboloid_apply hs a (differentiable_timeCoord _),
    boost_timeCoord]
  rfl

/-- The two sides of the second-order formula for `u = t`, computed independently of it:
`Λ_a Λ_b φ_s = Λ_a x_b = φ_s δ_ab`, and `L_a L_b t = L_a x_b = t δ_ab`, whose restriction to `H_s`
is `φ_s δ_ab`. -/
example {s : ℝ} (hs : s ≠ 0) (a b : Fin 3) :
    hyperboloidalWeightedDeriv s a
        (hyperboloidalWeightedDeriv s b fun x ↦ √(s ^ 2 + ‖x‖ ^ 2)) =
        (fun x ↦ √(s ^ 2 + ‖x‖ ^ 2) * if a = b then 1 else 0) ∧
      restrictHyperboloid s (boost a (boost b timeCoord)) =
        (fun x ↦ √(s ^ 2 + ‖x‖ ^ 2) * if a = b then 1 else 0) := by
  refine ⟨?_, by rw [boost_timeCoord, boost_spaceCoord]; rfl⟩
  have h1 : hyperboloidalWeightedDeriv s b (fun x ↦ √(s ^ 2 + ‖x‖ ^ 2)) = fun x ↦ x b := by
    funext x
    have hφ : √(s ^ 2 + ‖x‖ ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    rw [hyperboloidalWeightedDeriv, fderiv_sqrt_sq_add_norm_sq_apply hs,
      EuclideanSpace.inner_single_right, conj_trivial, one_mul, mul_div_cancel₀ _ hφ]
  funext x
  rw [h1, hyperboloidalWeightedDeriv, (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x b).fderiv,
    PiLp.proj_apply, PiLp.ofLp_single]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab, Ne.symm hab]

end VectorFieldMethod.Minkowski
