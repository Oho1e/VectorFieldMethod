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

For `s > 0` let `H_s = {(t, x) : t = √(s ^ 2 + ‖x‖ ^ 2)}` (`hyperboloid s`) be the upper sheet of
the hyperboloid `t ^ 2 - ‖x‖ ^ 2 = s ^ 2`. The restriction of a function `v` on spacetime to `H_s`
is the function `v|_{H_s} x = v (√(s ^ 2 + ‖x‖ ^ 2), x)` on `ℝ³` (`restrictHyperboloid s v`).

This file connects the weighted derivatives `Λ_a = φ_s ∂_a` on `ℝ³` of the analysis layer
(`EuclideanSobolev.hyperboloidalWeightedDeriv s a`, with `φ_s x = √(s ^ 2 + ‖x‖ ^ 2)`) with the
Lorentz boosts `L_a = t ∂_a + x_a ∂_t` (`boost a`), and deduces from the weighted inequality on
`ℝ³` (`EuclideanSobolev.exists_hyperboloidalSobolev`) the Klainerman–Sobolev inequality on
hyperboloids
`sup_{H_s} t ^ (3/2) |u| ≤ C ∑_{|J| ≤ 2} ‖L^J u‖_{L²_f(H_s)}`,
where `‖v‖_{L²_f(H_s)} = ‖v|_{H_s}‖_{L²(ℝ³)}` is the `L²` norm on `H_s` for the flat measure `dx`
and `C` is an absolute constant. See `docs/hyperboloidal-sobolev.md`.

## Main definitions

* `hyperboloid s`: the hyperboloid `H_s = {p | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)}`.
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
* `continuous_restrictHyperboloid_boosts`: under the hypotheses of the inequality, the thirteen
  functions `(L^J u)|_{H_s}` on its right-hand side are continuous, hence measurable.
* `eLpNorm_restrictHyperboloid_boosts_lt_top`: for `u` of class `C²` with compact support, the
  right-hand side of the inequality is finite.

## Implementation notes

The restriction and the statements about its regularity, continuity, compact support and square
integrability are for functions with values in a real normed space `F`. The restriction formulas
and the inequality are for real-valued functions, since the weighted derivatives
`hyperboloidalWeightedDeriv` of the analysis layer are defined for real-valued functions.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace VectorFieldMethod.Minkowski

open VectorFieldMethod.EuclideanSobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### The hyperboloid and the restriction to it -/

/-- The hyperboloid `H_s = {(t, x) : t = √(s ^ 2 + ‖x‖ ^ 2)}`. For `s ≠ 0` it is the upper sheet
of `t ^ 2 - ‖x‖ ^ 2 = s ^ 2`. -/
def hyperboloid (s : ℝ) : Set Spacetime :=
  {p | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)}

theorem mem_hyperboloid {s : ℝ} {p : Spacetime} :
    p ∈ hyperboloid s ↔ p.1 = √(s ^ 2 + ‖p.2‖ ^ 2) :=
  Iff.rfl

/-- The point `(√(s ^ 2 + ‖x‖ ^ 2), x)` of the hyperboloid `H_s` above `x ∈ ℝ³`. -/
def hyperboloidPoint (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : Spacetime :=
  (√(s ^ 2 + ‖x‖ ^ 2), x)

/-- `hyperboloidPoint s x` lies on the hyperboloid `H_s`. -/
theorem hyperboloidPoint_mem_hyperboloid (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    hyperboloidPoint s x ∈ hyperboloid s :=
  rfl

/-- The restriction `v|_{H_s}` of `v : Spacetime → F` to the hyperboloid `H_s`, as a function on
`ℝ³`: `v|_{H_s} x = v (√(s ^ 2 + ‖x‖ ^ 2), x)`. -/
def restrictHyperboloid (s : ℝ) (v : Spacetime → F) : EuclideanSpace ℝ (Fin 3) → F :=
  fun x ↦ v (√(s ^ 2 + ‖x‖ ^ 2), x)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem restrictHyperboloid_apply (s : ℝ) (v : Spacetime → F) (x : EuclideanSpace ℝ (Fin 3)) :
    restrictHyperboloid s v x = v (√(s ^ 2 + ‖x‖ ^ 2), x) :=
  rfl

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem restrictHyperboloid_eq_comp (s : ℝ) (v : Spacetime → F) :
    restrictHyperboloid s v = v ∘ hyperboloidPoint s :=
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
theorem contDiffAt_of_contDiffOn_of_hyperboloid_subset {s : ℝ} {n : ℕ∞ω} {u : Spacetime → F}
    {U : Set Spacetime} (hU : IsOpen U) (hHU : hyperboloid s ⊆ U) (hu : ContDiffOn ℝ n u U)
    (x : EuclideanSpace ℝ (Fin 3)) : ContDiffAt ℝ n u (√(s ^ 2 + ‖x‖ ^ 2), x) :=
  hu.contDiffAt (hU.mem_nhds (hHU (hyperboloidPoint_mem_hyperboloid s x)))

/-- **Restriction formula on `H_s`.** For `s ≠ 0` and `u` differentiable on an open set `U`
containing `H_s`, `Λ_a (u|_{H_s}) = (L_a u)|_{H_s}` as functions on `ℝ³`. -/
theorem hyperboloidalWeightedDeriv_restrictHyperboloid_of_differentiableOn {s : ℝ}
    (hs : s ≠ 0) {u : Spacetime → ℝ} {U : Set Spacetime} (hU : IsOpen U)
    (hHU : hyperboloid s ⊆ U) (hu : DifferentiableOn ℝ u U) (a : Fin 3) :
    hyperboloidalWeightedDeriv s a (restrictHyperboloid s u) =
      restrictHyperboloid s (boost a u) :=
  hyperboloidalWeightedDeriv_restrictHyperboloid hs a fun x ↦
    hu.differentiableAt (hU.mem_nhds (hHU (hyperboloidPoint_mem_hyperboloid s x)))

/-- **Second-order restriction formula.** For `s ≠ 0` and `u` of class `C²` on an open set `U`
containing `H_s`, `Λ_a Λ_b (u|_{H_s}) = (L_a L_b u)|_{H_s}` as functions on `ℝ³`, with the indices
in the same order. -/
theorem hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid {s : ℝ}
    (hs : s ≠ 0) {u : Spacetime → ℝ} {U : Set Spacetime} (hU : IsOpen U)
    (hHU : hyperboloid s ⊆ U) (hu : ContDiffOn ℝ 2 u U) (a b : Fin 3) :
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
theorem contDiff_restrictHyperboloid {s : ℝ} (hs : s ≠ 0) {n : ℕ∞ω} {u : Spacetime → F}
    {U : Set Spacetime} (hU : IsOpen U) (hHU : hyperboloid s ⊆ U) (hu : ContDiffOn ℝ n u U) :
    ContDiff ℝ n (restrictHyperboloid s u) :=
  contDiff_iff_contDiffAt.mpr fun x ↦
    ContDiffAt.comp (f := hyperboloidPoint s) x
      (contDiffAt_of_contDiffOn_of_hyperboloid_subset hU hHU hu x)
      (contDiff_hyperboloidPoint hs).contDiffAt

/-! ### The Klainerman–Sobolev inequality on hyperboloids -/

/-- **Klainerman–Sobolev inequality on hyperboloids.** There is an absolute constant `C` such that
for all `s > 0`, every `u` of class `C²` on an open set `U` containing the hyperboloid
`H_s = hyperboloid s` and every point `(t₀, x₀) = (√(s ^ 2 + ‖x₀‖ ^ 2), x₀)` of `H_s`,
`t₀ ^ (3/2) |u (t₀, x₀)| ≤ C ∑_{|J| ≤ 2} ‖L^J u‖_{L²_f(H_s)}`, where
`‖v‖_{L²_f(H_s)} = ‖v|_{H_s}‖_{L²(ℝ³)}` is the `L²` norm on `H_s` for the flat measure `dx`, and
`L^J` runs over `1`, the three boosts `L_a` and the nine products `L_a L_b`. -/
theorem exists_klainermanSobolev_hyperboloid :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ (u : Spacetime → ℝ) (U : Set Spacetime), IsOpen U →
      hyperboloid s ⊆ U → ContDiffOn ℝ 2 u U →
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

/-! ### Continuity and square integrability of restrictions -/

/-- The map `x ↦ (√(s ^ 2 + ‖x‖ ^ 2), x)` is continuous, for every `s`. -/
theorem continuous_hyperboloidPoint (s : ℝ) : Continuous (hyperboloidPoint s) :=
  (continuous_const.add (continuous_norm.pow 2)).sqrt.prodMk continuous_id

omit [NormedSpace ℝ F] in
/-- The restriction of a continuous function to `H_s` is continuous. -/
theorem continuous_restrictHyperboloid (s : ℝ) {v : Spacetime → F} (hv : Continuous v) :
    Continuous (restrictHyperboloid s v) :=
  hv.comp (continuous_hyperboloidPoint s)

omit [NormedSpace ℝ F] in
/-- The restriction to `H_s` of a function that is continuous on a set containing `H_s` is
continuous. -/
theorem continuous_restrictHyperboloid_of_continuousOn (s : ℝ) {v : Spacetime → F}
    {U : Set Spacetime} (hHU : hyperboloid s ⊆ U) (hv : ContinuousOn v U) :
    Continuous (restrictHyperboloid s v) :=
  hv.comp_continuous (continuous_hyperboloidPoint s) fun x ↦
    hHU (hyperboloidPoint_mem_hyperboloid s x)

/-- If `u` is `C^{n+1}` on an open set `U`, then `L_a u` is `C^n` on `U`. -/
theorem contDiffOn_boost {n : ℕ∞ω} {u : Spacetime → F} {U : Set Spacetime} (hU : IsOpen U)
    (hu : ContDiffOn ℝ (n + 1) u U) (a : Fin 3) : ContDiffOn ℝ n (boost a u) U :=
  (hu.fderiv_of_isOpen hU le_rfl).clm_apply (contDiff_boostField a).contDiffOn

/-- Under the hypotheses of `exists_klainermanSobolev_hyperboloid`, the thirteen functions
`(L^J u)|_{H_s}` (`|J| ≤ 2`) of its right-hand side are continuous on `ℝ³`. In particular they
are measurable, so an `L²` norm equal to `∞` on that side means that the function is not square
integrable. -/
theorem continuous_restrictHyperboloid_boosts {s : ℝ} {u : Spacetime → F} {U : Set Spacetime}
    (hU : IsOpen U) (hHU : hyperboloid s ⊆ U) (hu : ContDiffOn ℝ 2 u U) :
    Continuous (restrictHyperboloid s u) ∧
      (∀ a, Continuous (restrictHyperboloid s (boost a u))) ∧
      ∀ a b, Continuous (restrictHyperboloid s (boost a (boost b u))) := by
  have h1 (b : Fin 3) : ContDiffOn ℝ 1 (boost b u) U := contDiffOn_boost (n := 1) hU hu b
  refine ⟨continuous_restrictHyperboloid_of_continuousOn s hHU hu.continuousOn,
    fun a ↦ continuous_restrictHyperboloid_of_continuousOn s hHU (h1 a).continuousOn,
    fun a b ↦ continuous_restrictHyperboloid_of_continuousOn s hHU ?_⟩
  exact (contDiffOn_boost (n := 0) hU (h1 b) a).continuousOn

/-! ### Restrictions of compactly supported functions -/

omit [NormedSpace ℝ F] in
/-- The restriction to `H_s` of a function with compact support has compact support. -/
theorem hasCompactSupport_restrictHyperboloid (s : ℝ) {v : Spacetime → F}
    (hv : HasCompactSupport v) : HasCompactSupport (restrictHyperboloid s v) :=
  HasCompactSupport.intro (hv.isCompact.image continuous_snd) fun x hx ↦
    image_eq_zero_of_notMem_tsupport (f := v) (x := (√(s ^ 2 + ‖x‖ ^ 2), x)) fun h ↦
      hx ⟨_, h, rfl⟩

omit [NormedSpace ℝ F] in
/-- The restriction to `H_s` of a continuous function with compact support is square
integrable on `ℝ³`. -/
theorem eLpNorm_restrictHyperboloid_lt_top (s : ℝ) {v : Spacetime → F} (hv : Continuous v)
    (hvs : HasCompactSupport v) : eLpNorm (restrictHyperboloid s v) 2 volume < ⊤ :=
  ((continuous_restrictHyperboloid s hv).memLp_of_hasCompactSupport
    (hasCompactSupport_restrictHyperboloid s hvs)).eLpNorm_lt_top

/-- The derivative along a vector field of a function with compact support has compact
support. -/
theorem hasCompactSupport_derivAlong (V : Spacetime → Spacetime) {u : Spacetime → F}
    (hu : HasCompactSupport u) : HasCompactSupport (derivAlong V u) :=
  (hu.fderiv (𝕜 := ℝ)).mono fun p hp h ↦ hp (by rw [derivAlong_apply, h]; rfl)

/-- For `u` of class `C²` with compact support, the right-hand side of the Klainerman–Sobolev
inequality is finite: the thirteen functions `(L^J u)|_{H_s}` (`|J| ≤ 2`) are continuous with
compact support, hence square integrable. -/
theorem eLpNorm_restrictHyperboloid_boosts_lt_top (s : ℝ) {u : Spacetime → F}
    (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) :
    eLpNorm (restrictHyperboloid s u) 2 volume +
        ∑ a, eLpNorm (restrictHyperboloid s (boost a u)) 2 volume +
        ∑ a, ∑ b, eLpNorm (restrictHyperboloid s (boost a (boost b u))) 2 volume < ⊤ := by
  have h1 (b : Fin 3) : ContDiff ℝ 1 (boost b u) := contDiff_boost (n := 1) b hu
  simp only [ENNReal.add_lt_top, ENNReal.sum_lt_top, Finset.mem_univ, forall_const]
  exact ⟨⟨eLpNorm_restrictHyperboloid_lt_top s hu.continuous hcs, fun a ↦
    eLpNorm_restrictHyperboloid_lt_top s (h1 a).continuous (hasCompactSupport_derivAlong _ hcs)⟩,
    fun a b ↦ eLpNorm_restrictHyperboloid_lt_top s (contDiff_boost (n := 0) a (h1 b)).continuous
      (hasCompactSupport_derivAlong _ (hasCompactSupport_derivAlong _ hcs))⟩

/-! ### Sanity checks -/

/-- The hypotheses of `exists_klainermanSobolev_hyperboloid` hold for `u = t`, which is smooth on
the whole spacetime `U = Set.univ`. The right-hand side is `∞` here: `t|_{H_s} = φ_s` is not
square integrable on `ℝ³`. -/
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
every `s > 0`, and is singular at `t = 0`. The right-hand side is `∞` here as well:
`(1/t)|_{H_s} = 1/φ_s` and `∫ φ_s⁻² dx = 4π ∫₀^∞ r² / (s² + r²) dr = ∞`. -/
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
  change 0 < p.1
  rw [mem_hyperboloid.mp hp]
  positivity

/-- A function with a nonzero left side and a finite right side: there is a function `u` of
class `C^∞` on spacetime such that, at the point `(1, 0)` of `H_1` (`s = 1`, `x₀ = 0`), the left
side of the inequality of `exists_klainermanSobolev_hyperboloid` is `1` and its right side (the
sum of the thirteen `L²` norms) is finite. The proof takes a smooth bump function, equal to `1`
on the closed unit ball (for the max norm) and with compact support. This example does not apply
the theorem; the next one does. -/
example : ∃ u : Spacetime → ℝ, ContDiff ℝ ∞ u ∧
    ENNReal.ofReal (√(1 ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2) ^ (3 / 2 : ℝ) *
      |u (√(1 ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2), 0)|) = 1 ∧
    eLpNorm (restrictHyperboloid 1 u) 2 volume +
        ∑ a, eLpNorm (restrictHyperboloid 1 (boost a u)) 2 volume +
        ∑ a, ∑ b, eLpNorm (restrictHyperboloid 1 (boost a (boost b u))) 2 volume < ⊤ := by
  let f : ContDiffBump (0 : Spacetime) := ⟨1, 2, one_pos, one_lt_two⟩
  have hmem : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) ∈ Metric.closedBall 0 f.rIn := by
    change dist _ _ ≤ 1
    simp [Prod.norm_def]
  have hφ : √(1 ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2) = 1 := by simp
  refine ⟨f, f.contDiff, ?_,
    eLpNorm_restrictHyperboloid_boosts_lt_top 1 f.contDiff f.hasCompactSupport⟩
  rw [hφ, f.one_of_mem_closedBall hmem]
  simp

/-- **The inequality with a finite right-hand side.** `exists_klainermanSobolev_hyperboloid`
gives a constant `C`. Applied with `U = Set.univ` to the bump function `u` of the previous example
at the point `(1, 0)` of `H_1`, where the left side is `1`, it gives `1 ≤ C * R`, where `R` is
the right-hand side for `u`, and `R` is finite. So for this `u` the theorem is a genuine
inequality, and the constant `C` is positive. -/
example : ∃ C : NNReal,
    (∀ s : ℝ, 0 < s → ∀ (u : Spacetime → ℝ) (U : Set Spacetime), IsOpen U →
      hyperboloid s ⊆ U → ContDiffOn ℝ 2 u U → ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |u (√(s ^ 2 + ‖x₀‖ ^ 2), x₀)|) ≤
        (C : ENNReal) *
          (eLpNorm (restrictHyperboloid s u) 2 volume +
            ∑ a, eLpNorm (restrictHyperboloid s (boost a u)) 2 volume +
            ∑ a, ∑ b, eLpNorm (restrictHyperboloid s (boost a (boost b u))) 2 volume)) ∧
    ∃ u : Spacetime → ℝ, ContDiff ℝ ∞ u ∧ ∃ R : ENNReal,
      R = eLpNorm (restrictHyperboloid 1 u) 2 volume +
          ∑ a, eLpNorm (restrictHyperboloid 1 (boost a u)) 2 volume +
          ∑ a, ∑ b, eLpNorm (restrictHyperboloid 1 (boost a (boost b u))) 2 volume ∧
      R < ⊤ ∧ 1 ≤ (C : ENNReal) * R ∧ 0 < C := by
  obtain ⟨C, hC⟩ := exists_klainermanSobolev_hyperboloid
  let f : ContDiffBump (0 : Spacetime) := ⟨1, 2, one_pos, one_lt_two⟩
  have hmem : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) ∈ Metric.closedBall 0 f.rIn := by
    change dist _ _ ≤ 1
    simp [Prod.norm_def]
  have hφ : √(1 ^ 2 + ‖(0 : EuclideanSpace ℝ (Fin 3))‖ ^ 2) = 1 := by simp
  have h1 := hC 1 one_pos f Set.univ isOpen_univ (Set.subset_univ _) f.contDiff.contDiffOn 0
  rw [hφ, f.one_of_mem_closedBall hmem] at h1
  simp only [Real.one_rpow, abs_one, mul_one, ENNReal.ofReal_one] at h1
  refine ⟨C, hC, f, f.contDiff, _, rfl,
    eLpNorm_restrictHyperboloid_boosts_lt_top 1 f.contDiff f.hasCompactSupport, h1,
    pos_iff_ne_zero.mpr fun hC0 ↦ ?_⟩
  simp [hC0] at h1

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

/-- The restriction formula for `v = x_b`, which tests the term `t ∂_a v` of `L_a v` (for `v = t`
only the term `x_a ∂_t v` contributes). Computed independently, the left side is
`Λ_a (x_b|_{H_s}) = Λ_a x_b = φ_s δ_ab` and the right side is
`(L_a x_b)|_{H_s} = (t δ_ab)|_{H_s} = φ_s δ_ab`; the formula applies, as `x_b` is differentiable,
and states that the two sides are equal. -/
example {s : ℝ} (hs : s ≠ 0) (a b : Fin 3) :
    hyperboloidalWeightedDeriv s a (fun x ↦ x b) =
        (fun x ↦ √(s ^ 2 + ‖x‖ ^ 2) * if a = b then 1 else 0) ∧
      restrictHyperboloid s (boost a (spaceCoord b)) =
        (fun x ↦ √(s ^ 2 + ‖x‖ ^ 2) * if a = b then 1 else 0) ∧
      hyperboloidalWeightedDeriv s a (restrictHyperboloid s (spaceCoord b)) =
        restrictHyperboloid s (boost a (spaceCoord b)) := by
  refine ⟨funext fun x ↦ ?_, by rw [boost_spaceCoord]; rfl,
    hyperboloidalWeightedDeriv_restrictHyperboloid hs a fun x ↦ differentiable_spaceCoord b _⟩
  rw [hyperboloidalWeightedDeriv, (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x b).fderiv,
    PiLp.proj_apply, PiLp.ofLp_single]
  by_cases hab : a = b
  · subst hab
    simp
  · simp [hab, Ne.symm hab]

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

/-- The second-order restriction formula
(`hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid`) applied to `u = x_c`
with `U = Set.univ`. Since `L_b x_c = t δ_bc` and `L_a t = x_a`, it gives
`Λ_a Λ_b x_c = (L_a L_b x_c)|_{H_s} = δ_bc x_a`. The result is not symmetric in `a` and `b`, so
this also checks the order of the indices. -/
example {s : ℝ} (hs : s ≠ 0) (a b c : Fin 3) :
    hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b fun x ↦ x c) =
      fun x ↦ (if b = c then 1 else 0) * x a := by
  rw [show (fun x : EuclideanSpace ℝ (Fin 3) ↦ x c) = restrictHyperboloid s (spaceCoord c) from
      rfl, hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid hs isOpen_univ
      (Set.subset_univ _) (contDiff_spaceCoord c).contDiffOn a b, boost_spaceCoord]
  funext x
  by_cases hbc : b = c
  · simp [hbc, restrictHyperboloid, spaceCoord]
  · simp [hbc, restrictHyperboloid]

end VectorFieldMethod.Minkowski
