/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.HyperboloidalEnergy
public import VectorFieldMethod.ForMathlib.MeasureTheory.Integral.DivergenceTheoremHyperboloid

/-!
# The hyperboloidal energy identity for the Klein–Gordon field

Let `0 < s₁ < s₂`, let `D = {(t, x) | √(s₁ ^ 2 + ‖x‖ ^ 2) ≤ t ≤ √(s₂ ^ 2 + ‖x‖ ^ 2)}` be the
closed region of `Spacetime` between the hyperboloids `H_{s₁}` and `H_{s₂}`, and
`K = {(t, x) | ‖x‖ ≤ t - 1}` the closed solid cone. For a field `u` which is `C²` on an open set
`U ⊇ D ∩ K` and whose closed support meets `D` only inside `K`, we prove the energy identity of
LeFloch–Ma's hyperboloidal foliation method,
`E_m(s₂, u) - E_m(s₁, u) = -2 ∫_D ⟪□u - m² u, ∂_t u⟫`,
for the hyperboloidal energy `E_m` of `HyperboloidalEnergy.lean`. The proof applies the localized
divergence theorem between two hyperboloids,
`MeasureTheory.integral_divergence_between_hyperboloids_of_contDiffOn`, to the energy current `P`
of `EnergyMomentum.lean`: its divergence is `-⟪□u - m² u, ∂_t u⟫` (`spacetimeDiv_energyCurrent`),
and its flux density through `H_s` is `e_m[u] / 2` (`hyperboloidalEnergyDensity_eq_energyCurrent`).

The divergence theorems use the coordinates `(x, t)` of `E × ℝ` (time second), while
`Spacetime = ℝ × ℝ³` has time first; the first section of this file translates between the two.

## Main statements

* `deriv_add_spatialDivergence_eq_spacetimeDiv`: the divergence of a vector field `J` on
  `Spacetime` (time first) agrees with the divergence `∂_t X₀ + div_x X` of the same field written
  in the coordinates `(x, t)` of the divergence theorems (time second).
* `measurePreserving_swap_spacetime`, `setIntegral_spacetime_eq_setIntegral_swap`: the coordinate
  swap `(x, t) ↦ (t, x)` is measure preserving, and the corresponding change of variables.
* `hyperboloidalEnergy_sub_hyperboloidalEnergy`: the energy identity above.
* `integrable_hyperboloidalEnergyDensity`, `integrableOn_inner_kleinGordon_timeDeriv`: under the
  same hypotheses, the integrands of both sides are integrable, so that the identity is not an
  identity between junk values `0` of integrals of non-integrable functions.
* `hyperboloidalEnergy_eq_of_kleinGordon_eq_zero`: conservation of the energy,
  `E_m(s₁, u) = E_m(s₂, u)`, if moreover `□u - m² u = 0` on `D ∩ K`.

## Sign conventions

`kleinGordon m u = □u - m² u` with `□ = -∂_t² + Δ`. LeFloch–Ma's Klein–Gordon operator is
`-(□u - m² u)`, so in their notation the identity reads
`E_m(s₂, u) - E_m(s₁, u) = 2 ∫_D ⟪□u + m² u, ∂_t u⟫`.
-/

@[expose] public noncomputable section

open Set Filter Function Topology MeasureTheory
open scoped RealInnerProductSpace

namespace VectorFieldMethod.Minkowski

/-! ### From `Spacetime` to the coordinates `(x, t)` of the divergence theorems -/

/-- The divergence of a vector field `J` with real components `J α` on `Spacetime`, written in the
coordinates `(x, t)` (time second) of the divergence theorems. Let `X₀ (x, t) = J 0 (t, x)` and
`X (x, t) = ∑ a, J (a + 1) (t, x) e_a`. If the components of `J` are differentiable at `(t, x)`,
then `∂_t X₀ + div_x X = ∂_α J^α` at `(x, t)`. -/
theorem deriv_add_spatialDivergence_eq_spacetimeDiv (J : Fin 4 → Spacetime → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} {t : ℝ} (hJ : ∀ α, DifferentiableAt ℝ (J α) (t, x)) :
    deriv (fun s ↦ J 0 (s, x)) t +
        spatialDivergence (fun q ↦ ∑ a, J a.succ (q.2, q.1) • EuclideanSpace.single a 1) (x, t) =
      spacetimeDiv J (t, x) := by
  -- the time derivative
  have h₀ : deriv (fun s ↦ J 0 (s, x)) t = ∂[0] (J 0) (t, x) := by
    have h : HasDerivAt (fun s : ℝ ↦ (s, x)) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact ((hJ 0).hasFDerivAt.comp_hasDerivAt t h).deriv
  -- the spatial divergence
  have hcomp (a : Fin 3) : (fun y : EuclideanSpace ℝ (Fin 3) ↦
      (∑ b : Fin 3, J b.succ (t, y) • EuclideanSpace.single b (1 : ℝ) :
        EuclideanSpace ℝ (Fin 3)) a) = fun y ↦ J a.succ (t, y) := by
    funext y
    simp [Pi.single_apply]
  have hdiff : DifferentiableAt ℝ
      (fun y : EuclideanSpace ℝ (Fin 3) ↦
        ∑ b : Fin 3, J b.succ (t, y) • EuclideanSpace.single b (1 : ℝ)) x := by
    refine DifferentiableAt.fun_sum fun (b : Fin 3) _ ↦ ?_
    have hb : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 3) ↦ J b.succ (t, y)) x :=
      (hJ b.succ).comp x (hasFDerivAt_prodMk_right t x).differentiableAt
    exact hb.smul_const _
  have h₁ : spatialDivergence
      (fun q : EuclideanSpace ℝ (Fin 3) × ℝ ↦
        ∑ a : Fin 3, J a.succ (q.2, q.1) • EuclideanSpace.single a (1 : ℝ)) (x, t) =
      ∑ a : Fin 3, ∂[a.succ] (J a.succ) (t, x) := by
    rw [spatialDivergence_euclideanSpace (p := (x, t)) hdiff]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    simp only [hcomp]
    have h : HasFDerivAt (fun y ↦ J a.succ (t, y))
        ((fderiv ℝ (J a.succ) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ _)) x :=
      (hJ a.succ).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    rw [h.fderiv]
    rfl
  rw [h₀, h₁, spacetimeDiv_apply, Fin.sum_univ_succ (n := 3)]

/-- The coordinate swap `(x, t) ↦ (t, x)` from `ℝ³ × ℝ`, the spacetime of the divergence theorems
(time second), to `Spacetime` (time first) is measure preserving for the Lebesgue measures. -/
theorem measurePreserving_swap_spacetime :
    MeasurePreserving (Prod.swap : EuclideanSpace ℝ (Fin 3) × ℝ → Spacetime)
      (volume.prod volume) volume :=
  Measure.measurePreserving_swap

/-- Change of variables `p = (x, t) ↦ (t, x)` between a set integral on `Spacetime` and the
corresponding set integral on `ℝ³ × ℝ`. -/
theorem setIntegral_spacetime_eq_setIntegral_swap {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (f : Spacetime → G) (s : Set Spacetime) :
    ∫ p in s, f p = ∫ q in Prod.swap ⁻¹' s, f q.swap ∂(volume.prod volume) :=
  (measurePreserving_swap_spacetime.setIntegral_preimage_emb
    MeasurableEquiv.prodComm.measurableEmbedding f s).symm

/-! ### Localization near the cone -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {u : Spacetime → F}

/-- If `u` is `C²` on an open set `U` containing `A ∩ K`, and the points of `A` in the closed
support of `u` lie in `K`, then `u` is `C²` at every point of `A`: at the points of `A ∩ K` by
the first assumption, at the other points because `u` vanishes near them. -/
theorem contDiffAt_of_inter_tsupport_subset {A K U : Set Spacetime} (hU : IsOpen U)
    (hAU : A ∩ K ⊆ U) (hu : ContDiffOn ℝ 2 u U) (hsupp : A ∩ tsupport u ⊆ K) {p : Spacetime}
    (hp : p ∈ A) : ContDiffAt ℝ 2 u p := by
  by_cases h : p ∈ tsupport u
  · exact hu.contDiffAt (hU.mem_nhds (hAU ⟨hp, hsupp ⟨hp, h⟩⟩))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 h)

/-- The Klein–Gordon operator of `u` is continuous at a point where `u` is `C²`. -/
theorem continuousAt_kleinGordon (m : ℝ) {p : Spacetime} (hu : ContDiffAt ℝ 2 u p) :
    ContinuousAt (kleinGordon m u) p := by
  have hu' : ContDiffAt ℝ (0 + 1 + 1) u p := by rwa [zero_add, one_add_one_eq_two]
  have h2 (α β : Fin 4) : ContinuousAt (∂[α] (∂[β] u)) p :=
    (contDiffAt_partialDeriv α (contDiffAt_partialDeriv β hu')).continuousAt
  change ContinuousAt (fun q ↦ ∑ α, ∑ β, η α β • ∂[α] (∂[β] u) q - m ^ 2 • u q) p
  exact (tendsto_finsetSum _ fun α _ ↦ tendsto_finsetSum _ fun β _ ↦ (h2 α β).const_smul _).sub
    (hu.continuousAt.const_smul _)

/-- The Klein–Gordon operator of `u` vanishes outside the closed support of `u`. -/
theorem kleinGordon_of_notMem_tsupport (m : ℝ) {p : Spacetime} (hp : p ∉ tsupport u) :
    kleinGordon m u p = 0 := by
  have hD (β : Fin 4) : tsupport (∂[β] u) ⊆ tsupport u :=
    closure_minimal (fun q hq ↦ by_contra fun h ↦ hq (derivAlong_of_notMem_tsupport _ h))
      (isClosed_tsupport u)
  have h2 (α β : Fin 4) : ∂[α] (∂[β] u) p = 0 :=
    derivAlong_of_notMem_tsupport _ fun h ↦ hp (hD β h)
  simp [kleinGordon_apply, dAlembertian_apply, h2, image_eq_zero_of_notMem_tsupport hp]

/-- The part of the closed region between the hyperboloids `t = √(s₁ ^ 2 + ‖x‖ ^ 2)` and
`t = √(s₂ ^ 2 + ‖x‖ ^ 2)` of `Spacetime` which lies in the cone `‖x‖ ≤ t - 1` is compact. -/
theorem isCompact_region_between_hyperboloids_inter_cone_spacetime (s₁ s₂ : ℝ) :
    IsCompact ({p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
      {p | ‖p.2‖ ≤ p.1 - 1}) := by
  have h := (isCompact_region_between_hyperboloids_inter_cone (E := EuclideanSpace ℝ (Fin 3))
    s₁ s₂).image continuous_swap
  rwa [image_swap_eq_preimage_swap] at h

/-- The flux density through a hyperboloid of the energy current written in the coordinates
`(x, t)`: `P⁰ - ⟪x, ∑ a, P^a e_a⟫ / t = e_m[u] / 2` at `(t, x)`. -/
theorem energyCurrent_sub_inner_div_eq (m : ℝ) (u : Spacetime → F)
    (x : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    energyCurrent m u 0 (t, x) - ⟪x, ∑ a : Fin 3,
        energyCurrent m u a.succ (t, x) • EuclideanSpace.single a (1 : ℝ)⟫ / t =
      hyperboloidalEnergyDensity m u (t, x) / 2 := by
  have hinner : ⟪x, ∑ a : Fin 3,
      energyCurrent m u a.succ (t, x) • EuclideanSpace.single a (1 : ℝ)⟫ =
      ∑ a : Fin 3, energyCurrent m u a.succ (t, x) * x a := by
    simp [inner_sum, real_inner_smul_right, EuclideanSpace.inner_single_right]
  have hsum : (∑ a : Fin 3, energyCurrent m u a.succ (t, x) * x a) / t =
      ∑ a : Fin 3, spaceCoord a (t, x) / timeCoord (t, x) * energyCurrent m u a.succ (t, x) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [spaceCoord_apply, timeCoord_apply]; ring
  rw [hinner, hsum, hyperboloidalEnergyDensity_eq_energyCurrent]
  ring

/-! ### Integrability -/

/-- Under the hypotheses of the energy identity `hyperboloidalEnergy_sub_hyperboloidalEnergy`,
`⟪KG_m u, ∂_t u⟫` is integrable on the region `D` between the hyperboloids: it is continuous on
`D` and vanishes on `D` outside the compact set `D ∩ K`. -/
theorem integrableOn_inner_kleinGordon_timeDeriv {m s₁ s₂ : ℝ} {U : Set Spacetime}
    (hU : IsOpen U)
    (hDU : {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
      {p | ‖p.2‖ ≤ p.1 - 1} ⊆ U)
    (hu : ContDiffOn ℝ 2 u U)
    (hsupp : {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
      tsupport u ⊆ {p | ‖p.2‖ ≤ p.1 - 1}) :
    IntegrableOn (fun p ↦ ⟪kleinGordon m u p, ∂ₜ u p⟫)
      {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} := by
  have hcont (p : Spacetime)
      (hp : p ∈ {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)}) :
      ContinuousAt (fun p ↦ ⟪kleinGordon m u p, ∂ₜ u p⟫) p := by
    have hp' := contDiffAt_of_inter_tsupport_subset hU hDU hu hsupp hp
    have hu' : ContDiffAt ℝ (0 + 1) u p := by rw [zero_add]; exact hp'.of_le one_le_two
    exact (continuousAt_kleinGordon m hp').inner (contDiffAt_partialDeriv 0 hu').continuousAt
  have hDm : MeasurableSet
      {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} :=
    ((isClosed_le (by fun_prop) (by fun_prop)).inter
      (isClosed_le (by fun_prop) (by fun_prop))).measurableSet
  have hKm : MeasurableSet {p : Spacetime | ‖p.2‖ ≤ p.1 - 1} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have h₁ : IntegrableOn (fun p ↦ ⟪kleinGordon m u p, ∂ₜ u p⟫)
      ({p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
        {p | ‖p.2‖ ≤ p.1 - 1}) :=
    ContinuousOn.integrableOn_compact (isCompact_region_between_hyperboloids_inter_cone_spacetime
      s₁ s₂) fun p hp ↦ (hcont p hp.1).continuousWithinAt
  have h₂ : IntegrableOn (fun p ↦ ⟪kleinGordon m u p, ∂ₜ u p⟫)
      ({p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} \
        {p | ‖p.2‖ ≤ p.1 - 1}) := by
    refine integrableOn_zero.congr_fun (fun p hp ↦ ?_) (hDm.diff hKm)
    have h : p ∉ tsupport u := fun h ↦ hp.2 (hsupp ⟨hp.1, h⟩)
    have ht : ∂ₜ u p = 0 := derivAlong_of_notMem_tsupport _ h
    change (0 : ℝ) = ⟪kleinGordon m u p, ∂ₜ u p⟫
    rw [ht, inner_zero_right]
  have h := h₁.union h₂
  rwa [inter_union_sdiff] at h

/-- Under the hypotheses of the energy identity `hyperboloidalEnergy_sub_hyperboloidalEnergy`,
the energy density on the hyperboloid `H_s` is integrable for every `s ∈ [s₁, s₂]`, in
particular for `s = s₁` and `s = s₂`: it is continuous and vanishes for `‖x‖ > s ^ 2`. -/
theorem integrable_hyperboloidalEnergyDensity {m s₁ s₂ s : ℝ} (hs₁ : 0 < s₁) (hs : s ∈ Icc s₁ s₂)
    {U : Set Spacetime} (hU : IsOpen U)
    (hDU : {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
      {p | ‖p.2‖ ≤ p.1 - 1} ⊆ U)
    (hu : ContDiffOn ℝ 2 u U)
    (hsupp : {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
      tsupport u ⊆ {p | ‖p.2‖ ≤ p.1 - 1}) :
    Integrable fun x : EuclideanSpace ℝ (Fin 3) ↦
      hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x) := by
  have hs0 : 0 < s := hs₁.trans_le hs.1
  have hmem (x : EuclideanSpace ℝ (Fin 3)) : ((√(s ^ 2 + ‖x‖ ^ 2), x) : Spacetime) ∈
      {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} :=
    ⟨Real.sqrt_le_sqrt (by nlinarith [hs.1]), Real.sqrt_le_sqrt (by nlinarith [hs.2])⟩
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 3) ↦
      hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x) := by
    refine continuous_iff_continuousAt.2 fun x ↦ ?_
    have hx := contDiffAt_of_inter_tsupport_subset hU hDU hu hsupp (hmem x)
    have hf : Continuous fun x : EuclideanSpace ℝ (Fin 3) ↦ ((√(s ^ 2 + ‖x‖ ^ 2), x) : Spacetime) :=
      by fun_prop
    exact ContinuousAt.comp (g := hyperboloidalEnergyDensity m u)
      (f := fun y : EuclideanSpace ℝ (Fin 3) ↦ ((√(s ^ 2 + ‖y‖ ^ 2), y) : Spacetime))
      (continuousAt_hyperboloidalEnergyDensity m (hx.of_le one_le_two)
        (Real.sqrt_pos.2 (by positivity)).ne') hf.continuousAt
  have hsub : support (fun x : EuclideanSpace ℝ (Fin 3) ↦
      hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x)) ⊆ Metric.closedBall 0 (s ^ 2) := by
    intro x hx
    have hxu : ((√(s ^ 2 + ‖x‖ ^ 2), x) : Spacetime) ∈ tsupport u :=
      support_hyperboloidalEnergyDensity_subset m u (Function.mem_support.2 hx)
    have hK' : ((√(s ^ 2 + ‖x‖ ^ 2), x) : Spacetime) ∈ {p : Spacetime | ‖p.2‖ ≤ p.1 - 1} :=
      hsupp ⟨hmem x, hxu⟩
    have hK : ‖x‖ ≤ √(s ^ 2 + ‖x‖ ^ 2) - 1 := hK'
    have h₁ := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ ‖x‖ + 1)
      (by linarith : ‖x‖ + 1 ≤ √(s ^ 2 + ‖x‖ ^ 2))
    have h₂ := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ s ^ 2 + ‖x‖ ^ 2)
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg x]
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (s ^ 2)) hsub)

/-! ### The hyperboloidal energy identity -/

/-- **The hyperboloidal energy identity** (localized version). Let `0 < s₁ < s₂`, let
`D = {(t, x) | √(s₁² + |x|²) ≤ t ≤ √(s₂² + |x|²)}` be the closed region between the hyperboloids
`H_{s₁}` and `H_{s₂}`, and `K = {(t, x) | |x| ≤ t - 1}` the closed solid cone. Let `U` be an open
set containing `D ∩ K`, let `u` be `C²` on `U`, and assume that the points of `D` in the closed
support of `u` lie in `K`. Then
`E_m(s₂, u) - E_m(s₁, u) = -2 ∫_D ⟪KG_m u, ∂_t u⟫`,
where `KG_m u = □u - m² u` and the integral is for Lebesgue measure on `Spacetime`.

Both integrands are integrable (`integrable_hyperboloidalEnergyDensity`,
`integrableOn_inner_kleinGordon_timeDeriv`), so the identity is between genuine integrals. -/
theorem hyperboloidalEnergy_sub_hyperboloidalEnergy {m s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) {U : Set Spacetime} (hU : IsOpen U)
    (hDU : {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
      {p | ‖p.2‖ ≤ p.1 - 1} ⊆ U)
    (hu : ContDiffOn ℝ 2 u U)
    (hsupp : {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
      tsupport u ⊆ {p | ‖p.2‖ ≤ p.1 - 1}) :
    hyperboloidalEnergy m s₂ u - hyperboloidalEnergy m s₁ u =
      -2 * ∫ p in {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)},
        ⟪kleinGordon m u p, ∂ₜ u p⟫ := by
  -- the energy current `J`, written in the coordinates `(x, t)` as `(X₀, X)`, is `C¹` on the
  -- preimage of `U` and satisfies the support condition of the divergence theorem
  have hswap : ContDiffOn ℝ 1 (Prod.swap : EuclideanSpace ℝ (Fin 3) × ℝ → Spacetime)
      (Prod.swap ⁻¹' U) :=
    (contDiff_snd.prodMk contDiff_fst).contDiffOn
  have hJ (α : Fin 4) : ContDiffOn ℝ 1
      (fun q : EuclideanSpace ℝ (Fin 3) × ℝ ↦ energyCurrent m u α (q.2, q.1)) (Prod.swap ⁻¹' U) :=
    (contDiffOn_energyCurrent m hU hu α).comp hswap fun _ hq ↦ hq
  have hX : ContDiffOn ℝ 1 (fun q : EuclideanSpace ℝ (Fin 3) × ℝ ↦
      ∑ a : Fin 3, energyCurrent m u a.succ (q.2, q.1) • EuclideanSpace.single a (1 : ℝ))
      (Prod.swap ⁻¹' U) :=
    ContDiffOn.sum fun a _ ↦ (hJ a.succ).smul contDiffOn_const
  have hcl : IsClosed (Prod.swap ⁻¹' tsupport u : Set (EuclideanSpace ℝ (Fin 3) × ℝ)) :=
    (isClosed_tsupport u).preimage continuous_swap
  have hJs (α : Fin 4) (q : EuclideanSpace ℝ (Fin 3) × ℝ) (hq : q ∉ Prod.swap ⁻¹' tsupport u) :
      energyCurrent m u α (q.2, q.1) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hq (tsupport_energyCurrent_subset m u α h)
  have hsX₀ : tsupport (fun q : EuclideanSpace ℝ (Fin 3) × ℝ ↦ energyCurrent m u 0 (q.2, q.1)) ⊆
      Prod.swap ⁻¹' tsupport u :=
    closure_minimal (fun q hq ↦ by_contra fun h ↦ hq (hJs 0 q h)) hcl
  have hsX : tsupport (fun q : EuclideanSpace ℝ (Fin 3) × ℝ ↦
      ∑ a : Fin 3, energyCurrent m u a.succ (q.2, q.1) • EuclideanSpace.single a (1 : ℝ)) ⊆
      Prod.swap ⁻¹' tsupport u :=
    closure_minimal (fun q hq ↦ by_contra fun h ↦ hq (by simp [hJs _ q h])) hcl
  have hDU' (q : EuclideanSpace ℝ (Fin 3) × ℝ)
      (hq : q.swap ∈ {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
        {p | ‖p.2‖ ≤ p.1 - 1}) : q.swap ∈ U :=
    hDU hq
  have hsupp' (q : EuclideanSpace ℝ (Fin 3) × ℝ)
      (hq : q.swap ∈ {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)})
      (hq' : q.swap ∈ tsupport u) : q.swap ∈ {p : Spacetime | ‖p.2‖ ≤ p.1 - 1} :=
    hsupp ⟨hq, hq'⟩
  have hdiv := integral_divergence_between_hyperboloids_of_contDiffOn (μ := volume) hs₁ hs₁₂
    (hU.preimage continuous_swap) (fun q hq ↦ hDU' q hq) (hJ 0) hX
    (fun q hq ↦ hsupp' q hq.1 (hq.2.elim (fun h ↦ hsX₀ h) (fun h ↦ hsX h)))
  -- the divergence of the energy current is `-⟪KG_m u, ∂_t u⟫`
  have hlhs : -∫ p in {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)},
        ⟪kleinGordon m u p, ∂ₜ u p⟫ =
      ∫ q in {q : EuclideanSpace ℝ (Fin 3) × ℝ |
          q.2 ∈ Icc √(s₁ ^ 2 + ‖q.1‖ ^ 2) √(s₂ ^ 2 + ‖q.1‖ ^ 2)},
        (deriv (fun t ↦ energyCurrent m u 0 (t, q.1)) q.2 +
          spatialDivergence (fun q' : EuclideanSpace ℝ (Fin 3) × ℝ ↦ ∑ a : Fin 3,
            energyCurrent m u a.succ (q'.2, q'.1) • EuclideanSpace.single a (1 : ℝ)) q)
        ∂(volume.prod volume) := by
    rw [← integral_neg, setIntegral_spacetime_eq_setIntegral_swap]
    refine setIntegral_congr_fun ?_ fun q hq ↦ ?_
    · exact ((isClosed_le (by fun_prop) (by fun_prop)).inter
        (isClosed_le (by fun_prop) (by fun_prop))).measurableSet
    · have hq' := contDiffAt_of_inter_tsupport_subset hU hDU hu hsupp (p := q.swap) hq
      exact (spacetimeDiv_energyCurrent m hq').symm.trans
        (deriv_add_spatialDivergence_eq_spacetimeDiv (energyCurrent m u) (x := q.1) (t := q.2)
          fun α ↦ (contDiffAt_energyCurrent m α hq').differentiableAt one_ne_zero).symm
  -- the fluxes are half the energies
  have hflux (s : ℝ) : ∫ x : EuclideanSpace ℝ (Fin 3),
      (energyCurrent m u 0 (√(s ^ 2 + ‖x‖ ^ 2), x) -
        ⟪x, ∑ a : Fin 3, energyCurrent m u a.succ (√(s ^ 2 + ‖x‖ ^ 2), x) •
        EuclideanSpace.single a (1 : ℝ)⟫ / √(s ^ 2 + ‖x‖ ^ 2)) =
      hyperboloidalEnergy m s u / 2 := by
    rw [hyperboloidalEnergy_apply, ← integral_div]
    congr 1
    funext x
    exact energyCurrent_sub_inner_div_eq m u x _
  have key := hlhs.trans (hdiv.trans (congrArg₂ (· - ·) (hflux s₂) (hflux s₁)))
  linarith

/-- **Conservation of the hyperboloidal energy.** Under the hypotheses of
`hyperboloidalEnergy_sub_hyperboloidalEnergy`, if moreover `u` solves the Klein–Gordon equation
`□u - m² u = 0` on `D ∩ K`, then `E_m(s₁, u) = E_m(s₂, u)`. -/
theorem hyperboloidalEnergy_eq_of_kleinGordon_eq_zero {m s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) {U : Set Spacetime} (hU : IsOpen U)
    (hDU : {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
      {p | ‖p.2‖ ≤ p.1 - 1} ⊆ U)
    (hu : ContDiffOn ℝ 2 u U)
    (hsupp : {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
      tsupport u ⊆ {p | ‖p.2‖ ≤ p.1 - 1})
    (hKG : ∀ p ∈ {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)} ∩
      {p | ‖p.2‖ ≤ p.1 - 1}, kleinGordon m u p = 0) :
    hyperboloidalEnergy m s₁ u = hyperboloidalEnergy m s₂ u := by
  have h := hyperboloidalEnergy_sub_hyperboloidalEnergy (m := m) hs₁ hs₁₂ hU hDU hu hsupp
  have h0 : ∫ p in {p : Spacetime | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)},
      ⟪kleinGordon m u p, ∂ₜ u p⟫ = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun p hp ↦ ?_
    by_cases hK : p ∈ {p : Spacetime | ‖p.2‖ ≤ p.1 - 1}
    · rw [hKG p ⟨hp, hK⟩, inner_zero_left]
    · have ht : ∂ₜ u p = 0 := derivAlong_of_notMem_tsupport _ fun h ↦ hK (hsupp ⟨hp, h⟩)
      rw [ht, inner_zero_right]
  rw [h0, mul_zero, sub_eq_zero] at h
  exact h.symm

/-! ### Sanity checks

The hypotheses of the energy identity `hyperboloidalEnergy_sub_hyperboloidalEnergy` hold for the
following real field `u : Spacetime → ℝ` (`F = ℝ`), with `s₁ = 2`, `s₂ = 4` and `U` the whole
spacetime: `u` is a smooth bump function centered at `(t, x) = (4, 0)`, equal to `1` on the closed
ball of radius `1 / 4` and vanishing outside the open ball of radius `1 / 2`, for the max norm
`max |t - 4| ‖x‖` of `Spacetime`. Its closed support `{|t - 4| ≤ 1 / 2, ‖x‖ ≤ 1 / 2}` lies in the
cone `‖x‖ ≤ t - 1`, since `t ≥ 7 / 2` there; it meets the upper hyperboloid `H_4` near `(4, 0)`. -/

section SanityChecks

/-- A smooth bump function on `Spacetime` centered at `(t, x) = (4, 0)`, equal to `1` on the
closed ball of radius `1 / 4` and vanishing outside the open ball of radius `1 / 2`. -/
private def sanityBump : ContDiffBump ((4 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The points `(t, x)` of the closed support of the bump function satisfy `|t - 4| ≤ 1 / 2` and
`‖x‖ ≤ 1 / 2`. -/
private theorem mem_tsupport_sanityBump {t : ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (h : ((t, x) : Spacetime) ∈ tsupport (sanityBump : Spacetime → ℝ)) :
    -(1 / 2) ≤ t - 4 ∧ t - 4 ≤ 1 / 2 ∧ ‖x‖ ≤ 1 / 2 := by
  rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq,
    dist_zero_right] at h
  have hr : sanityBump.rOut = 1 / 2 := rfl
  rw [hr, abs_le] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The bump function equals `1` at the points `(t, x)` with `|t - 4| ≤ 1 / 4` and
`‖x‖ ≤ 1 / 4`. -/
private theorem sanityBump_eq_one {t : ℝ} {x : EuclideanSpace ℝ (Fin 3)} (h₁ : -(1 / 4) ≤ t - 4)
    (h₂ : t - 4 ≤ 1 / 4) (h₃ : ‖x‖ ≤ 1 / 4) : (sanityBump : Spacetime → ℝ) (t, x) = 1 := by
  refine sanityBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, Real.dist_eq, dist_zero_right]
  have hr : sanityBump.rIn = 1 / 4 := rfl
  rw [hr, abs_le]
  exact ⟨⟨h₁, h₂⟩, h₃⟩

/-- The closed support of the bump function lies in the cone `‖x‖ ≤ t - 1`. -/
private theorem tsupport_sanityBump_subset :
    tsupport (sanityBump : Spacetime → ℝ) ⊆ {p : Spacetime | ‖p.2‖ ≤ p.1 - 1} := by
  intro p hp
  obtain ⟨h₁, -, h₃⟩ := mem_tsupport_sanityBump (t := p.1) (x := p.2) hp
  change ‖p.2‖ ≤ p.1 - 1
  linarith

/-- The hyperboloidal energy identity for the bump function `u = sanityBump` (`F = ℝ`, any mass
`m`) between the hyperboloids `s₁ = 2` and `s₂ = 4`, with `U` the whole spacetime. -/
example (m : ℝ) :
    hyperboloidalEnergy m 4 (sanityBump : Spacetime → ℝ) -
        hyperboloidalEnergy m 2 (sanityBump : Spacetime → ℝ) =
      -2 * ∫ p in {p : Spacetime | p.1 ∈ Icc √(2 ^ 2 + ‖p.2‖ ^ 2) √(4 ^ 2 + ‖p.2‖ ^ 2)},
        ⟪kleinGordon m (sanityBump : Spacetime → ℝ) p, ∂ₜ (sanityBump : Spacetime → ℝ) p⟫ :=
  hyperboloidalEnergy_sub_hyperboloidalEnergy (by norm_num) (by norm_num) isOpen_univ
    (subset_univ _) sanityBump.contDiff.contDiffOn
    (inter_subset_right.trans tsupport_sanityBump_subset)

/-- Both sides of the identity of the previous example are nonzero for `m ≠ 0`. The lower energy
vanishes, since the closed support of `u` does not meet `H_2`. The upper energy is positive: on
`H_4` the energy density is nonnegative (`hyperboloidalEnergyDensity_nonneg`), and it is at least
`m² > 0` where `u = 1`, which is the case at the points of `H_4` with `‖x‖ < 1 / 4`; and it is
integrable (`integrable_hyperboloidalEnergyDensity`). -/
example {m : ℝ} (hm : m ≠ 0) :
    hyperboloidalEnergy m 2 (sanityBump : Spacetime → ℝ) = 0 ∧
      0 < hyperboloidalEnergy m 4 (sanityBump : Spacetime → ℝ) := by
  constructor
  · -- the hyperboloid `H_2` does not meet the closed support of `u`
    have h0 (x : EuclideanSpace ℝ (Fin 3)) :
        hyperboloidalEnergyDensity m (sanityBump : Spacetime → ℝ) (√(2 ^ 2 + ‖x‖ ^ 2), x) = 0 := by
      by_contra hne
      obtain ⟨h₁, -, h₃⟩ :=
        mem_tsupport_sanityBump (support_hyperboloidalEnergyDensity_subset m _ hne)
      have h₂ := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 ^ 2 + ‖x‖ ^ 2)
      have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
      -- `linarith` would normalize the radicand of the square root in some hypotheses only
      generalize √(2 ^ 2 + ‖x‖ ^ 2) = S at h₁ h₂
      nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 7 / 2)
        (by linarith : (7 : ℝ) / 2 ≤ S), mul_self_le_mul_self hx0 h₃]
    simp only [hyperboloidalEnergy_apply, h0, integral_zero]
  · -- the energy density on `H_4` is nonnegative, integrable, and positive near `x = 0`
    have hnonneg : 0 ≤ fun x : EuclideanSpace ℝ (Fin 3) ↦
        hyperboloidalEnergyDensity m (sanityBump : Spacetime → ℝ) (√(4 ^ 2 + ‖x‖ ^ 2), x) :=
      fun x ↦ hyperboloidalEnergyDensity_nonneg m _
        ((Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg 4))).trans (le_abs_self _))
        (Real.sqrt_pos.2 (by positivity)).ne'
    have hint := integrable_hyperboloidalEnergyDensity (m := m) (s₁ := 2) (s₂ := 4) (s := 4)
      (by norm_num) ⟨by norm_num, le_rfl⟩ isOpen_univ (subset_univ _)
      sanityBump.contDiff.contDiffOn (inter_subset_right.trans tsupport_sanityBump_subset)
    have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4) ⊆ support fun x ↦
        hyperboloidalEnergyDensity m (sanityBump : Spacetime → ℝ) (√(4 ^ 2 + ‖x‖ ^ 2), x) := by
      intro x hx
      rw [Metric.mem_ball, dist_zero_right] at hx
      have h₄ : (4 : ℝ) ≤ √(4 ^ 2 + ‖x‖ ^ 2) :=
        Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg x])
      have h₄' : √(4 ^ 2 + ‖x‖ ^ 2) ≤ 4 + 1 / 4 := by
        calc √(4 ^ 2 + ‖x‖ ^ 2) ≤ √((4 + 1 / 4) ^ 2) :=
              Real.sqrt_le_sqrt (by nlinarith [norm_nonneg x])
          _ = 4 + 1 / 4 := Real.sqrt_sq (by norm_num)
      have hu1 : (sanityBump : Spacetime → ℝ) (√(4 ^ 2 + ‖x‖ ^ 2), x) = 1 := by
        generalize √(4 ^ 2 + ‖x‖ ^ 2) = S at h₄ h₄' ⊢
        exact sanityBump_eq_one (by linarith) (by linarith) hx.le
      rw [Function.mem_support,
        hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv_of_hyperboloid m _
          (by norm_num : (4 : ℝ) ≠ 0), hu1, norm_one, one_pow, mul_one]
      positivity
    rw [hyperboloidalEnergy_apply, integral_pos_iff_support_of_nonneg hnonneg hint]
    exact (Metric.measure_ball_pos volume 0 (by norm_num)).trans_le (measure_mono hball)

/-- The hypotheses of the conservation law `hyperboloidalEnergy_eq_of_kleinGordon_eq_zero` hold for
the same bump function between the hyperboloids `s₁ = 5` and `s₂ = 6`: the region between them
lies in `{t ≥ 5}` and does not meet the closed support of `u` (where `t ≤ 9 / 2`), so `u` and
`□u - m² u` vanish on it. (Both energies are `0` here.) -/
example (m : ℝ) :
    hyperboloidalEnergy m 5 (sanityBump : Spacetime → ℝ) =
      hyperboloidalEnergy m 6 (sanityBump : Spacetime → ℝ) := by
  have hD (p : Spacetime)
      (hp : p ∈ {p : Spacetime | p.1 ∈ Icc √(5 ^ 2 + ‖p.2‖ ^ 2) √(6 ^ 2 + ‖p.2‖ ^ 2)}) :
      p ∉ tsupport (sanityBump : Spacetime → ℝ) := by
    intro h
    obtain ⟨-, h₂, -⟩ := mem_tsupport_sanityBump (t := p.1) (x := p.2) h
    have h₅ : (5 : ℝ) ≤ √(5 ^ 2 + ‖p.2‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg p.2])
    have h₁ : √(5 ^ 2 + ‖p.2‖ ^ 2) ≤ p.1 := hp.1
    linarith
  exact hyperboloidalEnergy_eq_of_kleinGordon_eq_zero (by norm_num) (by norm_num) isOpen_univ
    (subset_univ _) sanityBump.contDiff.contDiffOn (fun p hp ↦ absurd hp.2 (hD p hp.1))
    fun p hp ↦ kleinGordon_of_notMem_tsupport m (hD p hp.1)

end SanityChecks

end VectorFieldMethod.Minkowski
