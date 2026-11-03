/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.Derivative

/-!
# The wave operator and the Klein–Gordon operator

## Main definitions

* `dAlembertian u`: the wave operator (d'Alembertian)
  `□u = η^{αβ} ∂_α ∂_β u = -∂_t² u + ∑ a, ∂_a² u`.
* `kleinGordon m u`: the Klein–Gordon operator `□u - m² u`.

## Main statements

* `dAlembertian_eq`: `□u = -∂_t² u + ∑ a, ∂_a² u`.
* Linearity: `dAlembertian_smul`, `kleinGordon_smul` (real scalars, no hypothesis);
  `dAlembertian_const_smul_field`, `kleinGordon_const_smul_field` (scalars `c : R` acting on `F`,
  no hypothesis); `dAlembertian_add`, `kleinGordon_add` (for `u`, `v` that are `C²` at the point).
* Values on constants: `dAlembertian_const` (`0`) and `kleinGordon_const` (`-m² c`).
* Function-level additivity: `dAlembertian_add_of_contDiff`, `kleinGordon_add_of_contDiff`
  (for `u`, `v` of class `C²`).
* Smoothness: `contDiff_dAlembertian`, `contDiff_kleinGordon` (`C^{n+2} → C^n`) and their `C^∞`
  versions.
* Commutation with continuous linear maps: `dAlembertian_comp_left`, `kleinGordon_comp_left`
  (`□ (T ∘ u) = T (□ u)` at a point where `u` is `C²`) with their eta-expanded forms `fun_*`, and
  `dAlembertian_comp_left_equiv`, `kleinGordon_comp_left_equiv` (`□ (e ∘ u) = e ∘ □ u` for a
  continuous linear equivalence `e`, without hypotheses).

Both operators act on functions `Spacetime → F` with values in an arbitrary real normed space `F`;
the coefficients `η α β` and `m ^ 2` act by scalar multiplication.

## Sign conventions

With the signature `(-, +, +, +)`, `□ = -∂_t² + Δ`. LeFloch–Ma write `□ = ∂_t² - Δ`, which is
`-□` in the convention of this file, and write the Klein–Gordon operator as `□u + m²u` with their
`□`, which is `-(□u - m²u)`, the negative of `kleinGordon m u` here.

## Notation

`□` for `dAlembertian`, scoped in `VectorFieldMethod.Minkowski`.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology

namespace VectorFieldMethod.Minkowski

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {R : Type*} [DivisionSemiring R] [Module R F] [SMulCommClass ℝ R F]
  [ContinuousConstSMul R F]
variable {u v : Spacetime → F} {p : Spacetime} {n : ℕ∞ω}

/-- The wave operator (d'Alembertian) `□u = η^{αβ} ∂_α ∂_β u = -∂_t² u + ∑ a, ∂_a² u`.

The coefficients are the entries of the *inverse* metric `η^{αβ}`. They are written as entries of
`minkowskiMetric` because `η⁻¹ = η` (`inv_minkowskiMetric`), so `η^{αβ}` and `η_{αβ}` agree
numerically. LeFloch–Ma's `□ = ∂_t² - Δ` is the negative of this operator. -/
def dAlembertian (u : Spacetime → F) : Spacetime → F :=
  fun p ↦ ∑ α, ∑ β, η α β • ∂[α] (∂[β] u) p

@[inherit_doc] scoped notation "□" => dAlembertian

theorem dAlembertian_apply (u : Spacetime → F) (p : Spacetime) :
    □ u p = ∑ α, ∑ β, η α β • ∂[α] (∂[β] u) p :=
  rfl

/-- `□u = -∂_t² u + ∑ a, ∂_a² u`. -/
theorem dAlembertian_eq (u : Spacetime → F) (p : Spacetime) :
    □ u p = -∂ₜ (∂ₜ u) p + ∑ a, ∂ₓ[a] (∂ₓ[a] u) p := by
  simp only [dAlembertian_apply, Fin.sum_univ_succ (n := 3), minkowskiMetric_zero_zero,
    minkowskiMetric_zero_succ, minkowskiMetric_succ_zero, minkowskiMetric_succ_succ,
    partialDeriv_zero, partialDeriv_succ, zero_smul, Finset.sum_const_zero, add_zero, zero_add,
    ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, neg_one_smul]

/-! ### Values on constants and coordinates -/

@[simp]
theorem dAlembertian_const (c : F) : □ (fun _ ↦ c) = fun _ ↦ 0 := by
  funext p
  simp [dAlembertian_apply]

/-- `□t = 0`. -/
@[simp]
theorem dAlembertian_timeCoord : □ timeCoord = fun _ ↦ 0 := by
  funext p
  simp [dAlembertian_eq]

/-- `□x_b = 0`. -/
@[simp]
theorem dAlembertian_spaceCoord (b : Fin 3) : □ (spaceCoord b) = fun _ ↦ 0 := by
  funext p
  simp [dAlembertian_eq]

/-! ### The Klein–Gordon operator -/

/-- The Klein–Gordon operator `□u - m² u`. LeFloch–Ma's Klein–Gordon operator `□u + m²u` (with
their `□ = ∂_t² - Δ`) is the negative of this operator. -/
def kleinGordon (m : ℝ) (u : Spacetime → F) : Spacetime → F :=
  fun p ↦ □ u p - m ^ 2 • u p

theorem kleinGordon_apply (m : ℝ) (u : Spacetime → F) (p : Spacetime) :
    kleinGordon m u p = □ u p - m ^ 2 • u p :=
  rfl

/-- `KG_m c = -m² c` for a constant function `c`. -/
@[simp]
theorem kleinGordon_const (m : ℝ) (c : F) : kleinGordon m (fun _ ↦ c) = fun _ ↦ -(m ^ 2 • c) := by
  funext p
  simp [kleinGordon_apply]

/-! ### Linearity -/

/-- `□ (c u) = c □ u` for `c : ℝ`, without hypotheses. -/
theorem dAlembertian_smul (c : ℝ) (u : Spacetime → F) : □ (c • u) = c • □ u := by
  funext p
  simp only [dAlembertian_apply, partialDeriv_smul, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ smul_comm _ _ _

/-- Second derivatives are additive at a point where `u` and `v` are `C²`. -/
theorem partialDeriv_partialDeriv_add (α β : Fin 4) (hu : ContDiffAt ℝ 2 u p)
    (hv : ContDiffAt ℝ 2 v p) : ∂[α] (∂[β] (u + v)) p = ∂[α] (∂[β] u) p + ∂[α] (∂[β] v) p := by
  have h : ∂[β] (u + v) =ᶠ[𝓝 p] ∂[β] u + ∂[β] v := by
    filter_upwards [hu.eventually (by simp), hv.eventually (by simp)] with q hu' hv'
    exact partialDeriv_add β (hu'.differentiableAt two_ne_zero) (hv'.differentiableAt two_ne_zero)
  rw [partialDeriv, derivAlong_congr_of_eventuallyEq _ h, ← partialDeriv]
  have hu1 : ContDiffAt ℝ (1 + 1) u p := by rwa [one_add_one_eq_two]
  have hv1 : ContDiffAt ℝ (1 + 1) v p := by rwa [one_add_one_eq_two]
  exact partialDeriv_add α ((contDiffAt_partialDeriv β hu1).differentiableAt one_ne_zero)
    ((contDiffAt_partialDeriv β hv1).differentiableAt one_ne_zero)

/-- `□(u + v) = □u + □v` at a point where `u` and `v` are `C²`. -/
theorem dAlembertian_add (hu : ContDiffAt ℝ 2 u p) (hv : ContDiffAt ℝ 2 v p) :
    □ (u + v) p = □ u p + □ v p := by
  simp only [dAlembertian_apply, partialDeriv_partialDeriv_add _ _ hu hv, smul_add,
    Finset.sum_add_distrib]

/-- `KG (c u) = c KG u` for `c : ℝ`, without hypotheses. -/
theorem kleinGordon_smul (m c : ℝ) (u : Spacetime → F) :
    kleinGordon m (c • u) = c • kleinGordon m u := by
  funext p
  simp only [kleinGordon_apply, dAlembertian_smul, Pi.smul_apply, smul_sub]
  rw [smul_comm]

/-- `KG(u + v) = KG u + KG v` at a point where `u` and `v` are `C²`. -/
theorem kleinGordon_add (m : ℝ) (hu : ContDiffAt ℝ 2 u p) (hv : ContDiffAt ℝ 2 v p) :
    kleinGordon m (u + v) p = kleinGordon m u p + kleinGordon m v p := by
  simp only [kleinGordon_apply, dAlembertian_add hu hv, Pi.add_apply, smul_add]
  abel

/-- `□ (c u) = c □ u` for a scalar `c : R` acting on `F` (for instance `c : ℂ` when `F = ℂ`),
without hypotheses. -/
theorem dAlembertian_const_smul_field (c : R) (u : Spacetime → F) : □ (c • u) = c • □ u := by
  funext p
  simp only [dAlembertian_apply, partialDeriv_const_smul_field, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ smul_comm _ _ _

/-- `KG (c u) = c KG u` for a scalar `c : R` acting on `F`, without hypotheses. -/
theorem kleinGordon_const_smul_field (m : ℝ) (c : R) (u : Spacetime → F) :
    kleinGordon m (c • u) = c • kleinGordon m u := by
  funext p
  simp only [kleinGordon_apply, dAlembertian_const_smul_field, Pi.smul_apply, smul_sub]
  congr 1
  exact smul_comm _ _ _

/-- `□(u + v) = □u + □v` for `u` and `v` of class `C²`. -/
theorem dAlembertian_add_of_contDiff (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    □ (u + v) = □ u + □ v :=
  funext fun _ ↦ dAlembertian_add hu.contDiffAt hv.contDiffAt

/-- `KG(u + v) = KG u + KG v` for `u` and `v` of class `C²`. -/
theorem kleinGordon_add_of_contDiff (m : ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    kleinGordon m (u + v) = kleinGordon m u + kleinGordon m v :=
  funext fun _ ↦ kleinGordon_add m hu.contDiffAt hv.contDiffAt

/-! ### Commutation with continuous linear maps -/

/-- `∂_α ∂_β (T ∘ u) = T (∂_α ∂_β u)` at a point where `u` is `C²`. -/
@[to_fun]
theorem partialDeriv_partialDeriv_comp_left (α β : Fin 4) (T : F →L[ℝ] G)
    (hu : ContDiffAt ℝ 2 u p) : ∂[α] (∂[β] (T ∘ u)) p = T (∂[α] (∂[β] u) p) := by
  have h : ∂[β] (T ∘ u) =ᶠ[𝓝 p] T ∘ ∂[β] u := by
    filter_upwards [hu.eventually (by simp)] with q hu'
    exact partialDeriv_comp_left β T (hu'.differentiableAt two_ne_zero)
  rw [partialDeriv, derivAlong_congr_of_eventuallyEq _ h, ← partialDeriv]
  have hu1 : ContDiffAt ℝ (1 + 1) u p := by rwa [one_add_one_eq_two]
  exact partialDeriv_comp_left α T ((contDiffAt_partialDeriv β hu1).differentiableAt one_ne_zero)

/-- `□ (T ∘ u) = T (□ u)` for a continuous linear map `T`, at a point where `u` is `C²`. The
eta-expanded form `fun_dAlembertian_comp_left` is about `fun q ↦ T (u q)`. -/
@[to_fun]
theorem dAlembertian_comp_left (T : F →L[ℝ] G) (hu : ContDiffAt ℝ 2 u p) :
    □ (T ∘ u) p = T (□ u p) := by
  simp only [dAlembertian_apply, partialDeriv_partialDeriv_comp_left _ _ T hu, map_sum, map_smul]

/-- `KG (T ∘ u) = T (KG u)` for a continuous linear map `T`, at a point where `u` is `C²`. -/
@[to_fun]
theorem kleinGordon_comp_left (m : ℝ) (T : F →L[ℝ] G) (hu : ContDiffAt ℝ 2 u p) :
    kleinGordon m (T ∘ u) p = T (kleinGordon m u p) := by
  rw [kleinGordon_apply, kleinGordon_apply, dAlembertian_comp_left T hu, map_sub, map_smul]
  rfl

/-- `□ (e ∘ u) = e ∘ □ u` for a continuous linear equivalence `e`, without hypotheses. -/
@[to_fun]
theorem dAlembertian_comp_left_equiv (e : F ≃L[ℝ] G) (u : Spacetime → F) :
    □ (e ∘ u) = e ∘ □ u := by
  funext p
  simp only [dAlembertian_apply, partialDeriv_comp_left_equiv, Function.comp_apply, map_sum,
    map_smul]

/-- `KG (e ∘ u) = e ∘ KG u` for a continuous linear equivalence `e`, without hypotheses. -/
@[to_fun]
theorem kleinGordon_comp_left_equiv (m : ℝ) (e : F ≃L[ℝ] G) (u : Spacetime → F) :
    kleinGordon m (e ∘ u) = e ∘ kleinGordon m u := by
  funext p
  simp only [kleinGordon_apply, dAlembertian_comp_left_equiv, Function.comp_apply, map_sub,
    map_smul]

/-! ### Smoothness -/

/-- If `u` is `C^{n+2}`, then `□u` is `C^n`. -/
theorem contDiff_dAlembertian (hu : ContDiff ℝ (n + 2) u) : ContDiff ℝ n (□ u) := by
  have hu' : ContDiff ℝ (n + 1 + 1) u := by rwa [add_assoc, one_add_one_eq_two]
  refine ContDiff.sum fun α _ ↦ ContDiff.sum fun β _ ↦ contDiff_const.smul ?_
  exact contDiff_partialDeriv α (contDiff_partialDeriv β hu')

/-- If `u` is `C^{n+2}`, then `□u - m²u` is `C^n`. -/
theorem contDiff_kleinGordon (m : ℝ) (hu : ContDiff ℝ (n + 2) u) :
    ContDiff ℝ n (kleinGordon m u) :=
  (contDiff_dAlembertian hu).sub (contDiff_const.smul (hu.of_le le_self_add))

theorem contDiff_infty_dAlembertian (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (□ u) :=
  contDiff_dAlembertian hu

theorem contDiff_infty_kleinGordon (m : ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (kleinGordon m u) :=
  contDiff_kleinGordon m hu

end VectorFieldMethod.Minkowski
