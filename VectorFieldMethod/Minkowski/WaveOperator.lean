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

* `wave u`: the wave operator `□u = η^{αβ} ∂_α ∂_β u = -∂_t² u + ∑ a, ∂_a² u`.
* `kleinGordon m u`: the Klein–Gordon operator `□u - m² u`.

## Main statements

* `wave_eq`: `□u = -∂_t² u + ∑ a, ∂_a² u`.
* Linearity: `wave_smul`, `kleinGordon_smul` (no hypothesis); `wave_add`, `kleinGordon_add`
  (for `u`, `v` that are `C²` at the point).
* Smoothness: `contDiff_wave`, `contDiff_kleinGordon` (`C^{n+2} → C^n`) and their `C^∞` versions.

## Sign conventions

With the signature `(-, +, +, +)`, `□ = -∂_t² + Δ`. LeFloch–Ma write `□ = ∂_t² - Δ`, which is
`-□` in the convention of this file, and write the Klein–Gordon operator as `□u + m²u` with their
`□`, which is `-(□u - m²u)`, the negative of `kleinGordon m u` here.

## Notation

`□` for `wave`, scoped in `VectorFieldMethod.Minkowski`.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology

namespace VectorFieldMethod.Minkowski

variable {u v : Spacetime → ℝ} {p : Spacetime} {n : ℕ∞ω}

/-- The wave operator (d'Alembertian) `□u = η^{αβ} ∂_α ∂_β u = -∂_t² u + ∑ a, ∂_a² u`.

The coefficients are the entries of the *inverse* metric `η^{αβ}`. They are written as entries of
`minkowskiMetric` because `η⁻¹ = η` (`inv_minkowskiMetric`), so `η^{αβ}` and `η_{αβ}` agree
numerically. LeFloch–Ma's `□ = ∂_t² - Δ` is the negative of this operator. -/
def wave (u : Spacetime → ℝ) : Spacetime → ℝ :=
  fun p ↦ ∑ α, ∑ β, η α β * ∂[α] (∂[β] u) p

@[inherit_doc] scoped notation "□" => wave

theorem wave_apply (u : Spacetime → ℝ) (p : Spacetime) :
    □ u p = ∑ α, ∑ β, η α β * ∂[α] (∂[β] u) p :=
  rfl

/-- `□u = -∂_t² u + ∑ a, ∂_a² u`. -/
theorem wave_eq (u : Spacetime → ℝ) (p : Spacetime) :
    □ u p = -∂ₜ (∂ₜ u) p + ∑ a, ∂ₓ[a] (∂ₓ[a] u) p := by
  simp only [wave_apply, Fin.sum_univ_succ (n := 3), minkowskiMetric_zero_zero,
    minkowskiMetric_zero_succ, minkowskiMetric_succ_zero, minkowskiMetric_succ_succ,
    partialDeriv_zero, partialDeriv_succ, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, neg_one_mul]

/-! ### Values on constants and coordinates -/

@[simp]
theorem wave_const (c : ℝ) : □ (fun _ ↦ c) = fun _ ↦ 0 := by
  funext p
  simp [wave_apply]

/-- `□t = 0`. -/
@[simp]
theorem wave_timeCoord : □ timeCoord = fun _ ↦ 0 := by
  funext p
  simp [wave_eq]

/-- `□x_b = 0`. -/
@[simp]
theorem wave_spaceCoord (b : Fin 3) : □ (spaceCoord b) = fun _ ↦ 0 := by
  funext p
  simp [wave_eq]

/-! ### The Klein–Gordon operator -/

/-- The Klein–Gordon operator `□u - m² u`. LeFloch–Ma's Klein–Gordon operator `□u + m²u` (with
their `□ = ∂_t² - Δ`) is the negative of this operator. -/
def kleinGordon (m : ℝ) (u : Spacetime → ℝ) : Spacetime → ℝ :=
  fun p ↦ □ u p - m ^ 2 * u p

theorem kleinGordon_apply (m : ℝ) (u : Spacetime → ℝ) (p : Spacetime) :
    kleinGordon m u p = □ u p - m ^ 2 * u p :=
  rfl

/-! ### Linearity -/

theorem wave_smul (c : ℝ) (u : Spacetime → ℝ) : □ (c • u) = c • □ u := by
  funext p
  simp only [wave_apply, partialDeriv_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

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
theorem wave_add (hu : ContDiffAt ℝ 2 u p) (hv : ContDiffAt ℝ 2 v p) :
    □ (u + v) p = □ u p + □ v p := by
  simp only [wave_apply, partialDeriv_partialDeriv_add _ _ hu hv, mul_add,
    Finset.sum_add_distrib]

theorem kleinGordon_smul (m c : ℝ) (u : Spacetime → ℝ) :
    kleinGordon m (c • u) = c • kleinGordon m u := by
  funext p
  simp only [kleinGordon_apply, wave_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- `KG(u + v) = KG u + KG v` at a point where `u` and `v` are `C²`. -/
theorem kleinGordon_add (m : ℝ) (hu : ContDiffAt ℝ 2 u p) (hv : ContDiffAt ℝ 2 v p) :
    kleinGordon m (u + v) p = kleinGordon m u p + kleinGordon m v p := by
  simp only [kleinGordon_apply, wave_add hu hv, Pi.add_apply]
  ring

/-! ### Smoothness -/

/-- If `u` is `C^{n+2}`, then `□u` is `C^n`. -/
theorem contDiff_wave (hu : ContDiff ℝ (n + 2) u) : ContDiff ℝ n (□ u) := by
  have hu' : ContDiff ℝ (n + 1 + 1) u := by rwa [add_assoc, one_add_one_eq_two]
  refine ContDiff.sum fun α _ ↦ ContDiff.sum fun β _ ↦ contDiff_const.mul ?_
  exact contDiff_partialDeriv α (contDiff_partialDeriv β hu')

/-- If `u` is `C^{n+2}`, then `□u - m²u` is `C^n`. -/
theorem contDiff_kleinGordon (m : ℝ) (hu : ContDiff ℝ (n + 2) u) :
    ContDiff ℝ n (kleinGordon m u) :=
  (contDiff_wave hu).sub (contDiff_const.mul (hu.of_le le_self_add))

theorem contDiff_infty_wave (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (□ u) :=
  contDiff_wave hu

theorem contDiff_infty_kleinGordon (m : ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (kleinGordon m u) :=
  contDiff_kleinGordon m hu

end VectorFieldMethod.Minkowski
