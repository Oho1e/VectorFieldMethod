/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.EnergyMomentum
public import VectorFieldMethod.Minkowski.VectorFields
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The semi-hyperboloidal frame and the hyperboloidal energy

LeFloch–Ma's hyperboloidal foliation method works on the hyperboloids
`H_s = {t = √(s ^ 2 + ‖x‖ ^ 2)}` and replaces the spatial derivatives `∂_a` by the
*semi-hyperboloidal* derivatives `∂̲_a = ∂_a + (x_a / t) ∂_t`, which are tangent to the
hyperboloids. The energy of a Klein–Gordon field on `H_s` is the integral over `x ∈ ℝ³` of the
energy density `e_m[u]` at the point `(√(s ^ 2 + ‖x‖ ^ 2), x)` of `H_s`.

## Main definitions

* `semiHyperboloidalDeriv a u`: the semi-hyperboloidal derivative
  `∂̲_a u = ∂_a u + (x_a / t) ∂_t u`, for `a : Fin 3`.
* `hyperboloidalEnergyDensity m u`: the energy density
  `e_m[u] = ‖∂_t u‖² + ∑ a, ‖∂_a u‖² + 2 ∑ a, (x_a / t) ⟪∂_a u, ∂_t u⟫ + m² ‖u‖²`.
* `hyperboloidalEnergy m s u`: the hyperboloidal energy
  `E_m(s, u) = ∫_{ℝ³} e_m[u](√(s ^ 2 + ‖x‖ ^ 2), x) dx`.

## Main statements

* `boost_eq_timeCoord_smul_semiHyperboloidalDeriv`: `L_a u = t ∂̲_a u` where `t ≠ 0`.
* `hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv`: where `t ≠ 0`,
  `e_m[u] = ∑ a, ‖∂̲_a u‖² + ((t² - r²) / t²) ‖∂_t u‖² + m² ‖u‖²`; on `H_s` the coefficient is
  `s² / t²` (`hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv_of_hyperboloid`).
* `hyperboloidalEnergyDensity_nonneg`: `e_m[u] ≥ 0` where `r ≤ |t|` and `t ≠ 0`; hence
  `hyperboloidalEnergy_nonneg`: `E_m(s, u) ≥ 0` for `s ≠ 0`.
-/

@[expose] public noncomputable section

open Function
open scoped RealInnerProductSpace

namespace VectorFieldMethod.Minkowski

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {u : Spacetime → F} {p : Spacetime}

/-! ### The semi-hyperboloidal derivatives -/

/-- The semi-hyperboloidal derivative `∂̲_a u = ∂_a u + (x_a / t) ∂_t u`, for `a : Fin 3` (the
mathematical index is `a + 1`). At `t = 0` the coefficient `x_a / t` is the junk value `0`. -/
def semiHyperboloidalDeriv (a : Fin 3) (u : Spacetime → F) : Spacetime → F :=
  fun p ↦ ∂ₓ[a] u p + (spaceCoord a p / timeCoord p) • ∂ₜ u p

theorem semiHyperboloidalDeriv_apply (a : Fin 3) (u : Spacetime → F) (p : Spacetime) :
    semiHyperboloidalDeriv a u p = ∂ₓ[a] u p + (spaceCoord a p / timeCoord p) • ∂ₜ u p :=
  rfl

/-- The boost is `t` times the semi-hyperboloidal derivative: `L_a u = t ∂̲_a u` at a point where
`t ≠ 0`. -/
theorem boost_eq_timeCoord_smul_semiHyperboloidalDeriv (a : Fin 3) (u : Spacetime → F)
    (hp : timeCoord p ≠ 0) : boost a u p = timeCoord p • semiHyperboloidalDeriv a u p := by
  rw [boost_eq, semiHyperboloidalDeriv_apply, smul_add, smul_smul, mul_div_cancel₀ _ hp]

/-- `‖∂̲_a u‖² = ‖∂_a u‖² + 2 (x_a / t) ⟪∂_a u, ∂_t u⟫ + (x_a / t)² ‖∂_t u‖²`. -/
theorem norm_semiHyperboloidalDeriv_sq (a : Fin 3) (u : Spacetime → F) (p : Spacetime) :
    ‖semiHyperboloidalDeriv a u p‖ ^ 2 = ‖∂ₓ[a] u p‖ ^ 2 +
      2 * (spaceCoord a p / timeCoord p * ⟪∂ₓ[a] u p, ∂ₜ u p⟫) +
      (spaceCoord a p / timeCoord p) ^ 2 * ‖∂ₜ u p‖ ^ 2 := by
  rw [semiHyperboloidalDeriv_apply, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]

/-! ### The hyperboloidal energy density and energy -/

/-- The hyperboloidal energy density of the Klein–Gordon field `u` of mass `m`, in the
normalization of LeFloch–Ma (without a factor `½`):
`e_m[u] = ‖∂_t u‖² + ∑ a, ‖∂_a u‖² + 2 ∑ a, (x_a / t) ⟪∂_a u, ∂_t u⟫ + m² ‖u‖²`.

It is twice the flux density `P⁰ - ∑ a, (x_a / t) P^a` of the energy current `P` through the
hyperboloids (`hyperboloidalEnergyDensity_eq_energyCurrent`). At `t = 0` the coefficients
`x_a / t` are the junk value `0`. -/
def hyperboloidalEnergyDensity (m : ℝ) (u : Spacetime → F) : Spacetime → ℝ :=
  fun p ↦ ‖∂ₜ u p‖ ^ 2 + ∑ a, ‖∂ₓ[a] u p‖ ^ 2 +
    2 * ∑ a, spaceCoord a p / timeCoord p * ⟪∂ₓ[a] u p, ∂ₜ u p⟫ + m ^ 2 * ‖u p‖ ^ 2

theorem hyperboloidalEnergyDensity_apply (m : ℝ) (u : Spacetime → F) (p : Spacetime) :
    hyperboloidalEnergyDensity m u p = ‖∂ₜ u p‖ ^ 2 + ∑ a, ‖∂ₓ[a] u p‖ ^ 2 +
      2 * ∑ a, spaceCoord a p / timeCoord p * ⟪∂ₓ[a] u p, ∂ₜ u p⟫ + m ^ 2 * ‖u p‖ ^ 2 :=
  rfl

/-- The hyperboloidal energy `E_m(s, u) = ∫_{ℝ³} e_m[u](√(s ^ 2 + ‖x‖ ^ 2), x) dx` of `u` on the
hyperboloid `H_s = {t = √(s ^ 2 + ‖x‖ ^ 2)}`, in the normalization of LeFloch–Ma (without a factor
`½`). The integral is for Lebesgue measure on `ℝ³`; it is the junk value `0` if
`x ↦ e_m[u](√(s ^ 2 + ‖x‖ ^ 2), x)` is not integrable. -/
def hyperboloidalEnergy (m s : ℝ) (u : Spacetime → F) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin 3), hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x)

theorem hyperboloidalEnergy_apply (m s : ℝ) (u : Spacetime → F) :
    hyperboloidalEnergy m s u =
      ∫ x : EuclideanSpace ℝ (Fin 3), hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x) :=
  rfl

/-! ### The energy density in the semi-hyperboloidal frame -/

/-- The energy density in the semi-hyperboloidal frame: at a point where `t ≠ 0`,
`e_m[u] = ∑ a, ‖∂̲_a u‖² + ((t² - r²) / t²) ‖∂_t u‖² + m² ‖u‖²`. -/
theorem hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv (m : ℝ) (u : Spacetime → F)
    (hp : timeCoord p ≠ 0) :
    hyperboloidalEnergyDensity m u p = ∑ a, ‖semiHyperboloidalDeriv a u p‖ ^ 2 +
      (timeCoord p ^ 2 - radius p ^ 2) / timeCoord p ^ 2 * ‖∂ₜ u p‖ ^ 2 + m ^ 2 * ‖u p‖ ^ 2 := by
  simp only [norm_semiHyperboloidalDeriv_sq, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, div_pow, ← Finset.sum_div, ← radius_sq, hyperboloidalEnergyDensity_apply]
  field_simp
  ring

/-- The energy density on the hyperboloid `H_s`, where `t² - r² = s²`: at the point
`(√(s² + |x|²), x)`, for `s ≠ 0`,
`e_m[u] = ∑ a, ‖∂̲_a u‖² + (s² / t²) ‖∂_t u‖² + m² ‖u‖²` with `t = √(s² + |x|²)`. -/
theorem hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv_of_hyperboloid (m : ℝ)
    (u : Spacetime → F) {s : ℝ} (hs : s ≠ 0) (x : EuclideanSpace ℝ (Fin 3)) :
    hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x) =
      ∑ a, ‖semiHyperboloidalDeriv a u (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2 +
        s ^ 2 / √(s ^ 2 + ‖x‖ ^ 2) ^ 2 * ‖∂ₜ u (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2 +
        m ^ 2 * ‖u (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2 := by
  have hpos : 0 < s ^ 2 + ‖x‖ ^ 2 := by positivity
  rw [hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv m u
    (p := (√(s ^ 2 + ‖x‖ ^ 2), x)) (Real.sqrt_pos.2 hpos).ne']
  simp only [timeCoord_apply, radius_apply, Real.sq_sqrt hpos.le]
  ring

/-- The energy density is nonnegative at a point with `|x| ≤ |t|` and `t ≠ 0`. -/
theorem hyperboloidalEnergyDensity_nonneg (m : ℝ) (u : Spacetime → F)
    (hr : radius p ≤ |timeCoord p|) (hp : timeCoord p ≠ 0) :
    0 ≤ hyperboloidalEnergyDensity m u p := by
  rw [hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv m u hp]
  have hr0 : 0 ≤ radius p := norm_nonneg p.2
  have h : radius p ^ 2 ≤ timeCoord p ^ 2 := sq_le_sq.2 (by rwa [abs_of_nonneg hr0])
  have h' : 0 ≤ (timeCoord p ^ 2 - radius p ^ 2) / timeCoord p ^ 2 :=
    div_nonneg (sub_nonneg.2 h) (sq_nonneg _)
  exact add_nonneg (add_nonneg (Finset.sum_nonneg fun a _ ↦ sq_nonneg _)
    (mul_nonneg h' (sq_nonneg _))) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The hyperboloidal energy is nonnegative, for `s ≠ 0`. -/
theorem hyperboloidalEnergy_nonneg (m : ℝ) (u : Spacetime → F) {s : ℝ} (hs : s ≠ 0) :
    0 ≤ hyperboloidalEnergy m s u := by
  refine MeasureTheory.integral_nonneg fun x ↦ hyperboloidalEnergyDensity_nonneg m u ?_ ?_
  · have hx : ‖x‖ ≤ √(s ^ 2 + ‖x‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg s))
    exact hx.trans (le_abs_self _)
  · exact (Real.sqrt_pos.2 (by positivity)).ne'

/-! ### Sanity checks -/

/-- The hypotheses `r ≤ |t|`, `t ≠ 0` of `hyperboloidalEnergyDensity_nonneg` hold at the point
`(t, x) = (1, 0)`. -/
example (m : ℝ) (u : Spacetime → F) :
    0 ≤ hyperboloidalEnergyDensity m u ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) :=
  hyperboloidalEnergyDensity_nonneg m u (by simp [radius_apply, timeCoord_apply])
    (by simp [timeCoord_apply])

end VectorFieldMethod.Minkowski
