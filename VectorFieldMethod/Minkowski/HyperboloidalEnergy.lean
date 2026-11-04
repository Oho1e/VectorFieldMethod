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
* `hyperboloidalEnergyDensity_nonneg`: `e_m[u] ≥ 0` where `r ≤ |t|` and `t ≠ 0`, and
  `hyperboloidalEnergy_nonneg`: `E_m(s, u) ≥ 0` for every `s`.
* `hyperboloidalEnergyDensity_eq_energyCurrent`: `e_m[u] = 2 (P⁰ - ∑ a, (x_a / t) P^a)` for the
  energy current `P` of `EnergyMomentum.lean`.
* `contDiffOn_energyCurrent`, `tsupport_energyCurrent_subset`: if `u` is `C²` on an open set `U`,
  the components of the energy current are `C¹` on `U`; their closed supports lie in that of `u`.

## Normalization

The energy density and the energy carry no factor `½`, as in LeFloch–Ma: apart from the cross
terms `2 ∑ a, (x_a / t) ⟪∂_a u, ∂_t u⟫`, the energy density is
`‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²`, twice the energy density `P⁰` of `EnergyMomentum.lean`,
whose energy-momentum tensor carries the factor `½`. Precisely,
`e_m[u] = 2 (P⁰ - ∑ a, (x_a / t) P^a)` (`hyperboloidalEnergyDensity_eq_energyCurrent`).

## Notation

In this file the subscript of `e_m[u]` and `E_m(s, u)` is the mass `m`. LeFloch–Ma
(*The hyperboloidal foliation method*, arXiv:1411.4910, §2.3, (2.3.2)) write the energy of a field
of mass `c` as `E_{m,c}(s, u)`, where the subscript `m` refers to Minkowski spacetime, and write
`E_m(s, u) := E_{m,0}(s, u)` for the massless energy. So `hyperboloidalEnergy c s u` is their
`E_{m,c}(s, u)`, and `hyperboloidalEnergy 0 s u` is their `E_m(s, u)`.
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
`x ↦ e_m[u](√(s ^ 2 + ‖x‖ ^ 2), x)` is not integrable.

Notation: here the subscript `m` is the mass. LeFloch–Ma write `E_{m,c}(s, u)` for the energy of
a field of mass `c` (their subscript `m` refers to Minkowski spacetime) and `E_m(s, u)` for the
massless energy `E_{m,0}(s, u)`: `hyperboloidalEnergy c s u` is their `E_{m,c}(s, u)`, and
`hyperboloidalEnergy 0 s u` is their `E_m(s, u)`. -/
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

/-- The hyperboloidal energy is nonnegative, for every `s`. (At the points of the integrand where
`t = √(s ^ 2 + ‖x‖ ^ 2)` vanishes, that is `s = 0` and `x = 0`, the coefficients `x_a / t` are the
junk value `0` and the energy density is a sum of squares.) -/
theorem hyperboloidalEnergy_nonneg (m s : ℝ) (u : Spacetime → F) :
    0 ≤ hyperboloidalEnergy m s u := by
  refine MeasureTheory.integral_nonneg fun x ↦ ?_
  by_cases ht : √(s ^ 2 + ‖x‖ ^ 2) = 0
  · simp only [hyperboloidalEnergyDensity_apply, timeCoord_apply, ht, div_zero, zero_mul,
      Finset.sum_const_zero, mul_zero, add_zero]
    positivity
  · have hx : ‖x‖ ≤ √(s ^ 2 + ‖x‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg s))
    exact hyperboloidalEnergyDensity_nonneg m u (hx.trans (le_abs_self _)) ht

/-! ### The energy density and the energy current -/

/-- The energy density is twice the flux density of the energy current through the hyperboloids:
`e_m[u] = 2 (P⁰ - ∑ a, (x_a / t) P^a)`, where `P` is the energy current `energyCurrent m u`
(which carries the factor `½`). No hypothesis is needed: both sides are the same algebraic
expression in `u(p)` and its derivatives at `p`, with the same coefficients `x_a / t` (junk value
`0` at `t = 0`). -/
theorem hyperboloidalEnergyDensity_eq_energyCurrent (m : ℝ) (u : Spacetime → F) (p : Spacetime) :
    hyperboloidalEnergyDensity m u p = 2 * (energyCurrent m u 0 p -
      ∑ a, spaceCoord a p / timeCoord p * energyCurrent m u a.succ p) := by
  simp only [hyperboloidalEnergyDensity_apply, energyCurrent_zero, energyCurrent_succ, mul_neg,
    Finset.sum_neg_distrib, sub_neg_eq_add]
  ring

/-! ### Regularity and support of the energy current -/

/-- If `u` is `C²` at `p`, every component of the energy current is `C¹` at `p`. -/
theorem contDiffAt_energyCurrent (m : ℝ) (α : Fin 4) (hu : ContDiffAt ℝ 2 u p) :
    ContDiffAt ℝ 1 (energyCurrent m u α) p := by
  have hu' : ContDiffAt ℝ (1 + 1) u p := by rwa [one_add_one_eq_two]
  have hD (β : Fin 4) : ContDiffAt ℝ 1 (∂[β] u) p := contDiffAt_partialDeriv β hu'
  have hu1 : ContDiffAt ℝ 1 u p := hu.of_le one_le_two
  simp only [energyCurrent_eq, energyMomentum_eq]
  exact contDiffAt_const.mul (((hD α).inner ℝ (hD 0)).sub (contDiffAt_const.mul
    ((ContDiffAt.sum fun γ _ ↦ contDiffAt_const.mul ((hD γ).norm_sq ℝ)).add
      (contDiffAt_const.mul (hu1.norm_sq ℝ)))))

/-- If `u` is `C²` on an open set `U`, every component of the energy current is `C¹` on `U`. -/
theorem contDiffOn_energyCurrent (m : ℝ) {U : Set Spacetime} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (α : Fin 4) : ContDiffOn ℝ 1 (energyCurrent m u α) U :=
  fun _ hq ↦ (contDiffAt_energyCurrent m α (hu.contDiffAt (hU.mem_nhds hq))).contDiffWithinAt

/-- The derivatives of `u` vanish outside the closed support of `u`. -/
theorem derivAlong_of_notMem_tsupport (V : Spacetime → Spacetime) (hp : p ∉ tsupport u) :
    derivAlong V u p = 0 := by
  have h : fderiv ℝ u p = 0 := by
    by_contra h'
    exact hp (support_fderiv_subset ℝ h')
  rw [derivAlong_apply, h]
  rfl

/-- The closed support of each component of the energy current lies in the closed support of
`u`. -/
theorem tsupport_energyCurrent_subset (m : ℝ) (u : Spacetime → F) (α : Fin 4) :
    tsupport (energyCurrent m u α) ⊆ tsupport u := by
  refine closure_minimal (fun q hq ↦ by_contra fun h ↦ hq ?_) (isClosed_tsupport u)
  have hD (β : Fin 4) : ∂[β] u q = 0 := derivAlong_of_notMem_tsupport _ h
  simp [energyCurrent_apply, energyMomentum_apply, hD, image_eq_zero_of_notMem_tsupport h]

/-- The energy density vanishes outside the closed support of `u`. -/
theorem support_hyperboloidalEnergyDensity_subset (m : ℝ) (u : Spacetime → F) :
    support (hyperboloidalEnergyDensity m u) ⊆ tsupport u := fun q hq ↦ by
  by_contra h
  have ht : ∂ₜ u q = 0 := derivAlong_of_notMem_tsupport _ h
  have hs (a : Fin 3) : ∂ₓ[a] u q = 0 := derivAlong_of_notMem_tsupport _ h
  exact hq (by simp [hyperboloidalEnergyDensity_apply, ht, hs, image_eq_zero_of_notMem_tsupport h])

/-- The energy density is continuous at a point where `t ≠ 0` and `u` is `C¹`. -/
theorem continuousAt_hyperboloidalEnergyDensity (m : ℝ) (hu : ContDiffAt ℝ 1 u p)
    (hp : timeCoord p ≠ 0) : ContinuousAt (hyperboloidalEnergyDensity m u) p := by
  have hu' : ContDiffAt ℝ (0 + 1) u p := by rwa [zero_add]
  have hD (β : Fin 4) : ContinuousAt (∂[β] u) p := (contDiffAt_partialDeriv β hu').continuousAt
  have ht : ContinuousAt (∂ₜ u) p := hD 0
  have hs (a : Fin 3) : ContinuousAt (∂ₓ[a] u) p := hD a.succ
  have hx (a : Fin 3) : ContinuousAt (fun q ↦ spaceCoord a q / timeCoord q) p :=
    ((differentiable_spaceCoord a).continuous.continuousAt).div
      differentiable_timeCoord.continuous.continuousAt hp
  exact (((ht.norm.pow 2).add (tendsto_finsetSum _ fun a _ ↦ (hs a).norm.pow 2)).add
    (continuousAt_const.mul (tendsto_finsetSum _ fun a _ ↦ (hx a).mul
      ((hs a).inner ht)))).add (continuousAt_const.mul (hu.continuousAt.norm.pow 2))

/-! ### Sanity checks -/

/-- The hypotheses `r ≤ |t|`, `t ≠ 0` of `hyperboloidalEnergyDensity_nonneg` hold at the point
`(t, x) = (1, 0)`. -/
example (m : ℝ) (u : Spacetime → F) :
    0 ≤ hyperboloidalEnergyDensity m u ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin 3))) :=
  hyperboloidalEnergyDensity_nonneg m u (by simp [radius_apply, timeCoord_apply])
    (by simp [timeCoord_apply])

end VectorFieldMethod.Minkowski
