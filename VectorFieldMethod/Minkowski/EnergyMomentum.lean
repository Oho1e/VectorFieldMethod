/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.WaveOperator
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# The energy-momentum tensor of the Klein–Gordon field

For a field `u : Spacetime → F` with values in a real inner product space `F` (real fields have
`F = ℝ`, complex fields `F = ℂ` with the real inner product `⟪z, w⟫ = Re (conj z * w)`) and a mass
`m : ℝ`, this file defines the energy-momentum tensor of the Klein–Gordon equation
`□u - m² u = 0`.

## Main definitions

* `energyMomentum m u α β`: the energy-momentum tensor
  `T_{αβ} = ⟪∂_α u, ∂_β u⟫ - ½ η_{αβ} (η^{γδ} ⟪∂_γ u, ∂_δ u⟫ + m² ‖u‖²)`.
* `spacetimeDiv J`: the spacetime divergence `∂_α J^α = ∑ α, ∂_α J^α` of a vector field with real
  components `J α : Spacetime → ℝ`.
* `energyCurrent m u α`: the energy current `P^α = -η^{αγ} T_{γ0}` associated with `∂_t`.

## Main statements

* `derivAlong_inner`, `derivAlong_norm_sq`: the Leibniz rules `V ⟪u, v⟫ = ⟪V u, v⟫ + ⟪u, V v⟫`
  and `V ‖u‖² = 2 ⟪u, V u⟫` at a point where `u` and `v` are differentiable.
* `energyMomentum_swap`: `T_{αβ} = T_{βα}`.
* `sum_sum_minkowskiMetric_mul_partialDeriv_energyMomentum`: the divergence identity
  `η^{αγ} ∂_γ T_{αβ} = ⟪□u - m² u, ∂_β u⟫` at a point where `u` is `C²`.
* `spacetimeDiv_energyCurrent`: the energy identity `∂_α P^α = -⟪□u - m² u, ∂_t u⟫` at a point
  where `u` is `C²`, and `spacetimeDiv_energyCurrent_eq_zero`: `∂_α P^α = 0` at `p` if moreover
  `□u - m² u = 0` near `p`.
* `energyCurrent_zero`, `energyCurrent_zero_nonneg`, `energyCurrent_succ`: the energy density
  `P^0 = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²) ≥ 0` and the components
  `P^a = -⟪∂_a u, ∂_t u⟫`, without hypotheses on `u`.

## Normalization

The tensor carries the factor `½`, so that the energy density is
`P^0 = T_{00} = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)`. Texts that define the energy density
without the factor `½`, as `‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²`, use the tensor `2 T_{αβ}` and the
current `2 P^α`, which differ from the ones of this file by the factor `2`; their versions of the
identities below are the ones of this file multiplied by `2`.

## Conventions

Signature `(-, +, +, +)`. The inverse metric `η^{αβ}` has the same entries as `η_{αβ}`
(`inv_minkowskiMetric`), so both are written with `minkowskiMetric`. The Klein–Gordon operator is
`kleinGordon m u = □u - m² u` with `□ = -∂_t² + Δ`.
-/

@[expose] public noncomputable section

open Filter
open scoped RealInnerProductSpace Topology

namespace VectorFieldMethod.Minkowski

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {u v : Spacetime → F} {p : Spacetime}

/-! ### The Leibniz rule for the inner product -/

/-- The Leibniz rule `V ⟪u, v⟫ = ⟪V u, v⟫ + ⟪u, V v⟫` at a point where `u` and `v` are
differentiable. -/
theorem derivAlong_inner (V : Spacetime → Spacetime) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    derivAlong V (fun q ↦ ⟪u q, v q⟫) p = ⟪derivAlong V u p, v p⟫ + ⟪u p, derivAlong V v p⟫ := by
  rw [derivAlong_apply, derivAlong_apply, derivAlong_apply, fderiv_inner_apply ℝ hu hv]
  exact add_comm _ _

/-- The Leibniz rule `V ‖u‖² = 2 ⟪u, V u⟫` at a point where `u` is differentiable. -/
theorem derivAlong_norm_sq (V : Spacetime → Spacetime) (hu : DifferentiableAt ℝ u p) :
    derivAlong V (fun q ↦ ‖u q‖ ^ 2) p = 2 * ⟪u p, derivAlong V u p⟫ := by
  rw [derivAlong_eq_of_hasFDerivAt hu.hasFDerivAt.norm_sq, derivAlong_apply]
  simp

/-- `∂_α ⟪u, v⟫ = ⟪∂_α u, v⟫ + ⟪u, ∂_α v⟫` at a point where `u` and `v` are differentiable. -/
theorem partialDeriv_inner (α : Fin 4) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    ∂[α] (fun q ↦ ⟪u q, v q⟫) p = ⟪∂[α] u p, v p⟫ + ⟪u p, ∂[α] v p⟫ :=
  derivAlong_inner _ hu hv

/-- `∂_α ‖u‖² = 2 ⟪u, ∂_α u⟫` at a point where `u` is differentiable. -/
theorem partialDeriv_norm_sq (α : Fin 4) (hu : DifferentiableAt ℝ u p) :
    ∂[α] (fun q ↦ ‖u q‖ ^ 2) p = 2 * ⟪u p, ∂[α] u p⟫ :=
  derivAlong_norm_sq _ hu

/-! ### Definitions -/

/-- The energy-momentum tensor of the Klein–Gordon field `u` of mass `m`:
`T_{αβ} = ⟪∂_α u, ∂_β u⟫ - ½ η_{αβ} (η^{γδ} ⟪∂_γ u, ∂_δ u⟫ + m² ‖u‖²)`.

The coefficients `η_{αβ}` and `η^{γδ}` are both entries of `minkowskiMetric` (`η⁻¹ = η`). With the
factor `½`, the energy density is `T_{00} = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)`; texts whose
energy density has no factor `½` use `2 T_{αβ}`. -/
def energyMomentum (m : ℝ) (u : Spacetime → F) (α β : Fin 4) : Spacetime → ℝ :=
  fun p ↦ ⟪∂[α] u p, ∂[β] u p⟫ -
    1 / 2 * η α β * (∑ γ, ∑ δ, η γ δ * ⟪∂[γ] u p, ∂[δ] u p⟫ + m ^ 2 * ‖u p‖ ^ 2)

theorem energyMomentum_apply (m : ℝ) (u : Spacetime → F) (α β : Fin 4) (p : Spacetime) :
    energyMomentum m u α β p = ⟪∂[α] u p, ∂[β] u p⟫ -
      1 / 2 * η α β * (∑ γ, ∑ δ, η γ δ * ⟪∂[γ] u p, ∂[δ] u p⟫ + m ^ 2 * ‖u p‖ ^ 2) :=
  rfl

/-- The spacetime divergence `∂_α J^α = ∑ α, ∂_α J^α` of the vector field with real components
`J α : Spacetime → ℝ`. -/
def spacetimeDiv (J : Fin 4 → Spacetime → ℝ) : Spacetime → ℝ :=
  fun p ↦ ∑ α, ∂[α] (J α) p

theorem spacetimeDiv_apply (J : Fin 4 → Spacetime → ℝ) (p : Spacetime) :
    spacetimeDiv J p = ∑ α, ∂[α] (J α) p :=
  rfl

/-- The energy current `P^α = -η^{αγ} T_{γ0}` of the Klein–Gordon field `u`, associated with the
vector field `∂_t`. Its time component is the energy density
`P^0 = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)`. -/
def energyCurrent (m : ℝ) (u : Spacetime → F) (α : Fin 4) : Spacetime → ℝ :=
  fun p ↦ -∑ γ, η α γ * energyMomentum m u γ 0 p

theorem energyCurrent_apply (m : ℝ) (u : Spacetime → F) (α : Fin 4) (p : Spacetime) :
    energyCurrent m u α p = -∑ γ, η α γ * energyMomentum m u γ 0 p :=
  rfl

/-! ### Symmetry -/

/-- The energy-momentum tensor is symmetric: `T_{αβ} = T_{βα}`. -/
theorem energyMomentum_swap (m : ℝ) (u : Spacetime → F) (α β : Fin 4) :
    energyMomentum m u α β = energyMomentum m u β α := by
  funext p
  rw [energyMomentum_apply, energyMomentum_apply, real_inner_comm (∂[β] u p),
    Matrix.IsSymm.apply transpose_minkowskiMetric β α]

/-! ### Sums against the diagonal metric -/

/-- The off-diagonal entries of `η` vanish. -/
theorem minkowskiMetric_apply_of_ne {α β : Fin 4} (h : α ≠ β) : η α β = 0 :=
  Matrix.diagonal_apply_ne _ h

/-- `η_{αα}² = 1`. -/
theorem minkowskiMetric_self_mul_self (α : Fin 4) : η α α * η α α = 1 := by
  cases α using Fin.cases <;> simp [minkowskiMetric_zero_zero, minkowskiMetric_succ_succ]

/-- `η` is diagonal: `∑ γ, η_{αγ} f_γ = η_{αα} f_α`, for `f` with values in a real vector space. -/
theorem sum_minkowskiMetric_smul {M : Type*} [AddCommMonoid M] [Module ℝ M] (α : Fin 4)
    (f : Fin 4 → M) : ∑ γ, η α γ • f γ = η α α • f α :=
  Fintype.sum_eq_single α fun γ hγ ↦ by rw [minkowskiMetric_apply_of_ne hγ.symm, zero_smul]

/-- `η` is diagonal: `∑ γ, η_{αγ} f_γ = η_{αα} f_α`. -/
theorem sum_minkowskiMetric_mul (α : Fin 4) (f : Fin 4 → ℝ) :
    ∑ γ, η α γ * f γ = η α α * f α :=
  sum_minkowskiMetric_smul α f

/-- Since `η` is diagonal, the energy-momentum tensor is
`T_{αβ} = ⟪∂_α u, ∂_β u⟫ - ½ η_{αβ} (∑ γ, η_{γγ} ‖∂_γ u‖² + m² ‖u‖²)`. -/
theorem energyMomentum_eq (m : ℝ) (u : Spacetime → F) (α β : Fin 4) :
    energyMomentum m u α β = fun q ↦ ⟪∂[α] u q, ∂[β] u q⟫ -
      1 / 2 * η α β * (∑ γ, η γ γ * ‖∂[γ] u q‖ ^ 2 + m ^ 2 * ‖u q‖ ^ 2) := by
  funext q
  simp only [energyMomentum_apply, sum_minkowskiMetric_mul, real_inner_self_eq_norm_sq]

/-! ### The divergence identity -/

/-- The derivative `∂_γ T_{αβ}` at a point where `u` is `C²`. -/
theorem partialDeriv_energyMomentum (m : ℝ) (α β γ : Fin 4) (hu : ContDiffAt ℝ 2 u p) :
    ∂[γ] (energyMomentum m u α β) p =
      ⟪∂[γ] (∂[α] u) p, ∂[β] u p⟫ + ⟪∂[α] u p, ∂[γ] (∂[β] u) p⟫ -
        η α β * (∑ δ, η δ δ * ⟪∂[δ] u p, ∂[γ] (∂[δ] u) p⟫ + m ^ 2 * ⟪u p, ∂[γ] u p⟫) := by
  have hu' : ContDiffAt ℝ (1 + 1) u p := by rwa [one_add_one_eq_two]
  have hD (δ : Fin 4) : DifferentiableAt ℝ (∂[δ] u) p :=
    (contDiffAt_partialDeriv δ hu').differentiableAt one_ne_zero
  have hu1 : DifferentiableAt ℝ u p := hu.differentiableAt two_ne_zero
  have h := ((hD α).hasFDerivAt.inner ℝ (hD β).hasFDerivAt).fun_sub
    (((HasFDerivAt.fun_sum (u := Finset.univ) fun δ _ ↦
      (hD δ).hasFDerivAt.norm_sq.const_mul (η δ δ)).fun_add
      (hu1.hasFDerivAt.norm_sq.const_mul (m ^ 2))).const_mul (1 / 2 * η α β))
  rw [partialDeriv, energyMomentum_eq, derivAlong_eq_of_hasFDerivAt h]
  simp only [sub_apply, smul_apply, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, innerSL_apply_apply, smul_eq_mul,
    ← partialDeriv_apply]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_left_comm _ (2 : ℝ), ← Finset.mul_sum]
  ring

/-- The divergence identity `η^{αγ} ∂_γ T_{αβ} = ⟪□u - m² u, ∂_β u⟫` at a point where `u` is
`C²`. -/
theorem sum_sum_minkowskiMetric_mul_partialDeriv_energyMomentum (m : ℝ) (β : Fin 4)
    (hu : ContDiffAt ℝ 2 u p) :
    ∑ α, ∑ γ, η α γ * ∂[γ] (energyMomentum m u α β) p = ⟪kleinGordon m u p, ∂[β] u p⟫ := by
  have hdiag (f : Fin 4 → ℝ) : ∑ α, η α α * (η α β * f α) = f β := by
    rw [Fintype.sum_eq_single β fun α hα ↦ by
        rw [minkowskiMetric_apply_of_ne hα, zero_mul, mul_zero],
      ← mul_assoc, minkowskiMetric_self_mul_self, one_mul]
  have hsymm : ∑ α, η α α * ⟪∂[α] u p, ∂[α] (∂[β] u) p⟫ =
      ∑ α, η α α * ⟪∂[α] u p, ∂[β] (∂[α] u) p⟫ :=
    Finset.sum_congr rfl fun α _ ↦ by rw [partialDeriv_comm_apply α β hu]
  simp only [sum_minkowskiMetric_mul, partialDeriv_energyMomentum m _ _ _ hu, mul_sub,
    Finset.sum_sub_distrib, hdiag]
  simp only [mul_add, Finset.sum_add_distrib, hsymm, kleinGordon_apply, dAlembertian_apply,
    sum_minkowskiMetric_smul, inner_sub_left, sum_inner, real_inner_smul_left]
  ring

/-! ### The energy current -/

/-- Since `η` is diagonal, `P^α = -η_{αα} T_{α0}`. -/
theorem energyCurrent_eq (m : ℝ) (u : Spacetime → F) (α : Fin 4) :
    energyCurrent m u α = fun q ↦ -η α α * energyMomentum m u α 0 q := by
  funext q
  rw [energyCurrent_apply, sum_minkowskiMetric_mul, neg_mul]

/-- The energy identity `∂_α P^α = -⟪□u - m² u, ∂_t u⟫` at a point where `u` is `C²`. -/
theorem spacetimeDiv_energyCurrent (m : ℝ) (hu : ContDiffAt ℝ 2 u p) :
    spacetimeDiv (energyCurrent m u) p = -⟪kleinGordon m u p, ∂ₜ u p⟫ := by
  rw [← partialDeriv_zero, ← sum_sum_minkowskiMetric_mul_partialDeriv_energyMomentum m 0 hu]
  simp only [spacetimeDiv_apply, energyCurrent_eq, partialDeriv, derivAlong_const_mul,
    sum_minkowskiMetric_mul]
  simp only [neg_mul, Finset.sum_neg_distrib]

/-- The energy current of a solution is divergence free: if `u` is `C²` at `p` and
`□u - m² u = 0` on a neighbourhood of `p`, then `∂_α P^α = 0` at `p`. -/
theorem spacetimeDiv_energyCurrent_eq_zero (m : ℝ) (hu : ContDiffAt ℝ 2 u p)
    (hKG : kleinGordon m u =ᶠ[𝓝 p] 0) : spacetimeDiv (energyCurrent m u) p = 0 := by
  rw [spacetimeDiv_energyCurrent m hu, hKG.eq_of_nhds, Pi.zero_apply, inner_zero_left, neg_zero]

/-! ### Components of the energy current -/

/-- `η^{γδ} ⟪∂_γ u, ∂_δ u⟫ = -‖∂_t u‖² + ∑ a, ‖∂_a u‖²`. -/
theorem sum_sum_minkowskiMetric_mul_inner (u : Spacetime → F) (p : Spacetime) :
    ∑ γ, ∑ δ, η γ δ * ⟪∂[γ] u p, ∂[δ] u p⟫ = -‖∂ₜ u p‖ ^ 2 + ∑ a, ‖∂ₓ[a] u p‖ ^ 2 := by
  simp only [sum_minkowskiMetric_mul, real_inner_self_eq_norm_sq]
  simp [Fin.sum_univ_succ (n := 3), minkowskiMetric_zero_zero, minkowskiMetric_succ_succ]

/-- The energy density `P^0 = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)`. -/
theorem energyCurrent_zero (m : ℝ) (u : Spacetime → F) (p : Spacetime) :
    energyCurrent m u 0 p = 1 / 2 * (‖∂ₜ u p‖ ^ 2 + ∑ a, ‖∂ₓ[a] u p‖ ^ 2 + m ^ 2 * ‖u p‖ ^ 2) := by
  rw [energyCurrent_apply, sum_minkowskiMetric_mul, energyMomentum_apply,
    sum_sum_minkowskiMetric_mul_inner, minkowskiMetric_zero_zero, partialDeriv_zero,
    real_inner_self_eq_norm_sq]
  ring

/-- The energy density is nonnegative: `0 ≤ P^0`. -/
theorem energyCurrent_zero_nonneg (m : ℝ) (u : Spacetime → F) (p : Spacetime) :
    0 ≤ energyCurrent m u 0 p := by
  rw [energyCurrent_zero]
  positivity

/-- The spatial components `P^a = -⟪∂_a u, ∂_t u⟫`, for `a : Fin 3` (the mathematical index is
`a + 1`). -/
theorem energyCurrent_succ (m : ℝ) (u : Spacetime → F) (a : Fin 3) (p : Spacetime) :
    energyCurrent m u a.succ p = -⟪∂ₓ[a] u p, ∂ₜ u p⟫ := by
  rw [energyCurrent_apply, sum_minkowskiMetric_mul, energyMomentum_apply,
    minkowskiMetric_succ_zero, minkowskiMetric_succ_succ, partialDeriv_succ, partialDeriv_zero]
  simp

/-! ### Sanity checks -/

/-- The hypotheses of `spacetimeDiv_energyCurrent_eq_zero` hold for `u = t`, which is smooth and
solves the massless equation `□u = 0`. -/
example (p : Spacetime) : spacetimeDiv (energyCurrent 0 timeCoord) p = 0 :=
  spacetimeDiv_energyCurrent_eq_zero 0 contDiff_timeCoord.contDiffAt
    (Eventually.of_forall fun q ↦ by simp [kleinGordon_apply])

/-- For the real field `u = t` (`F = ℝ`), the energy density is `P^0 = ½ (1 + m² t²)`. -/
example (m : ℝ) :
    energyCurrent m timeCoord 0 = fun p ↦ 1 / 2 * (1 + m ^ 2 * timeCoord p ^ 2) := by
  funext p
  rw [energyCurrent_zero]
  simp

/-- A complex field (`F = ℂ`, with the real inner product `⟪z, w⟫ = Re (conj z * w)`): for
`u = t + i x¹`, the energy density is `P^0 = 1 + m² (t² + (x¹)²) / 2`, and `P^1 = -⟪i, 1⟫ = 0`.
(The Lean index `0` of `spaceCoord` and `Fin.succ 0` of `energyCurrent` is the mathematical
index `1`.) -/
example (m : ℝ) (p : Spacetime) :
    energyCurrent m (fun q ↦ (timeCoord q : ℂ) + spaceCoord 0 q • Complex.I) 0 p =
        1 + m ^ 2 * (timeCoord p ^ 2 + spaceCoord 0 p ^ 2) / 2 ∧
      energyCurrent m (fun q ↦ (timeCoord q : ℂ) + spaceCoord 0 q • Complex.I) (Fin.succ 0) p =
        0 := by
  set u : Spacetime → ℂ := fun q ↦ (timeCoord q : ℂ) + spaceCoord 0 q • Complex.I
  have hu : u = Complex.ofRealCLM ∘ timeCoord +
      ContinuousLinearMap.toSpanSingleton ℝ Complex.I ∘ spaceCoord 0 :=
    rfl
  have hd (V : Spacetime → Spacetime) :
      derivAlong V u p = ((V p).1 : ℂ) + (V p).2 0 • Complex.I := by
    rw [hu, derivAlong_add V ((Complex.ofRealCLM.differentiable.comp differentiable_timeCoord) p)
      (((ContinuousLinearMap.toSpanSingleton ℝ Complex.I).differentiable.comp
        (differentiable_spaceCoord 0)) p),
      derivAlong_comp_left V _ (differentiable_timeCoord p),
      derivAlong_comp_left V _ (differentiable_spaceCoord 0 p), derivAlong_timeCoord,
      derivAlong_spaceCoord]
    rfl
  have ht : ∂ₜ u p = 1 := by
    rw [timeDeriv, hd]
    simp [timeField]
  have hs (a : Fin 3) : ∂ₓ[a] u p = if a = 0 then Complex.I else 0 := by
    rw [spaceDeriv, hd]
    by_cases ha : a = 0
    · subst ha
      simp [spaceField]
    · simp [spaceField, Ne.symm ha, ha]
  constructor
  · rw [energyCurrent_zero, ht]
    simp only [hs, Fin.sum_univ_three]
    simp [u, Complex.sq_norm, Complex.normSq_apply]
    ring
  · rw [energyCurrent_succ, ht, hs]
    simp

/-- The plane wave `u = e^{-imt}` (`F = ℂ`) solves `□u - m² u = 0` for every mass `m`, so the
hypotheses of `spacetimeDiv_energyCurrent_eq_zero` hold for it and its energy current is
divergence free; its energy density is `P^0 = m²`. -/
example (m : ℝ) (p : Spacetime) :
    spacetimeDiv (energyCurrent m fun q ↦ Complex.exp (-(m * timeCoord q) • Complex.I)) p = 0 ∧
      energyCurrent m (fun q ↦ Complex.exp (-(m * timeCoord q) • Complex.I)) 0 p = m ^ 2 := by
  set u : Spacetime → ℂ := fun q ↦ Complex.exp (-(m * timeCoord q) • Complex.I)
  have hd (V : Spacetime → Spacetime) (q : Spacetime) :
      derivAlong V u q = (-(m * (V q).1)) • Complex.I * u q := by
    have h := HasFDerivAt.cexp
      ((((hasFDerivAt_timeCoord q).const_mul m).fun_neg).smul_const Complex.I)
    rw [derivAlong_eq_of_hasFDerivAt h]
    simp [u]
    ring
  have ht : ∂ₜ u = (-m • Complex.I) • u := by
    funext q
    rw [timeDeriv, hd]
    simp [timeField]
  have hs (a : Fin 3) : ∂ₓ[a] u = fun _ ↦ 0 := by
    funext q
    rw [spaceDeriv, hd]
    simp [spaceField]
  have hnorm (q : Spacetime) : ‖u q‖ = 1 := by
    simp only [u, Complex.real_smul]
    exact Complex.norm_exp_ofReal_mul_I _
  have hKG : kleinGordon m u = 0 := by
    funext q
    rw [kleinGordon_apply, dAlembertian_eq, ht, timeDeriv_const_smul_field, ht]
    simp only [hs, spaceDeriv_const, Finset.sum_const_zero, add_zero, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, Complex.real_smul]
    push_cast
    linear_combination (-(m : ℂ) ^ 2 * u q) * Complex.I_sq
  have hu : ContDiffAt ℝ 2 u p := by
    simp only [u]
    fun_prop
  refine ⟨spacetimeDiv_energyCurrent_eq_zero m hu (Eventually.of_forall fun q ↦ congrFun hKG q),
    ?_⟩
  rw [energyCurrent_zero, ht]
  simp [hs, hnorm]
  ring

end VectorFieldMethod.Minkowski
