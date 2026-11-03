/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import VectorFieldMethod.Minkowski.Spacetime
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Derivatives along vector fields and coordinate partial derivatives

A vector field on `Spacetime` is represented by its *component field*
`V : Spacetime → Spacetime`, so that `V p = (V⁰(p), (V¹(p), V²(p), V³(p)))` are the components of
`V = V^α ∂_α` at `p`. All first-order operators of this project are instances of the single
operator `derivAlong V u p = Du(p) (V p)`.

## Main definitions

* `derivAlong V u`: the derivative `V u = V^α ∂_α u` of `u : Spacetime → F` along `V`.
* `timeField`, `spaceField a`, `coordField α`: the constant component fields of `∂_t`, `∂_a`,
  `∂_α`.
* `timeDeriv`, `spaceDeriv a`, `partialDeriv α`: the coordinate derivatives `∂_t`, `∂_a`, `∂_α`.

## Main statements

* Linearity: `derivAlong_smul` (real scalars, no hypothesis), `derivAlong_const_smul_field`
  (scalars `c : R` acting on `F`, no hypothesis) and `derivAlong_add` (differentiability at the
  point), and the same for `timeDeriv`, `spaceDeriv`, `partialDeriv`.
* Commutation with continuous linear maps: `derivAlong_comp_left` (`V (T ∘ u) = T (V u)` at a point
  where `u` is differentiable), its eta-expanded form `fun_derivAlong_comp_left`, and
  `derivAlong_comp_left_equiv` (`V (e ∘ u) = e ∘ V u` for a continuous linear equivalence `e`,
  without hypotheses); the same for `timeDeriv`, `spaceDeriv`, `partialDeriv`.
* Smoothness: `contDiff_partialDeriv` (`C^{n+1} → C^n`) and `contDiff_infty_partialDeriv`.
* Symmetry of second derivatives: `partialDeriv_comm_apply` (for `u` that is `C²` at the point)
  and `partialDeriv_comm`.
* Derivatives of the coordinates: `timeDeriv_timeCoord`, `spaceDeriv_spaceCoord`, etc.

## Notation

Scoped in `VectorFieldMethod.Minkowski`: `∂ₜ` for `timeDeriv`, `∂ₓ[a]` for `spaceDeriv a`, and
`∂[α]` for `partialDeriv α`.

## Implementation notes

The operators are plain functions `(Spacetime → F) → Spacetime → F` built from `fderiv`, for an
arbitrary real normed space `F` (the type of values, an implicit argument inferred from `u`): real
fields have `F = ℝ`, complex fields `F = ℂ`. The coordinate functions are real-valued. Since
`fderiv` is `0` at points of non-differentiability, additivity needs differentiability
hypotheses, while homogeneity under constant scalars does not.

`F` is inferred from `u`. A statement without a function argument, such as
`partialDeriv_zero : ∂[0] = ∂ₜ`, carries a type ascription to fix `F`, and a function whose values
are only numerals, such as `fun _ ↦ 1`, needs a type ascription `(1 : ℝ)`.
-/

@[expose] public noncomputable section

open Filter
open scoped ContDiff Topology

namespace VectorFieldMethod.Minkowski

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {R : Type*} [DivisionSemiring R] [Module R F] [SMulCommClass ℝ R F]
  [ContinuousConstSMul R F]
variable {V : Spacetime → Spacetime} {u v : Spacetime → F} {p : Spacetime} {n : ℕ∞ω}

/-! ### Smoothness of the coordinate functions -/

@[fun_prop]
theorem contDiff_timeCoord : ContDiff ℝ n timeCoord :=
  contDiff_fst

@[fun_prop]
theorem contDiff_spaceCoord (a : Fin 3) : ContDiff ℝ n (spaceCoord a) :=
  (contDiff_piLp_apply 2).comp contDiff_snd

@[fun_prop]
theorem differentiable_timeCoord : Differentiable ℝ timeCoord :=
  contDiff_timeCoord.differentiable one_ne_zero

@[fun_prop]
theorem differentiable_spaceCoord (a : Fin 3) : Differentiable ℝ (spaceCoord a) :=
  (contDiff_spaceCoord a).differentiable one_ne_zero

theorem hasFDerivAt_timeCoord (p : Spacetime) :
    HasFDerivAt timeCoord (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3))) p :=
  hasFDerivAt_fst

theorem hasFDerivAt_spaceCoord (a : Fin 3) (p : Spacetime) :
    HasFDerivAt (spaceCoord a)
      ((PiLp.proj 2 (fun _ : Fin 3 ↦ ℝ) a).comp
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))) p := by
  have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 p.2 a).comp p (hasFDerivAt_snd (p := p))
  exact h

/-! ### The derivative along a component field -/

/-- The derivative of `u` along the vector field with component field `V`:
`(V u)(p) = V^α(p) ∂_α u(p) = Du(p) (V p)`. -/
def derivAlong (V : Spacetime → Spacetime) (u : Spacetime → F) : Spacetime → F :=
  fun p ↦ fderiv ℝ u p (V p)

theorem derivAlong_apply (V : Spacetime → Spacetime) (u : Spacetime → F) (p : Spacetime) :
    derivAlong V u p = fderiv ℝ u p (V p) :=
  rfl

theorem derivAlong_eq_of_hasFDerivAt {L : Spacetime →L[ℝ] F} (h : HasFDerivAt u L p) :
    derivAlong V u p = L (V p) := by
  rw [derivAlong_apply, h.fderiv]

/-- `V (c u) = c (V u)` for `c : ℝ`, without any differentiability assumption. -/
theorem derivAlong_smul (V : Spacetime → Spacetime) (c : ℝ) (u : Spacetime → F) :
    derivAlong V (c • u) = c • derivAlong V u := by
  funext p
  simp [derivAlong_apply, fderiv_const_smul_field]

/-- `V (c u) = c (V u)` for a scalar `c : R` acting on `F` (for instance `c : ℂ` when `F = ℂ`),
without any differentiability assumption. -/
theorem derivAlong_const_smul_field (V : Spacetime → Spacetime) (c : R) (u : Spacetime → F) :
    derivAlong V (c • u) = c • derivAlong V u := by
  funext p
  simp [derivAlong_apply, fderiv_const_smul_field]

/-- `V (c u) = c (V u)` for a real-valued `u`, with the product written pointwise. -/
theorem derivAlong_const_mul (V : Spacetime → Spacetime) (c : ℝ) (u : Spacetime → ℝ) :
    derivAlong V (fun q ↦ c * u q) = fun q ↦ c * derivAlong V u q :=
  derivAlong_smul V c u

/-- `V (u + v) = V u + V v` at a point where `u` and `v` are differentiable. -/
theorem derivAlong_add (V : Spacetime → Spacetime) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    derivAlong V (u + v) p = derivAlong V u p + derivAlong V v p := by
  simp [derivAlong_apply, fderiv_add hu hv]

@[simp]
theorem derivAlong_const (V : Spacetime → Spacetime) (c : F) :
    derivAlong V (fun _ ↦ c) = fun _ ↦ 0 := by
  funext p
  simp [derivAlong_apply]

/-- `V u` at `p` only depends on `u` near `p`. -/
theorem derivAlong_congr_of_eventuallyEq (V : Spacetime → Spacetime) (h : u =ᶠ[𝓝 p] v) :
    derivAlong V u p = derivAlong V v p := by
  rw [derivAlong_apply, derivAlong_apply, h.fderiv_eq]

@[simp]
theorem derivAlong_timeCoord (V : Spacetime → Spacetime) :
    derivAlong V timeCoord = fun p ↦ (V p).1 := by
  funext p
  rw [derivAlong_eq_of_hasFDerivAt (hasFDerivAt_timeCoord p)]
  rfl

@[simp]
theorem derivAlong_spaceCoord (V : Spacetime → Spacetime) (a : Fin 3) :
    derivAlong V (spaceCoord a) = fun p ↦ (V p).2 a := by
  funext p
  rw [derivAlong_eq_of_hasFDerivAt (hasFDerivAt_spaceCoord a p)]
  rfl

theorem contDiffAt_derivAlong (hV : ContDiffAt ℝ n V p) (hu : ContDiffAt ℝ (n + 1) u p) :
    ContDiffAt ℝ n (derivAlong V u) p :=
  (hu.fderiv_right le_rfl).clm_apply hV

/-- If `V` is `C^n` and `u` is `C^{n+1}`, then `V u` is `C^n`. -/
theorem contDiff_derivAlong (hV : ContDiff ℝ n V) (hu : ContDiff ℝ (n + 1) u) :
    ContDiff ℝ n (derivAlong V u) :=
  (hu.fderiv_right le_rfl).clm_apply hV

/-- `V (T ∘ u) = T (V u)` for a continuous linear map `T`, at a point where `u` is
differentiable. The eta-expanded form `fun_derivAlong_comp_left` is about
`fun q ↦ T (u q)`. -/
@[to_fun]
theorem derivAlong_comp_left (V : Spacetime → Spacetime) (T : F →L[ℝ] G)
    (hu : DifferentiableAt ℝ u p) : derivAlong V (T ∘ u) p = T (derivAlong V u p) := by
  rw [derivAlong_eq_of_hasFDerivAt (T.hasFDerivAt.comp p hu.hasFDerivAt)]
  rfl

/-- `V (e ∘ u) = e ∘ V u` for a continuous linear equivalence `e`, without any differentiability
assumption: `e ∘ u` is differentiable exactly where `u` is. -/
@[to_fun]
theorem derivAlong_comp_left_equiv (V : Spacetime → Spacetime) (e : F ≃L[ℝ] G)
    (u : Spacetime → F) : derivAlong V (e ∘ u) = e ∘ derivAlong V u := by
  funext p
  rw [derivAlong_apply, e.comp_fderiv]
  rfl

/-- For a constant component field `W ≡ w`, the second derivative `V (W u)` at `p` is the second
Fréchet derivative `D²u(p) (V p) w`. -/
theorem derivAlong_derivAlong_of_const {W : Spacetime → Spacetime} {w : Spacetime}
    (hW : ∀ q, W q = w) (hu : DifferentiableAt ℝ (fderiv ℝ u) p) :
    derivAlong V (derivAlong W u) p = fderiv ℝ (fderiv ℝ u) p (V p) w := by
  have hWu : derivAlong W u = fun q ↦ fderiv ℝ u q w := by
    funext q
    rw [derivAlong_apply, hW q]
  rw [derivAlong_apply, hWu, fderiv_clm_apply hu (differentiableAt_const w)]
  simp

/-! ### Coordinate vector fields and partial derivatives -/

/-- The component field of `∂_t`: constantly `(1, 0)`. -/
def timeField : Spacetime → Spacetime :=
  fun _ ↦ (1, 0)

/-- The component field of `∂_a` for `a : Fin 3`: constantly `(0, e_a)`. -/
def spaceField (a : Fin 3) : Spacetime → Spacetime :=
  fun _ ↦ (0, EuclideanSpace.single a 1)

/-- The component field of `∂_α` for `α : Fin 4`: `timeField` for `α = 0` and `spaceField a`
for `α = Fin.succ a`. -/
def coordField (α : Fin 4) : Spacetime → Spacetime :=
  Fin.cases (motive := fun _ ↦ Spacetime → Spacetime) timeField spaceField α

theorem coordField_zero : coordField 0 = timeField :=
  rfl

theorem coordField_succ (a : Fin 3) : coordField a.succ = spaceField a :=
  rfl

/-- The coordinate fields are constant. -/
theorem coordField_eq_const (α : Fin 4) (p : Spacetime) : coordField α p = coordField α 0 := by
  cases α using Fin.cases <;> rfl

/-- The time derivative `∂_t u`. -/
def timeDeriv : (Spacetime → F) → Spacetime → F :=
  derivAlong timeField

/-- The spatial derivative `∂_a u` for `a : Fin 3` (the mathematical index is `a + 1`). -/
def spaceDeriv (a : Fin 3) : (Spacetime → F) → Spacetime → F :=
  derivAlong (spaceField a)

/-- The spacetime derivative `∂_α u` for `α : Fin 4`, with `∂_0 = ∂_t` and `∂_{a+1} = ∂_a`. -/
def partialDeriv (α : Fin 4) : (Spacetime → F) → Spacetime → F :=
  derivAlong (coordField α)

@[inherit_doc] scoped notation "∂ₜ" => timeDeriv
@[inherit_doc] scoped notation "∂ₓ[" a "]" => spaceDeriv a
@[inherit_doc] scoped notation "∂[" α "]" => partialDeriv α

theorem timeDeriv_apply (u : Spacetime → F) (p : Spacetime) :
    ∂ₜ u p = fderiv ℝ u p (1, 0) :=
  rfl

theorem spaceDeriv_apply (a : Fin 3) (u : Spacetime → F) (p : Spacetime) :
    ∂ₓ[a] u p = fderiv ℝ u p (0, EuclideanSpace.single a 1) :=
  rfl

theorem partialDeriv_apply (α : Fin 4) (u : Spacetime → F) (p : Spacetime) :
    ∂[α] u p = fderiv ℝ u p (coordField α p) :=
  rfl

@[simp]
theorem partialDeriv_zero : (∂[0] : (Spacetime → F) → Spacetime → F) = ∂ₜ :=
  rfl

@[simp]
theorem partialDeriv_succ (a : Fin 3) : (∂[a.succ] : (Spacetime → F) → Spacetime → F) = ∂ₓ[a] :=
  rfl

@[simp]
theorem partialDeriv_one : (∂[1] : (Spacetime → F) → Spacetime → F) = ∂ₓ[0] :=
  rfl

@[simp]
theorem partialDeriv_two : (∂[2] : (Spacetime → F) → Spacetime → F) = ∂ₓ[1] :=
  rfl

@[simp]
theorem partialDeriv_three : (∂[3] : (Spacetime → F) → Spacetime → F) = ∂ₓ[2] :=
  rfl

/-! #### Linearity -/

theorem timeDeriv_smul (c : ℝ) (u : Spacetime → F) : ∂ₜ (c • u) = c • ∂ₜ u :=
  derivAlong_smul _ c u

theorem spaceDeriv_smul (a : Fin 3) (c : ℝ) (u : Spacetime → F) : ∂ₓ[a] (c • u) = c • ∂ₓ[a] u :=
  derivAlong_smul _ c u

theorem partialDeriv_smul (α : Fin 4) (c : ℝ) (u : Spacetime → F) :
    ∂[α] (c • u) = c • ∂[α] u :=
  derivAlong_smul _ c u

theorem timeDeriv_const_smul_field (c : R) (u : Spacetime → F) : ∂ₜ (c • u) = c • ∂ₜ u :=
  derivAlong_const_smul_field _ c u

theorem spaceDeriv_const_smul_field (a : Fin 3) (c : R) (u : Spacetime → F) :
    ∂ₓ[a] (c • u) = c • ∂ₓ[a] u :=
  derivAlong_const_smul_field _ c u

theorem partialDeriv_const_smul_field (α : Fin 4) (c : R) (u : Spacetime → F) :
    ∂[α] (c • u) = c • ∂[α] u :=
  derivAlong_const_smul_field _ c u

theorem timeDeriv_add (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    ∂ₜ (u + v) p = ∂ₜ u p + ∂ₜ v p :=
  derivAlong_add _ hu hv

theorem spaceDeriv_add (a : Fin 3) (hu : DifferentiableAt ℝ u p) (hv : DifferentiableAt ℝ v p) :
    ∂ₓ[a] (u + v) p = ∂ₓ[a] u p + ∂ₓ[a] v p :=
  derivAlong_add _ hu hv

theorem partialDeriv_add (α : Fin 4) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) : ∂[α] (u + v) p = ∂[α] u p + ∂[α] v p :=
  derivAlong_add _ hu hv

/-! #### Commutation with continuous linear maps -/

@[to_fun]
theorem timeDeriv_comp_left (T : F →L[ℝ] G) (hu : DifferentiableAt ℝ u p) :
    ∂ₜ (T ∘ u) p = T (∂ₜ u p) :=
  derivAlong_comp_left _ T hu

@[to_fun]
theorem spaceDeriv_comp_left (a : Fin 3) (T : F →L[ℝ] G) (hu : DifferentiableAt ℝ u p) :
    ∂ₓ[a] (T ∘ u) p = T (∂ₓ[a] u p) :=
  derivAlong_comp_left _ T hu

@[to_fun]
theorem partialDeriv_comp_left (α : Fin 4) (T : F →L[ℝ] G) (hu : DifferentiableAt ℝ u p) :
    ∂[α] (T ∘ u) p = T (∂[α] u p) :=
  derivAlong_comp_left _ T hu

@[to_fun]
theorem timeDeriv_comp_left_equiv (e : F ≃L[ℝ] G) (u : Spacetime → F) :
    ∂ₜ (e ∘ u) = e ∘ ∂ₜ u :=
  derivAlong_comp_left_equiv _ e u

@[to_fun]
theorem spaceDeriv_comp_left_equiv (a : Fin 3) (e : F ≃L[ℝ] G) (u : Spacetime → F) :
    ∂ₓ[a] (e ∘ u) = e ∘ ∂ₓ[a] u :=
  derivAlong_comp_left_equiv _ e u

@[to_fun]
theorem partialDeriv_comp_left_equiv (α : Fin 4) (e : F ≃L[ℝ] G) (u : Spacetime → F) :
    ∂[α] (e ∘ u) = e ∘ ∂[α] u :=
  derivAlong_comp_left_equiv _ e u

/-! #### Values on constants and coordinates -/

@[simp]
theorem timeDeriv_const (c : F) : ∂ₜ (fun _ ↦ c) = fun _ ↦ 0 :=
  derivAlong_const _ c

@[simp]
theorem spaceDeriv_const (a : Fin 3) (c : F) : ∂ₓ[a] (fun _ ↦ c) = fun _ ↦ 0 :=
  derivAlong_const _ c

@[simp]
theorem partialDeriv_const (α : Fin 4) (c : F) : ∂[α] (fun _ ↦ c) = fun _ ↦ 0 :=
  derivAlong_const _ c

/-- `∂_t t = 1`. -/
@[simp]
theorem timeDeriv_timeCoord : ∂ₜ timeCoord = fun _ ↦ 1 :=
  derivAlong_timeCoord _

/-- `∂_t x_b = 0`. -/
@[simp]
theorem timeDeriv_spaceCoord (b : Fin 3) : ∂ₜ (spaceCoord b) = fun _ ↦ 0 :=
  derivAlong_spaceCoord _ b

/-- `∂_a t = 0`. -/
@[simp]
theorem spaceDeriv_timeCoord (a : Fin 3) : ∂ₓ[a] timeCoord = fun _ ↦ 0 :=
  derivAlong_timeCoord _

/-- `∂_a x_b = δ_ab`. -/
@[simp]
theorem spaceDeriv_spaceCoord (a b : Fin 3) :
    ∂ₓ[a] (spaceCoord b) = fun _ ↦ if a = b then 1 else 0 := by
  rw [spaceDeriv, derivAlong_spaceCoord]
  funext p
  simp [spaceField, PiLp.single_apply, eq_comm]

/-! #### Smoothness -/

theorem contDiff_timeField : ContDiff ℝ n timeField :=
  contDiff_const

theorem contDiff_spaceField (a : Fin 3) : ContDiff ℝ n (spaceField a) :=
  contDiff_const

theorem contDiff_coordField (α : Fin 4) : ContDiff ℝ n (coordField α) := by
  cases α using Fin.cases
  · exact contDiff_timeField
  · exact contDiff_spaceField _

/-- If `u` is `C^{n+1}`, then `∂_t u` is `C^n`. -/
theorem contDiff_timeDeriv (hu : ContDiff ℝ (n + 1) u) : ContDiff ℝ n (∂ₜ u) :=
  contDiff_derivAlong contDiff_timeField hu

/-- If `u` is `C^{n+1}`, then `∂_a u` is `C^n`. -/
theorem contDiff_spaceDeriv (a : Fin 3) (hu : ContDiff ℝ (n + 1) u) : ContDiff ℝ n (∂ₓ[a] u) :=
  contDiff_derivAlong (contDiff_spaceField a) hu

/-- If `u` is `C^{n+1}`, then `∂_α u` is `C^n`. -/
theorem contDiff_partialDeriv (α : Fin 4) (hu : ContDiff ℝ (n + 1) u) :
    ContDiff ℝ n (∂[α] u) :=
  contDiff_derivAlong (contDiff_coordField α) hu

/-- Pointwise version of `contDiff_partialDeriv`. -/
theorem contDiffAt_partialDeriv (α : Fin 4) (hu : ContDiffAt ℝ (n + 1) u p) :
    ContDiffAt ℝ n (∂[α] u) p :=
  contDiffAt_derivAlong (contDiff_coordField α).contDiffAt hu

theorem contDiff_infty_timeDeriv (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (∂ₜ u) :=
  contDiff_timeDeriv hu

theorem contDiff_infty_spaceDeriv (a : Fin 3) (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (∂ₓ[a] u) :=
  contDiff_spaceDeriv a hu

theorem contDiff_infty_partialDeriv (α : Fin 4) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (∂[α] u) :=
  contDiff_partialDeriv α hu

/-! #### Symmetry of second derivatives -/

/-- `∂_α ∂_β u (p) = D²u(p) e_α e_β`, where `e_α` is the value of `coordField α`. -/
theorem partialDeriv_partialDeriv_apply (α β : Fin 4) (hu : DifferentiableAt ℝ (fderiv ℝ u) p) :
    ∂[α] (∂[β] u) p = fderiv ℝ (fderiv ℝ u) p (coordField α 0) (coordField β 0) := by
  rw [partialDeriv, partialDeriv, derivAlong_derivAlong_of_const (coordField_eq_const β) hu,
    coordField_eq_const α p]

/-- `∂_α ∂_β u = ∂_β ∂_α u` at a point where `u` is `C²`. -/
theorem partialDeriv_comm_apply (α β : Fin 4) (hu : ContDiffAt ℝ 2 u p) :
    ∂[α] (∂[β] u) p = ∂[β] (∂[α] u) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) p :=
    (hu.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero
  rw [partialDeriv_partialDeriv_apply α β hd, partialDeriv_partialDeriv_apply β α hd]
  exact hu.isSymmSndFDerivAt (by simp) _ _

/-- `∂_α ∂_β u = ∂_β ∂_α u` for `u` of class `C²`. -/
theorem partialDeriv_comm (α β : Fin 4) (hu : ContDiff ℝ 2 u) :
    ∂[α] (∂[β] u) = ∂[β] (∂[α] u) :=
  funext fun _ ↦ partialDeriv_comm_apply α β hu.contDiffAt

end VectorFieldMethod.Minkowski
