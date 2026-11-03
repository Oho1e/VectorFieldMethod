/-
Copyright (c) 2026 VectorFieldMethod contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: VectorFieldMethod contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Spatial divergence of a time-dependent vector field

Let `E` be a real normed space ("space"), so that `E × ℝ` is spacetime, with time as the second
coordinate. A time-dependent vector field on `E` is a map `X : E × ℝ → E`. We define its spatial
divergence `spatialDivergence X : E × ℝ → ℝ`: at `p = (x, t)` it is the trace of the derivative at
`x` of the vector field `y ↦ X (y, t)`.

## Main definitions

* `spatialDivergence X p`: the spatial divergence of `X : E × ℝ → E` at `p : E × ℝ`.

## Main statements

* `spatialDivergence_eq_trace_comp_inl`: if `X` is differentiable at `p`, then
  `spatialDivergence X p` is the trace of `fderiv ℝ X p ∘L ContinuousLinearMap.inl ℝ E ℝ`.
* `ContDiff.continuous_spatialDivergence`, `HasCompactSupport.spatialDivergence`: the spatial
  divergence of a compactly supported `C¹` field is continuous with compact support.
* `spatialDivergence_shear`: the chain rule for the spatial divergence of `X` composed with the
  shear `(x, τ) ↦ (x, τ + φ x)`.
* `spatialDivergence_eq_sum_inner`, `spatialDivergence_euclideanSpace`: the spatial divergence in
  an orthonormal basis, and in the coordinates of `EuclideanSpace ℝ (Fin n)`.

## Implementation notes

The definition does not assume that `E` is finite-dimensional. If it is not, `LinearMap.trace` is
identically zero, hence so is `spatialDivergence`; all nontrivial statements assume
`[FiniteDimensional ℝ E]`.
-/

@[expose] public noncomputable section

open Filter Function Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The *spatial divergence* of a time-dependent vector field `X : E × ℝ → E` at `p = (x, t)`:
the trace of the derivative at `x` of the vector field `y ↦ X (y, t)`. -/
def spatialDivergence (X : E × ℝ → E) (p : E × ℝ) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ X (y, p.2)) p.1 : E →ₗ[ℝ] E)

@[simp]
theorem spatialDivergence_zero : spatialDivergence (0 : E × ℝ → E) = 0 := by
  ext p
  simp [spatialDivergence]

/-- The spatial divergence at `p` only depends on the germ of the vector field at `p`. -/
theorem Filter.EventuallyEq.spatialDivergence_eq {X Y : E × ℝ → E} {p : E × ℝ}
    (h : X =ᶠ[𝓝 p] Y) : spatialDivergence X p = spatialDivergence Y p := by
  have h' : (fun y ↦ X (y, p.2)) =ᶠ[𝓝 p.1] fun y ↦ Y (y, p.2) :=
    h.comp_tendsto (Continuous.tendsto' (by fun_prop) _ _ rfl)
  simp only [spatialDivergence, h'.fderiv_eq]

theorem spatialDivergence_of_notMem_tsupport {X : E × ℝ → E} {p : E × ℝ}
    (hp : p ∉ tsupport X) : spatialDivergence X p = 0 := by
  rw [(notMem_tsupport_iff_eventuallyEq.1 hp).spatialDivergence_eq, spatialDivergence_zero,
    Pi.zero_apply]

theorem support_spatialDivergence_subset (X : E × ℝ → E) :
    support (spatialDivergence X) ⊆ tsupport X := fun _ hp ↦
  by_contra fun h ↦ hp (spatialDivergence_of_notMem_tsupport h)

theorem HasCompactSupport.spatialDivergence {X : E × ℝ → E} (hX : HasCompactSupport X) :
    HasCompactSupport (spatialDivergence X) :=
  hX.mono' (support_spatialDivergence_subset X)

/-- If `X` is differentiable at `p`, its spatial divergence at `p` is the trace of the restriction
of `fderiv ℝ X p` to the spatial directions. -/
theorem spatialDivergence_eq_trace_comp_inl {X : E × ℝ → E} {p : E × ℝ}
    (hX : DifferentiableAt ℝ X p) :
    spatialDivergence X p =
      LinearMap.trace ℝ E ((fderiv ℝ X p).comp (ContinuousLinearMap.inl ℝ E ℝ) : E →ₗ[ℝ] E) := by
  exact congrArg (fun L : E →L[ℝ] E ↦ LinearMap.trace ℝ E (L : E →ₗ[ℝ] E))
    (hX.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 p.2)).fderiv

/-- The partial derivative in time of a function on `E × ℝ` which is differentiable at `p`. -/
theorem deriv_comp_prodMk_right {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × ℝ → F} {p : E × ℝ} (hf : DifferentiableAt ℝ f p) :
    deriv (fun t ↦ f (p.1, t)) p.2 = fderiv ℝ f p (0, 1) := by
  have h : HasDerivAt (fun t : ℝ ↦ (p.1, t)) ((0 : E), (1 : ℝ)) p.2 := by
    simpa using (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2).hasDerivAt
  exact (hf.hasFDerivAt.comp_hasDerivAt (x := p.2) (f := fun t : ℝ ↦ (p.1, t)) h).deriv

/-- The partial derivative in time of a `C¹` function on `E × ℝ` is continuous. -/
theorem ContDiff.continuous_deriv_comp_prodMk_right {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E × ℝ → F} (hf : ContDiff ℝ 1 f) :
    Continuous fun p : E × ℝ ↦ deriv (fun t ↦ f (p.1, t)) p.2 := by
  have h : (fun p : E × ℝ ↦ deriv (fun t ↦ f (p.1, t)) p.2) = fun p ↦ fderiv ℝ f p (0, 1) := by
    ext1 p
    exact deriv_comp_prodMk_right (hf.differentiable one_ne_zero p)
  rw [h]
  exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

omit [NormedSpace ℝ E] in
/-- The partial derivative in time of a function with compact support has compact support. -/
theorem HasCompactSupport.deriv_comp_prodMk_right {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E × ℝ → F} (hf : HasCompactSupport f) :
    HasCompactSupport fun p : E × ℝ ↦ deriv (fun t ↦ f (p.1, t)) p.2 := by
  refine hf.mono' fun p hp ↦ by_contra fun h ↦ hp ?_
  have h' : (fun t ↦ f (p.1, t)) =ᶠ[𝓝 p.2] fun _ ↦ 0 :=
    (notMem_tsupport_iff_eventuallyEq.1 h).comp_tendsto (Continuous.tendsto' (by fun_prop) _ _ rfl)
  simp only [h'.deriv_eq, deriv_const]

variable [FiniteDimensional ℝ E]

/-- The spatial divergence of a `C¹` vector field is continuous. -/
theorem ContDiff.continuous_spatialDivergence {X : E × ℝ → E} (hX : ContDiff ℝ 1 X) :
    Continuous (spatialDivergence X) := by
  have h : spatialDivergence X = fun p ↦ ((LinearMap.trace ℝ E).comp
      (ContinuousLinearMap.coeLM ℝ)) ((fderiv ℝ X p).comp (ContinuousLinearMap.inl ℝ E ℝ)) := by
    ext1 p
    exact spatialDivergence_eq_trace_comp_inl (hX.differentiable one_ne_zero p)
  rw [h]
  exact (LinearMap.continuous_of_finiteDimensional _).comp
    ((hX.continuous_fderiv one_ne_zero).clm_comp continuous_const)

/-- **Chain rule for the spatial divergence along a shear.** If `φ : E → ℝ` is differentiable at
`x` and `X` is differentiable at `(x, τ + φ x)`, then the spatial divergence of
`(y, σ) ↦ X (y, σ + φ y)` at `(x, τ)` is the spatial divergence of `X` at `(x, τ + φ x)` plus the
derivative of `φ` at `x` applied to the time derivative of `X` at `(x, τ + φ x)`. -/
theorem spatialDivergence_shear {X : E × ℝ → E} {φ : E → ℝ} {x : E} {τ : ℝ}
    (hφ : DifferentiableAt ℝ φ x) (hX : DifferentiableAt ℝ X (x, τ + φ x)) :
    spatialDivergence (fun q ↦ X (q.1, q.2 + φ q.1)) (x, τ) =
      spatialDivergence X (x, τ + φ x) + fderiv ℝ φ x (deriv (fun t ↦ X (x, t)) (τ + φ x)) := by
  set L := fderiv ℝ X (x, τ + φ x)
  have h₁ : HasFDerivAt (fun y ↦ (y, τ + φ y))
      ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ φ x)) x :=
    (hasFDerivAt_id x).prodMk (hφ.hasFDerivAt.const_add τ)
  have h₂ : L.comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ φ x)) =
      L.comp (ContinuousLinearMap.inl ℝ E ℝ) + (fderiv ℝ φ x).smulRight (L (0, 1)) := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hv : (v, fderiv ℝ φ x v) = (v, 0) + fderiv ℝ φ x v • ((0 : E), (1 : ℝ)) := by
      simp
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_id', id_eq, add_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.smulRight_apply]
    rw [hv, map_add, map_smul]
  have h₃ : fderiv ℝ (fun y ↦ X (y, τ + φ y)) x =
      L.comp ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ φ x)) :=
    (hX.hasFDerivAt.comp x h₁).fderiv
  rw [spatialDivergence_eq_trace_comp_inl hX,
    deriv_comp_prodMk_right (p := (x, τ + φ x)) hX]
  change LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ X (y, τ + φ y)) x : E →ₗ[ℝ] E) = _
  rw [h₃, h₂, ContinuousLinearMap.toLinearMap_add, map_add, ContinuousLinearMap.coe_smulRight,
    LinearMap.trace_smulRight]
  rfl

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

open scoped RealInnerProductSpace

/-- The spatial divergence in an orthonormal basis `b`:
`spatialDivergence X p = ∑ i, ⟪b i, ∂_{b i} X p⟫`. -/
theorem spatialDivergence_eq_sum_inner {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ F)
    (X : F × ℝ → F) (p : F × ℝ) :
    spatialDivergence X p = ∑ i, ⟪b i, fderiv ℝ (fun y ↦ X (y, p.2)) p.1 (b i)⟫ :=
  LinearMap.trace_eq_sum_inner _ b

end InnerProductSpace

/-- The spatial divergence in the coordinates of `EuclideanSpace ℝ (Fin n)`: if `y ↦ X (y, t)` is
differentiable at `x`, then the spatial divergence of `X` at `(x, t)` is the sum over `i` of the
partial derivatives along `EuclideanSpace.single i 1` of the `i`-th components of `X`. -/
theorem spatialDivergence_euclideanSpace {n : ℕ} {X : EuclideanSpace ℝ (Fin n) × ℝ →
    EuclideanSpace ℝ (Fin n)} {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hX : DifferentiableAt ℝ (fun y ↦ X (y, p.2)) p.1) :
    spatialDivergence X p =
      ∑ i, fderiv ℝ (fun y ↦ X (y, p.2) i) p.1 (EuclideanSpace.single i 1) := by
  rw [spatialDivergence_eq_sum_inner (EuclideanSpace.basisFun (Fin n) ℝ)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : HasFDerivAt (fun y ↦ X (y, p.2) i)
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).comp
        (fderiv ℝ (fun y ↦ X (y, p.2)) p.1)) p.1 :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).hasFDerivAt.comp p.1
      hX.hasFDerivAt
  rw [h.fderiv, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simp
