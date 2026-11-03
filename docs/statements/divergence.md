# Divergence theorem on regions bounded by graphs: statements

Layer: `VectorFieldMethod/ForMathlib/` (main files `Analysis/Calculus/SpatialDivergence.lean`,
`MeasureTheory/Integral/DivergenceTheoremHypograph.lean`,
`MeasureTheory/Integral/DivergenceTheoremLocal.lean`,
`MeasureTheory/Integral/DivergenceTheoremHyperboloid.lean`; the other files of the directory
contain auxiliary lemmas). The declarations are in Mathlib-style namespaces, not in
`VectorFieldMethod`: `spatialDivergence` and `spatialDivergence_euclideanSpace` are in the root
namespace, the integral theorems in `MeasureTheory`. The links below point to commit
[`3fac872`](https://github.com/Oho1e/VectorFieldMethod/tree/3fac872e390477a31fdbf56d88d4cc6989748e1e)
of `main`. How to read the entries: [`README.md`](README.md).

## Coordinates: time is the second coordinate here

In this layer spacetime is $`E \times \mathbb{R}`$: a point is $`p = (x, t)`$ with the spatial
point $`x \in E`$ **first** and the time $`t`$ **second** (`p.1 = x`, `p.2 = t`). This differs from
the Minkowski layer, where `Spacetime = ℝ × EuclideanSpace ℝ (Fin 3)` has time first. The theorem
`MeasureTheory.integral_divergence_hypograph_swap` (below) restates the main theorem on
$`\mathbb{R} \times E`$, time first, and is the bridge between the two conventions: with
$`E = \mathbb{R}^3`$ (`EuclideanSpace ℝ (Fin 3)`) and $`\mu`$ = Lebesgue measure (`volume`),
$`\mathbb{R} \times E`$ is `Spacetime` and `volume.prod volume` is Lebesgue measure on it. The other
theorems of this file exist only in the time-second form at this commit.

**Notation in the Math lines below.** $`E`$ is a real normed space ("space"), $`\mu`$ a measure on
$`E`$, $`\mathcal{L}^1`$ Lebesgue measure on $`\mathbb{R}`$. A vector field on spacetime is given by
its time component $`X_0 : E \times \mathbb{R} \to \mathbb{R}`$ and its spatial component
$`X : E \times \mathbb{R} \to E`$. We write

- $`\partial_t X_0(x, t)`$ for the derivative of $`s \mapsto X_0(x, s)`$ at $`s = t`$ (Lean
  `deriv (fun s ↦ X₀ (x, s)) t`, or `deriv (fun t ↦ X₀ (p.1, t)) p.2` at $`p = (x, t)`$);
- $`\operatorname{div}_x X(x, t)`$ for the spatial divergence (`spatialDivergence X (x, t)`,
  defined below);
- $`C^1_c`$ for $`C^1`$ functions with compact (closed) support, and
  $`\operatorname{supp} f = \overline{\{f \neq 0\}}`$ (Lean `tsupport f`).

## Context

These `variable` lines supply the ambient hypotheses of the theorems below them.

[`SpatialDivergence.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/Analysis/Calculus/SpatialDivergence.lean#L49)
($`E`$ is a real normed space; `F` is not used by the entries below):

```lean
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]
```

[`DivergenceTheoremHypograph.lean`, section `NormedSpace`](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremHypograph.lean#L100)
($`E`$ a finite-dimensional real normed space with its Borel $`\sigma`$-algebra, $`\mu`$ an
additive Haar measure on $`E`$), followed by the `variable` line 225 of the same file:

```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {φ : E → ℝ} {X₀ : E × ℝ → ℝ} {X : E × ℝ → E}

variable {φ₁ φ₂ : E → ℝ}
```

[`DivergenceTheoremHypograph.lean`, section `InnerProductSpace`](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremHypograph.lean#L319)
(the same, with $`E`$ a real inner product space):

```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {φ : E → ℝ} {X₀ : E × ℝ → ℝ} {X : E × ℝ → E}
```

[`DivergenceTheoremLocal.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremLocal.lean#L75)
(as in the `NormedSpace` section):

```lean
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {φ₁ φ₂ : E → ℝ} {X₀ : E × ℝ → ℝ} {X : E × ℝ → E}
```

[`DivergenceTheoremHyperboloid.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremHyperboloid.lean#L38)
(lines 38 and 57–58: $`E`$ a finite-dimensional real inner product space with its Borel
$`\sigma`$-algebra, $`\mu`$ an additive Haar measure):

```lean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {X₀ : E × ℝ → ℝ} {X : E × ℝ → E}
```

## Definition

### Spatial divergence

- **Math.** Let $`E`$ be a real normed space and $`X : E \times \mathbb{R} \to E`$. For
  $`p = (x, t)`$,
  ```math
  \operatorname{div}_x X(x, t) = \operatorname{tr} \big( D[X(\cdot, t)](x) \big),
  ```
  the trace of the derivative at $`x`$ of the map $`y \mapsto X(y, t)`$.
- **Hypotheses.** $`E`$ is a real normed space (from the `variable` line); no hypothesis on
  $`X`$.
- **Lean.** `spatialDivergence` (root namespace), [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/Analysis/Calculus/SpatialDivergence.lean#L84)

```lean
def spatialDivergence (X : E × ℝ → E) (p : E × ℝ) : ℝ :=
  LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ X (y, p.2)) p.1 : E →ₗ[ℝ] E)
```

- **Notes.** Junk values: if $`y \mapsto X(y, t)`$ is not differentiable at $`x`$, the derivative
  is $`0`$ and so is $`\operatorname{div}_x X(x, t)`$; if $`E`$ is infinite-dimensional, the trace
  and hence `spatialDivergence` are identically $`0`$ (all theorems below assume
  `[FiniteDimensional ℝ E]`). Only the spatial derivative enters, not the time derivative. In
  coordinates on $`\mathbb{R}^n`$ it is $`\sum_i \partial X^i / \partial x^i`$
  (`spatialDivergence_euclideanSpace`).

## Main theorems

### Divergence theorem below a graph

- **Math.** Let $`E`$ be a finite-dimensional real normed space with its Borel $`\sigma`$-algebra
  and $`\mu`$ an additive Haar measure on $`E`$. Let $`\varphi \in C^1(E; \mathbb{R})`$,
  $`X_0 \in C^1_c(E \times \mathbb{R}; \mathbb{R})`$ and $`X \in C^1_c(E \times \mathbb{R}; E)`$.
  Then
  ```math
  \int_{\{(x, t) \,:\, t \le \varphi(x)\}} \big( \partial_t X_0 + \operatorname{div}_x X \big)\, d(\mu \otimes \mathcal{L}^1)
  = \int_E \Big( X_0\big(x, \varphi(x)\big) - D\varphi(x)\, X\big(x, \varphi(x)\big) \Big)\, d\mu(x).
  ```
- **Hypotheses.** $`E`$ finite-dimensional real normed space, Borel; $`\mu`$ additive Haar;
  $`\varphi`$ is $`C^1`$; $`X_0`$ and $`X`$ are $`C^1`$ with compact support.
- **Lean.** `MeasureTheory.integral_divergence_hypograph`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremHypograph.lean#L109)

```lean
theorem integral_divergence_hypograph (hφ : ContDiff ℝ 1 φ) (hX₀ : ContDiff ℝ 1 X₀)
    (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ p in {p : E × ℝ | p.2 ≤ φ p.1},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      ∫ x, (X₀ (x, φ x) - fderiv ℝ φ x (X (x, φ x))) ∂μ
```

- **Notes.** The right-hand side is the flux of $`(X_0, X)`$ through the graph of $`\varphi`$,
  written in the parametrization $`x \mapsto (x, \varphi(x))`$: no normal vector and no surface
  measure appear. For $`E = \mathbb{R}^n`$ with Lebesgue measure it is the usual
  $`\int_{\partial\Omega} (X_0, X) \cdot \nu\, dS`$ with outer normal
  $`\nu = (-\nabla\varphi, 1)/\sqrt{1 + \lvert\nabla\varphi\rvert^2}`$ (see also the gradient
  version below). Both integrands are continuous with compact support, so both integrals are
  genuine (not junk zeros). The same $`\mu`$ appears on both sides, so the normalization of the Haar
  measure does not matter.

### Divergence theorem between two graphs (iterated, oriented)

- **Math.** Let $`E, \mu`$ be as above, $`\varphi_1, \varphi_2 \in C^1(E; \mathbb{R})`$ (in any
  order), $`X_0 \in C^1_c(E \times \mathbb{R}; \mathbb{R})`$, $`X \in C^1_c(E \times \mathbb{R}; E)`$.
  Then
  ```math
  \int_E \left( \int_{\varphi_1(x)}^{\varphi_2(x)} \big( \partial_t X_0 + \operatorname{div}_x X \big)(x, t)\, dt \right) d\mu(x)
  = \Phi_{\varphi_2} - \Phi_{\varphi_1},
  ```
  where the inner integral is oriented ($`\int_a^b = -\int_b^a`$) and
  ```math
  \Phi_{\varphi_i} = \int_E \Big( X_0\big(x, \varphi_i(x)\big) - D\varphi_i(x)\, X\big(x, \varphi_i(x)\big) \Big)\, d\mu(x).
  ```
- **Hypotheses.** $`E`$ finite-dimensional real normed space, Borel; $`\mu`$ additive Haar;
  $`\varphi_1, \varphi_2`$ are $`C^1`$; $`X_0, X`$ are $`C^1`$ with compact support. No order
  between $`\varphi_1`$ and $`\varphi_2`$.
- **Lean.** `MeasureTheory.integral_intervalIntegral_divergence`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremHypograph.lean#L231)

```lean
theorem integral_intervalIntegral_divergence (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂)
    (hX₀ : ContDiff ℝ 1 X₀) (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) :
    ∫ x, (∫ t in φ₁ x..φ₂ x, (deriv (fun s ↦ X₀ (x, s)) t + spatialDivergence X (x, t))) ∂μ =
      (∫ x, (X₀ (x, φ₂ x) - fderiv ℝ φ₂ x (X (x, φ₂ x))) ∂μ) -
        ∫ x, (X₀ (x, φ₁ x) - fderiv ℝ φ₁ x (X (x, φ₁ x))) ∂μ
```

- **Notes.** `∫ t in a..b` is the oriented integral for Lebesgue measure (see the README). Where
  $`\varphi_1(x) > \varphi_2(x)`$ the inner integral counts negatively.

### Divergence theorem on the closed region between two graphs

- **Math.** Let $`E, \mu, X_0, X`$ be as above and $`\varphi_1, \varphi_2 \in C^1(E; \mathbb{R})`$
  with $`\varphi_1(x) \le \varphi_2(x)`$ for all $`x`$. Then
  ```math
  \int_{\{(x, t) \,:\, \varphi_1(x) \le t \le \varphi_2(x)\}} \big( \partial_t X_0 + \operatorname{div}_x X \big)\, d(\mu \otimes \mathcal{L}^1)
  = \Phi_{\varphi_2} - \Phi_{\varphi_1},
  ```
  with $`\Phi_{\varphi_i}`$ as in the previous entry.
- **Hypotheses.** $`E`$ finite-dimensional real normed space, Borel; $`\mu`$ additive Haar;
  $`\varphi_1, \varphi_2`$ are $`C^1`$ and $`\varphi_1 \le \varphi_2`$ pointwise; $`X_0, X`$ are
  $`C^1`$ with compact support.
- **Lean.** `MeasureTheory.integral_divergence_region_between_cc`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremHypograph.lean#L257)

```lean
theorem integral_divergence_region_between_cc (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂)
    (hφ : φ₁ ≤ φ₂) (hX₀ : ContDiff ℝ 1 X₀) (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) :
    ∫ p in {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      (∫ x, (X₀ (x, φ₂ x) - fderiv ℝ φ₂ x (X (x, φ₂ x))) ∂μ) -
        ∫ x, (X₀ (x, φ₁ x) - fderiv ℝ φ₁ x (X (x, φ₁ x))) ∂μ
```

- **Notes.** `hφ : φ₁ ≤ φ₂` is the pointwise order of functions. Without it the region would be
  empty over the set where $`\varphi_1 > \varphi_2`$ while the right-hand side would still count it.

### Divergence theorem on the open region between two graphs

- **Math.** Under the hypotheses of the previous entry,
  ```math
  \int_{\{(x, t) \,:\, \varphi_1(x) < t < \varphi_2(x)\}} \big( \partial_t X_0 + \operatorname{div}_x X \big)\, d(\mu \otimes \mathcal{L}^1)
  = \Phi_{\varphi_2} - \Phi_{\varphi_1}.
  ```
- **Hypotheses.** $`E`$ finite-dimensional real normed space, Borel; $`\mu`$ additive Haar;
  $`\varphi_1, \varphi_2`$ are $`C^1`$ and $`\varphi_1 \le \varphi_2`$ pointwise; $`X_0, X`$ are
  $`C^1`$ with compact support.
- **Lean.** `MeasureTheory.integral_divergence_regionBetween`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremHypograph.lean#L279)

```lean
theorem integral_divergence_regionBetween (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂)
    (hφ : φ₁ ≤ φ₂) (hX₀ : ContDiff ℝ 1 X₀) (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X)
    (hXc : HasCompactSupport X) :
    ∫ p in regionBetween φ₁ φ₂ univ,
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      (∫ x, (X₀ (x, φ₂ x) - fderiv ℝ φ₂ x (X (x, φ₂ x))) ∂μ) -
        ∫ x, (X₀ (x, φ₁ x) - fderiv ℝ φ₁ x (X (x, φ₁ x))) ∂μ
```

- **Notes.** Mathlib's `regionBetween φ₁ φ₂ univ` is
  $`\{(x, t) : x \in E,\ \varphi_1(x) < t < \varphi_2(x)\}`$. The open and closed regions differ by
  the two graphs, which are null sets.

### Divergence theorem below a graph, gradient form

- **Math.** Let $`E`$ be a finite-dimensional real **inner product** space with its Borel
  $`\sigma`$-algebra, $`\mu`$ an additive Haar measure, $`\varphi \in C^1(E; \mathbb{R})`$,
  $`X_0 \in C^1_c(E \times \mathbb{R}; \mathbb{R})`$, $`X \in C^1_c(E \times \mathbb{R}; E)`$. Then
  ```math
  \int_{\{(x, t) \,:\, t \le \varphi(x)\}} \big( \partial_t X_0 + \operatorname{div}_x X \big)\, d(\mu \otimes \mathcal{L}^1)
  = \int_E \Big( X_0\big(x, \varphi(x)\big) - \big\langle \nabla\varphi(x),\, X\big(x, \varphi(x)\big) \big\rangle \Big)\, d\mu(x).
  ```
- **Hypotheses.** $`E`$ finite-dimensional real inner product space, Borel; $`\mu`$ additive Haar;
  $`\varphi`$ is $`C^1`$; $`X_0, X`$ are $`C^1`$ with compact support.
- **Lean.** `MeasureTheory.integral_divergence_hypograph_gradient`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremHypograph.lean#L327)

```lean
theorem integral_divergence_hypograph_gradient (hφ : ContDiff ℝ 1 φ) (hX₀ : ContDiff ℝ 1 X₀)
    (hX₀c : HasCompactSupport X₀) (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ p in {p : E × ℝ | p.2 ≤ φ p.1},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      ∫ x, (X₀ (x, φ x) - ⟪∇ φ x, X (x, φ x)⟫) ∂μ
```

- **Notes.** Same statement as `integral_divergence_hypograph`, with
  $`D\varphi(x)\,v = \langle \nabla\varphi(x), v\rangle`$.

### Divergence theorem below a graph, time first

- **Math.** Let $`E, \mu`$ be as in `integral_divergence_hypograph` (finite-dimensional real normed
  space, Borel, additive Haar), and consider spacetime $`\mathbb{R} \times E`$ with points
  $`(t, x)`$. Let $`\varphi \in C^1(E; \mathbb{R})`$,
  $`X_0 \in C^1_c(\mathbb{R} \times E; \mathbb{R})`$ and $`X \in C^1_c(\mathbb{R} \times E; E)`$.
  Then
  ```math
  \int_{\{(t, x) \,:\, t \le \varphi(x)\}} \Big( \partial_t X_0(t, x) + \operatorname{tr}\big( D[X(t, \cdot)](x) \big) \Big)\, d(\mathcal{L}^1 \otimes \mu)(t, x)
  = \int_E \Big( X_0\big(\varphi(x), x\big) - D\varphi(x)\, X\big(\varphi(x), x\big) \Big)\, d\mu(x).
  ```
- **Hypotheses.** $`E`$ finite-dimensional real normed space, Borel; $`\mu`$ additive Haar;
  $`\varphi`$ is $`C^1`$; $`X_0, X`$ (now defined on $`\mathbb{R} \times E`$) are $`C^1`$ with
  compact support.
- **Lean.** `MeasureTheory.integral_divergence_hypograph_swap`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremHypograph.lean#L302)

```lean
theorem integral_divergence_hypograph_swap {X₀ : ℝ × E → ℝ} {X : ℝ × E → E}
    (hφ : ContDiff ℝ 1 φ) (hX₀ : ContDiff ℝ 1 X₀) (hX₀c : HasCompactSupport X₀)
    (hX : ContDiff ℝ 1 X) (hXc : HasCompactSupport X) :
    ∫ p in {p : ℝ × E | p.1 ≤ φ p.2},
        (deriv (fun t ↦ X₀ (t, p.2)) p.1 +
          LinearMap.trace ℝ E (fderiv ℝ (fun y ↦ X (p.1, y)) p.2 : E →ₗ[ℝ] E)) ∂volume.prod μ =
      ∫ x, (X₀ (φ x, x) - fderiv ℝ φ x (X (φ x, x))) ∂μ
```

- **Notes.** The arguments `{X₀ : ℝ × E → ℝ} {X : ℝ × E → E}` replace the variables of the same
  names (defined on $`E \times \mathbb{R}`$) of the *Context* section. The spatial divergence is
  written out (`LinearMap.trace` of the derivative of $`y \mapsto X(t, y)`$), because
  `spatialDivergence` expects time second. With $`E`$ = `EuclideanSpace ℝ (Fin 3)` and
  $`\mu`$ = `volume` this is a statement on `Spacetime` with its Lebesgue measure.

### Spatial divergence in Euclidean coordinates

- **Math.** Let $`n \in \mathbb{N}`$, $`X : \mathbb{R}^n \times \mathbb{R} \to \mathbb{R}^n`$ and
  $`p = (x, t)`$ such that $`y \mapsto X(y, t)`$ is differentiable at $`x`$. Then
  ```math
  \operatorname{div}_x X(x, t) = \sum_{i=1}^{n} \frac{\partial X^i}{\partial x^i}(x, t),
  ```
  where $`\frac{\partial X^i}{\partial x^i}(x, t) = D[X^i(\cdot, t)](x)\, e_i`$.
- **Hypotheses.** $`y \mapsto X(y, t)`$ is differentiable at $`x`$.
- **Lean.** `spatialDivergence_euclideanSpace` (root namespace), [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/Analysis/Calculus/SpatialDivergence.lean#L195)

```lean
theorem spatialDivergence_euclideanSpace {n : ℕ}
    {X : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n)}
    {p : EuclideanSpace ℝ (Fin n) × ℝ} (hX : DifferentiableAt ℝ (fun y ↦ X (y, p.2)) p.1) :
    spatialDivergence X p =
      ∑ i, fderiv ℝ (fun y ↦ X (y, p.2) i) p.1 (EuclideanSpace.single i 1)
```

- **Notes.** The Lean index `i : Fin n` runs over $`0, \dots, n - 1`$, i.e. the mathematical
  indices $`1, \dots, n`$; `X (y, p.2) i` is the component $`X^{i+1}(y, t)`$ and
  `EuclideanSpace.single i 1` is $`e_{i+1}`$. The hypothesis makes each component differentiable,
  so the right-hand side involves genuine partial derivatives (no junk values).

### Divergence theorem between two graphs, locally defined field (iterated, oriented)

- **Math.** Let $`E, \mu`$ be as in `integral_divergence_hypograph`, $`U \subseteq E \times \mathbb{R}`$
  open, $`\varphi_1, \varphi_2 \in C^1(E; \mathbb{R})`$ (in any order), and
  ```math
  D = \{ (x, t) : \min(\varphi_1(x), \varphi_2(x)) \le t \le \max(\varphi_1(x), \varphi_2(x)) \}.
  ```
  Assume $`D \subseteq U`$, $`X_0 : E \times \mathbb{R} \to \mathbb{R}`$ and
  $`X : E \times \mathbb{R} \to E`$ are $`C^1`$ on $`U`$, and
  $`D \cap (\operatorname{supp} X_0 \cup \operatorname{supp} X)`$ is compact. Then
  ```math
  \int_E \left( \int_{\varphi_1(x)}^{\varphi_2(x)} \big( \partial_t X_0 + \operatorname{div}_x X \big)(x, t)\, dt \right) d\mu(x)
  = \Phi_{\varphi_2} - \Phi_{\varphi_1},
  \qquad
  \Phi_{\varphi_i} = \int_E \Big( X_0\big(x, \varphi_i(x)\big) - D\varphi_i(x)\, X\big(x, \varphi_i(x)\big) \Big)\, d\mu(x),
  ```
  with the oriented inner integral.
- **Hypotheses.** $`E`$ finite-dimensional real normed space, Borel; $`\mu`$ additive Haar; $`U`$
  open; $`\varphi_1, \varphi_2`$ are $`C^1`$ on $`E`$; $`D \subseteq U`$; $`X_0, X`$ are $`C^1`$ on
  $`U`$; $`D \cap (\operatorname{supp} X_0 \cup \operatorname{supp} X)`$ is compact.
- **Lean.** `MeasureTheory.integral_intervalIntegral_divergence_of_contDiffOn`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremLocal.lean#L84)

```lean
theorem integral_intervalIntegral_divergence_of_contDiffOn {U : Set (E × ℝ)} (hU : IsOpen U)
    (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂)
    (hDU : {p : E × ℝ | p.2 ∈ uIcc (φ₁ p.1) (φ₂ p.1)} ⊆ U)
    (hX₀ : ContDiffOn ℝ 1 X₀ U) (hX : ContDiffOn ℝ 1 X U)
    (hK : IsCompact ({p : E × ℝ | p.2 ∈ uIcc (φ₁ p.1) (φ₂ p.1)} ∩ (tsupport X₀ ∪ tsupport X))) :
    ∫ x, (∫ t in φ₁ x..φ₂ x, (deriv (fun s ↦ X₀ (x, s)) t + spatialDivergence X (x, t))) ∂μ =
      (∫ x, (X₀ (x, φ₂ x) - fderiv ℝ φ₂ x (X (x, φ₂ x))) ∂μ) -
        ∫ x, (X₀ (x, φ₁ x) - fderiv ℝ φ₁ x (X (x, φ₁ x))) ∂μ
```

- **Notes.** Generalizes `integral_intervalIntegral_divergence`: no global smoothness and no
  compact support of $`X_0, X`$, and their values outside $`U`$ are arbitrary. The supports are the
  closed supports `tsupport`. Everything in the conclusion is evaluated on $`D`$, where $`X_0, X`$
  are $`C^1`$, so the derivatives in the integrands are genuine.

### Divergence theorem on the closed region between two graphs, locally defined field

- **Math.** Let $`E, \mu`$ be as in `integral_divergence_hypograph`, $`U \subseteq E \times \mathbb{R}`$
  open, $`\varphi_1, \varphi_2 \in C^1(E; \mathbb{R})`$ with $`\varphi_1 \le \varphi_2`$ pointwise,
  and $`D = \{(x, t) : \varphi_1(x) \le t \le \varphi_2(x)\}`$. Assume $`D \subseteq U`$, $`X_0`$ and
  $`X`$ are $`C^1`$ on $`U`$, and $`D \cap (\operatorname{supp} X_0 \cup \operatorname{supp} X)`$ is
  compact. Then
  ```math
  \int_{D} \big( \partial_t X_0 + \operatorname{div}_x X \big)\, d(\mu \otimes \mathcal{L}^1)
  = \Phi_{\varphi_2} - \Phi_{\varphi_1},
  ```
  with $`\Phi_{\varphi_i}`$ as in the previous entry.
- **Hypotheses.** $`E`$ finite-dimensional real normed space, Borel; $`\mu`$ additive Haar; $`U`$
  open; $`\varphi_1, \varphi_2`$ are $`C^1`$ and $`\varphi_1 \le \varphi_2`$; $`D \subseteq U`$;
  $`X_0, X`$ are $`C^1`$ on $`U`$; $`D \cap (\operatorname{supp} X_0 \cup \operatorname{supp} X)`$ is
  compact.
- **Lean.** `MeasureTheory.integral_divergence_region_between_cc_of_contDiffOn`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremLocal.lean#L112)

```lean
theorem integral_divergence_region_between_cc_of_contDiffOn {U : Set (E × ℝ)} (hU : IsOpen U)
    (hφ₁ : ContDiff ℝ 1 φ₁) (hφ₂ : ContDiff ℝ 1 φ₂) (hφ : φ₁ ≤ φ₂)
    (hDU : {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)} ⊆ U)
    (hX₀ : ContDiffOn ℝ 1 X₀ U) (hX : ContDiffOn ℝ 1 X U)
    (hK : IsCompact ({p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)} ∩ (tsupport X₀ ∪ tsupport X))) :
    ∫ p in {p : E × ℝ | p.2 ∈ Icc (φ₁ p.1) (φ₂ p.1)},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      (∫ x, (X₀ (x, φ₂ x) - fderiv ℝ φ₂ x (X (x, φ₂ x))) ∂μ) -
        ∫ x, (X₀ (x, φ₁ x) - fderiv ℝ φ₁ x (X (x, φ₁ x))) ∂μ
```

- **Notes.** Generalizes `integral_divergence_region_between_cc` in the same way as the previous
  entry. It is the form used for the hyperboloids below (with $`U = E \times \mathbb{R}`$).

### Divergence theorem between two hyperboloids

- **Math.** Let $`E`$ be a finite-dimensional real inner product space with its Borel
  $`\sigma`$-algebra and $`\mu`$ an additive Haar measure on $`E`$. Let $`0 < s_1 < s_2`$, put
  $`\varphi_i(x) = \sqrt{s_i^2 + \lvert x\rvert^2}`$ (so the graph of $`\varphi_i`$ is the
  hyperboloid $`t^2 - \lvert x\rvert^2 = s_i^2`$, $`t > 0`$), and let
  $`X_0 \in C^1(E \times \mathbb{R}; \mathbb{R})`$, $`X \in C^1(E \times \mathbb{R}; E)`$ with
  ```math
  \{X_0 \neq 0\} \cup \{X \neq 0\} \subseteq \{ (x, t) : \lvert x\rvert \le t - 1 \}.
  ```
  Then
  ```math
  \int_{\{(x, t) \,:\, \varphi_1(x) \le t \le \varphi_2(x)\}} \big( \partial_t X_0 + \operatorname{div}_x X \big)\, d(\mu \otimes \mathcal{L}^1)
  = \int_E \Big( X_0\big(x, \varphi_2(x)\big) - \frac{\langle x, X(x, \varphi_2(x)) \rangle}{\varphi_2(x)} \Big)\, d\mu(x)
  - \int_E \Big( X_0\big(x, \varphi_1(x)\big) - \frac{\langle x, X(x, \varphi_1(x)) \rangle}{\varphi_1(x)} \Big)\, d\mu(x).
  ```
- **Hypotheses.** $`E`$ finite-dimensional real inner product space, Borel; $`\mu`$ additive Haar;
  $`0 < s_1`$ and $`s_1 < s_2`$; $`X_0, X`$ are $`C^1`$ on $`E \times \mathbb{R}`$; their supports
  are contained in $`\{\lvert x\rvert \le t - 1\}`$.
- **Lean.** `MeasureTheory.integral_divergence_between_hyperboloids`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/3fac872e390477a31fdbf56d88d4cc6989748e1e/VectorFieldMethod/ForMathlib/MeasureTheory/Integral/DivergenceTheoremHyperboloid.lean#L66)

```lean
theorem integral_divergence_between_hyperboloids {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂)
    (hX₀ : ContDiff ℝ 1 X₀) (hX : ContDiff ℝ 1 X)
    (hX₀s : support X₀ ⊆ {p | ‖p.1‖ ≤ p.2 - 1}) (hXs : support X ⊆ {p | ‖p.1‖ ≤ p.2 - 1}) :
    ∫ p in {p : E × ℝ | p.2 ∈ Icc √(s₁ ^ 2 + ‖p.1‖ ^ 2) √(s₂ ^ 2 + ‖p.1‖ ^ 2)},
        (deriv (fun t ↦ X₀ (p.1, t)) p.2 + spatialDivergence X p) ∂μ.prod volume =
      (∫ x, (X₀ (x, √(s₂ ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, X (x, √(s₂ ^ 2 + ‖x‖ ^ 2))⟫ / √(s₂ ^ 2 + ‖x‖ ^ 2)) ∂μ) -
        ∫ x, (X₀ (x, √(s₁ ^ 2 + ‖x‖ ^ 2)) -
          ⟪x, X (x, √(s₁ ^ 2 + ‖x‖ ^ 2))⟫ / √(s₁ ^ 2 + ‖x‖ ^ 2)) ∂μ
```

- **Notes.** $`\lvert x\rvert`$ is the norm of the inner product space $`E`$ (time is the second
  coordinate, so `p.1` is $`x`$ and `p.2` is $`t`$). The vector field is not assumed to have compact
  support; the support condition (the closed solid cone $`\lvert x\rvert \le t - 1`$, as for
  solutions of wave equations with initial data at $`t = 2`$ supported in the unit ball; LeFloch–Ma's cone
  $`\mathcal{K} = \{r < t - 1\}`$ has this closure) makes its intersection with the region between
  the hyperboloids compact, so all integrands are integrable and the identity is not a junk
  $`0 = 0`$. The support hypotheses use `support` ($`\{f \neq 0\}`$), which is equivalent to the
  same condition on `tsupport` because the cone is closed. No junk value of `/` or `√` occurs:
  $`s_i^2 + \lvert x\rvert^2 > 0`$ and $`\varphi_i \ge s_i > 0`$. The flux uses
  $`D\varphi_i(x)\, v = \langle x, v\rangle / \varphi_i(x)`$ (`fderiv_sqrt_sq_add_norm_sq_apply`).
  The hypothesis $`s_1 < s_2`$ is strict, although the identity is trivial for $`s_1 = s_2`$.
