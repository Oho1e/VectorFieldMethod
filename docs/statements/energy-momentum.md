# Energy-momentum tensor of the Klein–Gordon field: statements

Layer: `VectorFieldMethod/Minkowski/EnergyMomentum.lean`, built on the Minkowski coordinate layer
(see [`minkowski.md`](minkowski.md) for $`\partial_\alpha`$, $`\Box`$, the Klein–Gordon operator
and their conventions). All declarations are in the namespace `VectorFieldMethod.Minkowski`. The
links below point to commit
[`c075659`](https://github.com/Oho1e/VectorFieldMethod/tree/c07565966e70ee96c016a711b0ee35a6d6a86777),
the last commit that changes the Lean file of this layer; it is identical at the head of the
branch. How to read the entries: [`README.md`](README.md).

## Conventions

Quoted from the module docstring of
[`EnergyMomentum.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L43)
(normalization):

> The tensor carries the factor `½`, so that the energy density is
> `P^0 = T_{00} = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)`. Texts that define the energy density
> without the factor `½`, as `‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²`, use the tensor `2 T_{αβ}` and the
> current `2 P^α`, which differ from the ones of this file by the factor `2`; their versions of the
> identities below are the ones of this file multiplied by `2`.

- **Normalization with $`\tfrac12`$.** This project's energy-momentum tensor, energy current and
  energy density carry the factor $`\tfrac12`$. If the energy density of a text has no factor
  $`\tfrac12`$, that is, it is $`\lVert\partial_t u\rVert^2 + \sum_a \lVert\partial_a u\rVert^2 + m^2 \lVert u\rVert^2`$,
  then its tensor, current and energy are **twice** the ones here, and its identities are the
  identities below multiplied by $`2`$.
- **Signs.** Signature $`(-, +, +, +)`$, $`\Box = -\partial_t^2 + \Delta`$, and the Klein–Gordon
  operator is $`\mathrm{KG}_m u = \Box u - m^2 u`$ (`kleinGordon m u`). LeFloch–Ma's Klein–Gordon
  operator is $`-\mathrm{KG}_m`$ (see [`minkowski.md`](minkowski.md)); with their operator the
  right-hand sides of the divergence and energy identities below change sign.
- **Metric.** $`\eta^{\alpha\beta}`$ and $`\eta_{\alpha\beta}`$ have the same entries
  (`inv_minkowskiMetric`), so both are written `η α β` (`minkowskiMetric`) in Lean.

**Notation in the Math lines below.** As in [`minkowski.md`](minkowski.md): $`p = (t, x)`$ is a
point of $`\mathbb{R}^{1+3}`$, spatial indices $`a \in \{1, 2, 3\}`$ correspond to the Lean
indices `a - 1 : Fin 3`, spacetime indices $`\alpha, \beta, \gamma \in \{0, 1, 2, 3\}`$ are the
Lean indices `α : Fin 4` (and the mathematical spatial index $`a`$ is the spacetime index
`Fin.succ (a - 1)`). Functions $`u, v : \mathbb{R}^{1+3} \to F`$ take values in a real inner
product space $`F`$ with inner product $`\langle \cdot, \cdot \rangle`$ and norm
$`\lVert \cdot \rVert`$; for instance $`F = \mathbb{R}`$ with $`\langle x, y\rangle = xy`$, or
$`F = \mathbb{C}`$ with the real inner product $`\langle z, w\rangle = \operatorname{Re}(\bar z w)`$
and $`\lVert z\rVert = \lvert z\rvert`$. $`m \in \mathbb{R}`$ is the mass (only $`m^2`$ enters).
Derivatives are the operators of the Minkowski layer, with the Lean convention that the
derivative of a function at a point where it is not differentiable is $`0`$ (see the README).
In Lean, `⟪x, y⟫` is the real inner product (`open scoped RealInnerProductSpace`).

## Context

The `variable` lines of the file declare the types of the letters used in the statements:
- `[NormedAddCommGroup F] [InnerProductSpace ℝ F]`: $`F`$ is a real inner product space. It is
  also a real normed space through its inner product, which is the structure the operators of the
  Minkowski layer use. No completeness or finite dimension is assumed.

[`EnergyMomentum.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L65):

```lean
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {u v : Spacetime → F} {p : Spacetime}
```

`u`, `v` and `p` are implicit arguments of the theorems that do not list them explicitly; they
are then inferred from the hypotheses (`hu : ContDiffAt ℝ 2 u p`, ...).

## Definitions

### Energy-momentum tensor $`T_{\alpha\beta}`$

- **Math.** For $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and
  $`\alpha, \beta \in \{0, 1, 2, 3\}`$, the function $`T_{\alpha\beta} : \mathbb{R}^{1+3} \to \mathbb{R}`$,
  ```math
  T_{\alpha\beta}(p) = \langle \partial_\alpha u(p), \partial_\beta u(p) \rangle
    - \frac12\, \eta_{\alpha\beta} \Big( \sum_{\gamma=0}^{3} \sum_{\delta=0}^{3} \eta^{\gamma\delta}
      \langle \partial_\gamma u(p), \partial_\delta u(p) \rangle + m^2 \lVert u(p) \rVert^2 \Big).
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`m`$ and $`u`$ are arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.energyMomentum`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L103)

```lean
def energyMomentum (m : ℝ) (u : Spacetime → F) (α β : Fin 4) : Spacetime → ℝ :=
  fun p ↦ ⟪∂[α] u p, ∂[β] u p⟫ -
    1 / 2 * η α β * (∑ γ, ∑ δ, η γ δ * ⟪∂[γ] u p, ∂[δ] u p⟫ + m ^ 2 * ‖u p‖ ^ 2)
```

- **Notes.** The normalization carries the factor $`\tfrac12`$ (see *Conventions*); texts whose
  energy density has no factor $`\tfrac12`$ use $`2T_{\alpha\beta}`$. Since $`\eta`$ is diagonal,
  the double sum is $`-\lVert\partial_t u\rVert^2 + \sum_a \lVert\partial_a u\rVert^2`$
  (`sum_sum_minkowskiMetric_mul_inner`). The definition makes sense for every $`u`$; at points
  where $`u`$ is not differentiable it contains the junk value $`0`$ of the derivatives.

### Spacetime divergence

- **Math.** For $`J = (J^0, J^1, J^2, J^3)`$ with real-valued components
  $`J^\alpha : \mathbb{R}^{1+3} \to \mathbb{R}`$,
  ```math
  (\operatorname{div} J)(p) = \partial_\alpha J^\alpha(p) = \sum_{\alpha=0}^{3} \partial_\alpha J^\alpha(p).
  ```
- **Hypotheses.** None; $`J`$ is arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.spacetimeDiv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L114)

```lean
def spacetimeDiv (J : Fin 4 → Spacetime → ℝ) : Spacetime → ℝ :=
  fun p ↦ ∑ α, ∂[α] (J α) p
```

- **Notes.** `J α` is the component $`J^\alpha`$. This is the divergence on all of spacetime
  (time derivative included); it is not the `spatialDivergence` of the `ForMathlib` layer.

### Energy current $`P^\alpha`$

- **Math.** For $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`\alpha \in \{0, 1, 2, 3\}`$,
  ```math
  P^\alpha(p) = -\sum_{\gamma=0}^{3} \eta^{\alpha\gamma}\, T_{\gamma 0}(p),
  ```
  the current associated with the vector field $`\partial_t`$ (so $`P^0 = T_{00}`$ and
  $`P^a = -T_{a0}`$).
- **Hypotheses.** $`F`$ is a real inner product space; $`m`$ and $`u`$ are arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.energyCurrent`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L124)

```lean
def energyCurrent (m : ℝ) (u : Spacetime → F) (α : Fin 4) : Spacetime → ℝ :=
  fun p ↦ -∑ γ, η α γ * energyMomentum m u γ 0 p
```

- **Notes.** `energyCurrent m u : Fin 4 → Spacetime → ℝ` is a vector field with real components,
  the argument of `spacetimeDiv`. Its components are computed below (`energyCurrent_zero`,
  `energyCurrent_succ`).

## Main theorems

### Leibniz rule for the inner product

- **Math.** Let $`V : \mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$ be any map (the components of a
  vector field), $`p \in \mathbb{R}^{1+3}`$, and let $`u, v : \mathbb{R}^{1+3} \to F`$ be
  differentiable at $`p`$. Then
  ```math
  V\langle u, v \rangle(p) = \langle Vu(p), v(p) \rangle + \langle u(p), Vv(p) \rangle .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`u`$ and $`v`$ are differentiable at
  $`p`$; no hypothesis on $`V`$.
- **Lean.** `VectorFieldMethod.Minkowski.derivAlong_inner`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L72)

```lean
theorem derivAlong_inner (V : Spacetime → Spacetime) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    derivAlong V (fun q ↦ ⟪u q, v q⟫) p = ⟪derivAlong V u p, v p⟫ + ⟪u p, derivAlong V v p⟫
```

- **Notes.** $`\langle u, v\rangle`$ is the real-valued function $`q \mapsto \langle u(q), v(q)\rangle`$
  and $`Vu = Du(\cdot)\,V(\cdot)`$ is `derivAlong V u`. The differentiability hypotheses are needed
  because of the junk value of `fderiv`. The same statement for $`\partial_\alpha`$ is
  `partialDeriv_inner` ([permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L85)).

### Leibniz rule for the squared norm

- **Math.** Let $`V : \mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$ be any map, $`p \in \mathbb{R}^{1+3}`$,
  and let $`u : \mathbb{R}^{1+3} \to F`$ be differentiable at $`p`$. Then
  ```math
  V\big(\lVert u \rVert^2\big)(p) = 2\, \langle u(p), Vu(p) \rangle .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`u`$ is differentiable at $`p`$; no
  hypothesis on $`V`$.
- **Lean.** `VectorFieldMethod.Minkowski.derivAlong_norm_sq`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L79)

```lean
theorem derivAlong_norm_sq (V : Spacetime → Spacetime) (hu : DifferentiableAt ℝ u p) :
    derivAlong V (fun q ↦ ‖u q‖ ^ 2) p = 2 * ⟪u p, derivAlong V u p⟫
```

- **Notes.** This is the previous entry with $`v = u`$. The version for $`\partial_\alpha`$ is
  `partialDeriv_norm_sq` ([permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L91)).

### Symmetry of the energy-momentum tensor

- **Math.** For every $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and
  $`\alpha, \beta \in \{0, 1, 2, 3\}`$, $`T_{\alpha\beta} = T_{\beta\alpha}`$ on $`\mathbb{R}^{1+3}`$.
- **Hypotheses.** $`F`$ is a real inner product space; no hypothesis on $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.energyMomentum_swap`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L134)

```lean
theorem energyMomentum_swap (m : ℝ) (u : Spacetime → F) (α β : Fin 4) :
    energyMomentum m u α β = energyMomentum m u β α
```

- **Notes.** It follows from the symmetry of the real inner product and of $`\eta`$; no
  regularity is needed.

### Divergence identity

- **Math.** Let $`m \in \mathbb{R}`$, $`\beta \in \{0, 1, 2, 3\}`$, $`p \in \mathbb{R}^{1+3}`$, and
  let $`u : \mathbb{R}^{1+3} \to F`$ be $`C^2`$ on a neighbourhood of $`p`$. Then
  ```math
  \sum_{\alpha=0}^{3} \sum_{\gamma=0}^{3} \eta^{\alpha\gamma}\, \partial_\gamma T_{\alpha\beta}(p)
    = \big\langle (\Box u - m^2 u)(p),\ \partial_\beta u(p) \big\rangle .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`u`$ is $`C^2`$ at $`p`$
  (`ContDiffAt ℝ 2 u p`).
- **Lean.** `VectorFieldMethod.Minkowski.sum_sum_minkowskiMetric_mul_partialDeriv_energyMomentum`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L192)

```lean
theorem sum_sum_minkowskiMetric_mul_partialDeriv_energyMomentum (m : ℝ) (β : Fin 4)
    (hu : ContDiffAt ℝ 2 u p) :
    ∑ α, ∑ γ, η α γ * ∂[γ] (energyMomentum m u α β) p = ⟪kleinGordon m u p, ∂[β] u p⟫
```

- **Notes.** In index notation, $`\partial^\alpha T_{\alpha\beta} = \langle \mathrm{KG}_m u, \partial_\beta u\rangle`$.
  `u` and `p` are the implicit variables of the *Context* section; $`\partial_\gamma T_{\alpha\beta}`$
  is the derivative of the real-valued function `energyMomentum m u α β`. The $`C^2`$ hypothesis
  is used twice: the first derivatives $`\partial_\alpha u`$ are differentiable at $`p`$, so that
  $`T_{\alpha\beta}`$ can be differentiated there by the Leibniz rules, and the second derivatives
  are symmetric at $`p`$ (`partialDeriv_comm_apply` of the Minkowski layer). The explicit
  derivative of $`T_{\alpha\beta}`$ is the auxiliary lemma `partialDeriv_energyMomentum`.

### Energy identity for the current of $`\partial_t`$

- **Math.** Let $`m \in \mathbb{R}`$, $`p \in \mathbb{R}^{1+3}`$, and let
  $`u : \mathbb{R}^{1+3} \to F`$ be $`C^2`$ on a neighbourhood of $`p`$. Then
  ```math
  (\operatorname{div} P)(p) = \sum_{\alpha=0}^{3} \partial_\alpha P^\alpha(p)
    = -\big\langle (\Box u - m^2 u)(p),\ \partial_t u(p) \big\rangle .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`u`$ is $`C^2`$ at $`p`$.
- **Lean.** `VectorFieldMethod.Minkowski.spacetimeDiv_energyCurrent`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L217)

```lean
theorem spacetimeDiv_energyCurrent (m : ℝ) (hu : ContDiffAt ℝ 2 u p) :
    spacetimeDiv (energyCurrent m u) p = -⟪kleinGordon m u p, ∂ₜ u p⟫
```

- **Notes.** This is the divergence identity for $`\beta = 0`$, rewritten with
  $`P^\alpha = -\eta^{\alpha\gamma} T_{\gamma 0}`$. With the factor-$`2`$ normalization of some texts
  (see *Conventions*) the right-hand side is $`-2\langle \mathrm{KG}_m u, \partial_t u\rangle`$.

### The energy current of a solution is divergence free

- **Math.** Let $`m \in \mathbb{R}`$, $`p \in \mathbb{R}^{1+3}`$, and let
  $`u : \mathbb{R}^{1+3} \to F`$ be $`C^2`$ on a neighbourhood of $`p`$ and satisfy
  $`\Box u - m^2 u = 0`$ on a neighbourhood of $`p`$. Then $`(\operatorname{div} P)(p) = 0`$.
- **Hypotheses.** $`F`$ is a real inner product space; $`u`$ is $`C^2`$ at $`p`$; $`u`$ solves the
  Klein–Gordon equation on a neighbourhood of $`p`$ (`kleinGordon m u =ᶠ[𝓝 p] 0`).
- **Lean.** `VectorFieldMethod.Minkowski.spacetimeDiv_energyCurrent_eq_zero`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L226)

```lean
theorem spacetimeDiv_energyCurrent_eq_zero (m : ℝ) (hu : ContDiffAt ℝ 2 u p)
    (hKG : kleinGordon m u =ᶠ[𝓝 p] 0) : spacetimeDiv (energyCurrent m u) p = 0
```

- **Notes.** `0` on the right of `=ᶠ[𝓝 p]` is the zero function. The proof only uses the value
  $`(\Box u - m^2 u)(p) = 0`$ at $`p`$. The hypotheses can hold simultaneously: the *Sanity checks*
  below apply the theorem to $`u = t`$ with $`m = 0`$ and to the plane wave $`e^{-imt}`$ for every
  $`m`$.

### Energy density

- **Math.** For every $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`p`$,
  ```math
  P^0(p) = \frac12 \Big( \lVert \partial_t u(p) \rVert^2 + \sum_{a=1}^{3} \lVert \partial_a u(p) \rVert^2
    + m^2 \lVert u(p) \rVert^2 \Big).
  ```
- **Hypotheses.** $`F`$ is a real inner product space; no hypothesis on $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.energyCurrent_zero`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L239)

```lean
theorem energyCurrent_zero (m : ℝ) (u : Spacetime → F) (p : Spacetime) :
    energyCurrent m u 0 p = 1 / 2 * (‖∂ₜ u p‖ ^ 2 + ∑ a, ‖∂ₓ[a] u p‖ ^ 2 + m ^ 2 * ‖u p‖ ^ 2)
```

- **Notes.** No hypothesis is needed: both sides are the same algebraic expression in the values
  $`\partial_\alpha u(p)`$ and $`u(p)`$ (junk values, if any, are the same on both sides). Texts
  without the factor $`\tfrac12`$ (see *Conventions*) have twice this energy density.

### Positivity of the energy density

- **Math.** For every $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`p`$,
  $`P^0(p) \ge 0`$.
- **Hypotheses.** $`F`$ is a real inner product space; no hypothesis on $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.energyCurrent_zero_nonneg`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L247)

```lean
theorem energyCurrent_zero_nonneg (m : ℝ) (u : Spacetime → F) (p : Spacetime) :
    0 ≤ energyCurrent m u 0 p
```

### Momentum density

- **Math.** For every $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$, $`p`$ and
  $`a \in \{1, 2, 3\}`$,
  ```math
  P^a(p) = -\langle \partial_a u(p), \partial_t u(p) \rangle .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; no hypothesis on $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.energyCurrent_succ`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L254)

```lean
theorem energyCurrent_succ (m : ℝ) (u : Spacetime → F) (a : Fin 3) (p : Spacetime) :
    energyCurrent m u a.succ p = -⟪∂ₓ[a] u p, ∂ₜ u p⟫
```

- **Notes.** The Lean argument `a : Fin 3` is the mathematical index $`a + 1`$, and `a.succ` is
  the corresponding spacetime index. No hypothesis is needed, for the same reason as for the
  energy density; $`m`$ does not enter since $`\eta_{a0} = 0`$.

## Sanity checks

The section "Sanity checks" at the end of the file contains the following `example`s.

| Statement | Line |
| --- | --- |
| $`u = t`$, $`m = 0`$ ($`F = \mathbb{R}`$): `spacetimeDiv_energyCurrent_eq_zero` applies, since $`t`$ is smooth and $`\Box t = 0`$ | [L264](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L264) |
| $`u = t`$ ($`F = \mathbb{R}`$): $`P^0 = \tfrac12 (1 + m^2 t^2)`$ | [L269](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L269) |
| $`u = t + i x^1`$ ($`F = \mathbb{C}`$): $`P^0 = 1 + m^2 (t^2 + (x^1)^2)/2`$ and $`P^1 = -\langle i, 1\rangle = 0`$ | [L279](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L279) |
| $`u = e^{-imt}`$ ($`F = \mathbb{C}`$, every $`m`$): $`u`$ solves $`\Box u - m^2 u = 0`$, so `spacetimeDiv_energyCurrent_eq_zero` applies and $`\operatorname{div} P = 0`$; moreover $`P^0 = m^2`$ | [L317](https://github.com/Oho1e/VectorFieldMethod/blob/c07565966e70ee96c016a711b0ee35a6d6a86777/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L317) |

The first and last examples show that the hypotheses of `spacetimeDiv_energyCurrent_eq_zero` can
hold simultaneously (massless and massive case). The complex examples show that the definitions
apply to complex-valued fields, with the real inner product of $`\mathbb{C}`$.
