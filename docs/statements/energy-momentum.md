# Energy-momentum tensor of the Klein–Gordon field: statements

Layer: `VectorFieldMethod/Minkowski/EnergyMomentum.lean`, built on the Minkowski coordinate layer
(see [`minkowski.md`](minkowski.md) for $`\partial_\alpha`$, $`\Box`$, the Klein–Gordon operator
and their conventions). All declarations are in the namespace `VectorFieldMethod.Minkowski`. The
links below point to commit
[`417e63e`](https://github.com/Oho1e/VectorFieldMethod/tree/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23),
the last commit that changes the Lean file of this layer; it is identical at the head of the
branch. How to read the entries: [`README.md`](README.md).

## Conventions

Quoted from the module docstring of
[`EnergyMomentum.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L47)
(normalization):

> The tensor carries the factor `½`, so that the energy density is
> `P^0 = T_{00} = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)`. LeFloch–Ma, among others, define the
> energy directly, without introducing an energy-momentum tensor; their energy density
> `‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²` corresponds to `2 P^0` in this project.

- **Normalization with $`\tfrac12`$.** This project's energy-momentum tensor, energy current and
  energy density carry the factor $`\tfrac12`$. LeFloch–Ma, among others, define the energy
  directly, without introducing an energy-momentum tensor; their energy density
  $`\lVert\partial_t u\rVert^2 + \sum_a \lVert\partial_a u\rVert^2 + m^2 \lVert u\rVert^2`$
  corresponds to $`2P^0`$ in this project, so their energy is twice the one obtained from
  $`P^0`$.
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

[`EnergyMomentum.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L67):

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
- **Lean.** `VectorFieldMethod.Minkowski.energyMomentum`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L105)

```lean
def energyMomentum (m : ℝ) (u : Spacetime → F) (α β : Fin 4) : Spacetime → ℝ :=
  fun p ↦ ⟪∂[α] u p, ∂[β] u p⟫ -
    1 / 2 * η α β * (∑ γ, ∑ δ, η γ δ * ⟪∂[γ] u p, ∂[δ] u p⟫ + m ^ 2 * ‖u p‖ ^ 2)
```

- **Notes.** The normalization carries the factor $`\tfrac12`$ (see *Conventions*). LeFloch–Ma
  define the energy directly, without a tensor; their energy density corresponds to
  $`2T_{00} = 2P^0`$. Since $`\eta`$ is diagonal,
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
- **Lean.** `VectorFieldMethod.Minkowski.spacetimeDiv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L116)

```lean
def spacetimeDiv (J : Fin 4 → Spacetime → ℝ) : Spacetime → ℝ :=
  fun p ↦ ∑ α, ∂[α] (J α) p
```

- **Notes.** `J α` is the component $`J^\alpha`$. This is the divergence on all of spacetime
  (time derivative included); it is not the `spatialDivergence` of the `ForMathlib` layer. If a
  component $`J^\alpha`$ is not differentiable at $`p`$, then $`\partial_\alpha J^\alpha(p)`$ is the
  junk value $`0`$ of `fderiv`, and the value $`(\operatorname{div} J)(p)`$ is a junk value: a
  statement about it is meaningful only where the components are differentiable.

### Energy current $`P^\alpha`$

- **Math.** For $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`\alpha \in \{0, 1, 2, 3\}`$,
  ```math
  P^\alpha(p) = -\sum_{\gamma=0}^{3} \eta^{\alpha\gamma}\, T_{\gamma 0}(p),
  ```
  the current associated with the vector field $`\partial_t`$ (so $`P^0 = T_{00}`$ and
  $`P^a = -T_{a0}`$).
- **Hypotheses.** $`F`$ is a real inner product space; $`m`$ and $`u`$ are arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.energyCurrent`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L126)

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
- **Lean.** `VectorFieldMethod.Minkowski.derivAlong_inner`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L74)

```lean
theorem derivAlong_inner (V : Spacetime → Spacetime) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    derivAlong V (fun q ↦ ⟪u q, v q⟫) p = ⟪derivAlong V u p, v p⟫ + ⟪u p, derivAlong V v p⟫
```

- **Notes.** $`\langle u, v\rangle`$ is the real-valued function $`q \mapsto \langle u(q), v(q)\rangle`$
  and $`Vu = Du(\cdot)\,V(\cdot)`$ is `derivAlong V u`. The differentiability hypotheses are needed
  because of the junk value of `fderiv`. The same statement for $`\partial_\alpha`$ is
  `partialDeriv_inner` ([permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L87)).

### Leibniz rule for the squared norm

- **Math.** Let $`V : \mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$ be any map, $`p \in \mathbb{R}^{1+3}`$,
  and let $`u : \mathbb{R}^{1+3} \to F`$ be differentiable at $`p`$. Then
  ```math
  V\big(\lVert u \rVert^2\big)(p) = 2\, \langle u(p), Vu(p) \rangle .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`u`$ is differentiable at $`p`$; no
  hypothesis on $`V`$.
- **Lean.** `VectorFieldMethod.Minkowski.derivAlong_norm_sq`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L81)

```lean
theorem derivAlong_norm_sq (V : Spacetime → Spacetime) (hu : DifferentiableAt ℝ u p) :
    derivAlong V (fun q ↦ ‖u q‖ ^ 2) p = 2 * ⟪u p, derivAlong V u p⟫
```

- **Notes.** This is the previous entry with $`v = u`$. The version for $`\partial_\alpha`$ is
  `partialDeriv_norm_sq` ([permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L93)).

### Symmetry of the energy-momentum tensor

- **Math.** For every $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and
  $`\alpha, \beta \in \{0, 1, 2, 3\}`$, $`T_{\alpha\beta} = T_{\beta\alpha}`$ on $`\mathbb{R}^{1+3}`$.
- **Hypotheses.** $`F`$ is a real inner product space; no hypothesis on $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.energyMomentum_swap`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L136)

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
- **Lean.** `VectorFieldMethod.Minkowski.sum_sum_minkowskiMetric_mul_partialDeriv_energyMomentum`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L197)

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
- **Lean.** `VectorFieldMethod.Minkowski.spacetimeDiv_energyCurrent`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L222)

```lean
theorem spacetimeDiv_energyCurrent (m : ℝ) (hu : ContDiffAt ℝ 2 u p) :
    spacetimeDiv (energyCurrent m u) p = -⟪kleinGordon m u p, ∂ₜ u p⟫
```

- **Notes.** This is the divergence identity for $`\beta = 0`$, rewritten with
  $`P^\alpha = -\eta^{\alpha\gamma} T_{\gamma 0}`$. The sign of the right-hand side is checked by a
  direct computation in the *Sanity checks* ($`u = t^2`$, where both sides equal $`4t`$).
  Multiplied by $`2`$, it is the identity for the current $`2P`$, whose time component is the
  energy density of LeFloch–Ma (see *Conventions*).

### The energy current of a solution is divergence free

- **Math.** Let $`m \in \mathbb{R}`$, $`p \in \mathbb{R}^{1+3}`$, and let
  $`u : \mathbb{R}^{1+3} \to F`$ be $`C^2`$ on a neighbourhood of $`p`$ and satisfy
  $`(\Box u - m^2 u)(p) = 0`$. Then $`(\operatorname{div} P)(p) = 0`$.
- **Hypotheses.** $`F`$ is a real inner product space; $`u`$ is $`C^2`$ at $`p`$; the
  Klein–Gordon operator of $`u`$ vanishes at the point $`p`$ (`kleinGordon m u p = 0`).
- **Lean.** `VectorFieldMethod.Minkowski.spacetimeDiv_energyCurrent_eq_zero`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L234)

```lean
theorem spacetimeDiv_energyCurrent_eq_zero (m : ℝ) (hu : ContDiffAt ℝ 2 u p)
    (hKG : kleinGordon m u p = 0) : spacetimeDiv (energyCurrent m u) p = 0
```

- **Notes.** The equation is assumed only at the point $`p`$; the $`C^2`$ hypothesis on a
  neighbourhood of $`p`$ is the hypothesis used. The versions on an open set and on all of
  spacetime are the next two entries. The hypotheses can hold simultaneously: the *Sanity checks*
  below apply the theorem to $`u = t`$ with $`m = 0`$ and to the spatially homogeneous mode
  $`e^{-imt}`$ (wave vector $`k = 0`$) for every $`m`$; the example $`u = t\,x^1`$ checks its
  conclusion by a direct computation.

### The energy current of a solution on an open set is divergence free

- **Math.** Let $`m \in \mathbb{R}`$, let $`U \subseteq \mathbb{R}^{1+3}`$ be open, and let
  $`u : \mathbb{R}^{1+3} \to F`$ be $`C^2`$ on $`U`$ and satisfy $`\Box u - m^2 u = 0`$ on $`U`$.
  Then $`\operatorname{div} P = 0`$ on $`U`$.
- **Hypotheses.** $`F`$ is a real inner product space; $`U`$ is open; $`u`$ is $`C^2`$ on $`U`$
  (`ContDiffOn ℝ 2 u U`); the Klein–Gordon operator of $`u`$ vanishes on $`U`$.
- **Lean.** `VectorFieldMethod.Minkowski.spacetimeDiv_energyCurrent_eqOn_zero`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L240)

```lean
theorem spacetimeDiv_energyCurrent_eqOn_zero (m : ℝ) {U : Set Spacetime} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hKG : Set.EqOn (kleinGordon m u) (fun _ ↦ 0) U) :
    Set.EqOn (spacetimeDiv (energyCurrent m u)) (fun _ ↦ 0) U
```

- **Notes.** `Set.EqOn f g U` means $`f(q) = g(q)`$ for every $`q \in U`$, and `fun _ ↦ 0` is the
  zero function. Since $`U`$ is open, `ContDiffOn ℝ 2 u U` gives $`C^2`$ on a neighbourhood of
  each point of $`U`$, and the previous entry applies at each point. The *Sanity checks* apply the
  theorem to $`u = t`$, $`m = 0`$ on the open half-space $`\{t \gt 0\}`$.

### The energy current of a global solution is divergence free

- **Math.** Let $`m \in \mathbb{R}`$ and let $`u \in C^2(\mathbb{R}^{1+3}, F)`$ satisfy
  $`\Box u - m^2 u = 0`$ on $`\mathbb{R}^{1+3}`$. Then $`\operatorname{div} P = 0`$ on
  $`\mathbb{R}^{1+3}`$.
- **Hypotheses.** $`F`$ is a real inner product space; $`u`$ is $`C^2`$ (`ContDiff ℝ 2 u`); the
  Klein–Gordon operator of $`u`$ vanishes identically.
- **Lean.** `VectorFieldMethod.Minkowski.spacetimeDiv_energyCurrent_eq_zero_of_contDiff`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L247)

```lean
theorem spacetimeDiv_energyCurrent_eq_zero_of_contDiff (m : ℝ) (hu : ContDiff ℝ 2 u)
    (hKG : kleinGordon m u = fun _ ↦ 0) : spacetimeDiv (energyCurrent m u) = fun _ ↦ 0
```

- **Notes.** An equality of functions on all of spacetime. The *Sanity checks* apply it to
  $`u = t`$, $`m = 0`$.

### Energy density

- **Math.** For every $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`p`$,
  ```math
  P^0(p) = \frac12 \Big( \lVert \partial_t u(p) \rVert^2 + \sum_{a=1}^{3} \lVert \partial_a u(p) \rVert^2
    + m^2 \lVert u(p) \rVert^2 \Big).
  ```
- **Hypotheses.** $`F`$ is a real inner product space; no hypothesis on $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.energyCurrent_zero`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L260)

```lean
theorem energyCurrent_zero (m : ℝ) (u : Spacetime → F) (p : Spacetime) :
    energyCurrent m u 0 p = 1 / 2 * (‖∂ₜ u p‖ ^ 2 + ∑ a, ‖∂ₓ[a] u p‖ ^ 2 + m ^ 2 * ‖u p‖ ^ 2)
```

- **Notes.** No hypothesis is needed: both sides are the same algebraic expression in the values
  $`\partial_\alpha u(p)`$ and $`u(p)`$ (junk values, if any, are the same on both sides). The
  energy density of LeFloch–Ma, who define the energy without a tensor, corresponds to $`2P^0`$
  (see *Conventions*).

### Positivity of the energy density

- **Math.** For every $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`p`$,
  $`P^0(p) \ge 0`$.
- **Hypotheses.** $`F`$ is a real inner product space; no hypothesis on $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.energyCurrent_zero_nonneg`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L268)

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
- **Lean.** `VectorFieldMethod.Minkowski.energyCurrent_succ`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L275)

```lean
theorem energyCurrent_succ (m : ℝ) (u : Spacetime → F) (a : Fin 3) (p : Spacetime) :
    energyCurrent m u a.succ p = -⟪∂ₓ[a] u p, ∂ₜ u p⟫
```

- **Notes.** The Lean argument `a : Fin 3` is the mathematical index $`a + 1`$, and `a.succ` is
  the corresponding spacetime index. No hypothesis is needed, for the same reason as for the
  energy density; $`m`$ does not enter since $`\eta_{a0} = 0`$.

## Sanity checks

The section "Sanity checks" at the end of the file contains the following `example`s. They are of
two kinds.

- **Hypotheses can hold.** The two examples that accompany the corollary
  `spacetimeDiv_energyCurrent_eq_zero` from the start, $`u = t`$ with $`m = 0`$ and the spatially
  homogeneous mode $`e^{-imt}`$, only check that its hypotheses can be satisfied simultaneously:
  their conclusion $`\operatorname{div} P = 0`$ is obtained from the theorem, not computed
  independently. The same holds for the example for the two variants on an open set and on all of
  spacetime.
- **Direct computations.** The other examples compute $`P`$ (and $`\operatorname{div} P`$) from
  the definitions. The last three ($`F = \mathbb{R}`$, $`m = 0`$) check signs: $`u = t - x^1`$ fixes
  the sign of $`P^a`$; $`u = t\,x^1`$ solves the wave equation, has a non-constant current, and
  its divergence vanishes by a non-trivial cancellation, as the corollary predicts; $`u = t^2`$ is
  not a solution, and both sides of `spacetimeDiv_energyCurrent` are computed and equal $`4t`$,
  which checks the sign of the right-hand side.

In Lean, $`x^1`$ is `spaceCoord 0`.

| Statement | Kind | Line |
| --- | --- | --- |
| $`u = t`$, $`m = 0`$ ($`F = \mathbb{R}`$): `spacetimeDiv_energyCurrent_eq_zero` applies, since $`t`$ is smooth and $`\Box t = 0`$ | hypotheses can hold | [L291](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L291) |
| $`u = t`$ ($`F = \mathbb{R}`$): $`P^0 = \tfrac12 (1 + m^2 t^2)`$ | direct computation | [L295](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L295) |
| $`u = t + i x^1`$ ($`F = \mathbb{C}`$): $`P^0 = 1 + m^2 (t^2 + (x^1)^2)/2`$ and $`P^1 = -\langle i, 1\rangle = 0`$ | direct computation | [L305](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L305) |
| $`u = e^{-imt}`$ ($`F = \mathbb{C}`$, every $`m`$), the spatially homogeneous mode (wave vector $`k = 0`$): $`u`$ solves $`\Box u - m^2 u = 0`$, so `spacetimeDiv_energyCurrent_eq_zero` applies and $`\operatorname{div} P = 0`$; moreover $`P^0 = m^2`$ | hypotheses can hold ($`P^0`$ computed directly) | [L343](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L343) |
| $`u = t`$, $`m = 0`$ ($`F = \mathbb{R}`$): `spacetimeDiv_energyCurrent_eqOn_zero` (on the open half-space $`\{t \gt 0\}`$) and `spacetimeDiv_energyCurrent_eq_zero_of_contDiff` apply | hypotheses can hold | [L382](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L382) |
| $`u = t - x^1`$ ($`F = \mathbb{R}`$, $`m = 0`$), a wave moving in the direction $`+x^1`$: $`P = (1, 1, 0, 0)`$, so the energy flux $`P^1 = 1`$ points in the direction of propagation | sign of $`P^a`$ | [L396](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L396) |
| $`u = t\,x^1`$ ($`F = \mathbb{R}`$, $`m = 0`$): $`\Box u = 0`$, $`P = (\tfrac12 (t^2 + (x^1)^2),\ -t x^1,\ 0,\ 0)`$, and $`\operatorname{div} P = \partial_t P^0 + \partial_1 P^1 = t - t = 0`$ | non-trivial check of the corollary | [L427](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L427) |
| $`u = t^2`$ ($`F = \mathbb{R}`$, $`m = 0`$), not a solution ($`\Box u = -2`$): $`P = (2t^2, 0, 0, 0)`$, $`\operatorname{div} P = 4t`$, and $`-\langle \Box u - m^2 u, \partial_t u\rangle = 4t`$ | sign of the energy identity | [L483](https://github.com/Oho1e/VectorFieldMethod/blob/417e63e61fe18c0edda69f5d0df4c8b3e0d31d23/VectorFieldMethod/Minkowski/EnergyMomentum.lean#L483) |
