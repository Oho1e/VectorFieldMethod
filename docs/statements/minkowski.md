# Minkowski coordinate layer: statements

Layer: `VectorFieldMethod/Minkowski/` (files `Spacetime.lean`, `Derivative.lean`,
`WaveOperator.lean`, `VectorFields.lean`, `Computations.lean`). All declarations are in the
namespace `VectorFieldMethod.Minkowski`. The links below point to commit
[`9896c75`](https://github.com/Oho1e/VectorFieldMethod/tree/9896c75cf0e393b40c485a05c3b6e9722be72a61), the commit of the pull request
that let the operators act on functions with values in a real normed space $`F`$ (to be replaced by
a commit of `main`). Design notes: [`docs/minkowski-layer.md`](../minkowski-layer.md). How to read the
entries: [`README.md`](README.md).

## Conventions

Quoted from the module docstring of
[`Spacetime.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Spacetime.lean#L22):

> * Signature `(-, +, +, +)`.
> * Spacetime indices `α : Fin 4`: `0` is time, `Fin.succ a` is the spatial component `a : Fin 3`.
>   The mathematical spatial indices `1, 2, 3` correspond to the Lean indices `0, 1, 2`.
> * `η * η = 1`, so the inverse metric `η^{αβ}` has the same entries as `η_{αβ}`.
> * The norm on `Spacetime` is the max norm of the product, `max |t| ‖x‖`, and `Spacetime` carries
>   no inner product. `‖p‖` is therefore *not* a spacetime distance and is not used as one.

Quoted from the docstring of `spaceCoord`
([`Spacetime.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Spacetime.lean#L52)):

> The Lean index `a = 0, 1, 2`
> corresponds to the mathematical index `1, 2, 3`. Spatial indices are raised and lowered without
> changing the value: `x_a = x^a`.

Quoted from the module docstring of
[`WaveOperator.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/WaveOperator.lean#L34)
(sign conventions):

> With the signature `(-, +, +, +)`, `□ = -∂_t² + Δ`. LeFloch–Ma write `□ = ∂_t² - Δ`, which is
> `-□` in the convention of this file, and write the Klein–Gordon operator as `□u + m²u` with their
> `□`, which is `-(□u - m²u)`, the negative of `kleinGordon m u` here.

**Notation in the Math lines below.** A point of Minkowski spacetime
$`\mathbb{R}^{1+3} = \mathbb{R}_t \times \mathbb{R}^3_x`$ is $`p = (t, x)`$ with
$`x = (x^1, x^2, x^3)`$, and $`e_1, e_2, e_3`$ is the standard basis of $`\mathbb{R}^3`$. Spatial
indices $`a, b, c`$ range over $`\{1, 2, 3\}`$ and spacetime indices $`\alpha, \beta`$ over
$`\{0, 1, 2, 3\}`$, as in the literature. The Lean argument for the mathematical spatial index
$`a`$ is the element $`a - 1`$ of `Fin 3`; the Lean argument for $`\alpha`$ is the element
$`\alpha`$ of `Fin 4`. Functions $`u, v : \mathbb{R}^{1+3} \to F`$ take values in a real normed
space $`F`$ (for instance $`F = \mathbb{R}`$ for real fields, $`F = \mathbb{C}`$ for complex
fields) and are arbitrary unless a hypothesis says otherwise; the coordinate functions
$`t, x^a, r`$ are real-valued, and the explicit computations are for $`F = \mathbb{R}`$.
$`Du(p)`$ is the Fréchet derivative, with the Lean convention $`Du(p) = 0`$ where $`u`$ is not
differentiable (see the README). Real coefficients such as $`\eta^{\alpha\beta}`$, $`m^2`$,
$`t`$, $`x^a`$ multiply values in $`F`$ by scalar multiplication, written `•` in Lean (for
$`F = \mathbb{R}`$ it is the product `*`).

## Context

The `variable` lines of the layer declare the types of the letters used in the statements. Their
only hypotheses are the structural ones `[NormedAddCommGroup F] [NormedSpace ℝ F]` (and the same
for `G`): $`F`$ and $`G`$ are real normed spaces. $`F`$ is the space of values of $`u, v`$; $`G`$
is the target of a continuous linear map $`T : F \to G`$ in the commutation lemmas.

[`Derivative.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L60):

```lean
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {V : Spacetime → Spacetime} {u v : Spacetime → F} {p : Spacetime} {n : ℕ∞ω}
```

[`WaveOperator.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/WaveOperator.lean#L52):

```lean
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {u v : Spacetime → F} {p : Spacetime} {n : ℕ∞ω}
```

[`VectorFields.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L41):

```lean
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {u v : Spacetime → F} {p : Spacetime} {n : ℕ∞ω}
```

`F` is an implicit argument of every operator: in `∂ₜ u` or `□ u` it is inferred from the type of
`u`.

## Definitions

### Minkowski spacetime

- **Math.** $`\mathbb{R}^{1+3} = \mathbb{R} \times \mathbb{R}^3`$, with points $`p = (t, x)`$: the
  first component is the time $`t`$, the second the spatial point $`x \in \mathbb{R}^3`$ (with its
  Euclidean structure).
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.Spacetime`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Spacetime.lean#L45)

```lean
abbrev Spacetime : Type := ℝ × EuclideanSpace ℝ (Fin 3)
```

- **Notes.** The norm Lean puts on this product is $`\max(\lvert t\rvert, \lvert x\rvert)`$ and
  there is no inner product; only the induced topology (the usual one on $`\mathbb{R}^4`$) and the
  linear structure matter for derivatives. The Minkowski form enters only through
  `minkowskiMetric`.

### Time coordinate $`t`$

- **Math.** $`t(p) = t`$ for $`p = (t, x)`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.timeCoord`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Spacetime.lean#L50)

```lean
def timeCoord (p : Spacetime) : ℝ := p.1
```

### Spatial coordinates $`x^a`$

- **Math.** For $`a \in \{1, 2, 3\}`$, $`x^a(p) = x^a`$ for $`p = (t, x)`$; also written $`x_a`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.spaceCoord`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Spacetime.lean#L55)

```lean
def spaceCoord (a : Fin 3) (p : Spacetime) : ℝ := p.2 a
```

- **Notes.** `spaceCoord 0`, `spaceCoord 1`, `spaceCoord 2` are $`x^1, x^2, x^3`$.

### Radius $`r = \lvert x\rvert`$

- **Math.** $`r(p) = \lvert x\rvert = \big(\sum_{a=1}^3 (x^a)^2\big)^{1/2}`$ for $`p = (t, x)`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.radius`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Spacetime.lean#L59)

```lean
def radius (p : Spacetime) : ℝ := ‖p.2‖
```

- **Notes.** `‖p.2‖` is the Euclidean norm of $`x`$, since `p.2 : EuclideanSpace ℝ (Fin 3)`. The
  identity $`r^2 = \sum_a (x^a)^2`$ is `radius_sq`. $`r`$ is not differentiable at $`x = 0`$, where
  Lean's derivatives of $`r`$ are junk zeros; the computations below only differentiate $`r^2`$.

### Minkowski metric $`\eta`$

- **Math.** $`\eta = (\eta_{\alpha\beta})_{\alpha, \beta = 0}^{3} = \operatorname{diag}(-1, 1, 1, 1)`$,
  signature $`(-, +, +, +)`$, with $`0`$ the time index. Notation: $`\eta`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.minkowskiMetric`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Spacetime.lean#L80)

```lean
def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (Fin.cons (-1) fun _ ↦ 1)

@[inherit_doc] scoped notation "η" => minkowskiMetric
```

- **Notes.** `Fin.cons (-1) fun _ ↦ 1` is the tuple $`(-1, 1, 1, 1)`$. The inverse metric
  $`\eta^{\alpha\beta}`$ is not a separate definition: it has the same entries
  (`minkowskiMetric_mul_self`, `inv_minkowskiMetric`).

### Derivative along a vector field

- **Math.** For a map $`V : \mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$ (the components
  $`V(p) = (V^0(p), V^1(p), V^2(p), V^3(p))`$ of the vector field $`V^\alpha \partial_\alpha`$) and
  $`u : \mathbb{R}^{1+3} \to F`$,
  ```math
  (Vu)(p) = Du(p)\,V(p) \qquad (= V^\alpha(p)\, \partial_\alpha u(p) \text{ if } u \text{ is differentiable at } p).
  ```
- **Hypotheses.** $`F`$ is a real normed space; $`V`$ and $`u`$ are arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.derivAlong`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L97)

```lean
def derivAlong (V : Spacetime → Spacetime) (u : Spacetime → F) : Spacetime → F :=
  fun p ↦ fderiv ℝ u p (V p)
```

- **Notes.** Where $`u`$ is not differentiable, $`(Vu)(p) = 0`$ (junk). All first-order operators
  of the layer ($`\partial_t, \partial_a, \partial_\alpha, \Omega_{ab}, L_a, S`$) are `derivAlong`
  of a named component field.

### Component field of $`\partial_t`$

- **Math.** The constant map $`p \mapsto (1, 0) \in \mathbb{R} \times \mathbb{R}^3`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.timeField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L180)

```lean
def timeField : Spacetime → Spacetime :=
  fun _ ↦ (1, 0)
```

### Component field of $`\partial_a`$

- **Math.** For $`a \in \{1, 2, 3\}`$, the constant map $`p \mapsto (0, e_a)`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.spaceField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L184)

```lean
def spaceField (a : Fin 3) : Spacetime → Spacetime :=
  fun _ ↦ (0, EuclideanSpace.single a 1)
```

- **Notes.** For the Lean index `a`, `EuclideanSpace.single a 1` is $`e_{a+1}`$.

### Component field of $`\partial_\alpha`$

- **Math.** For $`\alpha \in \{0, 1, 2, 3\}`$, the constant map $`p \mapsto E_\alpha`$, where
  $`E_0 = (1, 0)`$ and $`E_a = (0, e_a)`$ for $`a = 1, 2, 3`$ (the standard basis of
  $`\mathbb{R}^{1+3}`$).
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.coordField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L189)

```lean
def coordField (α : Fin 4) : Spacetime → Spacetime :=
  Fin.cases (motive := fun _ ↦ Spacetime → Spacetime) timeField spaceField α
```

- **Notes.** `Fin.cases timeField spaceField α` is `timeField` for $`\alpha = 0`$ and
  `spaceField a` for `α = Fin.succ a`; the `motive` argument only tells Lean the type of the
  result.

### Time derivative $`\partial_t`$

- **Math.** $`\partial_t u(p) = Du(p)\,(1, 0)`$, the partial derivative of $`u`$ in $`t`$ at $`p`$
  when $`u`$ is differentiable at $`p`$. Notation: $`\partial_t`$ (Lean `∂ₜ`).
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.timeDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L203)

```lean
def timeDeriv : (Spacetime → F) → Spacetime → F :=
  derivAlong timeField

@[inherit_doc] scoped notation "∂ₜ" => timeDeriv
```

- **Notes.** If $`u`$ is not differentiable at $`p`$, then `∂ₜ u p = 0`, even if the partial
  derivative $`\partial u / \partial t`$ exists at $`p`$. By definition (`timeDeriv_apply`, `rfl`),
  `∂ₜ u p = fderiv ℝ u p (1, 0)`.

### Spatial derivative $`\partial_a`$

- **Math.** For $`a \in \{1, 2, 3\}`$, $`\partial_a u(p) = Du(p)\,(0, e_a)`$, the partial
  derivative of $`u`$ in $`x^a`$ when $`u`$ is differentiable at $`p`$. Notation: Lean
  `∂ₓ[a - 1]`.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.spaceDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L207)

```lean
def spaceDeriv (a : Fin 3) : (Spacetime → F) → Spacetime → F :=
  derivAlong (spaceField a)

@[inherit_doc] scoped notation "∂ₓ[" a "]" => spaceDeriv a
```

- **Notes.** `∂ₓ[0]`, `∂ₓ[1]`, `∂ₓ[2]` are $`\partial_1, \partial_2, \partial_3`$. Junk value $`0`$
  at points where $`u`$ is not differentiable, as for $`\partial_t`$.

### Spacetime derivative $`\partial_\alpha`$

- **Math.** For $`\alpha \in \{0, 1, 2, 3\}`$, $`\partial_\alpha u(p) = Du(p)\,E_\alpha`$ with
  $`E_\alpha`$ as in `coordField`; so $`\partial_0 = \partial_t`$ and $`\partial_a`$
  ($`a = 1, 2, 3`$) is the spatial derivative. Notation: Lean `∂[α]`.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.partialDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L211)

```lean
def partialDeriv (α : Fin 4) : (Spacetime → F) → Spacetime → F :=
  derivAlong (coordField α)

@[inherit_doc] scoped notation "∂[" α "]" => partialDeriv α
```

- **Notes.** Here Lean and mathematical indices agree: `∂[0] = ∂ₜ` (`partialDeriv_zero`) and
  `∂[1] = ∂ₓ[0]`, `∂[2] = ∂ₓ[1]`, `∂[3] = ∂ₓ[2]` (`partialDeriv_one`, `_two`, `_three`); all hold by
  definition.

### Wave operator $`\Box`$

- **Math.** For any $`u`$,
  ```math
  \Box u(p) = \sum_{\alpha=0}^{3} \sum_{\beta=0}^{3} \eta^{\alpha\beta}\, \partial_\alpha \partial_\beta u(p),
  ```
  where the coefficients are the entries of $`\eta`$ (equal to those of $`\eta^{-1}`$). Notation:
  $`\Box`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.dAlembertian`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/WaveOperator.lean#L61)

```lean
def dAlembertian (u : Spacetime → F) : Spacetime → F :=
  fun p ↦ ∑ α, ∑ β, η α β • ∂[α] (∂[β] u) p

@[inherit_doc] scoped notation "□" => dAlembertian
```

- **Notes.** $`\Box = -\partial_t^2 + \Delta`$ (`dAlembertian_eq`); LeFloch–Ma's
  $`\Box = \partial_t^2 - \Delta`$ is $`-\Box`$ here. The second derivatives are iterated `∂[α]`,
  so at points where $`u`$ or $`\partial_\beta u`$ is not differentiable they contain junk zeros. The
  real coefficient `η α β` acts on the value `∂[α] (∂[β] u) p : F` by `•`; for $`F = \mathbb{R}`$
  this is the product, and `□ u p = ∑ α, ∑ β, η α β * ∂[α] (∂[β] u) p` holds by `rfl` (an `example`
  in the "Sanity checks" section of `Computations.lean`).

### Klein–Gordon operator

- **Math.** For $`m \in \mathbb{R}`$ and any $`u`$, $`\mathrm{KG}_m u(p) = \Box u(p) - m^2 u(p)`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.kleinGordon`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/WaveOperator.lean#L101)

```lean
def kleinGordon (m : ℝ) (u : Spacetime → F) : Spacetime → F :=
  fun p ↦ □ u p - m ^ 2 • u p
```

- **Notes.** LeFloch–Ma's Klein–Gordon operator $`\Box u + m^2 u`$ (with their
  $`\Box = \partial_t^2 - \Delta`$) is `-(kleinGordon m u)`. Only $`m^2`$ enters, so the sign of
  $`m`$ is irrelevant. For $`F = \mathbb{C}`$ this is the complex Klein–Gordon operator; `m ^ 2 • u p`
  is $`m^2 u(p)`$ with the real scalar $`m^2`$.

### Component field of the rotation $`\Omega_{ab}`$

- **Math.** For $`a, b \in \{1, 2, 3\}`$, the map $`p = (t, x) \mapsto (0,\ x^a e_b - x^b e_a)`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.rotationField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L49)

```lean
def rotationField (a b : Fin 3) : Spacetime → Spacetime :=
  fun p ↦
    (0, spaceCoord a p • EuclideanSpace.single b 1 - spaceCoord b p • EuclideanSpace.single a 1)
```

### Rotation $`\Omega_{ab}`$

- **Math.** For $`a, b \in \{1, 2, 3\}`$, $`\Omega_{ab} u(p) = Du(p)\,(0,\ x^a e_b - x^b e_a)`$,
  that is,
  ```math
  \Omega_{ab} u = x^a\, \partial_b u - x^b\, \partial_a u .
  ```
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.rotation`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L54)

```lean
def rotation (a b : Fin 3) : (Spacetime → F) → Spacetime → F :=
  derivAlong (rotationField a b)
```

- **Notes.** The displayed formula is the lemma `rotation_eq`
  (`rotation a b u p = spaceCoord a p • ∂ₓ[b] u p - spaceCoord b p • ∂ₓ[a] u p`), which holds for
  every $`u`$ and $`p`$ without hypotheses (both sides use the same `fderiv ℝ u p`). $`\Omega_{ab}`$ is defined for
  all nine pairs; $`\Omega_{ba} = -\Omega_{ab}`$ (`rotation_swap`) and $`\Omega_{aa} = 0`$
  (`rotation_self`), so three are independent.

### Component field of the boost $`L_a`$

- **Math.** For $`a \in \{1, 2, 3\}`$, the map $`p = (t, x) \mapsto (x^a,\ t\, e_a)`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.boostField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L58)

```lean
def boostField (a : Fin 3) : Spacetime → Spacetime :=
  fun p ↦ (spaceCoord a p, timeCoord p • EuclideanSpace.single a 1)
```

### Lorentz boost $`L_a`$

- **Math.** For $`a \in \{1, 2, 3\}`$, $`L_a u(p) = Du(p)\,(x^a,\ t\, e_a)`$, that is,
  ```math
  L_a u = t\, \partial_a u + x^a\, \partial_t u .
  ```
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.boost`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L62)

```lean
def boost (a : Fin 3) : (Spacetime → F) → Spacetime → F :=
  derivAlong (boostField a)
```

- **Notes.** The displayed formula is the lemma `boost_eq`
  (`boost a u p = timeCoord p • ∂ₓ[a] u p + spaceCoord a p • ∂ₜ u p`, no hypotheses).

### Component field of the scaling $`S`$

- **Math.** The identity map $`p = (t, x) \mapsto (t, x)`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.scalingField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L67)

```lean
def scalingField : Spacetime → Spacetime :=
  fun p ↦ p
```

### Scaling vector field $`S`$

- **Math.** $`S u(p) = Du(p)\,p`$, that is,
  ```math
  S u = t\, \partial_t u + \sum_{a=1}^{3} x^a\, \partial_a u .
  ```
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.scaling`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L71)

```lean
def scaling : (Spacetime → F) → Spacetime → F :=
  derivAlong scalingField
```

- **Notes.** The displayed formula is the lemma `scaling_eq`
  (`scaling u p = timeCoord p • ∂ₜ u p + ∑ a, spaceCoord a p • ∂ₓ[a] u p`, no hypotheses). With the four
  translations $`\partial_\alpha`$, the three rotations $`\Omega_{ab}`$ ($`a \lt b`$) and the three
  boosts, this gives the 11 vector fields.

## Main theorems

### The inverse metric has the same entries

- **Math.** $`\eta\,\eta = I_4`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.minkowskiMetric_mul_self`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Spacetime.lean#L101)

```lean
theorem minkowskiMetric_mul_self : η * η = 1
```

- **Notes.** `*` is matrix multiplication and `1` the identity matrix.

### Inverse metric

- **Math.** $`\eta^{-1} = \eta`$, so $`\eta^{\alpha\beta} = \eta_{\alpha\beta}`$ for all
  $`\alpha, \beta`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.inv_minkowskiMetric`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Spacetime.lean#L108)

```lean
theorem inv_minkowskiMetric : η⁻¹ = η
```

- **Notes.** Mathlib's matrix inverse `⁻¹` is defined for every square matrix (with a junk value
  for singular ones); since $`\eta\eta = I_4`$, here it is the genuine inverse.

### Explicit form of the wave operator

- **Math.** For every $`u : \mathbb{R}^{1+3} \to F`$ and every $`p`$,
  ```math
  \Box u(p) = -\partial_t \partial_t u(p) + \sum_{a=1}^{3} \partial_a \partial_a u(p).
  ```
- **Hypotheses.** $`F`$ is a real normed space; no regularity of $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.dAlembertian_eq`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/WaveOperator.lean#L71)

```lean
theorem dAlembertian_eq (u : Spacetime → F) (p : Spacetime) :
    □ u p = -∂ₜ (∂ₜ u) p + ∑ a, ∂ₓ[a] (∂ₓ[a] u) p
```

- **Notes.** No regularity is needed: the identity only evaluates the entries of $`\eta`$ in the
  double sum defining $`\Box`$ (the junk values, if any, are the same on both sides). For
  $`u \in C^2`$ it is $`\Box = -\partial_t^2 + \Delta`$.

### Symmetry of second derivatives at a point

- **Math.** Let $`\alpha, \beta \in \{0, 1, 2, 3\}`$, $`p \in \mathbb{R}^{1+3}`$, and let $`u`$ be
  $`C^2`$ on a neighbourhood of $`p`$. Then
  $`\partial_\alpha \partial_\beta u(p) = \partial_\beta \partial_\alpha u(p)`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is $`C^2`$ at $`p`$ (`ContDiffAt ℝ 2 u p`).
- **Lean.** `VectorFieldMethod.Minkowski.partialDeriv_comm_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L375)

```lean
theorem partialDeriv_comm_apply (α β : Fin 4) (hu : ContDiffAt ℝ 2 u p) :
    ∂[α] (∂[β] u) p = ∂[β] (∂[α] u) p
```

- **Notes.** `u` and `p` are the implicit variables of the *Context* section.

### Symmetry of second derivatives

- **Math.** Let $`\alpha, \beta \in \{0, 1, 2, 3\}`$ and $`u \in C^2(\mathbb{R}^{1+3})`$. Then
  $`\partial_\alpha \partial_\beta u = \partial_\beta \partial_\alpha u`$ on $`\mathbb{R}^{1+3}`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is $`C^2`$ (`ContDiff ℝ 2 u`).
- **Lean.** `VectorFieldMethod.Minkowski.partialDeriv_comm`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L383)

```lean
theorem partialDeriv_comm (α β : Fin 4) (hu : ContDiff ℝ 2 u) :
    ∂[α] (∂[β] u) = ∂[β] (∂[α] u)
```

### Additivity of $`\Box`$ at a point

- **Math.** Let $`p \in \mathbb{R}^{1+3}`$ and let $`u, v`$ be $`C^2`$ on a neighbourhood of
  $`p`$. Then $`\Box(u + v)(p) = \Box u(p) + \Box v(p)`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ and $`v`$ are $`C^2`$ at $`p`$.
- **Lean.** `VectorFieldMethod.Minkowski.dAlembertian_add`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/WaveOperator.lean#L128)

```lean
theorem dAlembertian_add (hu : ContDiffAt ℝ 2 u p) (hv : ContDiffAt ℝ 2 v p) :
    □ (u + v) p = □ u p + □ v p
```

- **Notes.** The hypotheses are needed because of the junk value of `fderiv` (see the README).
  The same statement for the Klein–Gordon operator is `kleinGordon_add`. Homogeneity
  $`\Box(cu) = c\,\Box u`$ needs no hypothesis (`dAlembertian_smul`).

### Additivity of $`\Box`$

- **Math.** Let $`u, v \in C^2(\mathbb{R}^{1+3})`$. Then $`\Box(u + v) = \Box u + \Box v`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ and $`v`$ are $`C^2`$.
- **Lean.** `VectorFieldMethod.Minkowski.dAlembertian_add_of_contDiff`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/WaveOperator.lean#L146)

```lean
theorem dAlembertian_add_of_contDiff (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    □ (u + v) = □ u + □ v
```

- **Notes.** The Klein–Gordon version is `kleinGordon_add_of_contDiff`.

## Linearity and smoothness (representative entries)

### Linearity of a first-order operator (representative)

- **Math.** Let $`V : \mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$ be any map, $`p \in \mathbb{R}^{1+3}`$,
  and let $`u, v`$ be differentiable at $`p`$. Then $`V(u + v)(p) = Vu(p) + Vv(p)`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ and $`v`$ are differentiable at $`p`$; no
  hypothesis on $`V`$.
- **Lean.** `VectorFieldMethod.Minkowski.derivAlong_add`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L120)

```lean
theorem derivAlong_add (V : Spacetime → Spacetime) (hu : DifferentiableAt ℝ u p)
    (hv : DifferentiableAt ℝ v p) :
    derivAlong V (u + v) p = derivAlong V u p + derivAlong V v p
```

- **Notes.** Naming pattern of the linearity lemmas, for `op` one of `derivAlong`, `timeDeriv`,
  `spaceDeriv`, `partialDeriv`, `rotation`, `boost`, `scaling`, `dAlembertian`, `kleinGordon`:
  - `op_smul`: $`\mathrm{op}(c\,u) = c\,\mathrm{op}(u)`$ for every real $`c \in \mathbb{R}`$ and every
    $`u`$, **without** hypotheses (for instance `derivAlong_smul`);
  - `op_const`: $`\mathrm{op}`$ of a constant function $`c \in F`$ is $`0`$;
  - `op_add`: additivity at a point $`p`$, assuming `DifferentiableAt ℝ u p` and
    `DifferentiableAt ℝ v p` for the first-order operators, and `ContDiffAt ℝ 2 u p`,
    `ContDiffAt ℝ 2 v p` for `dAlembertian_add` and `kleinGordon_add`;
  - `op_add_of_contDiff` (only for `dAlembertian`, `kleinGordon`): additivity as functions, for
    `ContDiff ℝ 2 u` and `ContDiff ℝ 2 v`.

  `derivAlong_const_mul` (`V (fun q ↦ c * u q) = fun q ↦ c * V u q`) is stated only for
  real-valued `u`, since it is about the product `*`; for general $`F`$ it is `derivAlong_smul`.

### Smoothness of a derivative (representative)

- **Math.** Let $`n \in \mathbb{N} \cup \{\infty, \omega\}`$, $`\alpha \in \{0, 1, 2, 3\}`$ and
  $`u \in C^{n+1}(\mathbb{R}^{1+3})`$. Then $`\partial_\alpha u \in C^n(\mathbb{R}^{1+3})`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is $`C^{n+1}`$ (with $`\infty + 1 = \infty`$, $`\omega + 1 = \omega`$;
  $`\omega`$ means analytic).
- **Lean.** `VectorFieldMethod.Minkowski.contDiff_partialDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L347)

```lean
theorem contDiff_partialDeriv (α : Fin 4) (hu : ContDiff ℝ (n + 1) u) :
    ContDiff ℝ n (∂[α] u)
```

- **Notes.** Naming pattern of the smoothness lemmas:
  - `contDiff_op` for `op` one of `timeDeriv`, `spaceDeriv`, `partialDeriv`, `rotation`, `boost`,
    `scaling`: $`C^{n+1} \to C^n`$; `contDiff_derivAlong` additionally assumes that the component
    field $`V`$ is $`C^n`$;
  - `contDiff_dAlembertian`, `contDiff_kleinGordon`: $`C^{n+2} \to C^n`$;
  - `contDiff_infty_op`: $`C^\infty \to C^\infty`$ (the case $`n = \infty`$);
  - `contDiffAt_partialDeriv`, `contDiffAt_derivAlong`: the same at a point
    (`ContDiffAt ℝ (n + 1) u p` gives `ContDiffAt ℝ n (∂[α] u) p`);
  - `contDiff_timeField`, `contDiff_rotationField`, ...: the component fields are $`C^n`$ for every
    $`n`$ (they are constant or linear).

## Commutation with continuous linear maps

These lemmas reduce statements about $`F`$-valued functions to their components, for instance the
real and imaginary parts of a complex field ($`T = \operatorname{Re}, \operatorname{Im} : \mathbb{C} \to \mathbb{R}`$)
or the components of a spinor field, and conversely embed real-valued computations into $`F`$
($`T = \mathbb{R} \hookrightarrow \mathbb{C}`$, `Complex.ofRealCLM`).

### First-order operators commute with continuous linear maps

- **Math.** Let $`F, G`$ be real normed spaces, $`T : F \to G`$ a continuous real-linear map,
  $`V : \mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$ any map, $`p \in \mathbb{R}^{1+3}`$, and let
  $`u : \mathbb{R}^{1+3} \to F`$ be differentiable at $`p`$. Then $`V(T \circ u)(p) = T\big(Vu(p)\big)`$.
- **Hypotheses.** $`F`$, $`G`$ are real normed spaces; $`T`$ is continuous and $`\mathbb{R}`$-linear;
  $`u`$ is differentiable at $`p`$; no hypothesis on $`V`$.
- **Lean.** `VectorFieldMethod.Minkowski.derivAlong_clm_comp`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L161)

```lean
theorem derivAlong_clm_comp (V : Spacetime → Spacetime) (T : F →L[ℝ] G)
    (hu : DifferentiableAt ℝ u p) : derivAlong V (T ∘ u) p = T (derivAlong V u p)
```

- **Notes.** `F →L[ℝ] G` is the type of continuous $`\mathbb{R}`$-linear maps and `T ∘ u` is the
  composition $`q \mapsto T(u(q))`$. The differentiability hypothesis is needed because of the junk
  value of `fderiv`. The same statement holds, with the same hypothesis, for each first-order
  operator: `timeDeriv_clm_comp`, `spaceDeriv_clm_comp`, `partialDeriv_clm_comp`
  (`Derivative.lean`) and `rotation_clm_comp`, `boost_clm_comp`, `scaling_clm_comp`
  (`VectorFields.lean`), for instance `∂ₜ (T ∘ u) p = T (∂ₜ u p)`.

### The wave operator commutes with continuous linear maps

- **Math.** Let $`F, G`$ be real normed spaces, $`T : F \to G`$ a continuous real-linear map,
  $`p \in \mathbb{R}^{1+3}`$, and let $`u : \mathbb{R}^{1+3} \to F`$ be $`C^2`$ on a neighbourhood of
  $`p`$. Then $`\Box(T \circ u)(p) = T\big(\Box u(p)\big)`$.
- **Hypotheses.** $`F`$, $`G`$ are real normed spaces; $`T`$ is continuous and $`\mathbb{R}`$-linear;
  $`u`$ is $`C^2`$ at $`p`$ (`ContDiffAt ℝ 2 u p`).
- **Lean.** `VectorFieldMethod.Minkowski.dAlembertian_clm_comp`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/WaveOperator.lean#L168)

```lean
theorem dAlembertian_clm_comp (T : F →L[ℝ] G) (hu : ContDiffAt ℝ 2 u p) :
    □ (T ∘ u) p = T (□ u p)
```

- **Notes.** It follows from `partialDeriv_partialDeriv_clm_comp`
  (`∂[α] (∂[β] (T ∘ u)) p = T (∂[α] (∂[β] u) p)` under the same hypothesis), which uses that
  $`\partial_\beta(T \circ u) = T \circ \partial_\beta u`$ on a neighbourhood of $`p`$.

### The Klein–Gordon operator commutes with continuous linear maps

- **Math.** Under the hypotheses of the previous entry, and for every $`m \in \mathbb{R}`$,
  $`\mathrm{KG}_m(T \circ u)(p) = T\big(\mathrm{KG}_m u(p)\big)`$.
- **Hypotheses.** $`F`$, $`G`$ are real normed spaces; $`T`$ is continuous and $`\mathbb{R}`$-linear;
  $`u`$ is $`C^2`$ at $`p`$.
- **Lean.** `VectorFieldMethod.Minkowski.kleinGordon_clm_comp`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/WaveOperator.lean#L173)

```lean
theorem kleinGordon_clm_comp (m : ℝ) (T : F →L[ℝ] G) (hu : ContDiffAt ℝ 2 u p) :
    kleinGordon m (T ∘ u) p = T (kleinGordon m u p)
```

- **Notes.** The "Sanity checks" section of `Computations.lean` uses these lemmas with
  `T = Complex.ofRealCLM` to compute $`\Box`$ and $`\mathrm{KG}_m`$ of the complex-valued function
  $`t^2`$, and with $`T(c) = c\,w`$ (`ContinuousLinearMap.toSpanSingleton ℝ w`) to show
  $`\Box(t^2 w) = -2w`$ for a vector $`w`$ of any real normed space.

## Checked computations

### Values of the operators on the coordinates and on quadratic functions

- **Math.** The following identities hold as equalities of functions on all of
  $`\mathbb{R}^{1+3}`$ (constants denote constant functions; $`\delta_{ab}`$ is the Kronecker
  delta; $`a, b, c \in \{1, 2, 3\}`$; in Lean $`\delta_{ab}`$ is `if a = b then 1 else 0`):

  | Statement | Lean name | File |
  | --- | --- | --- |
  | $`\partial_t t = 1`$, $`\partial_t x^b = 0`$, $`\partial_a t = 0`$, $`\partial_a x^b = \delta_{ab}`$ | [`timeDeriv_timeCoord`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L304), [`timeDeriv_spaceCoord`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L309), [`spaceDeriv_timeCoord`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L314), [`spaceDeriv_spaceCoord`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Derivative.lean#L319) | `Derivative.lean` |
  | $`\Box(t^2 - r^2) = -8`$, $`\Box(t^2) = -2`$, $`\Box\big((x^a)^2\big) = 2`$ | [`dAlembertian_timeCoord_sq_sub_radius_sq`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Computations.lean#L92), [`dAlembertian_timeCoord_sq`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Computations.lean#L102), [`dAlembertian_spaceCoord_sq`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Computations.lean#L108) | `Computations.lean` |
  | $`L_a t = x^a`$, $`L_a x^b = t\,\delta_{ab}`$ | [`boost_timeCoord`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L208), [`boost_spaceCoord`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L214) | `VectorFields.lean` |
  | $`L_a(t^2 - r^2) = 0`$ | [`boost_timeCoord_sq_sub_radius_sq`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Computations.lean#L129) | `Computations.lean` |
  | $`\Omega_{ab} x^c = \delta_{bc}\, x^a - \delta_{ac}\, x^b`$; $`\Omega_{ba} u = -\Omega_{ab} u`$ for every $`u`$ | [`rotation_spaceCoord`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L199), [`rotation_swap`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L129) | `VectorFields.lean` |
  | $`\Omega_{ab}(r^2) = 0`$ | [`rotation_radius_sq`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Computations.lean#L137) | `Computations.lean` |
  | $`S t = t`$, $`S x^a = x^a`$ | [`scaling_timeCoord`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L222), [`scaling_spaceCoord`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/VectorFields.lean#L228) | `VectorFields.lean` |
  | $`S(t^2 - r^2) = 2\,(t^2 - r^2)`$ | [`scaling_timeCoord_sq_sub_radius_sq`](https://github.com/Oho1e/VectorFieldMethod/blob/9896c75cf0e393b40c485a05c3b6e9722be72a61/VectorFieldMethod/Minkowski/Computations.lean#L144) | `Computations.lean` |

- **Hypotheses.** None: each identity holds for all points, and `rotation_swap` for every function
  $`u`$ (no differentiability needed).
- **Lean.** The names in the table, all in the namespace `VectorFieldMethod.Minkowski`; the links
  are permalinks to the declarations. The table reproduces the "Checked computations" table of
  [`docs/minkowski-layer.md`](../minkowski-layer.md).
- **Notes.** All functions in the table are real-valued: the operators are used with
  $`F = \mathbb{R}`$, inferred from `timeCoord`, `spaceCoord`, `radius`. In Lean the functions are
  written with `timeCoord`, `spaceCoord`, `radius`; for
  instance $`t^2 - r^2`$ is `fun p ↦ timeCoord p ^ 2 - radius p ^ 2` and the constant $`-8`$ is
  `fun _ ↦ -8`. The functions involved are polynomials in $`t, x`$ (note $`r^2 = \sum_a (x^a)^2`$,
  `radius_sq`), so no junk value of `fderiv` occurs.
