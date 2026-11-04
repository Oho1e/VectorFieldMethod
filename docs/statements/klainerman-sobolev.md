# The Klainerman–Sobolev inequality on hyperboloids: statements

Layer: `VectorFieldMethod/Minkowski/KlainermanSobolev.lean`, built on the Minkowski coordinate
layer (see [`minkowski.md`](minkowski.md) for the boosts $`L_a`$ and their conventions) and on
the Sobolev inequality layer on $`\mathbb{R}^3`$ (see [`euclidean-sobolev.md`](euclidean-sobolev.md)
for the weighted derivatives $`\Lambda_a`$ and the weighted inequality). All declarations are in
the namespace `VectorFieldMethod.Minkowski`. The links below point to commit
[`65434c1`](https://github.com/Oho1e/VectorFieldMethod/tree/65434c138668e720ea41dbd287fb6c1298ad00f9)
of `main`. How to read the
entries: [`README.md`](README.md). Background and proofs:
[`../hyperboloidal-sobolev.md`](../hyperboloidal-sobolev.md).

**Notation in the Math lines below.**
- A point of Minkowski spacetime $`\mathbb{R}^{1+3}`$ is $`p = (t, x)`$, time first, as in
  [`minkowski.md`](minkowski.md). $`\mathbb{R}^3`$ is `EuclideanSpace ℝ (Fin 3)` with Lebesgue
  measure (`volume`) and Euclidean norm $`\lvert x\rvert`$ (`‖x‖`). Spatial indices
  $`a, b, c \in \{1, 2, 3\}`$ are the Lean indices `a - 1 : Fin 3`, and $`e_a`$ is the standard
  basis vector `EuclideanSpace.single (a - 1) 1`.
- For $`s \in \mathbb{R}`$, $`\varphi_s(x) = \sqrt{s^2 + \lvert x\rvert^2}`$, written
  `√(s ^ 2 + ‖x‖ ^ 2)` in Lean, and
  ```math
  H_s = \{(t, x) \in \mathbb{R}^{1+3} : t = \varphi_s(x)\},
  ```
  written `hyperboloid s` (definition below). For $`s \neq 0`$ this is the upper sheet
  $`\{t^2 - \lvert x\rvert^2 = s^2,\ t \gt 0\}`$ of the hyperboloid.
- $`F`$ is a real normed space (see *Context*). The restriction of $`v : \mathbb{R}^{1+3} \to F`$ to
  $`H_s`$ is the function $`v|_{H_s}(x) = v(\varphi_s(x), x)`$ on $`\mathbb{R}^3`$
  (`restrictHyperboloid s v`, below).
- $`L_a v = t\,\partial_a v + x^a\,\partial_t v`$ is the Lorentz boost (`boost (a - 1) v`), and
  $`\Lambda_a w = \varphi_s\,\partial_a w`$, with $`\partial_a w(x) = Dw(x)\,e_a`$, is the weighted
  derivative of $`w : \mathbb{R}^3 \to \mathbb{R}`$ (`hyperboloidalWeightedDeriv s (a - 1) w`); it
  depends on $`s`$.
- $`\lVert g\rVert_{L^2}`$ is `eLpNorm g 2 volume`, the $`L^2`$ norm on $`\mathbb{R}^3`$, a value in
  $`[0, \infty]`$. The flat $`L^2`$ norm on $`H_s`$ is
  $`\lVert v\rVert_{L^2_f(H_s)} = \lVert v|_{H_s}\rVert_{L^2}`$, that is, the $`L^2`$ norm for the
  measure $`dx`$ transported to $`H_s`$ by $`x \mapsto (\varphi_s(x), x)`$ (not the measure induced
  on $`H_s`$ by the Minkowski metric).
- Derivatives follow the Lean convention that the derivative of a function at a point where it is
  not differentiable is $`0`$ (see the README).

## Context

The `variable` line of the file declares the type of values `F`:
- `[NormedAddCommGroup F] [NormedSpace ℝ F]`: $`F`$ is a real normed space, for instance
  $`\mathbb{R}`$ or $`\mathbb{C}`$. It is the space of values of the functions in the statements about
  the restriction itself (its definition, regularity, continuity, compact support and square
  integrability). The restriction formulas and the inequality are about real-valued functions
  only: their statements write `Spacetime → ℝ`.

[`KlainermanSobolev.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L62):

```lean
open MeasureTheory
open scoped ContDiff

namespace VectorFieldMethod.Minkowski

open VectorFieldMethod.EuclideanSobolev

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
```

`F` is an implicit argument, inferred from the function `v` or `u`. The definition
`restrictHyperboloid` uses no structure on `F`, and a few theorems drop the instances they do not
use (`omit [NormedSpace ℝ F] in` before `continuous_restrictHyperboloid`, for instance), which
only weakens their hypotheses. `volume` and `eLpNorm` are `MeasureTheory.volume` and
`MeasureTheory.eLpNorm`; `hyperboloidalWeightedDeriv` is
`VectorFieldMethod.EuclideanSobolev.hyperboloidalWeightedDeriv` (entry *The hyperboloidal weighted
derivative* of [`euclidean-sobolev.md`](euclidean-sobolev.md)); `boost`, `boostField`,
`Spacetime`, `timeCoord` and `spaceCoord` are the declarations of the Minkowski layer; and `ℕ∞ω`
(the type `WithTop ℕ∞` of smoothness orders: natural numbers, `∞` and `ω`) is the notation of the
scope `ContDiff`.

## Definitions

### The hyperboloid $`H_s`$

- **Math.** For $`s \in \mathbb{R}`$,
  $`H_s = \{(t, x) \in \mathbb{R}^{1+3} : t = \sqrt{s^2 + \lvert x\rvert^2}\}`$. For $`s \neq 0`$ it
  is the upper sheet $`\{t^2 - \lvert x\rvert^2 = s^2,\ t \gt 0\}`$ of the hyperboloid.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L75)

```lean
def hyperboloid (s : ℝ) : Set Spacetime :=
  {p | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)}
```

- **Notes.** `p.1` is the time $`t`$ and `p.2` the spatial point $`x`$ of $`p = (t, x)`$. The lemma
  `mem_hyperboloid` (`p ∈ hyperboloid s ↔ p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)`) holds by definition. The
  theorems below write "$`U`$ contains $`H_s`$" as `hyperboloid s ⊆ U`.

### The point of $`H_s`$ above $`x`$

- **Math.** For $`s \in \mathbb{R}`$ and $`x \in \mathbb{R}^3`$, the point
  $`(\varphi_s(x), x) = (\sqrt{s^2 + \lvert x\rvert^2}, x)`$ of $`H_s`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidPoint`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L83)

```lean
def hyperboloidPoint (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : Spacetime :=
  (√(s ^ 2 + ‖x‖ ^ 2), x)
```

- **Notes.** An auxiliary parametrization of $`H_s`$ by $`\mathbb{R}^3`$, used in the proofs. It is
  smooth for $`s \neq 0`$ (`contDiff_hyperboloidPoint`) and continuous for every $`s`$
  (`continuous_hyperboloidPoint`); `hyperboloidPoint_mem_hyperboloid` states that it lies on
  $`H_s`$.

### Restriction to the hyperboloid $`H_s`$

- **Math.** For $`s \in \mathbb{R}`$ and $`v : \mathbb{R}^{1+3} \to F`$, the function
  ```math
  v|_{H_s} : \mathbb{R}^3 \to F, \qquad v|_{H_s}(x) = v\big(\sqrt{s^2 + \lvert x\rvert^2},\ x\big).
  ```
- **Hypotheses.** None: this is a definition, for every real $`s`$ and every function $`v`$; no
  structure on $`F`$ is used.
- **Lean.** `VectorFieldMethod.Minkowski.restrictHyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L93)

```lean
def restrictHyperboloid (s : ℝ) (v : Spacetime → F) : EuclideanSpace ℝ (Fin 3) → F :=
  fun x ↦ v (√(s ^ 2 + ‖x‖ ^ 2), x)
```

- **Notes.** The restriction formulas and the inequality below use it with $`F = \mathbb{R}`$, since
  $`\Lambda_a`$ is defined for real-valued functions. The definition makes sense for every $`s`$
  (for $`s = 0`$ it restricts to the light cone $`t = \lvert x\rvert`$); the theorems below assume
  $`s \neq 0`$ or $`s \gt 0`$ where needed. By definition (`restrictHyperboloid_eq_comp`, `rfl`),
  `restrictHyperboloid s v = v ∘ hyperboloidPoint s`.

## Main theorems

### The restriction formula at a point

- **Math.** Let $`s \neq 0`$, $`a \in \{1, 2, 3\}`$, $`x \in \mathbb{R}^3`$, and let
  $`v : \mathbb{R}^{1+3} \to \mathbb{R}`$ be differentiable at the point $`(\varphi_s(x), x)`$ of
  $`H_s`$. Then
  ```math
  \Lambda_a\big(v|_{H_s}\big)(x) = (L_a v)|_{H_s}(x),
  \quad\text{that is,}\quad
  \varphi_s(x)\, \partial_a\big(v|_{H_s}\big)(x) = \big(t\, \partial_a v + x^a\, \partial_t v\big)(\varphi_s(x), x).
  ```
- **Hypotheses.** $`s \neq 0`$; $`v`$ is (Fréchet) differentiable at the single point
  $`(\varphi_s(x), x)`$; nothing is assumed about $`v`$ elsewhere.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalWeightedDeriv_restrictHyperboloid_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L127)

```lean
theorem hyperboloidalWeightedDeriv_restrictHyperboloid_apply {s : ℝ} (hs : s ≠ 0) (a : Fin 3)
    {v : Spacetime → ℝ} {x : EuclideanSpace ℝ (Fin 3)}
    (hv : DifferentiableAt ℝ v (√(s ^ 2 + ‖x‖ ^ 2), x)) :
    hyperboloidalWeightedDeriv s a (restrictHyperboloid s v) x =
      restrictHyperboloid s (boost a v) x
```

- **Notes.** Proof: by the chain rule and $`\partial_a \varphi_s = x^a / \varphi_s`$,
  $`\partial_a(v|_{H_s})(x) = Dv(\varphi_s(x), x)\,(x^a / \varphi_s(x),\ e_a)`$; multiplying by
  $`\varphi_s(x)`$, which is the value of $`t`$ at the point, gives
  $`Dv(\varphi_s(x), x)\,(x^a,\ t\, e_a)`$, the boost field at that point. The hypothesis
  $`s \neq 0`$ makes $`\varphi_s`$ differentiable at every $`x`$ (with $`\varphi_s \ge \lvert s\rvert \gt 0`$).
  Without differentiability of $`v`$ at the point, Lean's junk value $`Dv = 0`$ makes the right
  side $`0`$ while the left side need not be. The sanity checks test the formula on $`v = t`$
  (where only the term $`x^a \partial_t v`$ contributes) and on $`v = x^b`$ (where only the term
  $`t\, \partial_a v`$ contributes).

### The restriction formula as an equality of functions

- **Math.** Let $`s \neq 0`$ and $`a \in \{1, 2, 3\}`$. If $`v : \mathbb{R}^{1+3} \to \mathbb{R}`$ is
  differentiable at every point of $`H_s`$, then $`\Lambda_a(v|_{H_s}) = (L_a v)|_{H_s}`$ on
  $`\mathbb{R}^3`$. In particular this holds if $`u`$ is differentiable on an open set
  $`U \supseteq H_s`$ (second statement, with $`u`$ in place of $`v`$).
- **Hypotheses.** $`s \neq 0`$; first statement: $`v`$ is differentiable at
  $`(\varphi_s(x), x)`$ for every $`x \in \mathbb{R}^3`$; second statement: $`U`$ is open, contains
  $`H_s`$, and $`u`$ is differentiable at every point of $`U`$.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalWeightedDeriv_restrictHyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L146),
  and `VectorFieldMethod.Minkowski.hyperboloidalWeightedDeriv_restrictHyperboloid_of_differentiableOn`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L162)

```lean
theorem hyperboloidalWeightedDeriv_restrictHyperboloid {s : ℝ} (hs : s ≠ 0) (a : Fin 3)
    {v : Spacetime → ℝ}
    (hv : ∀ x : EuclideanSpace ℝ (Fin 3), DifferentiableAt ℝ v (√(s ^ 2 + ‖x‖ ^ 2), x)) :
    hyperboloidalWeightedDeriv s a (restrictHyperboloid s v) =
      restrictHyperboloid s (boost a v)

theorem hyperboloidalWeightedDeriv_restrictHyperboloid_of_differentiableOn {s : ℝ}
    (hs : s ≠ 0) {u : Spacetime → ℝ} {U : Set Spacetime} (hU : IsOpen U)
    (hHU : hyperboloid s ⊆ U) (hu : DifferentiableOn ℝ u U) (a : Fin 3) :
    hyperboloidalWeightedDeriv s a (restrictHyperboloid s u) =
      restrictHyperboloid s (boost a u)
```

- **Notes.** Both are the previous entry at every point. In the second one, openness of $`U`$
  turns differentiability on $`U`$ (`DifferentiableOn ℝ u U`) into differentiability at the points
  of $`H_s`$.

### The second-order restriction formula

- **Math.** Let $`s \neq 0`$, let $`U \subseteq \mathbb{R}^{1+3}`$ be an open set containing
  $`H_s`$, and let $`u : \mathbb{R}^{1+3} \to \mathbb{R}`$ be of class $`C^2`$ on $`U`$. Then for all
  $`a, b \in \{1, 2, 3\}`$,
  ```math
  \Lambda_a \Lambda_b \big(u|_{H_s}\big) = (L_a L_b u)|_{H_s} \qquad \text{on } \mathbb{R}^3 .
  ```
- **Hypotheses.** $`s \neq 0`$; $`U`$ is open and $`H_s \subseteq U`$; $`u`$ is $`C^2`$ on $`U`$
  (`ContDiffOn ℝ 2 u U`).
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L173)

```lean
theorem hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid {s : ℝ}
    (hs : s ≠ 0) {u : Spacetime → ℝ} {U : Set Spacetime} (hU : IsOpen U)
    (hHU : hyperboloid s ⊆ U) (hu : ContDiffOn ℝ 2 u U) (a b : Fin 3) :
    hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b (restrictHyperboloid s u)) =
      restrictHyperboloid s (boost a (boost b u))
```

- **Notes.** The indices are in the same order on both sides: the outer operator is
  $`\Lambda_a`$, resp. $`L_a`$. The order matters, since $`[L_a, L_b] = \Omega_{ab}`$ is nonzero for
  $`a \neq b`$; the sanity check applying the theorem to $`u = x^c`$ gives
  $`\Lambda_a \Lambda_b x^c = \delta_{bc}\, x^a`$, which is not symmetric in $`a, b`$. Proof: the
  first-order formula as functions gives $`\Lambda_b(u|_{H_s}) = (L_b u)|_{H_s}`$; since $`u`$ is
  $`C^2`$ near each point of $`H_s`$, $`L_b u`$ is $`C^1`$ there, and the first-order formula at each
  point, applied to $`v = L_b u`$, gives the claim. The values of $`u`$ outside $`U`$ play no role.

### Regularity of the restriction

- **Math.** Let $`s \neq 0`$, $`n \in \mathbb{N} \cup \{\infty, \omega\}`$, let
  $`U \subseteq \mathbb{R}^{1+3}`$ be an open set containing $`H_s`$, and let
  $`u : \mathbb{R}^{1+3} \to F`$ be of class $`C^n`$ on $`U`$. Then
  $`u|_{H_s} \in C^n(\mathbb{R}^3)`$. In particular, if $`u`$ is $`C^2`$ on $`U`$, then
  $`u|_{H_s}`$ is $`C^2`$ on $`\mathbb{R}^3`$.
- **Hypotheses.** $`F`$ is a real normed space; $`s \neq 0`$; $`U`$ is open and $`H_s \subseteq U`$;
  $`u`$ is $`C^n`$ on $`U`$.
- **Lean.** `VectorFieldMethod.Minkowski.contDiff_restrictHyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L195)

```lean
theorem contDiff_restrictHyperboloid {s : ℝ} (hs : s ≠ 0) {n : ℕ∞ω} {u : Spacetime → F}
    {U : Set Spacetime} (hU : IsOpen U) (hHU : hyperboloid s ⊆ U) (hu : ContDiffOn ℝ n u U) :
    ContDiff ℝ n (restrictHyperboloid s u)
```

- **Notes.** `n : ℕ∞ω` is a natural number, `∞` ($`C^\infty`$) or `ω` (real analytic); the case
  used below is `n = 2`. The proof composes $`u`$ with $`x \mapsto (\varphi_s(x), x)`$, which is
  smooth (and analytic) because $`s^2 + \lvert x\rvert^2 \gt 0`$ for $`s \neq 0`$
  (`contDiff_hyperboloidPoint`). For $`s = 0`$ and $`n \ge 1`$ the statement fails in general: for
  $`u = t`$ the restriction $`u|_{H_0}(x) = \lvert x\rvert`$ is not differentiable at $`0`$. For
  $`n = 0`$ the conclusion holds for every $`s`$, since the restriction of a function continuous on
  $`U`$ is continuous (`continuous_restrictHyperboloid_of_continuousOn`).

### The Klainerman–Sobolev inequality on hyperboloids

- **Math.** There is an absolute constant $`C \ge 0`$ such that for all $`s \gt 0`$, every open set
  $`U \subseteq \mathbb{R}^{1+3}`$ containing $`H_s`$, every $`u : \mathbb{R}^{1+3} \to \mathbb{R}`$ of
  class $`C^2`$ on $`U`$ and every $`x_0 \in \mathbb{R}^3`$, with
  $`t_0 = \varphi_s(x_0) = \sqrt{s^2 + \lvert x_0\rvert^2}`$,
  ```math
  t_0^{3/2}\, \lvert u(t_0, x_0)\rvert \le C \Big( \lVert u\rVert_{L^2_f(H_s)} + \sum_{a=1}^{3} \lVert L_a u\rVert_{L^2_f(H_s)} + \sum_{a=1}^{3} \sum_{b=1}^{3} \lVert L_a L_b u\rVert_{L^2_f(H_s)} \Big).
  ```
  Since $`(t_0, x_0)`$ runs over all of $`H_s`$ when $`x_0`$ runs over $`\mathbb{R}^3`$, this is
  ```math
  \sup_{H_s} t^{3/2} \lvert u\rvert \le C \sum_{\lvert J\rvert \le 2} \lVert L^J u\rVert_{L^2_f(H_s)},
  ```
  where $`L^J`$ runs over the $`1 + 3 + 9 = 13`$ ordered products $`1`$, $`L_a`$, $`L_a L_b`$.
- **Hypotheses.** $`s \gt 0`$; $`U`$ is open and contains $`H_s`$; $`u`$ is $`C^2`$ on $`U`$. There
  is no integrability, decay or support assumption.
- **Lean.** `VectorFieldMethod.Minkowski.exists_klainermanSobolev_hyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L211)

```lean
theorem exists_klainermanSobolev_hyperboloid :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ (u : Spacetime → ℝ) (U : Set Spacetime), IsOpen U →
      hyperboloid s ⊆ U → ContDiffOn ℝ 2 u U →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |u (√(s ^ 2 + ‖x₀‖ ^ 2), x₀)|) ≤
        (C : ENNReal) *
          (eLpNorm (restrictHyperboloid s u) 2 volume +
            ∑ a, eLpNorm (restrictHyperboloid s (boost a u)) 2 volume +
            ∑ a, ∑ b, eLpNorm (restrictHyperboloid s (boost a (boost b u))) 2 volume)
```

- **Notes.**
  - `C : NNReal` is quantified before `s`, `u`, `U` and `x₀`, so it is an absolute constant: it
    does not depend on $`s`$, on $`u`$, on $`U`$ or on the point. The proof takes the constant
    $`C`$ given by `EuclideanSobolev.exists_hyperboloidalSobolev` (Theorem 2 of
    [`euclidean-sobolev.md`](euclidean-sobolev.md)).
  - The inequality is stated in `ℝ≥0∞`: the left side is `ENNReal.ofReal` of a nonnegative real,
    and the right side may be `∞`, in which case the inequality holds trivially. It is finite for
    every $`u`$ of class $`C^2`$ with compact support (`eLpNorm_restrictHyperboloid_boosts_lt_top`,
    below); the sanity checks apply the theorem to such a $`u`$ and obtain $`1 \le C R`$ with
    $`R \lt \infty`$.
  - Under the hypotheses, the thirteen functions $`(L^J u)|_{H_s}`$ on the right are continuous on
    $`\mathbb{R}^3`$ (`continuous_restrictHyperboloid_boosts`, below), hence measurable. Since
    `eLpNorm` is `∞` for a function that is not (a.e. strongly) measurable, a right side equal to
    `∞` can only mean that one of them is genuinely not square integrable; it never comes from
    that convention.
  - `√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ)` is $`t_0^{3/2}`$ with a real exponent (`Real.rpow`; `√`
    binds tighter than `^`), and `u (√(s ^ 2 + ‖x₀‖ ^ 2), x₀)` is $`u(t_0, x_0)`$.
  - `restrictHyperboloid s (boost a u)` is $`(L_a u)|_{H_s}`$ and
    `restrictHyperboloid s (boost a (boost b u))` is $`(L_a L_b u)|_{H_s}`$; with `eLpNorm _ 2 volume`
    they give the flat norms $`\lVert L^J u\rVert_{L^2_f(H_s)}`$, for Lebesgue measure $`dx`$ on
    $`\mathbb{R}^3`$, not for the measure induced on $`H_s`$. The double sum runs over the nine
    ordered pairs $`(a, b)`$.
  - Only the values of $`u`$ on $`U`$ enter: $`L_a u`$ and $`L_a L_b u`$ at points of $`H_s`$
    depend only on $`u`$ near $`H_s`$, and $`U`$ is open. The sanity checks below apply the theorem
    with $`U = \mathbb{R}^{1+3}`$ and with $`U = \{t \gt 0\}`$.
  - Proof: `EuclideanSobolev.exists_hyperboloidalSobolev` applied to $`w = u|_{H_s}`$, which is
    $`C^2`$ by the regularity entry; its terms $`\Lambda_a w`$ and $`\Lambda_a \Lambda_b w`$ are
    rewritten with the first- and second-order restriction formulas.

### Continuity of the functions on the right-hand side

- **Math.** Let $`U \subseteq \mathbb{R}^{1+3}`$ be an open set containing $`H_s`$ and
  $`u : \mathbb{R}^{1+3} \to F`$ of class $`C^2`$ on $`U`$. Then $`u|_{H_s}`$, $`(L_a u)|_{H_s}`$ and
  $`(L_a L_b u)|_{H_s}`$ are continuous on $`\mathbb{R}^3`$ for all $`a, b \in \{1, 2, 3\}`$.
- **Hypotheses.** $`F`$ is a real normed space; $`U`$ is open and $`H_s \subseteq U`$; $`u`$ is
  $`C^2`$ on $`U`$. No hypothesis on $`s`$.
- **Lean.** `VectorFieldMethod.Minkowski.continuous_restrictHyperboloid_boosts`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L259)

```lean
theorem continuous_restrictHyperboloid_boosts {s : ℝ} {u : Spacetime → F} {U : Set Spacetime}
    (hU : IsOpen U) (hHU : hyperboloid s ⊆ U) (hu : ContDiffOn ℝ 2 u U) :
    Continuous (restrictHyperboloid s u) ∧
      (∀ a, Continuous (restrictHyperboloid s (boost a u))) ∧
      ∀ a b, Continuous (restrictHyperboloid s (boost a (boost b u)))
```

- **Notes.** `∧` is "and". The proof uses that $`L_a u`$ is $`C^1`$ and $`L_a L_b u`$ is $`C^0`$ on
  the open set $`U`$ (`contDiffOn_boost`), and that $`x \mapsto (\varphi_s(x), x)`$ is continuous
  and maps $`\mathbb{R}^3`$ into $`H_s \subseteq U`$.

### Finiteness of the right-hand side for compactly supported functions

- **Math.** Let $`s \in \mathbb{R}`$ and let $`u : \mathbb{R}^{1+3} \to F`$ be of class $`C^2`$ with
  compact support. Then
  ```math
  \lVert u\rVert_{L^2_f(H_s)} + \sum_{a=1}^{3} \lVert L_a u\rVert_{L^2_f(H_s)} + \sum_{a=1}^{3} \sum_{b=1}^{3} \lVert L_a L_b u\rVert_{L^2_f(H_s)} \lt \infty .
  ```
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is $`C^2`$ on $`\mathbb{R}^{1+3}`$ and has compact
  support. No hypothesis on $`s`$.
- **Lean.** `VectorFieldMethod.Minkowski.eLpNorm_restrictHyperboloid_boosts_lt_top`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L297)

```lean
theorem eLpNorm_restrictHyperboloid_boosts_lt_top (s : ℝ) {u : Spacetime → F}
    (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) :
    eLpNorm (restrictHyperboloid s u) 2 volume +
        ∑ a, eLpNorm (restrictHyperboloid s (boost a u)) 2 volume +
        ∑ a, ∑ b, eLpNorm (restrictHyperboloid s (boost a (boost b u))) 2 volume < ⊤
```

- **Notes.** `HasCompactSupport u` means that the closed support of $`u`$ is compact. The thirteen
  functions $`(L^J u)|_{H_s}`$ are continuous with compact support, hence square integrable
  (`eLpNorm_restrictHyperboloid_lt_top`, `hasCompactSupport_restrictHyperboloid`,
  `hasCompactSupport_derivAlong`). The sanity checks apply this theorem to a smooth bump function,
  which shows that its hypotheses can hold.

## Sanity checks

The section "Sanity checks" at the end of the file contains the following `example`s.

| Statement | Line |
| --- | --- |
| $`u = t`$, $`U = \mathbb{R}^{1+3}`$: the hypotheses of `exists_klainermanSobolev_hyperboloid` hold. Its right side is $`\infty`$ here, since $`t\vert_{H_s} = \varphi_s`$ is not square integrable | [L314](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L314) |
| $`u = 1/t`$, $`U = \{t \gt 0\}`$: the hypotheses hold with an open set $`U`$ smaller than spacetime, for a function singular at $`t = 0`$. Its right side is $`\infty`$ here as well: $`(1/t)\vert_{H_s} = 1/\varphi_s`$ and $`\int \varphi_s^{-2}\, dx = 4\pi \int_0^\infty r^2/(s^2 + r^2)\, dr = \infty`$ | [L329](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L329) |
| There is a function $`u`$ of class $`C^\infty`$ (`ContDiff ℝ ∞ u`) whose left side at the point $`(1, 0)`$ of $`H_1`$ is $`1`$ and whose right side for $`s = 1`$ is finite; the proof takes a smooth bump function. This example does not apply the theorem | [L350](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L350) |
| The theorem applied to the same bump function at $`(1, 0) \in H_1`$, with $`U = \mathbb{R}^{1+3}`$: for a constant $`C`$ for which the conclusion of the theorem holds, $`1 \le C R`$ where $`R`$ is the right side for $`u`$ and $`R \lt \infty`$; hence $`C \gt 0`$ | [L371](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L371) |
| $`v = t`$, computed independently of the restriction formula: $`\Lambda_a \varphi_s = x^a`$ and $`(L_a t)\vert_{H_s} = x^a`$ | [L401](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L401) |
| $`v = t`$: the restriction formula applies ($`t`$ is differentiable) and gives $`\Lambda_a \varphi_s(x) = x^a`$ | [L411](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L411) |
| $`v = x^b`$, testing the term $`t\, \partial_a v`$: both sides computed independently, $`\Lambda_a x^b = \varphi_s\, \delta_{ab}`$ and $`(L_a x^b)\vert_{H_s} = \varphi_s\, \delta_{ab}`$, and the restriction formula (as functions) applies | [L424](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L424) |
| $`u = t`$, second order, computed independently: $`\Lambda_a \Lambda_b \varphi_s = \varphi_s\, \delta_{ab}`$ and $`(L_a L_b t)\vert_{H_s} = \varphi_s\, \delta_{ab}`$ | [L443](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L443) |
| $`u = x^c`$, $`U = \mathbb{R}^{1+3}`$: the second-order formula applies and gives $`\Lambda_a \Lambda_b x^c = (L_a L_b x^c)\vert_{H_s} = \delta_{bc}\, x^a`$, which is not symmetric in $`a, b`$ | [L468](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L468) |

The first, second and fourth examples apply `exists_klainermanSobolev_hyperboloid`, so its
hypotheses can hold simultaneously, with $`U`$ the whole spacetime or a smaller open set. In the
first two the right side is $`\infty`$ (a remark in their docstrings, not proved in Lean), so
there the inequality holds trivially. The third example only asserts that some $`u`$ with
`ContDiff ℝ ∞ u` has left side $`1`$ at $`(1, 0) \in H_1`$ and a finite right side; it does not
apply the theorem. The fourth example applies the theorem to the same bump function and obtains
$`1 \le C R`$ with $`R \lt \infty`$, hence $`C \gt 0`$: for this $`u`$ the theorem is a genuine,
finite inequality. The third and fourth examples get the finiteness of $`R`$ from
`eLpNorm_restrictHyperboloid_boosts_lt_top`, applied to the bump function, so the hypotheses of
that theorem hold as well. The last five examples check the restriction formulas on $`t`$,
$`x^b`$ and $`x^c`$, for which both sides can be computed directly; in Lean, $`\delta_{ab}`$ is
`if a = b then 1 else 0`.
