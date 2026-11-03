# The Klainerman–Sobolev inequality on hyperboloids: statements

Layer: `VectorFieldMethod/Minkowski/KlainermanSobolev.lean`, built on the Minkowski coordinate
layer (see [`minkowski.md`](minkowski.md) for the boosts $`L_a`$ and their conventions) and on
the Sobolev inequality layer on $`\mathbb{R}^3`$ (see [`euclidean-sobolev.md`](euclidean-sobolev.md)
for the weighted derivatives $`\Lambda_a`$ and the weighted inequality). All declarations are in
the namespace `VectorFieldMethod.Minkowski`. The links below point to commit
[`2fcdc00`](https://github.com/Oho1e/VectorFieldMethod/tree/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87)
of the pull request branch of this layer, the last commit that changes the Lean file of this
layer; they are to be replaced by a `main` commit once the pull request is merged. How to read the
entries: [`README.md`](README.md). Background and proofs:
[`../hyperboloidal-sobolev.md`](../hyperboloidal-sobolev.md).

**Notation in the Math lines below.**
- A point of Minkowski spacetime $`\mathbb{R}^{1+3}`$ is $`p = (t, x)`$, time first, as in
  [`minkowski.md`](minkowski.md). $`\mathbb{R}^3`$ is `EuclideanSpace ℝ (Fin 3)` with Lebesgue
  measure (`volume`) and Euclidean norm $`\lvert x\rvert`$ (`‖x‖`). Spatial indices
  $`a, b \in \{1, 2, 3\}`$ are the Lean indices `a - 1 : Fin 3`, and $`e_a`$ is the standard basis
  vector `EuclideanSpace.single (a - 1) 1`.
- For $`s \in \mathbb{R}`$, $`\varphi_s(x) = \sqrt{s^2 + \lvert x\rvert^2}`$, written
  `√(s ^ 2 + ‖x‖ ^ 2)` in Lean, and
  ```math
  H_s = \{(t, x) \in \mathbb{R}^{1+3} : t = \varphi_s(x)\},
  ```
  written `{p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)}`. For $`s \neq 0`$ this is the upper sheet
  $`\{t^2 - \lvert x\rvert^2 = s^2,\ t \gt 0\}`$ of the hyperboloid.
- The restriction of $`v : \mathbb{R}^{1+3} \to \mathbb{R}`$ to $`H_s`$ is the function
  $`v|_{H_s}(x) = v(\varphi_s(x), x)`$ on $`\mathbb{R}^3`$ (`restrictHyperboloid s v`, below).
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

None. The declarations below do not depend on any `variable` line: the file has none, and all
hypotheses are explicit arguments. The file opens three namespaces
([`KlainermanSobolev.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L55)):

```lean
open MeasureTheory
open scoped ContDiff

namespace VectorFieldMethod.Minkowski

open VectorFieldMethod.EuclideanSobolev
```

So `volume` and `eLpNorm` are `MeasureTheory.volume` and `MeasureTheory.eLpNorm`;
`hyperboloidalWeightedDeriv` is `VectorFieldMethod.EuclideanSobolev.hyperboloidalWeightedDeriv`
(entry *The hyperboloidal weighted derivative* of [`euclidean-sobolev.md`](euclidean-sobolev.md));
`boost`, `boostField`, `Spacetime` and `timeCoord` are the declarations of the Minkowski layer;
and `ℕ∞ω` (the type `WithTop ℕ∞` of smoothness orders: natural numbers, `∞` and `ω`) is the
notation of the scope `ContDiff`.

## Definitions

### The point of $`H_s`$ above $`x`$

- **Math.** For $`s \in \mathbb{R}`$ and $`x \in \mathbb{R}^3`$, the point
  $`(\varphi_s(x), x) = (\sqrt{s^2 + \lvert x\rvert^2}, x)`$ of $`H_s`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidPoint`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L66)

```lean
def hyperboloidPoint (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : Spacetime :=
  (√(s ^ 2 + ‖x‖ ^ 2), x)
```

- **Notes.** An auxiliary parametrization of $`H_s`$ by $`\mathbb{R}^3`$, used in the proofs. It is
  smooth for $`s \neq 0`$ (`contDiff_hyperboloidPoint`) and continuous for every $`s`$
  (`continuous_hyperboloidPoint`); `hyperboloidPoint_mem` states that it lies on $`H_s`$.

### Restriction to the hyperboloid $`H_s`$

- **Math.** For $`s \in \mathbb{R}`$ and $`v : \mathbb{R}^{1+3} \to \mathbb{R}`$, the function
  ```math
  v|_{H_s} : \mathbb{R}^3 \to \mathbb{R}, \qquad v|_{H_s}(x) = v\big(\sqrt{s^2 + \lvert x\rvert^2},\ x\big).
  ```
- **Hypotheses.** None: this is a definition, for every real $`s`$ and every function $`v`$.
- **Lean.** `VectorFieldMethod.Minkowski.restrictHyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L72)

```lean
def restrictHyperboloid (s : ℝ) (v : Spacetime → ℝ) : EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x ↦ v (√(s ^ 2 + ‖x‖ ^ 2), x)
```

- **Notes.** Only real-valued $`v`$ are considered, since $`\Lambda_a`$ is defined for real-valued
  functions. The definition makes sense for every $`s`$ (for $`s = 0`$ it restricts to the light
  cone $`t = \lvert x\rvert`$); the theorems below assume $`s \neq 0`$ or $`s \gt 0`$. By definition
  (`restrictHyperboloid_eq_comp`, `rfl`), `restrictHyperboloid s v = v ∘ hyperboloidPoint s`.

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
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalWeightedDeriv_restrictHyperboloid_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L109)

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
  side $`0`$ while the left side need not be.

### The restriction formula as an equality of functions

- **Math.** Let $`s \neq 0`$ and $`a \in \{1, 2, 3\}`$. If $`v : \mathbb{R}^{1+3} \to \mathbb{R}`$ is
  differentiable at every point of $`H_s`$, then $`\Lambda_a(v|_{H_s}) = (L_a v)|_{H_s}`$ on
  $`\mathbb{R}^3`$. In particular this holds if $`u`$ is differentiable on an open set
  $`U \supseteq H_s`$ (second statement, with $`u`$ in place of $`v`$).
- **Hypotheses.** $`s \neq 0`$; first statement: $`v`$ is differentiable at
  $`(\varphi_s(x), x)`$ for every $`x \in \mathbb{R}^3`$; second statement: $`U`$ is open, contains
  $`H_s`$, and $`u`$ is differentiable at every point of $`U`$.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalWeightedDeriv_restrictHyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L128),
  and `VectorFieldMethod.Minkowski.hyperboloidalWeightedDeriv_restrictHyperboloid_of_differentiableOn`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L145)

```lean
theorem hyperboloidalWeightedDeriv_restrictHyperboloid {s : ℝ} (hs : s ≠ 0) (a : Fin 3)
    {v : Spacetime → ℝ}
    (hv : ∀ x : EuclideanSpace ℝ (Fin 3), DifferentiableAt ℝ v (√(s ^ 2 + ‖x‖ ^ 2), x)) :
    hyperboloidalWeightedDeriv s a (restrictHyperboloid s v) =
      restrictHyperboloid s (boost a v)

theorem hyperboloidalWeightedDeriv_restrictHyperboloid_of_differentiableOn {s : ℝ}
    (hs : s ≠ 0) {u : Spacetime → ℝ} {U : Set Spacetime} (hU : IsOpen U)
    (hHU : {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} ⊆ U) (hu : DifferentiableOn ℝ u U)
    (a : Fin 3) :
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
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L157)

```lean
theorem hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid {s : ℝ}
    (hs : s ≠ 0) {u : Spacetime → ℝ} {U : Set Spacetime} (hU : IsOpen U)
    (hHU : {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (a b : Fin 3) :
    hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b (restrictHyperboloid s u)) =
      restrictHyperboloid s (boost a (boost b u))
```

- **Notes.** The indices are in the same order on both sides: the outer operator is
  $`\Lambda_a`$, resp. $`L_a`$. The order matters, since $`[L_a, L_b] = \Omega_{ab}`$ is nonzero for
  $`a \neq b`$. Proof: the first-order formula as functions gives
  $`\Lambda_b(u|_{H_s}) = (L_b u)|_{H_s}`$; since $`u`$ is $`C^2`$ near each point of $`H_s`$,
  $`L_b u`$ is $`C^1`$ there, and the first-order formula at each point, applied to
  $`v = L_b u`$, gives the claim. The values of $`u`$ outside $`U`$ play no role.

### Regularity of the restriction

- **Math.** Let $`s \neq 0`$, $`n \in \mathbb{N} \cup \{\infty, \omega\}`$, let
  $`U \subseteq \mathbb{R}^{1+3}`$ be an open set containing $`H_s`$, and let
  $`u : \mathbb{R}^{1+3} \to \mathbb{R}`$ be of class $`C^n`$ on $`U`$. Then
  $`u|_{H_s} \in C^n(\mathbb{R}^3)`$. In particular, if $`u`$ is $`C^2`$ on $`U`$, then
  $`u|_{H_s}`$ is $`C^2`$ on $`\mathbb{R}^3`$.
- **Hypotheses.** $`s \neq 0`$; $`U`$ is open and $`H_s \subseteq U`$; $`u`$ is $`C^n`$ on $`U`$.
- **Lean.** `VectorFieldMethod.Minkowski.contDiff_restrictHyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L180)

```lean
theorem contDiff_restrictHyperboloid {s : ℝ} (hs : s ≠ 0) {n : ℕ∞ω} {u : Spacetime → ℝ}
    {U : Set Spacetime} (hU : IsOpen U)
    (hHU : {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} ⊆ U) (hu : ContDiffOn ℝ n u U) :
    ContDiff ℝ n (restrictHyperboloid s u)
```

- **Notes.** `n : ℕ∞ω` is a natural number, `∞` ($`C^\infty`$) or `ω` (real analytic); the case
  used below is `n = 2`. The proof composes $`u`$ with $`x \mapsto (\varphi_s(x), x)`$, which is
  smooth (and analytic) because $`s^2 + \lvert x\rvert^2 \gt 0`$ for $`s \neq 0`$
  (`contDiff_hyperboloidPoint`). For $`s = 0`$ the statement fails in general, since
  $`\lvert x\rvert`$ is not differentiable at $`0`$.

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
- **Lean.** `VectorFieldMethod.Minkowski.exists_klainermanSobolev_hyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L197)

```lean
theorem exists_klainermanSobolev_hyperboloid :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ (u : Spacetime → ℝ) (U : Set Spacetime), IsOpen U →
      {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} ⊆ U → ContDiffOn ℝ 2 u U →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |u (√(s ^ 2 + ‖x₀‖ ^ 2), x₀)|) ≤
        (C : ENNReal) *
          (eLpNorm (restrictHyperboloid s u) 2 volume +
            ∑ a, eLpNorm (restrictHyperboloid s (boost a u)) 2 volume +
            ∑ a, ∑ b, eLpNorm (restrictHyperboloid s (boost a (boost b u))) 2 volume)
```

- **Notes.**
  - `C : NNReal` is quantified before `s`, `u`, `U` and `x₀`, so it is an absolute constant: it
    does not depend on $`s`$, on $`u`$, on $`U`$ or on the point. The proof gives the constant of
    `EuclideanSobolev.exists_hyperboloidalSobolev` (Theorem 2 of
    [`euclidean-sobolev.md`](euclidean-sobolev.md)), that is, fifteen times the constant of the
    local embedding on balls.
  - The inequality is stated in `ℝ≥0∞`: the left side is `ENNReal.ofReal` of a nonnegative real,
    and the right side may be `∞`, in which case the inequality holds trivially.
  - Under the hypotheses, the thirteen functions $`(L^J u)|_{H_s}`$ on the right are continuous on
    $`\mathbb{R}^3`$ (`continuous_restrictHyperboloid_boosts`, next entry), hence measurable. Since
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
  $`u : \mathbb{R}^{1+3} \to \mathbb{R}`$ of class $`C^2`$ on $`U`$. Then $`u|_{H_s}`$,
  $`(L_a u)|_{H_s}`$ and $`(L_a L_b u)|_{H_s}`$ are continuous on $`\mathbb{R}^3`$ for all
  $`a, b \in \{1, 2, 3\}`$.
- **Hypotheses.** $`U`$ is open and $`H_s \subseteq U`$; $`u`$ is $`C^2`$ on $`U`$. No hypothesis on
  $`s`$.
- **Lean.** `VectorFieldMethod.Minkowski.continuous_restrictHyperboloid_boosts`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L242)

```lean
theorem continuous_restrictHyperboloid_boosts {s : ℝ} {u : Spacetime → ℝ} {U : Set Spacetime}
    (hU : IsOpen U) (hHU : {p : Spacetime | p.1 = √(s ^ 2 + ‖p.2‖ ^ 2)} ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) :
    Continuous (restrictHyperboloid s u) ∧
      (∀ a, Continuous (restrictHyperboloid s (boost a u))) ∧
      ∀ a b, Continuous (restrictHyperboloid s (boost a (boost b u)))
```

- **Notes.** `∧` is "and". The proof uses that $`L_a u`$ is $`C^1`$ and $`L_a L_b u`$ is $`C^0`$ on
  the open set $`U`$ (`contDiffOn_boost`), and that $`x \mapsto (\varphi_s(x), x)`$ is continuous
  and maps $`\mathbb{R}^3`$ into $`H_s \subseteq U`$.

## Sanity checks

The section "Sanity checks" at the end of the file contains the following `example`s.

| Statement | Line |
| --- | --- |
| $`u = t`$, $`U = \mathbb{R}^{1+3}`$: the hypotheses of `exists_klainermanSobolev_hyperboloid` hold (its right side is $`\infty`$, since $`t\vert_{H_s} = \varphi_s`$ is not square integrable) | [L282](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L282) |
| $`u = 1/t`$, $`U = \{t \gt 0\}`$: the hypotheses hold with an open set $`U`$ smaller than spacetime, for a function singular at $`t = 0`$ | [L296](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L296) |
| A smooth bump function $`u`$ on spacetime (equal to $`1`$ on the closed unit ball for the max norm, compactly supported): at the point $`(1, 0)`$ of $`H_1`$ the left side is $`1`$, and the right side is finite | [L317](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L317) |
| $`v = t`$, computed independently of the restriction formula: $`\Lambda_a \varphi_s = x^a`$ and $`(L_a t)\vert_{H_s} = x^a`$ | [L344](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L344) |
| $`v = t`$: the restriction formula applies ($`t`$ is differentiable) and gives $`\Lambda_a \varphi_s(x) = x^a`$ | [L354](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L354) |
| $`u = t`$, second order, computed independently: $`\Lambda_a \Lambda_b \varphi_s = \varphi_s\, \delta_{ab}`$ and $`(L_a L_b t)\vert_{H_s} = \varphi_s\, \delta_{ab}`$ | [L365](https://github.com/Oho1e/VectorFieldMethod/blob/2fcdc00e1cdab9bb1b21c64faef9e13641de6e87/VectorFieldMethod/Minkowski/KlainermanSobolev.lean#L365) |

The first three examples show that the hypotheses of `exists_klainermanSobolev_hyperboloid` can
hold simultaneously; the third one shows moreover that the inequality is not trivial, for a
function with a finite right side and a nonzero left side. Its finiteness part uses
`eLpNorm_restrictHyperboloid_lt_top` (the restriction to $`H_s`$ of a continuous function with
compact support is square integrable) and `hasCompactSupport_derivAlong` (a derivative along a
vector field of a compactly supported function is compactly supported). The last three examples
check the restriction formulas on $`t`$, for which both sides can be computed directly; in Lean,
$`\delta_{ab}`$ is `if a = b then 1 else 0`.
