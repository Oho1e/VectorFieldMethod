# Sobolev inequalities on ℝ³: statements

Layer: `VectorFieldMethod/Analysis/` (files `LocalSobolev.lean` and `HyperboloidalSobolev.lean`).
All declarations are in the namespace `VectorFieldMethod.EuclideanSobolev`. The links below
point to commit
[`65434c1`](https://github.com/Oho1e/VectorFieldMethod/tree/65434c138668e720ea41dbd287fb6c1298ad00f9)
of `main`. How to read the entries: [`README.md`](README.md). Background, including the
passage to the hyperboloid, and the proofs:
[`../hyperboloidal-sobolev.md`](../hyperboloidal-sobolev.md).

**Notation in the Math lines below.** $`\mathbb{R}^3`$ is `EuclideanSpace ℝ (Fin 3)` with
Lebesgue measure (`volume`), and $`\lvert x\rvert`$ is the Euclidean norm `‖x‖`.
$`B(x_0, \rho)`$ is the open ball `Metric.ball x₀ ρ`. $`Df`$ is `fderiv ℝ f` and $`D^2 f`$ is
`iteratedFDeriv ℝ 2 f`, both with their operator norms. $`\lVert g\rVert_{L^2(\mu)}`$ is
`eLpNorm g 2 μ`, a value in $`[0, \infty]`$ (`ℝ≥0∞`); $`L^2`$ without a measure means
$`L^2(\mathbb{R}^3)`$. Mathematical spatial indices $`a, b`$ run over $`\{1, 2, 3\}`$; the Lean
index `a : Fin 3` is the mathematical index $`a + 1`$, and `EuclideanSpace.single a 1` is
$`e_{a+1}`$.

## Context

None. The declarations below do not depend on any `variable` line: all their hypotheses are
explicit arguments. (`LocalSobolev.lean` has one `variable` line, in its section `Segment`, used
only by auxiliary lemmas; `HyperboloidalSobolev.lean` has none.) Both files `open MeasureTheory`,
so `volume` and `eLpNorm` below are `MeasureTheory.volume` and `MeasureTheory.eLpNorm`.

## Definitions

### The hyperboloidal weighted derivative

- **Math.** For $`s \in \mathbb{R}`$, $`a \in \{1, 2, 3\}`$ and
  $`w : \mathbb{R}^3 \to \mathbb{R}`$,
  ```math
  \Lambda_a w(x) = \sqrt{s^2 + \lvert x\rvert^2}\, \partial_a w(x), \qquad \partial_a w(x) = Dw(x)\, e_a .
  ```
- **Hypotheses.** None: this is a definition, for every real $`s`$ and every function $`w`$.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.hyperboloidalWeightedDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L79)

```lean
def hyperboloidalWeightedDeriv (s : ℝ) (a : Fin 3) (w : EuclideanSpace ℝ (Fin 3) → ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x ↦ √(s ^ 2 + ‖x‖ ^ 2) * fderiv ℝ w x (EuclideanSpace.single a 1)
```

- **Notes.** For `a : Fin 3`, `hyperboloidalWeightedDeriv s a w` is $`\Lambda_{a+1} w`$.
  `fderiv` is `0` where `w` is not differentiable, so $`\Lambda_a w`$ is defined for every `w`;
  the theorems below assume that `w` is `C²`. $`\Lambda_a`$ depends on $`s`$. If
  $`s \neq 0`$ and a spacetime function $`v`$ is differentiable at the points of the hyperboloid
  $`t = \sqrt{s^2 + \lvert x\rvert^2}`$, then $`\Lambda_a`$ of the restriction of $`v`$ to the
  hyperboloid is the restriction of the boost $`L_a v = t\,\partial_a v + x_a\,\partial_t v`$.
  This is proved in the Klainerman–Sobolev layer: *The restriction formula at a point* and *The
  restriction formula as an equality of functions* of
  [`klainerman-sobolev.md`](klainerman-sobolev.md)
  (`VectorFieldMethod.Minkowski.hyperboloidalWeightedDeriv_restrictHyperboloid_apply`,
  `VectorFieldMethod.Minkowski.hyperboloidalWeightedDeriv_restrictHyperboloid`); background in
  [`../hyperboloidal-sobolev.md`](../hyperboloidal-sobolev.md).

### The local Sobolev bound on balls (proposition)

- **Math.** The proposition: there is a constant $`C \ge 0`$ such that for all
  $`x_0 \in \mathbb{R}^3`$, all $`\rho \gt 0`$ and all $`f : \mathbb{R}^3 \to \mathbb{R}`$ of
  class $`C^2`$ on $`B = B(x_0, \rho)`$,
  ```math
  \lvert f(x_0)\rvert \le C \Big( \rho^{-3/2} \lVert f\rVert_{L^2(B)} + \rho^{-1/2} \lVert Df\rVert_{L^2(B)} + \rho^{1/2} \lVert D^2 f\rVert_{L^2(B)} \Big).
  ```
- **Hypotheses.** Inside the proposition: $`\rho \gt 0`$ and $`f`$ is $`C^2`$ on the open ball
  $`B(x_0, \rho)`$.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.LocalSobolevBound`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Analysis/LocalSobolev.lean#L76)

```lean
def LocalSobolevBound : Prop :=
  ∃ C : NNReal, ∀ (x₀ : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
    0 < ρ → ContDiffOn ℝ 2 f (Metric.ball x₀ ρ) →
    ENNReal.ofReal |f x₀| ≤ (C : ENNReal) *
      (ENNReal.ofReal (ρ ^ (-(3 / 2 : ℝ))) * eLpNorm f 2 (volume.restrict (Metric.ball x₀ ρ)) +
        ENNReal.ofReal (ρ ^ (-(1 / 2 : ℝ))) *
          eLpNorm (fderiv ℝ f) 2 (volume.restrict (Metric.ball x₀ ρ)) +
        ENNReal.ofReal (ρ ^ (1 / 2 : ℝ)) *
          eLpNorm (iteratedFDeriv ℝ 2 f) 2 (volume.restrict (Metric.ball x₀ ρ)))
```

- **Notes.** A `def … : Prop`. Its body is word for word the statement of Theorem 1, and the notes
  there apply. It is proved by `localSobolevBound_holds`, and it is the hypothesis of the two
  reductions at the end of this file.

## Main theorems

### Theorem 1: the local embedding $`H^2 \subset L^\infty`$ on balls of $`\mathbb{R}^3`$

- **Math.** There is an absolute constant $`C \ge 0`$ such that for all
  $`x_0 \in \mathbb{R}^3`$, all $`\rho \gt 0`$ and every $`f : \mathbb{R}^3 \to \mathbb{R}`$ of
  class $`C^2`$ on the open ball $`B = B(x_0, \rho)`$,
  ```math
  \lvert f(x_0)\rvert \le C \Big( \rho^{-3/2} \lVert f\rVert_{L^2(B)} + \rho^{-1/2} \lVert Df\rVert_{L^2(B)} + \rho^{1/2} \lVert D^2 f\rVert_{L^2(B)} \Big).
  ```
- **Hypotheses.** $`\rho \gt 0`$ and $`f`$ is $`C^2`$ on the open ball $`B(x_0, \rho)`$; there
  is no integrability, boundedness or support assumption.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.exists_abs_le_eLpNorm_ball`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Analysis/LocalSobolev.lean#L352)

```lean
theorem exists_abs_le_eLpNorm_ball :
    ∃ C : NNReal, ∀ (x₀ : EuclideanSpace ℝ (Fin 3)) (ρ : ℝ) (f : EuclideanSpace ℝ (Fin 3) → ℝ),
      0 < ρ → ContDiffOn ℝ 2 f (Metric.ball x₀ ρ) →
      ENNReal.ofReal |f x₀| ≤ (C : ENNReal) *
        (ENNReal.ofReal (ρ ^ (-(3 / 2 : ℝ))) * eLpNorm f 2 (volume.restrict (Metric.ball x₀ ρ)) +
          ENNReal.ofReal (ρ ^ (-(1 / 2 : ℝ))) *
            eLpNorm (fderiv ℝ f) 2 (volume.restrict (Metric.ball x₀ ρ)) +
          ENNReal.ofReal (ρ ^ (1 / 2 : ℝ)) *
            eLpNorm (iteratedFDeriv ℝ 2 f) 2 (volume.restrict (Metric.ball x₀ ρ)))
```

- **Notes.**
  - The inequality is stated in `ℝ≥0∞`: the left side is `ENNReal.ofReal |f x₀|`, and each
    `eLpNorm` on the right may be `∞`, in which case the inequality holds trivially.
  - Under the hypotheses every function on the right-hand side is measurable for the measure on
    the ball: $`f`$ and $`D^2 f`$ are continuous on the open ball, and $`Df`$ (`fderiv ℝ f`) is
    measurable on all of $`\mathbb{R}^3`$. Since `eLpNorm` is `∞` for a function that is not
    (a.e. strongly) measurable, a right-hand side equal to `∞` can only mean that $`f`$, $`Df`$ or
    $`D^2 f`$ is genuinely not square integrable on the ball; it never comes from that convention.
  - `C : NNReal` is quantified before `x₀`, `ρ` and `f`, so it is an absolute constant; the proof
    gives $`C = 2\,\lvert B(0,1)\rvert^{-1/2}`$.
  - The exponents `-(3 / 2 : ℝ)`, `-(1 / 2 : ℝ)` and `(1 / 2 : ℝ)` are real numbers
    (`Real.rpow`), and the three powers make the inequality invariant under dilations.
  - `ContDiffOn ℝ 2 f (Metric.ball x₀ ρ)` only concerns the open ball; the values of `f` outside
    the ball do not enter.

### Theorem 1 as a proof of the proposition

- **Math.** The proposition of the entry *The local Sobolev bound on balls* holds.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.localSobolevBound_holds`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Analysis/LocalSobolev.lean#L447)

```lean
theorem localSobolevBound_holds : LocalSobolevBound
```

- **Notes.** Same statement as Theorem 1 (the body of `LocalSobolevBound`), stated through the
  proposition; the proof is `exists_abs_le_eLpNorm_ball`.

### Theorem 2, local version

- **Math.** There is an absolute constant $`C \ge 0`$ such that for all $`s \gt 0`$, all
  $`w \in C^2(\mathbb{R}^3)`$ and all $`x_0 \in \mathbb{R}^3`$, with
  $`\varphi_0 = \sqrt{s^2 + \lvert x_0\rvert^2}`$ and $`B = B(x_0, \varphi_0 / 3)`$,
  ```math
  \varphi_0^{3/2}\, \lvert w(x_0)\rvert \le C \Big( \lVert w\rVert_{L^2(B)} + \sum_{a=1}^{3} \lVert \Lambda_a w\rVert_{L^2(B)} + \sum_{a=1}^{3} \sum_{b=1}^{3} \lVert \Lambda_a \Lambda_b w\rVert_{L^2(B)} \Big).
  ```
- **Hypotheses.** $`s \gt 0`$ and $`w`$ is $`C^2`$ on all of $`\mathbb{R}^3`$.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.exists_hyperboloidalSobolev_ball`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L427)

```lean
theorem exists_hyperboloidalSobolev_ball :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 w →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |w x₀|) ≤ (C : ENNReal) *
        (eLpNorm w 2 (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3))) +
          ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2
            (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3))) +
          ∑ a, ∑ b, eLpNorm (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w)) 2
            (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3))))
```

- **Notes.**
  - Stated in `ℝ≥0∞`; the right side may be `∞`.
  - Under the hypotheses every function on the right-hand side is measurable: $`w`$ is
    continuous, and $`\Lambda_a g`$ is measurable for every function $`g`$
    (`measurable_hyperboloidalWeightedDeriv`), in particular $`\Lambda_a w`$ and
    $`\Lambda_a \Lambda_b w`$. Since `eLpNorm` is `∞` for a function that is not (a.e. strongly)
    measurable, a right-hand side equal to `∞` can only mean that one of these functions is
    genuinely not square integrable on the ball; it never comes from that convention.
  - `C : NNReal` comes before `s`, `w` and `x₀`, so it does not depend on them.
  - `√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ)` is $`\varphi_0^{3/2}`$ with a real exponent (`√` binds
    tighter than `^`).
  - The double sum runs over the nine ordered pairs $`(a, b)`$; since
    $`[\Lambda_a, \Lambda_b] \ne 0`$ it is not reduced to $`a \le b`$.
  - It is `exists_hyperboloidalSobolev_ball_of_localSobolevBound` applied to
    `localSobolevBound_holds`.

### Theorem 2: the hyperboloidal Sobolev inequality on $`\mathbb{R}^3`$

- **Math.** There is an absolute constant $`C \ge 0`$ such that for all $`s \gt 0`$, all
  $`w \in C^2(\mathbb{R}^3)`$ and all $`x_0 \in \mathbb{R}^3`$,
  ```math
  \Big(\sqrt{s^2 + \lvert x_0\rvert^2}\Big)^{3/2} \lvert w(x_0)\rvert \le C \Big( \lVert w\rVert_{L^2} + \sum_{a=1}^{3} \lVert \Lambda_a w\rVert_{L^2} + \sum_{a=1}^{3} \sum_{b=1}^{3} \lVert \Lambda_a \Lambda_b w\rVert_{L^2} \Big),
  ```
  where $`L^2 = L^2(\mathbb{R}^3)`$.
- **Hypotheses.** $`s \gt 0`$ and $`w`$ is $`C^2`$ on all of $`\mathbb{R}^3`$; there is no
  integrability, decay or support assumption.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.exists_hyperboloidalSobolev`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L441)

```lean
theorem exists_hyperboloidalSobolev :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 w →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |w x₀|) ≤ (C : ENNReal) *
        (eLpNorm w 2 volume + ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2 volume +
          ∑ a, ∑ b, eLpNorm (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w))
            2 volume)
```

- **Notes.**
  - Stated in `ℝ≥0∞`; the right side may be `∞`.
  - Under the hypotheses every function on the right-hand side is measurable ($`w`$ is continuous,
    and $`\Lambda_a w`$, $`\Lambda_a \Lambda_b w`$ are measurable by
    `measurable_hyperboloidalWeightedDeriv`). Since `eLpNorm` is `∞` for a function that is not
    (a.e. strongly) measurable, a right-hand side equal to `∞` can only mean that one of these
    functions is genuinely not square integrable on $`\mathbb{R}^3`$; it never comes from that
    convention.
  - `C : NNReal` comes before `s`, `w` and `x₀`; it is an absolute constant, independent of `s`
    (the proof gives fifteen times the constant of Theorem 1).
  - The exponent `(3 / 2 : ℝ)` is real. The right side has $`1 + 3 + 9 = 13`$ terms, over all
    ordered pairs $`(a, b)`$; the term without $`\Lambda`$ carries no weight.
  - It is `exists_hyperboloidalSobolev_of_localSobolevBound` applied to `localSobolevBound_holds`.
  - Corollary on the hyperboloid: the Klainerman–Sobolev inequality. Let $`u`$ be a spacetime
    function of class $`C^2`$ on an open set containing $`H_s = \{t = \sqrt{s^2 + \lvert x\rvert^2}\}`$,
    and $`w(x) = u(\sqrt{s^2 + \lvert x\rvert^2}, x)`$. Then $`w \in C^2(\mathbb{R}^3)`$,
    $`\Lambda^J w = (L^J u)\vert_{H_s}`$ for $`\lvert J\rvert \le 2`$, and the theorem gives
    $`\sup_{H_s} t^{3/2} \lvert u\rvert \le C \sum_{\lvert J\rvert \le 2} \lVert L^J u\rVert_{L^2_f(H_s)}`$,
    where $`L^2_f(H_s)`$ uses the flat measure $`dx`$. This corollary is proved:
    `VectorFieldMethod.Minkowski.exists_klainermanSobolev_hyperboloid`, entry *The
    Klainerman–Sobolev inequality on hyperboloids* of
    [`klainerman-sobolev.md`](klainerman-sobolev.md), whose proof takes the constant $`C`$ of this
    theorem; see also
    [`../hyperboloidal-sobolev.md`](../hyperboloidal-sobolev.md).

## Reductions from the local Sobolev bound

### Theorem 2, local version, from the local Sobolev bound

- **Math.** The statement of *Theorem 2, local version*, with the additional hypothesis that the
  proposition `LocalSobolevBound` holds.
- **Hypotheses.** `h : LocalSobolevBound`; inside the statement, $`s \gt 0`$ and
  $`w \in C^2(\mathbb{R}^3)`$.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.exists_hyperboloidalSobolev_ball_of_localSobolevBound`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L335)

```lean
theorem exists_hyperboloidalSobolev_ball_of_localSobolevBound (h : LocalSobolevBound) :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 w →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |w x₀|) ≤ (C : ENNReal) *
        (eLpNorm w 2 (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3))) +
          ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2
            (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3))) +
          ∑ a, ∑ b, eLpNorm (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w)) 2
            (volume.restrict (Metric.ball x₀ (√(s ^ 2 + ‖x₀‖ ^ 2) / 3))))
```

- **Notes.** Statement as in *Theorem 2, local version*, plus the hypothesis
  `h : LocalSobolevBound`. The constant obtained is fifteen times the constant of `h`.

### Theorem 2 from the local Sobolev bound

- **Math.** The statement of *Theorem 2*, with the additional hypothesis that the proposition
  `LocalSobolevBound` holds.
- **Hypotheses.** `h : LocalSobolevBound`; inside the statement, $`s \gt 0`$ and
  $`w \in C^2(\mathbb{R}^3)`$.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.exists_hyperboloidalSobolev_of_localSobolevBound`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L408)

```lean
theorem exists_hyperboloidalSobolev_of_localSobolevBound (h : LocalSobolevBound) :
    ∃ C : NNReal, ∀ s : ℝ, 0 < s → ∀ w : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 w →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ) * |w x₀|) ≤ (C : ENNReal) *
        (eLpNorm w 2 volume + ∑ a, eLpNorm (hyperboloidalWeightedDeriv s a w) 2 volume +
          ∑ a, ∑ b, eLpNorm (hyperboloidalWeightedDeriv s a (hyperboloidalWeightedDeriv s b w))
            2 volume)
```

- **Notes.** Statement as in *Theorem 2*, plus the hypothesis `h : LocalSobolevBound`. It follows
  from the local version because `L²` norms over the ball are at most `L²` norms over
  $`\mathbb{R}^3`$.
