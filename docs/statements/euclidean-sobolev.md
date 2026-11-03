# Statements: Sobolev inequalities on ℝ³

Correspondence between the mathematical statements and the Lean declarations of
`VectorFieldMethod/Analysis/LocalSobolev.lean` and
`VectorFieldMethod/Analysis/HyperboloidalSobolev.lean` (namespace
`VectorFieldMethod.EuclideanSobolev`). The permalinks and the Lean code blocks
are taken from commit `7658e1e`, the last commit that changes these Lean files.
The background and the proofs are in `docs/hyperboloidal-sobolev.md`.

Common conventions: $`\mathbb{R}^3`$ is `EuclideanSpace ℝ (Fin 3)` with
Lebesgue measure `volume`; $`B(x_0, \rho)`$ is the open ball `Metric.ball x₀ ρ`;
$`Df`$ is `fderiv ℝ f` and $`D^2 f`$ is `iteratedFDeriv ℝ 2 f`, both with their
operator norms; $`\|g\|_{L^2(\mu)}`$ is `eLpNorm g 2 μ`, a value in
$`[0, \infty]`$ (`ℝ≥0∞`). Spatial indices $`a, b \in \{1, 2, 3\}`$ are the Lean
indices `0, 1, 2`, and $`e_a`$ is `EuclideanSpace.single a 1`.

### The hyperboloidal weighted derivative

- **Math.** For $`s \in \mathbb{R}`$, $`a \in \{1, 2, 3\}`$ and
  $`w : \mathbb{R}^3 \to \mathbb{R}`$,
  $$\Lambda_a w(x) = \sqrt{s^2 + |x|^2}\, \partial_a w(x), \qquad \partial_a w(x) = Dw(x)\, e_a .$$
- **Hypotheses.** None: this is a definition, for every real $`s`$ and every
  function $`w`$.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.hyperboloidalWeightedDeriv`
  (https://github.com/Oho1e/VectorFieldMethod/blob/7658e1e26e9bbfa68fa176c10a6c972a656aeec0/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L78)

```lean
def hyperboloidalWeightedDeriv (s : ℝ) (a : Fin 3) (w : EuclideanSpace ℝ (Fin 3) → ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x ↦ √(s ^ 2 + ‖x‖ ^ 2) * fderiv ℝ w x (EuclideanSpace.single a 1)
```

- **Notes.** The block shows the whole definition. `fderiv` is `0` where `w` is
  not differentiable, so $`\Lambda_a w`$ is defined for every `w`; the theorems
  below assume `w` is `C²`. $`\Lambda_a`$ depends on `s`. For `s > 0` it is the
  restriction of the boost $`L_a = t\partial_a + x_a\partial_t`$ to the
  hyperboloid $`t = \sqrt{s^2 + |x|^2}`$ (see `docs/hyperboloidal-sobolev.md`).

### The local Sobolev bound on balls (proposition)

- **Math.** The proposition: there is a constant $`C \ge 0`$ such that for all
  $`x_0 \in \mathbb{R}^3`$, all $`\rho > 0`$ and all
  $`f : \mathbb{R}^3 \to \mathbb{R}`$ of class $`C^2`$ on
  $`B = B(x_0, \rho)`$,
  $$|f(x_0)| \le C \Big( \rho^{-3/2} \|f\|_{L^2(B)} + \rho^{-1/2} \|Df\|_{L^2(B)} + \rho^{1/2} \|D^2 f\|_{L^2(B)} \Big).$$
- **Hypotheses.** Inside the proposition: $`\rho > 0`$ and $`f`$ is $`C^2`$ on
  the open ball $`B(x_0, \rho)`$.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.LocalSobolevBound`
  (https://github.com/Oho1e/VectorFieldMethod/blob/7658e1e26e9bbfa68fa176c10a6c972a656aeec0/VectorFieldMethod/Analysis/LocalSobolev.lean#L76)

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

- **Notes.** The block shows the whole definition; its body is word for word the
  statement of Theorem 1, and the notes there apply. It is proved by
  `VectorFieldMethod.EuclideanSobolev.localSobolevBound_holds`
  (https://github.com/Oho1e/VectorFieldMethod/blob/7658e1e26e9bbfa68fa176c10a6c972a656aeec0/VectorFieldMethod/Analysis/LocalSobolev.lean#L447), and it is the hypothesis of the
  reductions `exists_hyperboloidalSobolev_ball_of_localSobolevBound`
  (https://github.com/Oho1e/VectorFieldMethod/blob/7658e1e26e9bbfa68fa176c10a6c972a656aeec0/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L334) and
  `exists_hyperboloidalSobolev_of_localSobolevBound`
  (https://github.com/Oho1e/VectorFieldMethod/blob/7658e1e26e9bbfa68fa176c10a6c972a656aeec0/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L407).

### Theorem 1: the local embedding $`H^2 \subset L^\infty`$ on balls of $`\mathbb{R}^3`$

- **Math.** There is an absolute constant $`C \ge 0`$ such that for all
  $`x_0 \in \mathbb{R}^3`$, all $`\rho > 0`$ and every
  $`f : \mathbb{R}^3 \to \mathbb{R}`$ of class $`C^2`$ on the open ball
  $`B = B(x_0, \rho)`$,
  $$|f(x_0)| \le C \Big( \rho^{-3/2} \|f\|_{L^2(B)} + \rho^{-1/2} \|Df\|_{L^2(B)} + \rho^{1/2} \|D^2 f\|_{L^2(B)} \Big).$$
- **Hypotheses.** $`\rho > 0`$ and $`f`$ is $`C^2`$ on the open ball
  $`B(x_0, \rho)`$; there is no integrability, boundedness or support
  assumption.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.exists_abs_le_eLpNorm_ball`
  (https://github.com/Oho1e/VectorFieldMethod/blob/7658e1e26e9bbfa68fa176c10a6c972a656aeec0/VectorFieldMethod/Analysis/LocalSobolev.lean#L352)

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
  - The inequality is stated in `ℝ≥0∞`: the left side is `ENNReal.ofReal |f x₀|`,
    and each `eLpNorm` on the right may be `∞`, in which case the inequality
    holds trivially.
  - `C : NNReal` is quantified before `x₀`, `ρ` and `f`, so it is an absolute
    constant; the proof gives $`C = 2\,|B(0,1)|^{-1/2}`$.
  - The exponents `-(3 / 2 : ℝ)`, `-(1 / 2 : ℝ)` and `(1 / 2 : ℝ)` are real
    numbers (`Real.rpow`), and the three powers make the inequality invariant
    under dilations.
  - `ContDiffOn ℝ 2 f (Metric.ball x₀ ρ)` only concerns the open ball; the values
    of `f` outside the ball do not enter.

### Theorem 2, local version

- **Math.** There is an absolute constant $`C \ge 0`$ such that for all
  $`s > 0`$, all $`w \in C^2(\mathbb{R}^3)`$ and all
  $`x_0 \in \mathbb{R}^3`$, with $`\varphi_0 = \sqrt{s^2 + |x_0|^2}`$ and
  $`B = B(x_0, \varphi_0 / 3)`$,
  $$\varphi_0^{3/2}\, |w(x_0)| \le C \Big( \|w\|_{L^2(B)} + \sum_{a=1}^{3} \|\Lambda_a w\|_{L^2(B)} + \sum_{a=1}^{3} \sum_{b=1}^{3} \|\Lambda_a \Lambda_b w\|_{L^2(B)} \Big).$$
- **Hypotheses.** $`s > 0`$ and $`w`$ is $`C^2`$ on all of
  $`\mathbb{R}^3`$.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.exists_hyperboloidalSobolev_ball`
  (https://github.com/Oho1e/VectorFieldMethod/blob/7658e1e26e9bbfa68fa176c10a6c972a656aeec0/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L426)

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
  - `C : NNReal` comes before `s`, `w` and `x₀`, so it does not depend on them.
  - `√(s ^ 2 + ‖x₀‖ ^ 2) ^ (3 / 2 : ℝ)` is $`\varphi_0^{3/2}`$ with a real
    exponent (`√` binds tighter than `^`).
  - The double sum runs over the nine ordered pairs $`(a, b)`$; since
    $`[\Lambda_a, \Lambda_b] \ne 0`$ it is not reduced to $`a \le b`$.
  - It is `exists_hyperboloidalSobolev_ball_of_localSobolevBound`
    (https://github.com/Oho1e/VectorFieldMethod/blob/7658e1e26e9bbfa68fa176c10a6c972a656aeec0/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L334) applied to `localSobolevBound_holds`.

### Theorem 2: the hyperboloidal Sobolev inequality on $`\mathbb{R}^3`$

- **Math.** There is an absolute constant $`C \ge 0`$ such that for all
  $`s > 0`$, all $`w \in C^2(\mathbb{R}^3)`$ and all
  $`x_0 \in \mathbb{R}^3`$,
  $$\Big(\sqrt{s^2 + |x_0|^2}\Big)^{3/2} |w(x_0)| \le C \Big( \|w\|_{L^2} + \sum_{a=1}^{3} \|\Lambda_a w\|_{L^2} + \sum_{a=1}^{3} \sum_{b=1}^{3} \|\Lambda_a \Lambda_b w\|_{L^2} \Big),$$
  where $`L^2 = L^2(\mathbb{R}^3)`$.
- **Hypotheses.** $`s > 0`$ and $`w`$ is $`C^2`$ on all of
  $`\mathbb{R}^3`$; there is no integrability, decay or support assumption.
- **Lean.** `VectorFieldMethod.EuclideanSobolev.exists_hyperboloidalSobolev`
  (https://github.com/Oho1e/VectorFieldMethod/blob/7658e1e26e9bbfa68fa176c10a6c972a656aeec0/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L440)

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
  - `C : NNReal` comes before `s`, `w` and `x₀`; it is an absolute constant,
    independent of `s` (the proof gives fifteen times the constant of
    Theorem 1).
  - The exponent `(3 / 2 : ℝ)` is real. The right side has
    $`1 + 3 + 9 = 13`$ terms, over all ordered pairs $`(a, b)`$; the term
    without $`\Lambda`$ carries no weight.
  - It is `exists_hyperboloidalSobolev_of_localSobolevBound`
    (https://github.com/Oho1e/VectorFieldMethod/blob/7658e1e26e9bbfa68fa176c10a6c972a656aeec0/VectorFieldMethod/Analysis/HyperboloidalSobolev.lean#L407) applied to `localSobolevBound_holds`.
  - With $`w(x) = u(\sqrt{s^2 + |x|^2}, x)`$ it gives
    $`\sup_{H_s} t^{3/2} |u| \le C \sum_{|J| \le 2} \|L^J u\|_{L^2_f(H_s)}`$;
    see `docs/hyperboloidal-sobolev.md` (not formalized yet).
