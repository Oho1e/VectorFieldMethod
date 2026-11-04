# The hyperboloidal energy estimate for the Klein–Gordon field: statements

Layer: `VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean` (the foliation of the region
between two hyperboloids, the Cauchy–Schwarz bound on a hyperboloid, continuity of the energy, the
integral inequality and the energy estimate) and `VectorFieldMethod/Analysis/SqrtGronwall.lean` (a
square-root Grönwall inequality, which depends only on Mathlib). The layer is built on the
hyperboloidal energy layer ([`hyperboloidal-energy.md`](hyperboloidal-energy.md): the energy
$`E_m(s, u)`$, the region $`D`$, the cone $`K`$ and the energy identity) and uses the restriction
to a hyperboloid and the flat $`L^2`$ norm of the Klainerman–Sobolev layer
([`klainerman-sobolev.md`](klainerman-sobolev.md)). The declarations of the first file are in the
namespace `VectorFieldMethod.Minkowski`, those of the second in `VectorFieldMethod.Analysis`. The
links below point to commit
[`6f2b67a`](https://github.com/Oho1e/VectorFieldMethod/tree/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e)
of the pull request that adds this layer, the last commit that changes its Lean files (they are
identical at the head of the branch); they are to be replaced by a `main` commit later. How to read
the entries: [`README.md`](README.md).

## Conventions

- **Coordinates, hyperboloids, region, cone.** As in
  [`hyperboloidal-energy.md`](hyperboloidal-energy.md): a point of
  `Spacetime = ℝ × EuclideanSpace ℝ (Fin 3)` is $`p = (t, x)`$, time first. For $`s \in \mathbb{R}`$
  and $`x \in \mathbb{R}^3`$, $`\varphi_s(x) = \sqrt{s^2 + \lvert x\rvert^2}`$, written
  `√(s ^ 2 + ‖x‖ ^ 2)` in Lean, and $`H_s = \{t = \varphi_s(x)\}`$. For $`s_1 \le s_2`$,
  $`D(s_1, s_2) = \{(t, x) : \varphi_{s_1}(x) \le t \le \varphi_{s_2}(x)\}`$ is
  `regionBetweenHyperboloids s₁ s₂`, and $`K = \{(t, x) : \lvert x\rvert \le t - 1\}`$ is `cone`.
- **Energy.** $`E_m(s, u)`$ is `hyperboloidalEnergy m s u`, with energy density
  $`e_m[u] = \lVert \partial_t u\rVert^2 + \sum_a \lVert \partial_a u\rVert^2 + 2 \sum_a (x^a / t)\langle \partial_a u, \partial_t u\rangle + m^2 \lVert u\rVert^2`$,
  without a factor $`\tfrac12`$ (LeFloch–Ma's normalization); on $`H_s`$ it equals
  $`\sum_a \lVert \underline{\partial}_a u\rVert^2 + (s/t)^2 \lVert \partial_t u\rVert^2 + m^2 \lVert u\rVert^2`$.
- **Flat $`L^2`$ norm on a hyperboloid.** For $`f : \mathbb{R}^{1+3} \to F`$,
  ```math
  \lVert f\rVert_{L^2_f(H_s)} = \Big( \int_{\mathbb{R}^3} \lVert f(\varphi_s(x), x)\rVert^2\, dx \Big)^{1/2} \in [0, \infty],
  ```
  in Lean `eLpNorm (restrictHyperboloid s f) 2 volume`, where `restrictHyperboloid s f` is the
  function $`x \mapsto f(\varphi_s(x), x)`$ on $`\mathbb{R}^3`$. The measure is $`dx`$, not the
  measure induced on $`H_s`$ by the Minkowski metric. If $`x \mapsto f(\varphi_s(x), x)`$ is not
  (a.e. strongly) measurable, `eLpNorm` is $`\infty`$ by convention
  (`MeasureTheory.eLpNorm_of_not_aestronglyMeasurable`, see the README); under the standing
  hypotheses below, $`x \mapsto (\mathrm{KG}_m u)(\varphi_s(x), x)`$ is continuous for
  $`s \in [s_0, S]`$, so this convention plays no role there. In the real-valued statements below the
  norm appears as `(eLpNorm (restrictHyperboloid s f) 2 volume).toReal`, which is the norm when it is
  finite and the junk value $`0`$ when it is $`\infty`$; the statements that use it either assume
  that it is finite or prove it. The notation $`L^2_f`$ comes from LeFloch–Ma's later papers; in
  their monograph (arXiv:1411.4910) this norm is written $`\lVert \cdot\rVert_{L^2(H_s)}`$, (2.4.2),
  with the flat measure $`dx`$.
- **Klein–Gordon operator.** $`\mathrm{KG}_m u = \Box u - m^2 u`$ (`kleinGordon m u`), where in this
  project $`\Box = -\partial_t^2 + \Delta`$ (see [`minkowski.md`](minkowski.md)).
- **Correspondence with LeFloch–Ma.** References are to LeFloch–Ma, *The Hyperboloidal Foliation
  Method* (World Scientific, 2014; arXiv:1411.4910). The mass is denoted $`\sigma`$ in §2.1 and
  $`c_i`$ in §2.3, and their wave operator has the opposite sign, $`\partial_t^2 - \Delta`$, so their
  Klein–Gordon operator of mass $`\sigma`$ is
  $`(\partial_t^2 - \Delta + \sigma^2) u = -\mathrm{KG}_\sigma u`$. Their energy (2.1.11) is
  `hyperboloidalEnergy σ s u` (normalized without $`\tfrac12`$; in §2.3 the energy of mass $`c`$ is
  written $`E_{m,c}(s, u)`$, see [`hyperboloidal-energy.md`](hyperboloidal-energy.md)), their cone
  (2.1.2) is $`\{r \lt t - 1\}`$, whose closure is $`K`$, and their norm
  $`\lVert \cdot\rVert_{L^2(H_s)}`$ (2.4.2) is the flat norm above. The energy estimate of this layer
  is the counterpart of their scalar energy estimate (2.1.10), which starts from the initial
  hyperboloid $`H_{s_0}`$ with $`s_0 = B + 1`$ (not necessarily $`2`$). Only the norm of the
  Klein–Gordon operator enters, so with $`m = \sigma`$ and $`E_\sigma(s, u)`$ =
  `hyperboloidalEnergy σ s u` the estimate reads
  ```math
  E_\sigma(s, u)^{1/2} \le E_\sigma(s_0, u)^{1/2} + \int_{s_0}^{s} \big\lVert (\partial_t^2 - \Delta + \sigma^2) u \big\rVert_{L^2(H_{s'})}\, ds' ,
  ```
  with $`\lVert (\partial_t^2 - \Delta + \sigma^2) u\rVert = \lVert \mathrm{KG}_\sigma u\rVert`$.
- **Measures.** `volume` on $`\mathbb{R}`$ and on `EuclideanSpace ℝ (Fin 3)` is Lebesgue measure,
  and on `Spacetime` it is the product measure $`dt\, dx`$. Integrals without `∂μ` use `volume`.

**Notation in the Math lines below.** As in [`hyperboloidal-energy.md`](hyperboloidal-energy.md):
$`u : \mathbb{R}^{1+3} \to F`$ with $`F`$ a real inner product space, $`m \in \mathbb{R}`$ the
mass, $`\mathrm{supp}\, u`$ the closed support `tsupport u`, and the derivatives have the Lean
convention that the derivative at a point of non-differentiability is $`0`$ (see the README).
"$`u`$ is $`C^2`$ on $`U`$" is `ContDiffOn ℝ 2 u U`; for open $`U`$ this is the usual notion and
the values of $`u`$ outside $`U`$ play no role. $`[a, b]`$ is `Icc a b`, and
$`\int_a^b f(\tau)\, d\tau`$ is the interval integral `∫ τ in a..b, f τ`. `ENNReal` (also written
`ℝ≥0∞`) is $`[0, \infty]`$, and `ENNReal.ofReal r` is $`\max(r, 0)`$ as an element of
$`[0, \infty]`$; `∫⁻ x in A, f x` is the Lebesgue integral of $`f : \alpha \to [0, \infty]`$ over
$`A`$, a value in $`[0, \infty]`$.

### The standing hypotheses

The main statements of the Minkowski file share the hypotheses of the energy identity of
[`hyperboloidal-energy.md`](hyperboloidal-energy.md), stated on the region between an initial
hyperboloid $`H_{s_0}`$ and a final hyperboloid $`H_S`$. Writing $`D = D(s_0, S)`$:

- $`0 \lt s_0`$ (`hs₀ : 0 < s₀`);
- $`U \subseteq \mathbb{R}^{1+3}`$ is open (`hU : IsOpen U`);
- $`D \cap K \subseteq U`$ (`hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U`);
- $`u`$ is $`C^2`$ on $`U`$ (`hu : ContDiffOn ℝ 2 u U`);
- $`D \cap \mathrm{supp}\, u \subseteq K`$ (`hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone`).

The conclusions are for $`s \in [s_0, S]`$ (`hs : s ∈ Icc s₀ S`). No global smoothness, compact
support, integrability or decay of $`u`$ is assumed. These hypotheses imply that the energy
density and $`\mathrm{KG}_m u`$ are continuous on $`D`$ and vanish on $`D \setminus K`$, and that
$`D \cap K`$ is compact; the points of $`H_s \cap K`$, $`s \in [s_0, S]`$, satisfy
$`\lvert x\rvert \le S^2`$ (indeed $`2 \lvert x\rvert + 1 \le s^2`$).

## Context

The `variable` and `open` lines of the two files. Their only hypotheses are structural: $`F`$ is a
real inner product space (no completeness or finite dimension is assumed).

[`HyperboloidalEnergyEstimate.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L77):

```lean
open Set Filter Function Topology MeasureTheory
open scoped RealInnerProductSpace NNReal ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {u : Spacetime → F}
```

The two `variable` lines are at
[L230](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L230),
after the statements about the foliation, which do not involve $`F`$ or $`u`$.

[`SqrtGronwall.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Analysis/SqrtGronwall.lean#L45):

```lean
open Set Filter Topology MeasureTheory

variable {a b A : ℝ} {E g : ℝ → ℝ}
```

`u`, `a`, `b`, `A`, `E` and `g` are implicit arguments of the theorems that do not list them
explicitly; they are inferred from the hypotheses.

## Definitions

This layer introduces no new definitions. It uses `hyperboloidalEnergy`,
`hyperboloidalEnergyDensity`, `regionBetweenHyperboloids` and `cone`
([`hyperboloidal-energy.md`](hyperboloidal-energy.md)), `restrictHyperboloid`
([`klainerman-sobolev.md`](klainerman-sobolev.md)) and `kleinGordon`, `∂ₜ`
([`minkowski.md`](minkowski.md)).

## Main theorems

### The foliation of the region between two hyperboloids (identity of measures)

- **Math.** Let $`0 \lt s_1 \le s_2`$ and $`\Psi(s, x) = (\varphi_s(x), x)`$. The image under
  $`\Psi`$ of the measure $`\frac{s}{\varphi_s(x)}\, ds\, dx`$ on $`[s_1, s_2] \times \mathbb{R}^3`$
  is Lebesgue measure on $`D(s_1, s_2)`$: for every Borel set $`N \subseteq \mathbb{R}^{1+3}`$,
  ```math
  \lvert N \cap D(s_1, s_2)\rvert = \int_{s_1}^{s_2} \int_{\mathbb{R}^3} \mathbf{1}_N\big(\varphi_s(x), x\big)\, \frac{s}{\varphi_s(x)}\, dx\, ds .
  ```
- **Hypotheses.** $`0 \lt s_1`$ and $`s_1 \le s_2`$.
- **Lean.** `VectorFieldMethod.Minkowski.map_withDensity_eq_restrict_regionBetweenHyperboloids`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L112)

```lean
theorem map_withDensity_eq_restrict_regionBetweenHyperboloids {s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ ≤ s₂) :
    Measure.map (fun q : ℝ × EuclideanSpace ℝ (Fin 3) ↦ ((√(q.1 ^ 2 + ‖q.2‖ ^ 2), q.2) : Spacetime))
        (((volume.restrict (Icc s₁ s₂)).prod volume).withDensity
          fun q ↦ ENNReal.ofReal (q.1 / √(q.1 ^ 2 + ‖q.2‖ ^ 2))) =
      volume.restrict (regionBetweenHyperboloids s₁ s₂)
```

- **Notes.** `Measure.map Ψ μ` is the image measure $`\mu \circ \Psi^{-1}`$;
  `μ.withDensity ρ` is the measure $`\rho\, d\mu`$; `(volume.restrict (Icc s₁ s₂)).prod volume` is
  $`ds\vert_{[s_1, s_2]} \otimes dx`$ on $`\mathbb{R} \times \mathbb{R}^3`$ (the pair `q` is
  $`(s, x)`$); `volume.restrict A` is Lebesgue measure restricted to $`A`$. On $`[s_1, s_2]`$ the
  density $`s / \varphi_s(x)`$ is positive, so `ENNReal.ofReal` does not truncate it. Proof: at
  fixed $`x`$, $`s \mapsto \varphi_s(x)`$ is a $`C^1`$ increasing bijection from $`[s_1, s_2]`$
  onto $`[\varphi_{s_1}(x), \varphi_{s_2}(x)]`$, the segment of $`D`$ above $`x`$, with derivative
  $`s / \varphi_s(x)`$; the one-dimensional change of variables
  (`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`) and Tonelli's theorem give the
  identity on every measurable set. The multidimensional change of variables formula is not used.

### The foliation formula

- **Math.** Let $`0 \lt s_1 \le s_2`$. For $`g : \mathbb{R}^{1+3} \to \mathbb{R}`$ integrable on
  $`D = D(s_1, s_2)`$,
  ```math
  \int_{D} g\, dt\, dx = \int_{s_1}^{s_2} \int_{\mathbb{R}^3} \frac{s}{\varphi_s(x)}\, g\big(\varphi_s(x), x\big)\, dx\, ds ,
  ```
  and the same identity holds for every measurable $`g : \mathbb{R}^{1+3} \to [0, \infty]`$, with
  Lebesgue integrals in $`[0, \infty]`$ and no integrability hypothesis.
- **Hypotheses.** $`0 \lt s_1`$, $`s_1 \le s_2`$; first statement: $`g`$ is integrable on $`D`$;
  second statement: $`g`$ is measurable with values in $`[0, \infty]`$.
- **Lean.** `VectorFieldMethod.Minkowski.setIntegral_regionBetweenHyperboloids_eq`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L184),
  and `VectorFieldMethod.Minkowski.setLIntegral_regionBetweenHyperboloids_eq`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L164)

```lean
theorem setIntegral_regionBetweenHyperboloids_eq {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂)
    {g : Spacetime → ℝ} (hg : IntegrableOn g (regionBetweenHyperboloids s₁ s₂)) :
    ∫ p in regionBetweenHyperboloids s₁ s₂, g p =
      ∫ s in Icc s₁ s₂, ∫ x : EuclideanSpace ℝ (Fin 3),
        s / √(s ^ 2 + ‖x‖ ^ 2) * g (√(s ^ 2 + ‖x‖ ^ 2), x)

theorem setLIntegral_regionBetweenHyperboloids_eq {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂)
    {g : Spacetime → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p in regionBetweenHyperboloids s₁ s₂, g p =
      ∫⁻ s in Icc s₁ s₂, ∫⁻ x : EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (s / √(s ^ 2 + ‖x‖ ^ 2)) * g (√(s ^ 2 + ‖x‖ ^ 2), x)
```

- **Notes.** Both follow from the previous entry. In the first statement both sides are genuine
  integrals: the integrability of $`g`$ on $`D`$ gives the integrability of
  $`(s, x) \mapsto \frac{s}{\varphi_s(x)} g(\varphi_s(x), x)`$ on $`[s_1, s_2] \times \mathbb{R}^3`$
  (by the identity of measures), and Fubini's theorem applies. This is the formula
  $`dt = (s / t)\, ds`$ at fixed $`x`$ mentioned in the notes of the energy identity in
  [`hyperboloidal-energy.md`](hyperboloidal-energy.md).

### The energy identity between intermediate hyperboloids

- **Math.** Under the standing hypotheses on $`D(s_0, S)`$, for $`s_0 \le s_1 \le s_2 \le S`$ the
  hypotheses of the energy identity hold on $`D(s_1, s_2)`$ (with the same $`U`$ and $`u`$), and
  ```math
  E_m(s_2, u) - E_m(s_1, u) = -2 \int_{D(s_1, s_2)} \big\langle (\Box u - m^2 u)(t, x),\ \partial_t u(t, x) \big\rangle\, dt\, dx .
  ```
  In particular, for $`s \in [s_0, S]`$,
  $`E_m(s, u) - E_m(s_0, u) = -2 \int_{D(s_0, s)} \langle \mathrm{KG}_m u, \partial_t u\rangle`$.
- **Hypotheses.** The standing hypotheses; $`s_0 \le s_1`$, $`s_1 \le s_2`$, $`s_2 \le S`$. For
  the transfer of hypotheses: $`0 \le s_0 \le s_1 \le s_2 \le S`$ and the corresponding
  hypothesis on $`D(s_0, S)`$.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalEnergy_sub_hyperboloidalEnergy_of_le`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L260);
  the transfer of the hypotheses: `VectorFieldMethod.Minkowski.regionBetweenHyperboloids_inter_cone_subset_of_le`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L235),
  and `VectorFieldMethod.Minkowski.regionBetweenHyperboloids_inter_tsupport_subset_of_le`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L245)

```lean
theorem hyperboloidalEnergy_sub_hyperboloidalEnergy_of_le (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s₁ s₂ : ℝ} (h₀₁ : s₀ ≤ s₁) (h₁₂ : s₁ ≤ s₂) (h₂S : s₂ ≤ S) :
    hyperboloidalEnergy m s₂ u - hyperboloidalEnergy m s₁ u =
      -2 * ∫ p in regionBetweenHyperboloids s₁ s₂, ⟪kleinGordon m u p, ∂ₜ u p⟫

theorem regionBetweenHyperboloids_inter_cone_subset_of_le {s₀ s₁ s₂ S : ℝ} (hs₀ : 0 ≤ s₀)
    (h₀₁ : s₀ ≤ s₁) (h₁₂ : s₁ ≤ s₂) (h₂S : s₂ ≤ S) {U : Set Spacetime}
    (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U) :
    regionBetweenHyperboloids s₁ s₂ ∩ cone ⊆ U

theorem regionBetweenHyperboloids_inter_tsupport_subset_of_le {s₀ s₁ s₂ S : ℝ} (hs₀ : 0 ≤ s₀)
    (h₀₁ : s₀ ≤ s₁) (h₁₂ : s₁ ≤ s₂) (h₂S : s₂ ≤ S)
    (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone) :
    regionBetweenHyperboloids s₁ s₂ ∩ tsupport u ⊆ cone
```

- **Notes.** Both transfers come from $`D(s_1, s_2) \subseteq D(s_0, S)`$
  (`regionBetweenHyperboloids_subset`, which needs $`0 \le s_0`$ so that
  $`s_0^2 \le s_1^2`$); the hypotheses "$`U`$ open" and "$`u`$ is $`C^2`$ on $`U`$" do not involve
  the region. For $`s_1 \lt s_2`$ the identity is then `hyperboloidalEnergy_sub_hyperboloidalEnergy`
  of [`hyperboloidal-energy.md`](hyperboloidal-energy.md) on $`D(s_1, s_2)`$; for $`s_1 = s_2`$ both
  sides are $`0`$, since $`D(s_1, s_1) = H_{s_1}`$ has measure zero (by the foliation formula, the
  integral over $`D(s_1, s_1)`$ is an integral over $`[s_1, s_1]`$). Allowing $`s_1 = s_2`$ saves a
  case distinction in the integral inequality below. The second transfer lemma does not use the
  inner product on $`F`$ (it is stated with `omit [InnerProductSpace ℝ F]`).

### A pointwise bound on a hyperboloid

- **Math.** Let $`s \neq 0`$, $`x \in \mathbb{R}^3`$ and $`t = \varphi_s(x)`$. Then, at
  $`(t, x)`$,
  ```math
  \Big(\frac{s}{t}\Big)^2 \lVert \partial_t u(t, x)\rVert^2 \le e_m[u](t, x) .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`s \neq 0`$; no regularity of $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.sq_div_mul_norm_timeDeriv_sq_le_hyperboloidalEnergyDensity`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L279)

```lean
theorem sq_div_mul_norm_timeDeriv_sq_le_hyperboloidalEnergyDensity (m : ℝ) (u : Spacetime → F)
    {s : ℝ} (hs : s ≠ 0) (x : EuclideanSpace ℝ (Fin 3)) :
    (s / √(s ^ 2 + ‖x‖ ^ 2)) ^ 2 * ‖∂ₜ u (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2 ≤
      hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x)
```

- **Notes.** It drops the nonnegative terms $`\sum_a \lVert \underline{\partial}_a u\rVert^2`$ and
  $`m^2 \lVert u\rVert^2`$ from the semi-hyperboloidal form of the energy density
  (`hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv_of_hyperboloid` of
  [`hyperboloidal-energy.md`](hyperboloidal-energy.md)). Here `u` is an explicit argument.

### Cauchy–Schwarz on a hyperboloid

- **Math.** Let $`s \neq 0`$ and $`f : \mathbb{R}^{1+3} \to F`$ with
  $`\lVert f\rVert_{L^2_f(H_s)} \lt \infty`$. If $`x \mapsto \partial_t u(\varphi_s(x), x)`$ is
  measurable and $`x \mapsto e_m[u](\varphi_s(x), x)`$ is integrable on $`\mathbb{R}^3`$, then,
  with $`t = \varphi_s(x)`$,
  ```math
  \Big\lvert \int_{\mathbb{R}^3} \frac{s}{t}\, \big\langle f(t, x), \partial_t u(t, x) \big\rangle\, dx \Big\rvert \le \lVert f\rVert_{L^2_f(H_s)}\, E_m(s, u)^{1/2} .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`s \neq 0`$; $`f\vert_{H_s}`$ is square
  integrable (`MemLp (restrictHyperboloid s f) 2 volume`); $`\partial_t u\vert_{H_s}`$ is
  (a.e. strongly) measurable; $`e_m[u]\vert_{H_s}`$ is integrable.
- **Lean.** `VectorFieldMethod.Minkowski.abs_integral_mul_inner_timeDeriv_le`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L298)

```lean
theorem abs_integral_mul_inner_timeDeriv_le (m : ℝ) {s : ℝ} (hs : s ≠ 0) {f : Spacetime → F}
    (hf : MemLp (restrictHyperboloid s f) 2 volume)
    (hu : AEStronglyMeasurable (restrictHyperboloid s (∂ₜ u)) volume)
    (he : Integrable fun x : EuclideanSpace ℝ (Fin 3) ↦
      hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x)) :
    |∫ x : EuclideanSpace ℝ (Fin 3),
        s / √(s ^ 2 + ‖x‖ ^ 2) * ⟪f (√(s ^ 2 + ‖x‖ ^ 2), x), ∂ₜ u (√(s ^ 2 + ‖x‖ ^ 2), x)⟫| ≤
      (eLpNorm (restrictHyperboloid s f) 2 volume).toReal * √(hyperboloidalEnergy m s u)
```

- **Notes.** Proof: $`\lvert (s/t) \langle f, \partial_t u\rangle\rvert \le \lVert f\rVert\, \lVert (s/t) \partial_t u\rVert`$,
  Hölder's inequality with $`p = q = 2`$, and the previous entry. The hypotheses exclude the junk
  values: `MemLp` makes `toReal` of the norm the actual norm, and the integrability of
  $`e_m[u]\vert_{H_s}`$ makes `hyperboloidalEnergy m s u` the actual energy (the integral of a
  non-integrable function is $`0`$ in Lean); together with the measurability of
  $`\partial_t u\vert_{H_s}`$ it also shows that $`(s/t)\, \partial_t u\vert_{H_s}`$ is square
  integrable. Under the standing hypotheses all three hold for $`f = \mathrm{KG}_m u`$ and
  $`s \in [s_0, S]`$ (`memLp_restrictHyperboloid_kleinGordon`,
  `continuous_restrictHyperboloid_timeDeriv`, `integrable_hyperboloidalEnergyDensity`).

### Continuity of integrals over the hyperboloids

- **Math.** Let $`0 \le s_1`$, $`D = D(s_1, s_2)`$, and let $`f : \mathbb{R}^{1+3} \to \mathbb{R}`$
  be continuous at every point of $`D`$ and vanish at the points of $`D \setminus K`$. Then
  $`s \mapsto \int_{\mathbb{R}^3} f(\varphi_s(x), x)\, dx`$ is continuous on $`[s_1, s_2]`$.
- **Hypotheses.** $`0 \le s_1`$; $`f`$ is continuous at every point of $`D`$; $`f = 0`$ on
  $`D \setminus K`$.
- **Lean.** `VectorFieldMethod.Minkowski.continuousOn_integral_hyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L379)

```lean
theorem continuousOn_integral_hyperboloid {s₁ s₂ : ℝ} (hs₁ : 0 ≤ s₁) {f : Spacetime → ℝ}
    (hf : ∀ p ∈ regionBetweenHyperboloids s₁ s₂, ContinuousAt f p)
    (hfK : ∀ p ∈ regionBetweenHyperboloids s₁ s₂, p ∉ cone → f p = 0) :
    ContinuousOn (fun s ↦ ∫ x : EuclideanSpace ℝ (Fin 3), f (√(s ^ 2 + ‖x‖ ^ 2), x))
      (Icc s₁ s₂)
```

- **Notes.** `ContinuousAt f p` is continuity of $`f`$ at $`p`$ as a function on all of
  $`\mathbb{R}^{1+3}`$; nothing is assumed outside $`D`$. For $`s \in [s_1, s_2]`$ the point
  $`(\varphi_s(x), x)`$ lies in $`D`$, and in $`K`$ only if $`\lvert x\rvert \le s_2^2`$, so the
  integrand is continuous in $`(s, x)`$ on $`[s_1, s_2] \times \mathbb{R}^3`$ and vanishes for
  $`\lvert x\rvert \gt s_2^2`$; the statement is then continuity of a parametric integral with a
  uniform compact support (Mathlib's `continuousOn_integral_of_compact_support`, i.e. dominated
  convergence).

### Continuity of the energy

- **Math.** Under the standing hypotheses on $`D(s_0, S)`$, the functions $`s \mapsto E_m(s, u)`$
  and $`s \mapsto \lVert \mathrm{KG}_m u\rVert_{L^2_f(H_s)}`$ are continuous on $`[s_0, S]`$, and
  $`\lVert \mathrm{KG}_m u\rVert_{L^2_f(H_s)} \lt \infty`$ for $`s \in [s_0, S]`$.
- **Hypotheses.** The standing hypotheses; for the finiteness, $`s \in [s_0, S]`$.
- **Lean.** `VectorFieldMethod.Minkowski.continuousOn_hyperboloidalEnergy`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L399),
  `VectorFieldMethod.Minkowski.continuousOn_toReal_eLpNorm_restrictHyperboloid_kleinGordon`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L480),
  and `VectorFieldMethod.Minkowski.memLp_restrictHyperboloid_kleinGordon`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L443)

```lean
theorem continuousOn_hyperboloidalEnergy (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone) :
    ContinuousOn (fun s ↦ hyperboloidalEnergy m s u) (Icc s₀ S)

theorem continuousOn_toReal_eLpNorm_restrictHyperboloid_kleinGordon (m : ℝ) {s₀ S : ℝ}
    (hs₀ : 0 < s₀) {U : Set Spacetime} (hU : IsOpen U)
    (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone) :
    ContinuousOn (fun s ↦ (eLpNorm (restrictHyperboloid s (kleinGordon m u)) 2 volume).toReal)
      (Icc s₀ S)

theorem memLp_restrictHyperboloid_kleinGordon (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s : ℝ} (hs : s ∈ Icc s₀ S) :
    MemLp (restrictHyperboloid s (kleinGordon m u)) 2 volume
```

- **Notes.** All three are applications of the previous entry (with $`f = e_m[u]`$, respectively
  $`f = \lVert \mathrm{KG}_m u\rVert^2`$) or of the continuity and compact support of
  $`\mathrm{KG}_m u\vert_{H_s}`$. Since $`\lVert \mathrm{KG}_m u\rVert_{L^2_f(H_s)}`$ is finite on
  $`[s_0, S]`$, `toReal` is harmless in the second statement. The values at $`s = s_0`$ and
  $`s = S`$ are included: these are one-sided continuity statements at the endpoints.

### The integral inequality

- **Math.** Under the standing hypotheses on $`D(s_0, S)`$, for every $`s \in [s_0, S]`$,
  ```math
  E_m(s, u) \le E_m(s_0, u) + 2 \int_{s_0}^{s} \lVert \Box u - m^2 u\rVert_{L^2_f(H_{s'})}\, E_m(s', u)^{1/2}\, ds' .
  ```
- **Hypotheses.** The standing hypotheses; $`s \in [s_0, S]`$.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalEnergy_le_add_two_mul_integral`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L508)

```lean
theorem hyperboloidalEnergy_le_add_two_mul_integral (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s : ℝ} (hs : s ∈ Icc s₀ S) :
    hyperboloidalEnergy m s u ≤ hyperboloidalEnergy m s₀ u +
      2 * ∫ s' in s₀..s, (eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume).toReal *
        √(hyperboloidalEnergy m s' u)
```

- **Notes.** Proof: by the energy identity between $`H_{s_0}`$ and $`H_s`$ and the foliation
  formula,
  $`E_m(s, u) - E_m(s_0, u) = -2 \int_{s_0}^{s} \int_{\mathbb{R}^3} (s'/t) \langle \mathrm{KG}_m u, \partial_t u\rangle(t, x)\, dx\, ds'`$
  with $`t = \varphi_{s'}(x)`$, and the inner integral is bounded by Cauchy–Schwarz on
  $`H_{s'}`$. All quantities are genuine: the norms are finite (previous entry), the energies are
  integrals of integrable functions (`integrable_hyperboloidalEnergyDensity` of
  [`hyperboloidal-energy.md`](hyperboloidal-energy.md)), and the integrand on the right is
  continuous on $`[s_0, S]`$, hence integrable. The case $`s = s_0`$ needs no separate argument,
  since the energy identity between intermediate hyperboloids allows $`s_1 = s_2`$.

### The square-root Grönwall inequality

- **Math.** Let $`a, b, A \in \mathbb{R}`$, $`E : [a, b] \to \mathbb{R}`$ continuous, and
  $`g : [a, b] \to [0, \infty)`$ integrable. If
  ```math
  E(s) \le A + 2 \int_a^s g(\tau)\, E(\tau)^{1/2}\, d\tau \qquad \text{for all } s \in [a, b],
  ```
  then
  ```math
  E(s)^{1/2} \le A^{1/2} + \int_a^s g(\tau)\, d\tau \qquad \text{for all } s \in [a, b].
  ```
  (Usually one assumes $`E \ge 0`$ and $`A \ge 0`$; with the convention $`r^{1/2} = 0`$ for
  $`r \lt 0`$ the statement holds without these assumptions.) The main step: if $`A \gt 0`$, then
  $`\Phi(s)^{1/2} \le A^{1/2} + \int_a^s g`$ on $`[a, b]`$ for
  $`\Phi(s) = A + 2 \int_a^s g E^{1/2}`$.
- **Hypotheses.** $`E`$ is continuous on $`[a, b]`$; $`g`$ is integrable on $`[a, b]`$ and
  $`g \ge 0`$ on $`[a, b]`$; the integral inequality holds on $`[a, b]`$. For the main step,
  moreover $`A \gt 0`$.
- **Lean.** `VectorFieldMethod.Analysis.sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Analysis/SqrtGronwall.lean#L174),
  and `VectorFieldMethod.Analysis.sqrt_add_two_mul_integral_le_of_pos`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Analysis/SqrtGronwall.lean#L54)

```lean
theorem sqrt_le_sqrt_add_integral_of_le_add_two_mul_integral (hE : ContinuousOn E (Icc a b))
    (hg : IntegrableOn g (Icc a b)) (hg0 : ∀ s ∈ Icc a b, 0 ≤ g s)
    (h : ∀ s ∈ Icc a b, E s ≤ A + 2 * ∫ τ in a..s, g τ * √(E τ)) {s : ℝ} (hs : s ∈ Icc a b) :
    √(E s) ≤ √A + ∫ τ in a..s, g τ

theorem sqrt_add_two_mul_integral_le_of_pos (hA : 0 < A) (hE : ContinuousOn E (Icc a b))
    (hg : IntegrableOn g (Icc a b)) (hg0 : ∀ s ∈ Icc a b, 0 ≤ g s)
    (h : ∀ s ∈ Icc a b, E s ≤ A + 2 * ∫ τ in a..s, g τ * √(E τ)) {s : ℝ} (hs : s ∈ Icc a b) :
    √(A + 2 * ∫ τ in a..s, g τ * √(E τ)) ≤ √A + ∫ τ in a..s, g τ
```

- **Notes.**
  - `E` and `g` are functions on $`\mathbb{R}`$; only their values on $`[a, b]`$ enter. `√r` is
    `Real.sqrt r`, which is $`0`$ for $`r \lt 0`$; this is why the hypotheses $`E \ge 0`$,
    $`A \ge 0`$ are not needed (and an unused hypothesis would be reported by the linter, an error
    in CI). For $`a \gt b`$ the statement is empty.
  - Dropping $`E \ge 0`$ is a genuine gain: in the sanity check $`E(s) = 2s - 1`$, $`A = 1`$,
    $`g = 1`$ on $`[0, 1]`$, $`E(0) = -1 \lt 0`$, and the theorem gives
    $`(2s - 1)^{1/2} \le 1 + s`$. Dropping $`A \ge 0`$ only adds a degenerate case: for $`A \lt 0`$
    the hypothesis forces $`E \le A \lt 0`$ on $`[a, b]`$ (as long as $`E \lt 0`$ on $`[a, s]`$, the
    integral vanishes and $`E(s) \le A`$; by continuity this persists up to $`b`$), and the conclusion
    reduces to $`0 \le \int_a^s g`$.
  - `g` is only integrable, so $`\Phi`$ need not be differentiable everywhere, and the proof does
    not differentiate. With $`R = \Phi^{1/2}`$ and $`G(s) = \int_a^s g`$: since $`E \le \Phi`$ and
    $`\Phi`$ is nondecreasing, $`\Phi(z) - \Phi(x) \le 2 R(z) (G(z) - G(x))`$ for
    $`a \le x \le z \le b`$, hence
    $`2 A^{1/2} \big((R(z) - R(x)) - (G(z) - G(x))\big) \le (R(z) - R(x))(G(z) - G(x))`$: the
    increments of $`R - G`$ are of second order. A continuous induction on $`[a, b]`$
    (`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`), using the continuity of $`G`$, gives
    $`R - A^{1/2} - G \le \varepsilon (R - A^{1/2})`$ on $`[a, b]`$ for every
    $`\varepsilon \gt 0`$. The general case follows by applying the main step to
    $`\max(A, 0) + \delta^2`$ and letting $`\delta \to 0`$.
  - The integrals are interval integrals `∫ τ in a..s`; for $`s \in [a, b]`$ they are integrals
    over $`(a, s]`$ of integrable functions ($`g E^{1/2}`$ is integrable on $`[a, b]`$ since
    $`E^{1/2}`$ is continuous there), so they are genuine.

### The hyperboloidal energy estimate

- **Math.** Let $`F`$ be a real inner product space, $`m \in \mathbb{R}`$, $`0 \lt s_0`$,
  $`D = D(s_0, S)`$ and $`K`$ as in *Conventions*, $`U \subseteq \mathbb{R}^{1+3}`$ open with
  $`D \cap K \subseteq U`$, and $`u : \mathbb{R}^{1+3} \to F`$ of class $`C^2`$ on $`U`$ with
  $`D \cap \mathrm{supp}\, u \subseteq K`$. Then for every $`s \in [s_0, S]`$,
  ```math
  E_m(s, u)^{1/2} \le E_m(s_0, u)^{1/2} + \int_{s_0}^{s} \lVert \Box u - m^2 u\rVert_{L^2_f(H_{s'})}\, ds' ,
  ```
  where $`\lVert f\rVert_{L^2_f(H_{s'})} = \big(\int_{\mathbb{R}^3} \lVert f(\varphi_{s'}(x), x)\rVert^2 dx\big)^{1/2}`$.
  The right-hand side is finite.
- **Hypotheses.** $`F`$ is a real inner product space; the standing hypotheses
  ($`0 \lt s_0`$; $`U`$ open; $`D \cap K \subseteq U`$; $`u`$ is $`C^2`$ on $`U`$;
  $`D \cap \mathrm{supp}\, u \subseteq K`$); $`s \in [s_0, S]`$. For the finiteness, $`s \le S`$.
- **Lean.** `VectorFieldMethod.Minkowski.ofReal_sqrt_hyperboloidalEnergy_le`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L610);
  the same estimate in $`\mathbb{R}`$: `VectorFieldMethod.Minkowski.sqrt_hyperboloidalEnergy_le_add_integral`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L568);
  the finiteness of the right-hand side: `VectorFieldMethod.Minkowski.lintegral_eLpNorm_restrictHyperboloid_kleinGordon_lt_top`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L585)

```lean
theorem ofReal_sqrt_hyperboloidalEnergy_le (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s : ℝ} (hs : s ∈ Icc s₀ S) :
    ENNReal.ofReal √(hyperboloidalEnergy m s u) ≤ ENNReal.ofReal √(hyperboloidalEnergy m s₀ u) +
      ∫⁻ s' in Icc s₀ s, eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume

theorem sqrt_hyperboloidalEnergy_le_add_integral (m : ℝ) {s₀ S : ℝ} (hs₀ : 0 < s₀)
    {U : Set Spacetime} (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U)
    (hu : ContDiffOn ℝ 2 u U) (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone)
    {s : ℝ} (hs : s ∈ Icc s₀ S) :
    √(hyperboloidalEnergy m s u) ≤ √(hyperboloidalEnergy m s₀ u) +
      ∫ s' in s₀..s, (eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume).toReal

theorem lintegral_eLpNorm_restrictHyperboloid_kleinGordon_lt_top (m : ℝ) {s₀ S : ℝ}
    (hs₀ : 0 < s₀) {U : Set Spacetime} (hU : IsOpen U)
    (hDU : regionBetweenHyperboloids s₀ S ∩ cone ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hsupp : regionBetweenHyperboloids s₀ S ∩ tsupport u ⊆ cone) {s : ℝ} (hs : s ≤ S) :
    ∫⁻ s' in Icc s₀ s, eLpNorm (restrictHyperboloid s' (kleinGordon m u)) 2 volume < ∞
```

- **Notes.**
  - **Form of the statement.** The main statement is in `ENNReal` $`= [0, \infty]`$. The left side
    is `ENNReal.ofReal` of `√(hyperboloidalEnergy m s u)`; since `Real.sqrt` is always nonnegative,
    `ENNReal.ofReal` does not truncate it, and the nonnegativity of the energy
    (`hyperboloidalEnergy_nonneg`) only guarantees that `√` is the genuine square root
    (`Real.sqrt` is $`0`$ on negative numbers). The right side is a Lebesgue integral of
    $`s' \mapsto \lVert \mathrm{KG}_m u\rVert_{L^2_f(H_{s'})} \in [0, \infty]`$ over $`[s_0, s]`$,
    which makes sense without any integrability or measurability hypothesis. No integrability,
    finiteness or decay assumption is made. The integral over $`[s_0, s]`$ equals
    $`\int_{s_0}^{s}`$ (endpoints have measure zero).
  - **The right side is finite** under the hypotheses
    (`lintegral_eLpNorm_restrictHyperboloid_kleinGordon_lt_top`): the theorem is never the trivial
    inequality "$`\le \infty`$". The real form `sqrt_hyperboloidalEnergy_le_add_integral` uses
    `toReal` of the norms, which are finite on $`[s_0, S]`$ (`memLp_restrictHyperboloid_kleinGordon`),
    and an interval integral of a continuous function; it is the conclusion of the square-root
    Grönwall inequality.
  - **Proof.** The square-root Grönwall inequality with $`E(s) = E_m(s, u)`$,
    $`g(s) = \lVert \mathrm{KG}_m u\rVert_{L^2_f(H_s)}`$ and $`A = E_m(s_0, u)`$ on $`[s_0, S]`$:
    its hypotheses are *Continuity of the energy* and *The integral inequality*.
  - **Correspondence with LeFloch–Ma.** This is the counterpart of the scalar energy estimate
    (2.1.10) of LeFloch–Ma's monograph (arXiv:1411.4910; see *Conventions*). There the mass is
    $`\sigma`$ (in §2.3 the masses are $`c_i`$), the energy is defined in (2.1.11) and is
    `hyperboloidalEnergy σ s u` (normalized without $`\tfrac12`$ as here), and the Klein–Gordon
    operator is $`(\partial_t^2 - \Delta + \sigma^2) u = -\mathrm{KG}_\sigma u`$; with $`m = \sigma`$
    the theorem reads
    $`E_\sigma(s, u)^{1/2} \le E_\sigma(s_0, u)^{1/2} + \int_{s_0}^{s} \lVert (\partial_t^2 - \Delta + \sigma^2) u\rVert_{L^2(H_{s'})} ds'`$,
    with $`E_\sigma(s, u)`$ = `hyperboloidalEnergy σ s u` and their norm
    $`\lVert \cdot\rVert_{L^2(H_{s'})}`$ of (2.4.2), for the flat measure $`dx`$ (written
    $`L^2_f(H_{s'})`$ in this file, a notation from LeFloch–Ma's later papers). For $`\sigma = 0`$
    it is the estimate for the wave equation. The monograph starts from the initial hyperboloid
    $`H_{s_0}`$ with $`s_0 = B + 1`$, not necessarily $`2`$; here $`s_0 \gt 0`$ is arbitrary. Their
    cone (2.1.2), $`\{r \lt t - 1\}`$, has closure $`K`$. Here the field need only be $`C^2`$ near
    $`D \cap K`$, and $`u`$ need not solve any equation: the Klein–Gordon operator appears on the
    right-hand side.
  - **Content.** As for the energy identity, $`D \cap K`$ is nonempty only if $`S \ge 1`$. The
    sanity checks give data ($`s_0 = 2`$, $`S = 5`$, $`s = 4`$, $`m \neq 0`$) for which
    $`E_m(2, u) = 0`$ and the estimate reads
    $`0 \lt E_m(4, u)^{1/2} \le \int_2^4 \lVert \mathrm{KG}_m u\rVert_{L^2_f(H_{s'})} ds' \lt \infty`$.

## Sanity checks

The sections "Sanity checks" at the end of the two files contain the following `example`s. In the
Minkowski file, the field is $`F = \mathbb{R}`$ and $`u`$ is a smooth bump function
(`ContDiffBump`) centered at $`(t, x) = (4, 0)`$, equal to $`1`$ on the closed ball of radius
$`1/4`$ and vanishing outside the open ball of radius $`1/2`$, for the max norm
$`\max(\lvert t - 4\rvert, \lvert x\rvert)`$ of `Spacetime` (the function of the sanity checks of
[`hyperboloidal-energy.md`](hyperboloidal-energy.md), which is private to its file and is therefore
defined again). Its closed support $`\{\lvert t - 4\rvert \le 1/2,\ \lvert x\rvert \le 1/2\}`$ lies
in $`K`$ (there $`t \ge 7/2`$), meets $`H_4`$ near $`(4, 0)`$, and does not meet $`H_2`$. In all
examples but one, $`U = \mathbb{R}^{1+3}`$; the example for the transfer of the hypotheses uses the
smaller open set $`U = \{t \gt 1/2\}`$.

| Statement | Line |
| --- | --- |
| The foliation formula applies to $`g = u`$ (continuous with compact support, hence integrable on $`D(2, 4)`$) | [L656](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L656) |
| The foliation formula for nonnegative functions applies to $`g = \max(u, 0)`$ (`ENNReal.ofReal ∘ u`, measurable with values in $`[0, \infty]`$) on $`D(2, 4)`$ | [L665](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L665) |
| The hypotheses of the energy identity pass from $`D(2, 5)`$ to $`D(3, 4)`$: for $`U = \{t \gt 1/2\}`$, an open set containing $`K`$, and for the closed support of $`u`$ | [L694](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L694) |
| The energy identity between intermediate hyperboloids applies with the hypotheses on $`D(2, 5)`$, between $`H_3`$ and $`H_4`$ | [L708](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L708) |
| Cauchy–Schwarz on $`H_4`$ applies with $`f = u`$: $`f\vert_{H_4}`$ is continuous with compact support, $`\partial_t u\vert_{H_4}`$ is continuous, $`e_m[u]\vert_{H_4}`$ is integrable | [L721](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L721) |
| Continuity of integrals over the hyperboloids applies to $`f = u`$ on $`[2, 5]`$ ($`u`$ is continuous and vanishes outside $`K`$) | [L738](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L738) |
| $`s \mapsto E_m(s, u)`$ is continuous on $`[2, 5]`$ | [L744](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L744) |
| $`\lVert \mathrm{KG}_m u\rVert_{L^2_f(H_4)} \lt \infty`$, and $`s \mapsto \lVert \mathrm{KG}_m u\rVert_{L^2_f(H_s)}`$ is continuous on $`[2, 5]`$ | [L751](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L751) |
| The integral inequality applies with $`s_0 = 2`$, $`S = 5`$, $`s = 4`$ | [L764](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L764) |
| The energy estimate applies with $`s_0 = 2`$, $`S = 5`$, $`s = 4`$, every $`m`$ | [L776](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L776) |
| The real form of the energy estimate applies with the same data | [L787](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L787) |
| For $`m \neq 0`$: $`E_m(2, u) = 0`$, $`0 \lt E_m(4, u)^{1/2}`$, the estimate gives $`E_m(4, u)^{1/2} \le \int_{[2, 4]} \lVert \mathrm{KG}_m u\rVert_{L^2_f(H_{s'})} ds'`$, and this integral is finite | [L812](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Minkowski/HyperboloidalEnergyEstimate.lean#L812) |
| Square-root Grönwall inequality: $`E(s) = s^2`$, $`g = 1`$, $`A = 0`$ on $`[0, 1]`$; the hypothesis holds with equality ($`s^2 = 2 \int_0^s (\tau^2)^{1/2} d\tau`$), and the conclusion $`(s^2)^{1/2} \le 0^{1/2} + \int_0^s 1 = s`$ is an equality | [L201](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Analysis/SqrtGronwall.lean#L201) |
| Main step ($`A \gt 0`$): $`E(s) = (1 + s)^2`$, $`g = 1`$, $`A = 1`$ on $`[0, 1]`$; the hypothesis holds with equality ($`(1 + s)^2 = 1 + 2 \int_0^s ((1 + \tau)^2)^{1/2} d\tau`$) and the conclusion is an equality (both sides are $`1 + s`$); both equalities are proved, and the theorem is applied | [L216](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Analysis/SqrtGronwall.lean#L216) |
| Square-root Grönwall inequality with $`E`$ taking negative values: $`E(s) = 2s - 1`$, $`g = 1`$, $`A = 1`$ on $`[0, 1]`$; $`E(0) = -1 \lt 0`$, the hypothesis holds, and the theorem gives $`(2s - 1)^{1/2} \le 1 + s`$ | [L246](https://github.com/Oho1e/VectorFieldMethod/blob/6f2b67a6e3605923a6f00cb43a0ae77de1b00c5e/VectorFieldMethod/Analysis/SqrtGronwall.lean#L246) |

The examples apply each main theorem whose hypotheses go beyond regularity and signs of numbers to
concrete data satisfying all its hypotheses (the foliation formula for nonnegative functions, whose
only further hypothesis is measurability, is included as well). The example for $`m \neq 0`$ shows
that the energy estimate is then a genuine inequality between a positive left-hand side and a
finite right-hand side (the energy on $`H_2`$ vanishes, so the right-hand side reduces to the
integral of the norms of $`\mathrm{KG}_m u`$, which is therefore positive). The Grönwall examples
with $`E(s) = s^2`$ and $`E(s) = (1 + s)^2`$ show that the inequality and its main step are sharp,
and the example $`E(s) = 2s - 1`$ that $`E`$ may take negative values. The pointwise bound and the
identity of measures have only sign hypotheses and are not listed.
