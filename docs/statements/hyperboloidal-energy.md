# Hyperboloidal energy of the Klein–Gordon field: statements

Layer: `VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean` (the semi-hyperboloidal frame, the
energy density and the energy, pointwise identities) and
`VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean` (the passage to the coordinates of
the divergence theorems, the energy identity). The layer is built on the Minkowski coordinate layer
([`minkowski.md`](minkowski.md)), the energy-momentum layer
([`energy-momentum.md`](energy-momentum.md)) and the localized divergence theorem between two
hyperboloids ([`divergence.md`](divergence.md)). All declarations are in the namespace
`VectorFieldMethod.Minkowski`. The links below point to commit
[`65434c1`](https://github.com/Oho1e/VectorFieldMethod/tree/65434c138668e720ea41dbd287fb6c1298ad00f9)
of `main`. How to read the entries:
[`README.md`](README.md).

## Conventions

- **Coordinates.** As in the Minkowski layer, a point of `Spacetime = ℝ × EuclideanSpace ℝ (Fin 3)`
  is $`p = (t, x)`$, time first (`p.1 = t`, `p.2 = x`). The divergence theorems of
  [`divergence.md`](divergence.md) work on $`E \times \mathbb{R}`$, time second. The entries
  *Divergence in the coordinates of the divergence theorems*, *The coordinate swap is measure
  preserving* and *Change of variables* below connect the two.
- **Hyperboloids, region, cone.** For $`s \gt 0`$ the hyperboloid is
  $`H_s = \{(t, x) : t = \sqrt{s^2 + \lvert x\rvert^2}\}`$, written `√(s ^ 2 + ‖x‖ ^ 2)` in Lean. For
  $`s_1 \lt s_2`$ the closed region between two hyperboloids is
  ```math
  D = \{(t, x) : \sqrt{s_1^2 + |x|^2} \le t \le \sqrt{s_2^2 + |x|^2}\},
  ```
  in Lean `regionBetweenHyperboloids s₁ s₂`, and the closed solid cone is
  $`K = \{(t, x) : \lvert x\rvert \le t - 1\}`$, in Lean `cone` (both are defined in
  `HyperboloidalEnergyIdentity.lean`, see *Definitions*; LeFloch–Ma's cone $`\{r \lt t - 1\}`$,
  (2.1.2) of arXiv:1411.4910, has closure $`K`$).
- **Normalization: no factor $`\tfrac12`$.** Quoted from the module docstring of
  [`HyperboloidalEnergy.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L45):

  > The energy density and the energy carry no factor `½`, as in LeFloch–Ma: apart from the cross
  > terms `2 ∑ a, (x_a / t) ⟪∂_a u, ∂_t u⟫`, the energy density is
  > `‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²`, twice the energy density `P⁰` of `EnergyMomentum.lean`,
  > whose energy-momentum tensor carries the factor `½`. Precisely,
  > `e_m[u] = 2 (P⁰ - ∑ a, (x_a / t) P^a)` (`hyperboloidalEnergyDensity_eq_energyCurrent`).

  So, with the energy current $`P`$ of [`energy-momentum.md`](energy-momentum.md) (normalized with
  $`\tfrac12`$), $`e_m[u] = 2\big(P^0 - \sum_a (x^a / t) P^a\big)`$: the energy density is twice the
  flux density of $`P`$ through the hyperboloids.
- **Notation, and correspondence with LeFloch–Ma.** In this file the subscript of $`e_m[u]`$ and
  $`E_m(s, u)`$ is the mass $`m`$: $`E_m(s, u)`$ is `hyperboloidalEnergy m s u`. LeFloch–Ma,
  *The Hyperboloidal Foliation Method* (World Scientific, 2014; arXiv:1411.4910), define the
  hyperboloidal energy in (2.1.11) (§2.1, where the mass is denoted $`\sigma`$), and in §2.3,
  (2.3.2), write the energy of a field of mass $`c`$ as $`E_{m,c}(s, u)`$, where the subscript
  $`m`$ refers to Minkowski spacetime, not to the mass, and $`E_m(s, u) := E_{m,0}(s, u)`$ for the
  massless energy. So **`hyperboloidalEnergy c s u` is their $`E_{m,c}(s, u)`$, and
  `hyperboloidalEnergy 0 s u` is their $`E_m(s, u)`$.** Their energy estimate (2.1.10) is
  formalized in the next layer, [`hyperboloidal-energy-estimate.md`](hyperboloidal-energy-estimate.md).
  For a real field,
  ```math
  E_{m,c}(s, u) = \int_{H_s} \Big( (\partial_t u)^2 + \sum_a (\partial_a u)^2 + 2 \sum_a \frac{x^a}{t}\, \partial_t u\, \partial_a u + c^2 u^2 \Big)\, dx
  = \int_{H_s} \Big( \sum_a (\underline{\partial}_a u)^2 + \Big(\frac{s}{t}\Big)^2 (\partial_t u)^2 + c^2 u^2 \Big)\, dx ,
  ```
  where $`\int_{H_s} f\, dx`$ means $`\int_{\mathbb{R}^3} f\big(\sqrt{s^2 + \lvert x\rvert^2}, x\big)\, dx`$.
  For a general $`F`$ the products are replaced by inner products and the squares by squared
  norms. The second form is `hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv_of_hyperboloid`.
- **Signs.** The Klein–Gordon operator of this project is $`\mathrm{KG}_m u = \Box u - m^2 u`$
  (`kleinGordon m u`) with $`\Box = -\partial_t^2 + \Delta`$. LeFloch–Ma's wave operator has the
  opposite sign, $`\partial_t^2 - \Delta`$, and their Klein–Gordon operator for the mass $`c`$ is
  $`(\partial_t^2 - \Delta + c^2) u = -\mathrm{KG}_c u`$ (see [`minkowski.md`](minkowski.md)). To
  avoid the clash of notation, this file writes their operator as $`(\partial_t^2 - \Delta + c^2) u`$
  or $`-\mathrm{KG}_c u`$, never with the symbol $`\Box`$. In their notation the energy identity
  below reads
  $`E_{m,c}(s_2, u) - E_{m,c}(s_1, u) = 2 \int_D \big((\partial_t^2 - \Delta + c^2) u\big)\, \partial_t u\, dx\, dt = -2 \int_D (\mathrm{KG}_c u)\, \partial_t u\, dx\, dt`$;
  see the notes of *The hyperboloidal energy identity* for the forms in which they state it.
- **Measures.** On `EuclideanSpace ℝ (Fin 3)`, `volume` is Lebesgue measure on $`\mathbb{R}^3`$
  (Mathlib's measure on a finite-dimensional inner product space, normalized by orthonormal bases).
  On `Spacetime`, `volume` is the product measure `volume.prod volume`, i.e. $`dt\, dx`$ (Mathlib's
  `MeasureTheory.Measure.volume_eq_prod`, true by definition). Integrals without `∂μ` use `volume`.

**Notation in the Math lines below.** As in [`minkowski.md`](minkowski.md): $`p = (t, x)`$ is a
point of $`\mathbb{R}^{1+3}`$, $`r = \lvert x\rvert`$, spatial indices $`a \in \{1, 2, 3\}`$
correspond to the Lean indices `a - 1 : Fin 3` (and to the spacetime indices `Fin.succ (a - 1)`),
$`x^a = x_a`$, and $`e_1, e_2, e_3`$ is the standard basis of $`\mathbb{R}^3`$. Functions
$`u : \mathbb{R}^{1+3} \to F`$ take values in a real inner product space $`F`$ with inner product
$`\langle \cdot, \cdot \rangle`$ and norm $`\lVert \cdot \rVert`$; $`m \in \mathbb{R}`$ is the mass.
$`\partial_t, \partial_a, L_a, \Box`$ are the operators of the Minkowski layer, with the Lean
convention that derivatives at points of non-differentiability are $`0`$ (see the README).
$`P^\alpha`$ is the energy current `energyCurrent m u α` of the energy-momentum layer,
$`P^0 = \tfrac12 (\lVert \partial_t u\rVert^2 + \sum_a \lVert \partial_a u\rVert^2 + m^2 \lVert u\rVert^2)`$,
$`P^a = -\langle \partial_a u, \partial_t u\rangle`$. $`\mathrm{supp}\, f`$ is the closed support
`tsupport f`.

## Context

The `variable` lines of the two files. Their only hypotheses are structural: $`F`$ is a real inner
product space (no completeness or finite dimension is assumed; all integrals are integrals of
real-valued functions).

[`HyperboloidalEnergy.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L69):

```lean
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {u : Spacetime → F} {p : Spacetime}
```

[`HyperboloidalEnergyIdentity.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L156):

```lean
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {u : Spacetime → F}
```

`u` and `p` are implicit arguments of the theorems that do not list them explicitly; they are then
inferred from the hypotheses.

## Definitions

### Semi-hyperboloidal derivative $`\underline{\partial}_a`$

- **Math.** For $`a \in \{1, 2, 3\}`$ and $`u : \mathbb{R}^{1+3} \to F`$,
  ```math
  \underline{\partial}_a u(t, x) = \partial_a u(t, x) + \frac{x^a}{t}\, \partial_t u(t, x) \qquad (t \neq 0).
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`u`$ is arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.semiHyperboloidalDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L76)

```lean
def semiHyperboloidalDeriv (a : Fin 3) (u : Spacetime → F) : Spacetime → F :=
  fun p ↦ ∂ₓ[a] u p + (spaceCoord a p / timeCoord p) • ∂ₜ u p
```

- **Notes.** The Lean argument `a : Fin 3` is the mathematical index $`a + 1`$. At $`t = 0`$ the
  coefficient `spaceCoord a p / timeCoord p` is the junk value $`0`$ (`x / 0 = 0`), so the definition
  gives $`\partial_a u(0, x)`$ there; the statements below about $`\underline{\partial}_a`$ assume
  $`t \neq 0`$ or are about points $`(\sqrt{s^2 + \lvert x\rvert^2}, x)`$ of hyperboloids with
  $`s \neq 0`$, where $`t \ge \lvert s\rvert \gt 0`$. The vector fields
  $`\underline{\partial}_a`$ are tangent to the hyperboloids $`t^2 - r^2 = \mathrm{const}`$.

### Hyperboloidal energy density $`e_m[u]`$

- **Math.** For $`m \in \mathbb{R}`$ and $`u : \mathbb{R}^{1+3} \to F`$, at $`p = (t, x)`$ with
  $`t \neq 0`$,
  ```math
  e_m[u](p) = \lVert \partial_t u(p) \rVert^2 + \sum_{a=1}^{3} \lVert \partial_a u(p) \rVert^2
    + 2 \sum_{a=1}^{3} \frac{x^a}{t}\, \langle \partial_a u(p), \partial_t u(p) \rangle + m^2 \lVert u(p) \rVert^2 .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`m`$ and $`u`$ are arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalEnergyDensity`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L106)

```lean
def hyperboloidalEnergyDensity (m : ℝ) (u : Spacetime → F) : Spacetime → ℝ :=
  fun p ↦ ‖∂ₜ u p‖ ^ 2 + ∑ a, ‖∂ₓ[a] u p‖ ^ 2 +
    2 * ∑ a, spaceCoord a p / timeCoord p * ⟪∂ₓ[a] u p, ∂ₜ u p⟫ + m ^ 2 * ‖u p‖ ^ 2
```

- **Notes.** No factor $`\tfrac12`$ (see *Conventions*). At $`t = 0`$ the coefficients
  $`x^a / t`$ are the junk value $`0`$. For $`F = \mathbb{R}`$ it is
  $`(\partial_t u)^2 + \sum_a (\partial_a u)^2 + 2 \sum_a (x^a / t)\, \partial_a u\, \partial_t u + m^2 u^2`$.
  The definition makes sense for every $`u`$; where $`u`$ is not differentiable it contains the junk
  value $`0`$ of the derivatives.

### Hyperboloidal energy $`E_m(s, u)`$

- **Math.** For $`m, s \in \mathbb{R}`$ and $`u : \mathbb{R}^{1+3} \to F`$,
  ```math
  E_m(s, u) = \int_{\mathbb{R}^3} e_m[u]\big(\sqrt{s^2 + |x|^2}, x\big)\, dx .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`m`$, $`s`$, $`u`$ are arbitrary.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalEnergy`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L124)

```lean
def hyperboloidalEnergy (m s : ℝ) (u : Spacetime → F) : ℝ :=
  ∫ x : EuclideanSpace ℝ (Fin 3), hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x)
```

- **Notes.** The integral is for Lebesgue measure on $`\mathbb{R}^3`$; it is the junk value $`0`$
  if $`x \mapsto e_m[u](\sqrt{s^2 + \lvert x\rvert^2}, x)`$ is not integrable. Under the hypotheses
  of the energy identity the integrand is integrable for $`s = s_1`$, $`s = s_2`$ and every
  $`s`$ in between (`integrable_hyperboloidalEnergyDensity`, below). The argument order
  `hyperboloidalEnergy m s u` follows the notation $`E_m(s, u)`$, whose subscript is the mass (in
  LeFloch–Ma's notation this is $`E_{m,c}(s, u)`$ with $`c = m`$, see *Conventions*). The energy is
  nonnegative for every $`s`$ (`hyperboloidalEnergy_nonneg`, in the entry *Positivity of the energy
  density*).

### Region between two hyperboloids $`D`$

- **Math.** For $`s_1, s_2 \in \mathbb{R}`$,
  ```math
  D = \{(t, x) \in \mathbb{R}^{1+3} : \sqrt{s_1^2 + |x|^2} \le t \le \sqrt{s_2^2 + |x|^2}\}.
  ```
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.regionBetweenHyperboloids`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L131)

```lean
def regionBetweenHyperboloids (s₁ s₂ : ℝ) : Set Spacetime :=
  {p | p.1 ∈ Icc √(s₁ ^ 2 + ‖p.2‖ ^ 2) √(s₂ ^ 2 + ‖p.2‖ ^ 2)}
```

- **Notes.** For $`0 \lt s_1 \le s_2`$ it is the closed region between the hyperboloids $`H_{s_1}`$
  and $`H_{s_2}`$. Membership unfolds by `mem_regionBetweenHyperboloids`
  (`p ∈ regionBetweenHyperboloids s₁ s₂ ↔ √(s₁ ^ 2 + ‖p.2‖ ^ 2) ≤ p.1 ∧ p.1 ≤ √(s₂ ^ 2 + ‖p.2‖ ^ 2)`,
  by definition), and the set is closed (`isClosed_regionBetweenHyperboloids`). In the coordinates
  $`(x, t)`$ of the divergence theorems it is the region `{p : E × ℝ | p.2 ∈ Icc …}` of
  [`divergence.md`](divergence.md).

### Cone $`K`$

- **Math.** $`K = \{(t, x) \in \mathbb{R}^{1+3} : \lvert x\rvert \le t - 1\}`$.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.cone`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L136)

```lean
def cone : Set Spacetime :=
  {p | ‖p.2‖ ≤ p.1 - 1}
```

- **Notes.** The closed solid cone with vertex $`(1, 0)`$; LeFloch–Ma's cone $`\{r \lt t - 1\}`$
  ((2.1.2) of arXiv:1411.4910) has closure $`K`$. Membership: `mem_cone`
  (`p ∈ cone ↔ ‖p.2‖ ≤ p.1 - 1`, by definition); closedness: `isClosed_cone`. The set
  $`D \cap K`$ is compact (`isCompact_regionBetweenHyperboloids_inter_cone`).

## Main theorems

### The boost in the semi-hyperboloidal frame

- **Math.** Let $`a \in \{1, 2, 3\}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`p = (t, x)`$ with
  $`t \neq 0`$. Then $`L_a u(p) = t\, \underline{\partial}_a u(p)`$.
- **Hypotheses.** $`F`$ is a real inner product space; $`t \neq 0`$ (`timeCoord p ≠ 0`); no
  regularity of $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.boost_eq_timeCoord_smul_semiHyperboloidalDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L85)

```lean
theorem boost_eq_timeCoord_smul_semiHyperboloidalDeriv (a : Fin 3) (u : Spacetime → F)
    (hp : timeCoord p ≠ 0) : boost a u p = timeCoord p • semiHyperboloidalDeriv a u p
```

- **Notes.** `p` is the implicit variable of the *Context* section. No differentiability is needed:
  $`L_a u = t\,\partial_a u + x^a \partial_t u`$ (`boost_eq`) and $`\underline{\partial}_a u`$ use the
  same derivative $`Du(p)`$.

### The energy density in the semi-hyperboloidal frame

- **Math.** Let $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`p = (t, x)`$ with
  $`t \neq 0`$, $`r = \lvert x\rvert`$. Then
  ```math
  e_m[u](p) = \sum_{a=1}^{3} \lVert \underline{\partial}_a u(p) \rVert^2 + \frac{t^2 - r^2}{t^2}\, \lVert \partial_t u(p) \rVert^2 + m^2 \lVert u(p) \rVert^2 .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`t \neq 0`$; no regularity of $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L136)

```lean
theorem hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv (m : ℝ) (u : Spacetime → F)
    (hp : timeCoord p ≠ 0) :
    hyperboloidalEnergyDensity m u p = ∑ a, ‖semiHyperboloidalDeriv a u p‖ ^ 2 +
      (timeCoord p ^ 2 - radius p ^ 2) / timeCoord p ^ 2 * ‖∂ₜ u p‖ ^ 2 + m ^ 2 * ‖u p‖ ^ 2
```

- **Notes.** `radius p` is $`r = \lvert x\rvert`$. The identity is algebraic: it expands
  $`\lVert \underline{\partial}_a u\rVert^2`$ (`norm_semiHyperboloidalDeriv_sq`) and uses
  $`r^2 = \sum_a (x^a)^2`$.

### The energy density on a hyperboloid

- **Math.** Let $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$, $`s \neq 0`$, $`x \in \mathbb{R}^3`$
  and $`t = \sqrt{s^2 + \lvert x\rvert^2}`$ (so that $`(t, x) \in H_{\lvert s\rvert}`$ and
  $`t^2 - r^2 = s^2`$). Then, at the point $`(t, x)`$,
  ```math
  e_m[u](t, x) = \sum_{a=1}^{3} \lVert \underline{\partial}_a u(t, x) \rVert^2 + \frac{s^2}{t^2}\, \lVert \partial_t u(t, x) \rVert^2 + m^2 \lVert u(t, x) \rVert^2 .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`s \neq 0`$; no regularity of $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv_of_hyperboloid`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L148)

```lean
theorem hyperboloidalEnergyDensity_eq_sum_semiHyperboloidalDeriv_of_hyperboloid (m : ℝ)
    (u : Spacetime → F) {s : ℝ} (hs : s ≠ 0) (x : EuclideanSpace ℝ (Fin 3)) :
    hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x) =
      ∑ a, ‖semiHyperboloidalDeriv a u (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2 +
        s ^ 2 / √(s ^ 2 + ‖x‖ ^ 2) ^ 2 * ‖∂ₜ u (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2 +
        m ^ 2 * ‖u (√(s ^ 2 + ‖x‖ ^ 2), x)‖ ^ 2
```

- **Notes.** $`s^2 / t^2`$ is written `s ^ 2 / √(s ^ 2 + ‖x‖ ^ 2) ^ 2`. With $`s \neq 0`$ the radicand
  is positive and $`t \gt 0`$, so no junk value of `√` or `/` occurs. This is LeFloch–Ma's second
  form of the energy density (see *Conventions*).

### Positivity of the energy density

- **Math.** Let $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`p = (t, x)`$ with
  $`\lvert x\rvert \le \lvert t\rvert`$ and $`t \neq 0`$. Then $`e_m[u](p) \ge 0`$. Moreover
  $`E_m(s, u) \ge 0`$ for every $`s \in \mathbb{R}`$.
- **Hypotheses.** $`F`$ is a real inner product space; $`\lvert x\rvert \le \lvert t\rvert`$
  (`radius p ≤ |timeCoord p|`) and $`t \neq 0`$; no regularity of $`u`$. For the energy: none.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalEnergyDensity_nonneg`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L161),
  and `VectorFieldMethod.Minkowski.hyperboloidalEnergy_nonneg`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L175)

```lean
theorem hyperboloidalEnergyDensity_nonneg (m : ℝ) (u : Spacetime → F)
    (hr : radius p ≤ |timeCoord p|) (hp : timeCoord p ≠ 0) :
    0 ≤ hyperboloidalEnergyDensity m u p

theorem hyperboloidalEnergy_nonneg (m s : ℝ) (u : Spacetime → F) :
    0 ≤ hyperboloidalEnergy m s u
```

- **Notes.** It follows from the previous entries: $`(t^2 - r^2) / t^2 \ge 0`$. With Lean's junk value
  $`x^a / 0 = 0`$, `hyperboloidalEnergyDensity m u (0, x)` is
  $`\lVert \partial_t u\rVert^2 + \sum_a \lVert \partial_a u\rVert^2 + m^2 \lVert u\rVert^2 \ge 0`$, so
  the hypothesis $`t \neq 0`$ could be dropped in Lean; it is kept because it is part of the
  mathematical statement. In the integrand of $`E_m(s, u)`$, the points with $`t \neq 0`$ satisfy
  both hypotheses, and the only possible point with $`t = 0`$ is $`(0, 0)`$, for $`s = 0`$, where the
  density is a sum of squares by the junk value just described; so `hyperboloidalEnergy_nonneg` has
  no hypothesis on $`s`$.

### The energy density and the energy current

- **Math.** For every $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`p = (t, x)`$ (with
  $`t \neq 0`$ for the formula to be meaningful),
  ```math
  e_m[u](p) = 2 \Big( P^0(p) - \sum_{a=1}^{3} \frac{x^a}{t}\, P^a(p) \Big).
  ```
- **Hypotheses.** $`F`$ is a real inner product space; no hypothesis on $`u`$ or $`p`$.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalEnergyDensity_eq_energyCurrent`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L193)

```lean
theorem hyperboloidalEnergyDensity_eq_energyCurrent (m : ℝ) (u : Spacetime → F) (p : Spacetime) :
    hyperboloidalEnergyDensity m u p = 2 * (energyCurrent m u 0 p -
      ∑ a, spaceCoord a p / timeCoord p * energyCurrent m u a.succ p)
```

- **Notes.** `energyCurrent m u 0` is $`P^0`$ and `energyCurrent m u a.succ` is $`P^{a+1}`$ for the Lean
  index `a`. $`P`$ carries the factor $`\tfrac12`$ and $`e_m`$ does not, hence the factor $`2`$. The
  mathematical statement is for $`t \neq 0`$; the Lean statement has no such hypothesis because the
  identity holds at every point in Lean: both sides contain the same coefficients
  `spaceCoord a p / timeCoord p`, with the same junk value $`0`$ at $`t = 0`$ (a hypothesis that
  the proof does not use would moreover be reported by the unused-variables linter, an error in CI).
  The flux of $`P`$ through $`H_s`$ in the parametrization of the divergence theorems is
  $`P^0 - \langle x, \sum_a P^a e_a\rangle / t = e_m[u] / 2`$ (`energyCurrent_sub_inner_div_eq`,
  [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L199)), which is how the energy enters the proof of
  the energy identity.

### Regularity of the energy current

- **Math.** Let $`m \in \mathbb{R}`$, $`U \subseteq \mathbb{R}^{1+3}`$ open and $`u \in C^2(U; F)`$.
  Then $`P^\alpha \in C^1(U)`$ for every $`\alpha \in \{0, 1, 2, 3\}`$.
- **Hypotheses.** $`F`$ is a real inner product space; $`U`$ is open; $`u`$ is $`C^2`$ on $`U`$
  (`ContDiffOn ℝ 2 u U`).
- **Lean.** `VectorFieldMethod.Minkowski.contDiffOn_energyCurrent`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L214)

```lean
theorem contDiffOn_energyCurrent (m : ℝ) {U : Set Spacetime} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (α : Fin 4) : ContDiffOn ℝ 1 (energyCurrent m u α) U
```

- **Notes.** The pointwise version (`ContDiffAt ℝ 2 u p` gives `ContDiffAt ℝ 1 (energyCurrent m u α) p`)
  is `contDiffAt_energyCurrent` ([permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L203)). For open $`U`$,
  `ContDiffOn` is the usual notion and the values of $`u`$ outside $`U`$ play no role.

### Support of the energy current

- **Math.** For every $`m \in \mathbb{R}`$, $`u : \mathbb{R}^{1+3} \to F`$ and $`\alpha`$,
  $`\mathrm{supp}\, P^\alpha \subseteq \mathrm{supp}\, u`$ (closed supports).
- **Hypotheses.** $`F`$ is a real inner product space; no hypothesis on $`u`$.
- **Lean.** `VectorFieldMethod.Minkowski.tsupport_energyCurrent_subset`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L229)

```lean
theorem tsupport_energyCurrent_subset (m : ℝ) (u : Spacetime → F) (α : Fin 4) :
    tsupport (energyCurrent m u α) ⊆ tsupport u
```

- **Notes.** Outside $`\mathrm{supp}\, u`$ both $`u`$ and $`Du`$ vanish
  (`derivAlong_of_notMem_tsupport`). The same argument gives
  $`\{e_m[u] \neq 0\} \subseteq \mathrm{supp}\, u`$ (`support_hyperboloidalEnergyDensity_subset`) and
  $`\mathrm{KG}_m u = 0`$ outside $`\mathrm{supp}\, u`$ (`kleinGordon_of_notMem_tsupport`).

### Divergence in the coordinates of the divergence theorems

- **Math.** Let $`J = (J^0, J^1, J^2, J^3)`$ with $`J^\alpha : \mathbb{R}^{1+3} \to \mathbb{R}`$, and
  write it in the coordinates $`(x, t) \in \mathbb{R}^3 \times \mathbb{R}`$ of the divergence
  theorems as $`X_0(x, t) = J^0(t, x)`$, $`X(x, t) = \sum_{a=1}^{3} J^a(t, x)\, e_a`$. Let
  $`x \in \mathbb{R}^3`$, $`t \in \mathbb{R}`$, and assume that every $`J^\alpha`$ is differentiable
  at $`(t, x)`$. Then
  ```math
  \partial_t X_0(x, t) + \mathrm{div}_x\, X(x, t) = \sum_{\alpha=0}^{3} \partial_\alpha J^\alpha(t, x).
  ```
- **Hypotheses.** Each $`J^\alpha`$ is differentiable at $`(t, x)`$.
- **Lean.** `VectorFieldMethod.Minkowski.deriv_add_spatialDivergence_eq_spacetimeDiv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L75)

```lean
theorem deriv_add_spatialDivergence_eq_spacetimeDiv (J : Fin 4 → Spacetime → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} {t : ℝ} (hJ : ∀ α, DifferentiableAt ℝ (J α) (t, x)) :
    deriv (fun s ↦ J 0 (s, x)) t +
        spatialDivergence (fun q ↦ ∑ a, J a.succ (q.2, q.1) • EuclideanSpace.single a 1) (x, t) =
      spacetimeDiv J (t, x)
```

- **Notes.** In Lean $`X_0`$ appears through `fun s ↦ J 0 (s, x)`, which is $`s \mapsto X_0(x, s)`$,
  and $`X`$ is `fun q ↦ ∑ a, J a.succ (q.2, q.1) • EuclideanSpace.single a 1` with
  $`q = (x, t)`$ (`q.2` is the time, `q.1` the spatial point, `EuclideanSpace.single a 1` is
  $`e_{a+1}`$). `spatialDivergence` and `spacetimeDiv` are the divergences of
  [`divergence.md`](divergence.md) and [`energy-momentum.md`](energy-momentum.md). The
  differentiability hypothesis is needed because of the junk value of `fderiv`.

### The coordinate swap is measure preserving

- **Math.** The map $`(x, t) \mapsto (t, x)`$ from $`\mathbb{R}^3 \times \mathbb{R}`$ with Lebesgue
  measure $`dx \otimes dt`$ to $`\mathbb{R} \times \mathbb{R}^3`$ with Lebesgue measure
  $`dt \otimes dx`$ is measure preserving.
- **Hypotheses.** None.
- **Lean.** `VectorFieldMethod.Minkowski.measurePreserving_swap_spacetime`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L114)

```lean
theorem measurePreserving_swap_spacetime :
    MeasurePreserving (Prod.swap : EuclideanSpace ℝ (Fin 3) × ℝ → Spacetime)
      (volume.prod volume) volume
```

- **Notes.** `volume.prod volume` is the measure $`\mu \otimes \mathcal{L}^1`$ of the divergence
  theorems with $`\mu`$ = Lebesgue measure on $`\mathbb{R}^3`$; `volume` on `Spacetime` is
  $`\mathcal{L}^1 \otimes \mu`$.

### Change of variables between $`\mathbb{R} \times \mathbb{R}^3`$ and $`\mathbb{R}^3 \times \mathbb{R}`$

- **Math.** Let $`G`$ be a real normed space, $`f : \mathbb{R}^{1+3} \to G`$ and
  $`S \subseteq \mathbb{R}^{1+3}`$. Then
  ```math
  \int_S f(t, x)\, d(t, x) = \int_{\{(x, t) \,:\, (t, x) \in S\}} f(t, x)\, d(x, t).
  ```
- **Hypotheses.** $`G`$ is a real normed space; no hypothesis on $`f`$ or $`S`$.
- **Lean.** `VectorFieldMethod.Minkowski.setIntegral_spacetime_eq_setIntegral_swap`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L121)

```lean
theorem setIntegral_spacetime_eq_setIntegral_swap {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (f : Spacetime → G) (s : Set Spacetime) :
    ∫ p in s, f p = ∫ q in Prod.swap ⁻¹' s, f q.swap ∂(volume.prod volume)
```

- **Notes.** `Prod.swap ⁻¹' s` is $`\{(x, t) : (t, x) \in S\}`$ and `q.swap` is $`(t, x)`$ for
  $`q = (x, t)`$. No integrability or measurability is needed: the swap is a measurable
  isomorphism of measure spaces, so both sides are genuine integrals or both are junk zeros.

### The hyperboloidal energy identity

- **Math.** Let $`F`$ be a real inner product space, $`m \in \mathbb{R}`$, $`0 \lt s_1 \lt s_2`$,
  $`D`$ and $`K`$ as in *Conventions*, $`U \subseteq \mathbb{R}^{1+3}`$ open with
  $`D \cap K \subseteq U`$, and $`u : \mathbb{R}^{1+3} \to F`$ of class $`C^2`$ on $`U`$ with
  $`D \cap \mathrm{supp}\, u \subseteq K`$. Then
  ```math
  E_m(s_2, u) - E_m(s_1, u) = -2 \int_D \big\langle (\Box u - m^2 u)(t, x),\ \partial_t u(t, x) \big\rangle\, dt\, dx .
  ```
- **Hypotheses.** $`F`$ is a real inner product space; $`0 \lt s_1`$ and $`s_1 \lt s_2`$; $`U`$ is
  open; $`D \cap K \subseteq U`$; $`u`$ is $`C^2`$ on $`U`$; $`D \cap \mathrm{supp}\, u \subseteq K`$.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalEnergy_sub_hyperboloidalEnergy`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L296)

```lean
theorem hyperboloidalEnergy_sub_hyperboloidalEnergy (m : ℝ) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) {U : Set Spacetime} (hU : IsOpen U)
    (hDU : regionBetweenHyperboloids s₁ s₂ ∩ cone ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hsupp : regionBetweenHyperboloids s₁ s₂ ∩ tsupport u ⊆ cone) :
    hyperboloidalEnergy m s₂ u - hyperboloidalEnergy m s₁ u =
      -2 * ∫ p in regionBetweenHyperboloids s₁ s₂, ⟪kleinGordon m u p, ∂ₜ u p⟫
```

- **Notes.** This is LeFloch–Ma's energy identity. In their notation, for a field of mass $`c`$
  (`m = c` here), it reads
  $`E_{m,c}(s_2, u) - E_{m,c}(s_1, u) = 2 \int_D \big((\partial_t^2 - \Delta + c^2) u\big)\, \partial_t u`$,
  where $`(\partial_t^2 - \Delta + c^2) u = -\mathrm{KG}_c u`$ (see *Conventions*).
  LeFloch–Ma state it in differential form, for $`\frac{d}{ds} E_{m,c}(s, u)`$, and in integrated
  form ((2.3.8) of arXiv:1411.4910). The volume integral over $`D`$ used here is equivalent to these
  forms: at fixed $`x`$, the change of variables $`t = \sqrt{s^2 + \lvert x\rvert^2}`$,
  $`dt = (s / t)\, ds`$ maps $`s \in [s_1, s_2]`$ onto the segment of $`D`$ above $`x`$, so the
  identity is the integral over $`s \in [s_1, s_2]`$ of
  ```math
  \frac{d}{ds} E_{m,c}(s, u) = 2 \int_{\mathbb{R}^3} \Big( \frac{s}{t}\, \partial_t u\, (\partial_t^2 - \Delta + c^2) u \Big)\big(\sqrt{s^2 + |x|^2}, x\big)\, dx .
  ```
  - *Proof.* The divergence theorem between two hyperboloids
    (`integral_divergence_between_hyperboloids_of_contDiffOn` of
    [`divergence.md`](divergence.md)) is applied to the energy current $`P`$, written in the
    coordinates $`(x, t)`$ as in *Divergence in the coordinates of the divergence theorems*, with the
    open set $`\{(x, t) : (t, x) \in U\}`$. Its hypotheses follow from *Regularity of the energy
    current* and *Support of the energy current*. Its integrand is
    $`\partial_\alpha P^\alpha = -\langle \mathrm{KG}_m u, \partial_t u\rangle`$
    (`spacetimeDiv_energyCurrent` of [`energy-momentum.md`](energy-momentum.md)) at every point of
    $`D`$, since $`u`$ is $`C^2`$ near every point of $`D`$ (`contDiffAt_of_inter_tsupport_subset`:
    near the points of $`D \cap K`$ by assumption, near the other points of $`D`$ because $`u`$
    vanishes there). Its fluxes are $`\int (P^0 - \langle x, \sum_a P^a e_a\rangle / t) = E_m(s_i, u) / 2`$
    (*The energy density and the energy current*), and the set integral is transported to
    `Spacetime` by *Change of variables*.
  - *Hypotheses.* No global smoothness and no compact support of $`u`$ are assumed, and the values
    of $`u`$ outside $`U`$ play no role. The support condition uses the closed support `tsupport`;
    as for the localized divergence theorem it cannot be replaced by `support`, since $`D`$ is not
    open. The measure on `Spacetime` is `volume`, i.e. $`dt\, dx`$.
  - *Integrability.* Both sides are genuine integrals, not junk zeros: their integrands are
    integrable under the same hypotheses (the next two entries).
  - *Content.* As in the divergence layer, $`D \cap K`$ is nonempty only if $`s_2 \ge 1`$, so for
    $`s_2 \le 1`$ the field vanishes on $`D`$ (except possibly at $`(1, 0)`$ when $`s_2 = 1`$) and
    both sides are $`0`$: the theorem has content for $`s_2 \gt 1`$. The *Sanity checks* below give
    data with $`s_1 = 2`$, $`s_2 = 4`$ for which, for $`m \neq 0`$, both sides are nonzero.

### Integrability of $`\langle \mathrm{KG}_m u, \partial_t u \rangle`$ on $`D`$

- **Math.** Let $`m, s_1, s_2 \in \mathbb{R}`$, $`D`$, $`K`$ as in *Conventions*, $`U`$ open with
  $`D \cap K \subseteq U`$, $`u \in C^2(U; F)`$ with $`D \cap \mathrm{supp}\, u \subseteq K`$. Then
  $`(t, x) \mapsto \langle (\Box u - m^2 u)(t, x), \partial_t u(t, x)\rangle`$ is integrable on $`D`$.
- **Hypotheses.** $`F`$ is a real inner product space; $`U`$ is open; $`D \cap K \subseteq U`$; $`u`$
  is $`C^2`$ on $`U`$; $`D \cap \mathrm{supp}\, u \subseteq K`$. No condition on $`s_1, s_2`$.
- **Lean.** `VectorFieldMethod.Minkowski.integrableOn_inner_kleinGordon_timeDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L220)

```lean
theorem integrableOn_inner_kleinGordon_timeDeriv (m : ℝ) {s₁ s₂ : ℝ} {U : Set Spacetime}
    (hU : IsOpen U) (hDU : regionBetweenHyperboloids s₁ s₂ ∩ cone ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hsupp : regionBetweenHyperboloids s₁ s₂ ∩ tsupport u ⊆ cone) :
    IntegrableOn (fun p ↦ ⟪kleinGordon m u p, ∂ₜ u p⟫) (regionBetweenHyperboloids s₁ s₂)
```

- **Notes.** The integrand is continuous at every point of $`D`$ and vanishes on $`D \setminus K`$,
  and $`D \cap K`$ is compact (`isCompact_regionBetweenHyperboloids_inter_cone`). These are
  the hypotheses of the energy identity, without the conditions on $`s_1, s_2`$, which are not
  needed here.

### Integrability of the energy density on the hyperboloids

- **Math.** Let $`m \in \mathbb{R}`$, $`0 \lt s_1`$, $`s \in [s_1, s_2]`$, and $`U`$, $`u`$ as in the
  energy identity. Then $`x \mapsto e_m[u](\sqrt{s^2 + \lvert x\rvert^2}, x)`$ is integrable on
  $`\mathbb{R}^3`$. In particular the integrands of $`E_m(s_1, u)`$ and $`E_m(s_2, u)`$ are
  integrable.
- **Hypotheses.** $`F`$ is a real inner product space; $`0 \lt s_1`$; $`s_1 \le s \le s_2`$; $`U`$ is
  open; $`D \cap K \subseteq U`$; $`u`$ is $`C^2`$ on $`U`$; $`D \cap \mathrm{supp}\, u \subseteq K`$.
- **Lean.** `VectorFieldMethod.Minkowski.integrable_hyperboloidalEnergyDensity`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L247)

```lean
theorem integrable_hyperboloidalEnergyDensity (m : ℝ) {s₁ s₂ s : ℝ} (hs₁ : 0 < s₁)
    (hs : s ∈ Icc s₁ s₂) {U : Set Spacetime} (hU : IsOpen U)
    (hDU : regionBetweenHyperboloids s₁ s₂ ∩ cone ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hsupp : regionBetweenHyperboloids s₁ s₂ ∩ tsupport u ⊆ cone) :
    Integrable fun x : EuclideanSpace ℝ (Fin 3) ↦
      hyperboloidalEnergyDensity m u (√(s ^ 2 + ‖x‖ ^ 2), x)
```

- **Notes.** $`H_s \subseteq D`$, and the integrand is continuous and vanishes for
  $`\lvert x\rvert \gt s^2`$ (a point of $`H_s \cap K`$ satisfies $`2\lvert x\rvert + 1 \le s^2`$).
  The condition $`s_1 \lt s_2`$ of the energy identity is not needed here.

### Conservation of the hyperboloidal energy

- **Math.** Under the hypotheses of the energy identity, if moreover
  $`\Box u - m^2 u = 0`$ on $`D \cap K`$, then $`E_m(s_1, u) = E_m(s_2, u)`$.
- **Hypotheses.** Those of the energy identity, and $`(\Box u - m^2 u)(p) = 0`$ for every
  $`p \in D \cap K`$.
- **Lean.** `VectorFieldMethod.Minkowski.hyperboloidalEnergy_eq_of_kleinGordon_eq_zero`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L366)

```lean
theorem hyperboloidalEnergy_eq_of_kleinGordon_eq_zero (m : ℝ) {s₁ s₂ : ℝ} (hs₁ : 0 < s₁)
    (hs₁₂ : s₁ < s₂) {U : Set Spacetime} (hU : IsOpen U)
    (hDU : regionBetweenHyperboloids s₁ s₂ ∩ cone ⊆ U) (hu : ContDiffOn ℝ 2 u U)
    (hsupp : regionBetweenHyperboloids s₁ s₂ ∩ tsupport u ⊆ cone)
    (hKG : ∀ p ∈ regionBetweenHyperboloids s₁ s₂ ∩ cone, kleinGordon m u p = 0) :
    hyperboloidalEnergy m s₁ u = hyperboloidalEnergy m s₂ u
```

- **Notes.** The equation is only assumed on $`D \cap K`$: on the rest of $`D`$, $`u`$ vanishes near
  every point (support condition), so the integrand $`\langle \mathrm{KG}_m u, \partial_t u\rangle`$
  vanishes there anyway.

## Sanity checks

The sections "Sanity checks" at the end of the two files contain the following `example`s. The field
of the last four is $`F = \mathbb{R}`$ and $`u`$ = a smooth bump function (`ContDiffBump`) centered
at $`(t, x) = (4, 0)`$, equal to $`1`$ on the closed ball of radius $`1/4`$ and vanishing outside the
open ball of radius $`1/2`$, for the max norm $`\max(\lvert t - 4\rvert, \lvert x\rvert)`$ of
`Spacetime`. Its closed support $`\{\lvert t - 4\rvert \le 1/2,\ \lvert x\rvert \le 1/2\}`$ lies in the
cone $`K`$ (there $`t \ge 7/2`$), and it meets $`H_4`$ near $`(4, 0)`$.

| Statement | Line |
| --- | --- |
| `hyperboloidalEnergyDensity_nonneg` applies at $`(t, x) = (1, 0)`$, for every $`u`$ | [L261](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergy.lean#L261) |
| The energy identity applies to the bump function with $`s_1 = 2`$, $`s_2 = 4`$, $`U = \mathbb{R}^{1+3}`$, every $`m`$ | [L438](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L438) |
| Both integrability statements apply to the same data ($`s = 2`$ and $`s = 4`$) | [L449](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L449) |
| For $`m \neq 0`$ and the same data: $`E_m(2, u) = 0`$, $`E_m(4, u) \gt 0`$ and, by the identity, $`\int_D \langle \mathrm{KG}_m u, \partial_t u\rangle \neq 0`$, so both sides of the identity are nonzero | [L471](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L471) |
| The conservation law applies to the bump function with $`s_1 = 5`$, $`s_2 = 6`$. Degenerate: $`D`$ does not meet the closed support of $`u`$, and for this theorem that is equivalent to $`u = 0`$ (both energies are $`0`$) | [L533](https://github.com/Oho1e/VectorFieldMethod/blob/65434c138668e720ea41dbd287fb6c1298ad00f9/VectorFieldMethod/Minkowski/HyperboloidalEnergyIdentity.lean#L533) |

The second, third and fourth examples show that the hypotheses of the energy identity and of the
integrability statements can hold simultaneously for a field that is not identically zero on $`D`$,
and that for $`m \neq 0`$ the identity is then not a trivial $`0 = 0`$: its left-hand side is
$`E_m(4, u) \gt 0`$, and the integral on its right-hand side is nonzero. The last example is
degenerate: $`D`$ does not meet the closed support of $`u`$, and the hypotheses and the conclusion
of the conservation law only involve $`u`$ near $`D`$, so for that theorem the example is
equivalent to the case $`u = 0`$. It only shows that the hypotheses of the conservation law are
consistent; a nontrivial example would need an explicit solution of the Klein–Gordon equation
supported in the cone, which is not given here.
