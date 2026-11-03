# Statement documentation

The files in this directory list the main definitions and main theorems of the library, each
with a mathematical statement next to the verbatim Lean statement. They are written for readers
who know the mathematics but not Lean: reading them should be enough to check what each main
definition and theorem of the project says.

- **One file per layer.** Every `.md` file in this directory other than this README documents one
  layer of the library. At present:
  - [`minkowski.md`](minkowski.md): the Minkowski coordinate layer, `VectorFieldMethod/Minkowski/`;
  - [`divergence.md`](divergence.md): the divergence theorem on regions bounded by graphs,
    `VectorFieldMethod/ForMathlib/`.
- **Only main results.** Each file contains the main definitions and the main theorems of its
  layer. Auxiliary lemmas (unfolding lemmas, intermediate steps of proofs, technical
  measurability or support statements) are left out.
- **Statements, not proofs.** The proofs are checked by Lean: CI builds the library with warnings
  as errors and rejects `sorry`, and the project rules forbid `axiom`. A reader therefore only has
  to check the *statements*: that the Lean statement, read with the conventions below, says
  exactly what the **Math.** line says, with the same hypotheses.

Each Lean statement depends on the meaning of the Mathlib notions it uses (derivatives, integrals,
measures, ...). The table below translates the ones that occur in this project, and the section
after it lists the conventions of Lean and Mathlib that make some statements look different from
their textbook form.

## How to read the Lean statements

### Hypotheses and arguments

A Lean theorem `theorem name (args) : conclusion` reads "for all `args`, `conclusion`". Every
argument is a hypothesis or a quantified variable:

| Lean | Mathematics |
| --- | --- |
| `(hu : ContDiff ℝ 2 u)` | a hypothesis, named `hu`, that $`u`$ is $`C^2`$ |
| `(a : Fin 3)`, `{p : Spacetime}` | "for every $`a`$", "for every $`p`$"; braces only mean that Lean infers the argument |
| `[FiniteDimensional ℝ E]`, `[μ.IsAddHaarMeasure]` | structural hypotheses on the objects ("$`E`$ is finite-dimensional", "$`\mu`$ is a Haar measure"); they are hypotheses like the others |
| `variable ...` at the top of a section | arguments shared by the theorems of the section. They are part of every theorem that mentions them, so each layer file reproduces these lines in its *Context* section |

### Functions, derivatives, smoothness

| Lean | Mathematics |
| --- | --- |
| `fun x ↦ f x` | the function $`x \mapsto f(x)`$ |
| `fun _ ↦ c` | the constant function with value $`c`$ |
| `f x y` | $`f(x, y)`$; for instance `∂[α] u p` is $`(\partial_\alpha u)(p)`$ |
| `p.1`, `p.2` | the first and second components of a pair $`p = (p_1, p_2)`$ |
| `u + v`, `c • u`, `c * x` | pointwise sum of functions, scalar multiple, product of numbers |
| `fderiv ℝ u p v` | $`Du(p)\,v`$: the Fréchet derivative of $`u`$ at $`p`$ applied to the vector $`v`$; it is $`0`$ if $`u`$ is not differentiable at $`p`$ |
| `deriv f t` | $`f'(t)`$ for $`f`$ defined on $`\mathbb{R}`$; it is $`0`$ if $`f`$ is not differentiable at $`t`$. For instance `deriv (fun t ↦ X₀ (p.1, t)) p.2` is $`\partial_t X_0(x, t)`$ at $`p = (x, t)`$ |
| `DifferentiableAt ℝ u p` | $`u`$ is (Fréchet) differentiable at $`p`$ |
| `ContDiff ℝ n u` | $`u \in C^n`$ on the whole space. Here `n : ℕ∞ω` is a natural number, `∞` (meaning $`C^\infty`$) or `ω` (meaning real analytic); $`\infty + 1 = \infty`$ |
| `ContDiffAt ℝ n u p` | $`u`$ is $`C^n`$ at $`p`$; for finite $`n`$ this means $`C^n`$ on some neighbourhood of $`p`$ |
| `ContDiffOn ℝ n u U` | $`u`$ is $`C^n`$ on $`U`$; for open $`U`$ the usual notion, and the values of $`u`$ outside $`U`$ play no role |
| `u =ᶠ[𝓝 p] v` | $`u = v`$ on some neighbourhood of $`p`$ |
| `support f` | $`\{x : f(x) \neq 0\}`$ (`Function.support`) |
| `tsupport f` | the closed support $`\overline{\{x : f(x) \neq 0\}}`$ |
| `HasCompactSupport f` | `tsupport f` is compact |
| `E →L[ℝ] F`, `E →ₗ[ℝ] F` | continuous linear maps, linear maps. A cast `(L : E →ₗ[ℝ] E)` only forgets continuity |
| `LinearMap.trace ℝ E A` | the trace $`\operatorname{tr} A`$ of a linear map $`A : E \to E`$; it is $`0`$ if $`E`$ is infinite-dimensional |
| `⟪x, v⟫` | the real inner product $`\langle x, v\rangle`$ |
| `∇ φ x` | the gradient $`\nabla\varphi(x)`$, the vector with $`\langle \nabla\varphi(x), v\rangle = D\varphi(x)\,v`$ (it is $`0`$ if $`\varphi`$ is not differentiable at $`x`$) |
| `‖x‖` | the norm. On `EuclideanSpace` it is the Euclidean norm; on a product `A × B` it is the max norm $`\max(\lVert a\rVert, \lVert b\rVert)`$ |
| `√x`, `x ^ 2` | $`\sqrt{x}`$ (`Real.sqrt`), the square $`x^2`$ |
| `f ≤ g` for functions | $`f(x) \le g(x)`$ for every $`x`$ |

### Sets, sums, indices

| Lean | Mathematics |
| --- | --- |
| `{p : E × ℝ \| P p}` | the set $`\{p \in E \times \mathbb{R} : P(p)\}`$ |
| `Icc a b`, `Ioo a b`, `Iic a` | $`[a, b]`$, $`(a, b)`$, $`(-\infty, a]`$ |
| `uIcc a b` | $`[\min(a, b), \max(a, b)]`$ |
| `regionBetween f g s` | $`\{(x, t) : x \in s,\ f(x) \lt t \lt g(x)\}`$ (open in the $`t`$ direction) |
| `Fin n` | the index set $`\{0, 1, \dots, n - 1\}`$ |
| `∑ a, f a` | the sum over all values of the index; for `a : Fin 3`, over $`a = 0, 1, 2`$ |
| Lean indices `0, 1, 2` of `Fin 3` | the mathematical spatial indices $`1, 2, 3`$: Lean `a` is the mathematical index $`a + 1`$ |
| `α : Fin 4` | a spacetime index $`\alpha \in \{0, 1, 2, 3\}`$, with `0` the time index and `Fin.succ a` (that is, $`a + 1`$) the spatial index `a : Fin 3`; Lean and mathematics agree here |
| `Fin.cases x f α` | definition by cases on `α : Fin (n + 1)`: the value `x` if $`\alpha = 0`$, and `f a` if `α = Fin.succ a` |
| `Fin.cons (-1) fun _ ↦ 1` | the 4-tuple $`(-1, 1, 1, 1)`$ |
| `Matrix.diagonal d` | the diagonal matrix with diagonal $`d`$ |
| `EuclideanSpace ℝ (Fin 3)` | $`\mathbb{R}^3`$ with the Euclidean inner product and norm. A point `x` is a function on `Fin 3`, and `x a` is its coordinate $`x^{a+1}`$ |
| `EuclideanSpace.single a 1` | the standard basis vector $`e_{a+1}`$ of $`\mathbb{R}^3`$ |

### Integrals and measures

| Lean | Mathematics |
| --- | --- |
| `∫ x, f x ∂μ` | $`\int f\,d\mu`$ over the whole space (Bochner integral; it is $`0`$ if $`f`$ is not integrable, see below) |
| `∫ x in s, f x ∂μ` | $`\int_s f\,d\mu`$ |
| `∫ t in a..b, f t` | the oriented integral $`\int_a^b f(t)\,dt`$ for Lebesgue measure: $`\int_{(a, b]} f`$ if $`a \le b`$, and $`-\int_{(b, a]} f`$ if $`b \lt a`$ |
| `volume` | the canonical measure of a type: Lebesgue measure on $`\mathbb{R}`$ and on `EuclideanSpace ℝ (Fin n)` ($`= \mathbb{R}^n`$), and the product of these on a product type |
| `μ.prod volume` | the product measure $`\mu \otimes \mathcal{L}^1`$ on $`E \times \mathbb{R}`$ ($`\mathcal{L}^1`$ = Lebesgue measure on $`\mathbb{R}`$); `volume.prod μ` is $`\mathcal{L}^1 \otimes \mu`$ on $`\mathbb{R} \times E`$ |
| `[μ.IsAddHaarMeasure]` | $`\mu`$ is an additive Haar measure on $`E`$: translation invariant, finite on compact sets, positive on nonempty open sets. On a finite-dimensional real vector space these are exactly the positive multiples of Lebesgue measure in linear coordinates |
| `[MeasurableSpace E] [BorelSpace E]` | $`E`$ carries its Borel $`\sigma`$-algebra |
| `[NormedSpace ℝ E]`, `[InnerProductSpace ℝ E]`, `[FiniteDimensional ℝ E]` | $`E`$ is a real normed space, a real inner product space, finite-dimensional |

## Junk values and pitfalls

In Lean every function is total: an expression such as $`Du(p)`$ or $`x / y`$ has a value even
where mathematics leaves it undefined. These *junk values* are harmless in proved theorems, but
they change how statements must be written and read.

- **`fderiv` and `deriv` are `0` where the function is not differentiable.** So `fderiv ℝ u p v`
  is the derivative only when `DifferentiableAt ℝ u p`, and it is `0` even when the directional
  derivative in direction `v` exists but $`u`$ is not Fréchet differentiable at $`p`$. In
  particular additivity fails in general: on $`\mathbb{R}`$, for $`u(x) = \lvert x\rvert`$ and
  $`v(x) = x - \lvert x\rvert`$, Lean's derivatives at $`0`$ are $`u'(0) = v'(0) = 0`$ (junk)
  while $`(u + v)'(0) = 1`$. Hence in this project additivity carries hypotheses:
  `derivAlong_add` assumes `DifferentiableAt ℝ u p` and `DifferentiableAt ℝ v p`, and
  `dAlembertian_add` assumes `ContDiffAt ℝ 2 u p` and `ContDiffAt ℝ 2 v p`, while homogeneity
  `derivAlong_smul` holds without hypotheses. Also, `radius` ($`r = \lvert x\rvert`$) is not
  differentiable at $`x = 0`$, so its "derivatives" there are `0`; the project computes with
  $`r^2`$ instead (`radius_sq`). Definitions built from `fderiv` (`∂ₜ`, `□`, `spatialDivergence`,
  ...) are defined for *every* function; a theorem about them is only meaningful under the
  differentiability hypotheses it states.
- **`x / 0 = 0`, and `Real.sqrt x = 0` for `x < 0`.** A formula with a division or a square root
  is meaningful only where the denominator is nonzero and the radicand is nonnegative. Example:
  in `integral_divergence_between_hyperboloids` the flux contains
  `⟪x, X (x, φ x)⟫ / φ x` with `φ x = √(s ^ 2 + ‖x‖ ^ 2)`; the hypothesis `0 < s₁` (and
  `s₁ < s₂`) makes the radicand positive and `φ x ≥ s > 0`, so no junk value occurs. Similarly
  a matrix inverse `A⁻¹` is defined for every matrix (it is a junk value when `A` is singular);
  `inv_minkowskiMetric : η⁻¹ = η` is about the genuine inverse because `η * η = 1`.
- **`ENNReal.toReal` sends `∞` to `0`.** Measures take values in $`[0, \infty]`$ (`ENNReal`), and
  `(μ s).toReal` is $`0`$ when $`\mu(s) = \infty`$. A statement that uses `(μ s).toReal` therefore
  needs $`\mu(s) \lt \infty`$ to mean what it seems to. (No main statement of the project uses
  `toReal` at present.)
- **The Bochner integral of a non-integrable function is `0`.** An identity
  `∫ f ∂μ = ∫ g ∂ν` could hold for the trivial reason that both sides are junk zeros. When
  reading an integral identity, check that its hypotheses make every integrand integrable: in
  `integral_divergence_hypograph` and its variants all integrands are continuous with compact
  support (from `HasCompactSupport X₀`, `HasCompactSupport X`); in the `_of_contDiffOn` versions
  the compactness hypothesis on `D ∩ (tsupport X₀ ∪ tsupport X)` plays this role; in
  `integral_divergence_between_hyperboloids` it is the support condition `‖x‖ ≤ t - 1`. Likewise,
  `∫ t in a..b, f t` is $`0`$ if $`f`$ is not integrable on the interval.
- **Natural-number division truncates: `(3 / 2 : ℕ) = 1`.** In `x ^ (3 / 2)` the exponent is
  elaborated as a natural number when nothing forces otherwise, so `x ^ (3 / 2)` is `x ^ 1`.
  Fractional powers must be written with a real exponent, `x ^ (3 / 2 : ℝ)` (`Real.rpow`), and
  then `Real.rpow` has its own junk values for negative bases. Natural-number subtraction also
  truncates (`2 - 3 = 0` in `ℕ`). (All powers in the current statements are squares `^ 2`.)
- **Order of quantifiers: `∃ C, ∀ x, ...` versus `∀ x, ∃ C, ...`.** The first gives one constant
  for all `x` (a uniform estimate), the second lets the constant depend on `x`, which is usually
  much weaker. Check the order in every estimate. In the current files the same distinction
  appears in the cutoff lemma `exists_contDiff_hasCompactSupport_eventuallyEq_of_contDiffOn`
  (`ForMathlib/.../DivergenceTheoremLocal.lean`): it states
  `∃ Y₀ Y, ... ∧ ∀ p ∈ D, Y₀ =ᶠ[𝓝 p] X₀ ∧ Y =ᶠ[𝓝 p] X`, so a single compactly supported field
  agrees with `(X₀, X)` near every point of `D`, which is what the localized divergence theorems
  need.

Further conventions specific to this project:

- On `Spacetime = ℝ × EuclideanSpace ℝ (Fin 3)` the norm `‖p‖` is the max norm
  $`\max(\lvert t\rvert, \lvert x\rvert)`$, not a Minkowski or Euclidean distance on spacetime;
  no statement uses it as one.
- `ContDiff ℝ ⊤ u` means *analytic*, not $`C^\infty`$; $`C^\infty`$ is written `ContDiff ℝ ∞ u`.
- Spatial indices are shifted by one between Lean and mathematics (`spaceCoord 0` is $`x^1`$).
- The layers do not all use the same coordinate order: the Minkowski layer puts time first
  ($`\mathbb{R} \times \mathbb{R}^3`$), the divergence theorems put it second ($`E \times \mathbb{R}`$).

## Entry format

Each entry of a layer file has this form.

````markdown
### <short mathematical title>

- **Math.** The complete mathematical statement in LaTeX, with all hypotheses.
- **Hypotheses.** One sentence listing all hypotheses (including those coming from `variable`
  lines and from instance arguments `[...]`).
- **Lean.** `Full.Lean.name`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/<sha>/<path>#L<line>)

```lean
<the declaration, copied verbatim>
```

- **Notes.** (optional) Differences from the conventions of the literature, effects of junk
  values, relations to other entries.
````

Rules for writing entries:

- **Math.** Display formulas go in ` ```math ` blocks (GitHub renders them; they are more robust
  than `$$ … $$`, whose backslashes can be eaten by Markdown). Inline formulas are written
  ``$`…`$``. In inline formulas write `\lt`, `\gt` instead of `<`, `>` (GitHub escapes them
  twice there). Inside table cells, avoid the character `|` (use `\lvert … \rvert`, `\mid`).
- **Lean link.** The permalink points to a fixed commit, preferably a commit of `main`; the line
  is the line of the `theorem` / `def` keyword. If the declaration is added in the same pull
  request, use that pull request's head commit and replace it by a `main` commit later.
- **Lean block.** Copy the declaration from the file at that commit with
  `git show <sha>:<path>`, never from memory. For a theorem, copy from the keyword `theorem` up to
  (not including) the `:=` that starts the proof. For a definition, copy the whole definition,
  including its body: the body *is* the definition. Attributes (`@[simp]`, ...) and docstrings
  are omitted. Related lines (for instance the `scoped notation` line of a definition) may be
  added as a separate paragraph of the same block, each copied verbatim.
- **Context.** Each layer file starts with a *Context* section that copies the relevant
  `variable` lines verbatim, since they are hypotheses of the theorems below them.
- **New layers.** A new layer gets a new file `docs/statements/<layer>.md`. Each session edits
  only the file of its own layer.
