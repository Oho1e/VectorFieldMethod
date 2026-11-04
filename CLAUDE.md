# CLAUDE.md

Guidance for agents (and humans) working in this repository.

## Project

VectorFieldMethod is a Lean 4 + Mathlib library aiming to formalize the
foundations of the vector field method for hyperbolic PDEs. The library root is
`VectorFieldMethod.lean`; modules live under `VectorFieldMethod/`.

- Lean toolchain: `lean-toolchain` (currently `leanprover/lean4:v4.35.0`).
- Mathlib: pinned to the release tag `v4.35.0` in `lakefile.toml`; the exact
  commit is in `lake-manifest.json`.

## Building

```bash
lake exe cache get   # download the Mathlib oleans (needed once per Mathlib pin)
lake build           # build the whole library
```

Always run `lake exe cache get` before the first `lake build` after cloning or
after the Mathlib pin changes. If `cache.mathlib.org` is blocked by the network
policy, use the legacy host: `MATHLIB_CACHE_DEBUG_USE_LEGACY=1 lake exe cache get`.

In Claude Code cloud sessions the SessionStart hook
(`.claude/hooks/lean-warm.sh`) links `.lake` to the prebuilt tree under
`/opt/warm`, so `lake build` works immediately; if it says it started
`lake exe cache get` in the background, wait for that to finish first. See
`docs/lean-cloud.md`.

## Checking a single file

```bash
lake build VectorFieldMethod.Minkowski.Spacetime      # one module and its imports
lake lean VectorFieldMethod/Minkowski/Spacetime.lean
```

The first form uses Lake's build cache; the second builds the file's imports
and then elaborates the file itself with the project's options (including the
linters). For quick experiments, put a scratch file
outside `VectorFieldMethod/` (e.g. `Scratch.lean`, not committed) and run
`lake lean Scratch.lean`.

When adding a module, import it from `VectorFieldMethod.lean`. CI runs
`scripts/check-no-sorry.sh`, `lake build --wfail` (warnings are errors) and
`lake env lean scripts/CheckAxioms.lean`, which enforces the axiom policy (see
Verification) and also fails if a `.lean` file under `VectorFieldMethod/` is not
imported, directly or indirectly, by `VectorFieldMethod.lean`.

## Forbidden

- `lake update`, unless explicitly asked for. It moves the Mathlib pin.
- `lake clean`. In cloud sessions `.lake` is a symlink into the shared warm
  tree, and cleaning deletes the Mathlib oleans for everyone.
- Compiling Mathlib from source. Mathlib always comes from `lake exe cache get`;
  never run `lake build` while Mathlib oleans are missing or incomplete.
- Leaving `sorry` on `main`. CI fails on any `sorry` in `VectorFieldMethod/`
  or `VectorFieldMethod.lean` (comments included).
- `axiom` declarations.

## Unproved facts

Any statement that is not (yet) proved must appear as an explicit assumption:
either a hypothesis of the theorem that uses it, or a field of a `structure`
bundling the assumptions. Never introduce it with `axiom` or `sorry`. This
keeps every dependency on unproved mathematics visible in the statements.

## Verification

- **Axioms.** CI runs `lake env lean scripts/CheckAxioms.lean` after `lake build`:
  every declaration, auxiliary ones included, may depend only on `propext`,
  `Classical.choice` and `Quot.sound` (so no `sorry`, `native_decide` or `axiom`).
  It also fails unless the root imports all library files, directly or indirectly.
- **Non-vacuity.** Each main theorem whose hypotheses go beyond regularity (`C^k`,
  differentiability) and signs of numbers (`0 < r`), e.g. support conditions,
  inequalities between functions or assumptions bundled in a `structure`, gets an
  `example` in a `/-! ### Sanity checks -/` section at the end of its file: it
  applies the theorem to concrete objects satisfying all its hypotheses, showing
  that the hypotheses can hold simultaneously.

## Statement documentation

`docs/statements/` explains, for readers who do not know Lean, what each main
definition and theorem says. A session that adds a main definition or theorem
adds an entry for it to `docs/statements/<layer>.md`, in the format of
`docs/statements/README.md`. A new layer gets a new file. Each session edits only
the file of its own layer.

## Mathematical conventions

The Minkowski coordinate layer lives in `VectorFieldMethod/Minkowski/`; design
notes are in `docs/minkowski-layer.md`.

- **Namespace.** Every declaration of the layer is in
  `VectorFieldMethod.Minkowski`. Its notations are `scoped` there and become
  available with `open VectorFieldMethod.Minkowski` (or `open scoped
  VectorFieldMethod.Minkowski`). Declaration names are never single letters;
  single letters (`η`, `□`) appear only as scoped notation.
- **Spacetime.** `Spacetime` is an `abbrev` for `ℝ × EuclideanSpace ℝ (Fin 3)`:
  the first component is the time `t`, the second the spatial point `x`. The
  norm of this product is the max norm `max |t| ‖x‖`, and it has no inner
  product: never use `‖p‖` as a spacetime distance.
- **Signature** `(-, +, +, +)`. `η_{αβ} = minkowskiMetric =
  Matrix.diagonal (Fin.cons (-1) fun _ ↦ 1)`. Since `η * η = 1`
  (`minkowskiMetric_mul_self`), the inverse metric `η^{αβ}` has the same
  entries. Mathlib's `Matrix.indefiniteDiagonal` is not used (its index type is
  `p ⊕ q`, with the `+1` entries first).
- **Indices.** `α : Fin 4`, with `0` the time index and `Fin.succ a` the spatial
  index `a : Fin 3`. The mathematical spatial indices `1, 2, 3` are the Lean
  indices `0, 1, 2`. Spatial indices are raised and lowered without changing the
  value (`x_a = x^a`).
- **Values.** The operators of the definition layer act on functions
  `Spacetime → F` with values in an arbitrary real normed space `F`
  (`{F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]`, always an implicit
  argument, inferred from `u`); the energy layers (`EnergyMomentum.lean`,
  `HyperboloidalEnergy.lean`, `HyperboloidalEnergyIdentity.lean`,
  `HyperboloidalEnergyEstimate.lean`) require a real inner product space
  instead (`{F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]`, see
  "Values: extra structure on `F`" below); the
  coordinate functions `timeCoord`, `spaceCoord`, `radius` are real-valued. Real
  coefficients act on values by `•` (for `F = ℝ` this is `*`). In the definition
  layer no inner product or complex structure on `F` is assumed. `F` cannot be
  inferred in an equation between operators without a function argument (write a type ascription, as in
  `partialDeriv_zero : (∂[0] : (Spacetime → F) → Spacetime → F) = ∂ₜ`) or when
  the values of `u` are only numerals (write `∂ₜ (fun _ ↦ (1 : ℝ))`).
- **Values: commutation lemmas.** For `T : F →L[ℝ] G` the `*_comp_left` lemmas
  give `op (T ∘ u) p = T (op u p)` (first-order operators: `u` differentiable at
  `p`; `□`, Klein–Gordon: `u` of class `C²` at `p`); `@[to_fun]` generates the
  forms `fun_*_comp_left` about `fun q ↦ T (u q)`. For `e : F ≃L[ℝ] G` the
  `*_comp_left_equiv` lemmas give `op (e ∘ u) = e ∘ op u` without hypotheses.
- **Values: extra structure on `F`.** When a statement needs an inner product on
  `F`, declare `variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]`
  on its own; do not add `[InnerProductSpace ℝ F]` on top of an existing
  `[NormedSpace ℝ F]`, which would give two unrelated `NormedSpace ℝ F`
  instances. A future Bochner integral of `F`-valued functions needs
  `[CompleteSpace F]`; without it the integral is identically `0`.
- **Operators.** `□u = η^{αβ} ∂_α ∂_β u = -∂_t² u + ∑ a, ∂_a² u`; the
  Klein–Gordon operator is `□u - m² u`. LeFloch–Ma's `□ = ∂_t² - Δ` is `-□`
  here, and their Klein–Gordon operator `□u + m²u` is `-(□u - m²u)`.
- **Vector fields (11).** Translations `∂_α` (4); rotations
  `Ω_ab = x_a ∂_b - x_b ∂_a`, defined for all `a b : Fin 3`, of which the three
  with `a < b` are independent; boosts `L_a = t ∂_a + x_a ∂_t` (3); scaling
  `S = t ∂_t + ∑ a, x_a ∂_a` (1).
- **One first-order operator.** A vector field is given by its component field
  `V : Spacetime → Spacetime`, and `derivAlong V u p = fderiv ℝ u p (V p)`. All
  of `∂_t`, `∂_a`, `∂_α`, `Ω_ab`, `L_a`, `S` are `derivAlong` of a named
  component field, and are plain functions `(Spacetime → F) → Spacetime → F`.
  `∂_t u p` unfolds (by `rfl`) to `fderiv ℝ u p (1, 0)` and `∂_a u p` to
  `fderiv ℝ u p (0, EuclideanSpace.single a 1)`.
- **Hypotheses.** `fderiv` is `0` where `u` is not differentiable, so additivity
  needs hypotheses (`DifferentiableAt` for first-order operators, `ContDiffAt ℝ 2`
  for `□` and Klein–Gordon); homogeneity `c • u` needs none, both for a real
  scalar `c : ℝ` (`*_smul`) and for a scalar `c : R` acting on `F` with
  `[DivisionSemiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]`
  (`*_const_smul_field`, e.g. `c = Complex.I` for `F = ℂ`). Smoothness is stated
  for a general order `n : ℕ∞ω` (`open scoped ContDiff`): `C^{n+1} → C^n` for
  first-order operators and `C^{n+2} → C^n` for `□`; `∞` means `C^∞`. Do not
  write `⊤`, which means analytic.
- **Forms of statements.** Constant functions are written `fun _ ↦ c`, also in
  results (`∂ₜ timeCoord = fun _ ↦ 1`). The Kronecker delta `δ_ab` is
  `if a = b then 1 else 0`. The radius `r` is not differentiable at `x = 0`;
  compute with `r² = ∑ a, x_a²` (`radius_sq`).
- **`simp` policy.** `@[simp]` is only on the values of the operators on the
  coordinate functions and on constants, and on `∂[0] = ∂ₜ`,
  `∂[Fin.succ a] = ∂ₓ[a]` and `∂[1] = ∂ₓ[0]`, `∂[2] = ∂ₓ[1]`, `∂[3] = ∂ₓ[2]`.
  The unfolding lemmas `*_apply` (to `fderiv`) are not `simp`.
- **Commutators.** For first-order operators given by component fields `X`, `Y`,
  `[X, Y]u = X(Yu) - Y(Xu) = derivAlong (lieBracket ℝ X Y) u`, where
  `lieBracket ℝ X Y = DY · X - DX · Y` is Mathlib's `VectorField.lieBracket`
  (`derivAlong_derivAlong_sub_derivAlong_derivAlong`, for differentiable `X`,
  `Y` and `u` of class `C²`; `Commutators.lean`).
- **Energy normalization.** The energy-momentum layer (`EnergyMomentum.lean`)
  carries the factor `½`: `energyCurrent m u 0 = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)`.
  The hyperboloidal energy `hyperboloidalEnergy` and its density
  `hyperboloidalEnergyDensity` carry no `½` (LeFloch–Ma's normalization), so
  `hyperboloidalEnergyDensity m u = 2 (P⁰ - ∑ a, (x_a / t) P^a)` for the energy
  current `P` (`hyperboloidalEnergyDensity_eq_energyCurrent`).
- **Hyperboloidal energy and LeFloch–Ma.** `hyperboloidalEnergy c s u` is
  LeFloch–Ma's `E_{m,c}(s, u)` (arXiv:1411.4910, (2.3.2); their subscript `m`
  means Minkowski, `c` is the mass), and `hyperboloidalEnergy 0 s u` is their
  `E_m(s, u) = E_{m,0}(s, u)`. In the notation `E_m(s, u)` of this project's
  docstrings the subscript is the mass.

### Public interface (`namespace VectorFieldMethod.Minkowski`)

The operators of the definition layer act on functions with values in an
arbitrary real normed space `F` (implicit, `[NormedSpace ℝ F]`); the coordinate
functions are real-valued. The definitions of the energy layers
(`energyMomentum`, `energyCurrent`, `semiHyperboloidalDeriv`,
`hyperboloidalEnergyDensity`, `hyperboloidalEnergy`) require
`[InnerProductSpace ℝ F]` instead. When a statement needs an inner product on
`F`, declare `variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]`
on its own; do not add `[InnerProductSpace ℝ F]` on top of an existing
`[NormedSpace ℝ F]`, which would give two unrelated `NormedSpace ℝ F`
instances. `restrictHyperboloid` only needs `[NormedSpace ℝ F]`.

| Lean name | Type signature | Mathematical meaning |
| --- | --- | --- |
| `Spacetime` | `Type` (`abbrev` for `ℝ × EuclideanSpace ℝ (Fin 3)`) | Minkowski spacetime `ℝ^{1+3}`, `p = (t, x)` |
| `timeCoord` | `Spacetime → ℝ` | `t` |
| `spaceCoord` | `Fin 3 → Spacetime → ℝ` | `x_a` (Lean `a = 0, 1, 2` is math `1, 2, 3`) |
| `radius` | `Spacetime → ℝ` | `r = \|x\|` |
| `minkowskiMetric` (`η`) | `Matrix (Fin 4) (Fin 4) ℝ` | `η_{αβ} = diag(-1, 1, 1, 1)`, numerically also `η^{αβ}` |
| `derivAlong` | `(Spacetime → Spacetime) → (Spacetime → F) → Spacetime → F` | `V u = V^α ∂_α u`, i.e. `Du(p) (V p)` |
| `timeField` | `Spacetime → Spacetime` | components of `∂_t`: `(1, 0)` |
| `spaceField` | `Fin 3 → Spacetime → Spacetime` | components of `∂_a`: `(0, e_a)` |
| `coordField` | `Fin 4 → Spacetime → Spacetime` | components of `∂_α` |
| `timeDeriv` (`∂ₜ`) | `(Spacetime → F) → Spacetime → F` | `∂_t` |
| `spaceDeriv` (`∂ₓ[a]`) | `Fin 3 → (Spacetime → F) → Spacetime → F` | `∂_a` |
| `partialDeriv` (`∂[α]`) | `Fin 4 → (Spacetime → F) → Spacetime → F` | `∂_α` |
| `dAlembertian` (`□`) | `(Spacetime → F) → Spacetime → F` | `□u = η^{αβ} ∂_α ∂_β u = -∂_t² u + ∑ a, ∂_a² u` |
| `kleinGordon` | `ℝ → (Spacetime → F) → Spacetime → F` | `kleinGordon m u = □u - m² u` (`m ^ 2 • u p`) |
| `rotationField` | `Fin 3 → Fin 3 → Spacetime → Spacetime` | components of `Ω_ab`: `(0, x_a e_b - x_b e_a)` |
| `rotation` | `Fin 3 → Fin 3 → (Spacetime → F) → Spacetime → F` | `Ω_ab = x_a ∂_b - x_b ∂_a` |
| `boostField` | `Fin 3 → Spacetime → Spacetime` | components of `L_a`: `(x_a, t e_a)` |
| `boost` | `Fin 3 → (Spacetime → F) → Spacetime → F` | `L_a = t ∂_a + x_a ∂_t` |
| `scalingField` | `Spacetime → Spacetime` | components of `S`: `p ↦ p`, i.e. `(t, x)` |
| `scaling` | `(Spacetime → F) → Spacetime → F` | `S = t ∂_t + ∑ a, x_a ∂_a` |
| `energyMomentum` | `(m : ℝ) (u : Spacetime → F) (α β : Fin 4) : Spacetime → ℝ` | `T_{αβ} = ⟪∂_α u, ∂_β u⟫ - ½ η_{αβ} (η^{γδ} ⟪∂_γ u, ∂_δ u⟫ + m² ‖u‖²)` (`EnergyMomentum.lean`) |
| `spacetimeDiv` | `(J : Fin 4 → Spacetime → ℝ) : Spacetime → ℝ` | `∂_α J^α = ∑ α, ∂_α J^α` for real components `J α` |
| `energyCurrent` | `(m : ℝ) (u : Spacetime → F) (α : Fin 4) : Spacetime → ℝ` | `P^α = -η^{αγ} T_{γ0}`; `P^0 = ½ (‖∂_t u‖² + ∑ a, ‖∂_a u‖² + m² ‖u‖²)` |
| `semiHyperboloidalDeriv` | `(a : Fin 3) (u : Spacetime → F) : Spacetime → F` | `∂̲_a u = ∂_a u + (x_a / t) ∂_t u` (`HyperboloidalEnergy.lean`) |
| `hyperboloidalEnergyDensity` | `(m : ℝ) (u : Spacetime → F) : Spacetime → ℝ` | `e_m[u] = ‖∂_t u‖² + ∑ a, ‖∂_a u‖² + 2 ∑ a, (x_a / t) ⟪∂_a u, ∂_t u⟫ + m² ‖u‖²` (no `½`) |
| `hyperboloidalEnergy` | `(m s : ℝ) (u : Spacetime → F) : ℝ` | `E_m(s, u) = ∫_{ℝ³} e_m[u](√(s² + ‖x‖²), x) dx`; LeFloch–Ma's `E_{m,c}(s, u)` for `m = c` |
| `regionBetweenHyperboloids` | `(s₁ s₂ : ℝ) : Set Spacetime` | `{(t, x) \| √(s₁² + ‖x‖²) ≤ t ≤ √(s₂² + ‖x‖²)}` (`HyperboloidalEnergyIdentity.lean`) |
| `cone` | `: Set Spacetime` | the closed solid cone `K = {(t, x) \| ‖x‖ ≤ t - 1}` |
| `hyperboloid` | `(s : ℝ) : Set Spacetime` | `H_s = {(t, x) \| t = √(s² + ‖x‖²)}` (`KlainermanSobolev.lean`) |
| `hyperboloidPoint` | `(s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) : Spacetime` | the point `(√(s² + ‖x‖²), x)` of `H_s` |
| `restrictHyperboloid` | `(s : ℝ) (v : Spacetime → F) : EuclideanSpace ℝ (Fin 3) → F` | `v\|_{H_s}(x) = v(√(s² + ‖x‖²), x)` |
| `EuclideanSobolev.hyperboloidalWeightedDeriv` | `(s : ℝ) (a : Fin 3) (w : EuclideanSpace ℝ (Fin 3) → ℝ) : EuclideanSpace ℝ (Fin 3) → ℝ` | `Λ_a w = √(s² + ‖x‖²) ∂_a w` on `ℝ³` (`Analysis/HyperboloidalSobolev.lean`, namespace `VectorFieldMethod.EuclideanSobolev`) |

For the definitions after `scaling` (the later layers), the second column is the
signature copied from the source: the binders and the result type, between the
name and `:=` (for `hyperboloidalWeightedDeriv` the two source lines are joined
with one space). `hyperboloidalWeightedDeriv` is in the namespace
`VectorFieldMethod.EuclideanSobolev`, all other entries in
`VectorFieldMethod.Minkowski`.

Scoped notation: `η` (`minkowskiMetric`), `∂ₜ` (`timeDeriv`), `∂ₓ[a]`
(`spaceDeriv a`), `∂[α]` (`partialDeriv α`), `□` (`dAlembertian`). With the scope open
these are tokens, so for example `η` cannot be used as a variable name there.
