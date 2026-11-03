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
`scripts/check-no-sorry.sh` and `lake build --wfail` (warnings are errors).

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
  component field, and are plain functions `(Spacetime → ℝ) → Spacetime → ℝ`.
  `∂_t u p` unfolds (by `rfl`) to `fderiv ℝ u p (1, 0)` and `∂_a u p` to
  `fderiv ℝ u p (0, EuclideanSpace.single a 1)`.
- **Hypotheses.** `fderiv` is `0` where `u` is not differentiable, so additivity
  needs hypotheses (`DifferentiableAt` for first-order operators, `ContDiffAt ℝ 2`
  for `□` and Klein–Gordon); homogeneity `c • u` needs none. Smoothness is stated
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

### Public interface (`namespace VectorFieldMethod.Minkowski`)

| Lean name | Type signature | Mathematical meaning |
| --- | --- | --- |
| `Spacetime` | `Type` (`abbrev` for `ℝ × EuclideanSpace ℝ (Fin 3)`) | Minkowski spacetime `ℝ^{1+3}`, `p = (t, x)` |
| `timeCoord` | `Spacetime → ℝ` | `t` |
| `spaceCoord` | `Fin 3 → Spacetime → ℝ` | `x_a` (Lean `a = 0, 1, 2` is math `1, 2, 3`) |
| `radius` | `Spacetime → ℝ` | `r = \|x\|` |
| `minkowskiMetric` (`η`) | `Matrix (Fin 4) (Fin 4) ℝ` | `η_{αβ} = diag(-1, 1, 1, 1)`, numerically also `η^{αβ}` |
| `derivAlong` | `(Spacetime → Spacetime) → (Spacetime → ℝ) → Spacetime → ℝ` | `V u = V^α ∂_α u`, i.e. `Du(p) (V p)` |
| `timeField` | `Spacetime → Spacetime` | components of `∂_t`: `(1, 0)` |
| `spaceField` | `Fin 3 → Spacetime → Spacetime` | components of `∂_a`: `(0, e_a)` |
| `coordField` | `Fin 4 → Spacetime → Spacetime` | components of `∂_α` |
| `timeDeriv` (`∂ₜ`) | `(Spacetime → ℝ) → Spacetime → ℝ` | `∂_t` |
| `spaceDeriv` (`∂ₓ[a]`) | `Fin 3 → (Spacetime → ℝ) → Spacetime → ℝ` | `∂_a` |
| `partialDeriv` (`∂[α]`) | `Fin 4 → (Spacetime → ℝ) → Spacetime → ℝ` | `∂_α` |
| `wave` (`□`) | `(Spacetime → ℝ) → Spacetime → ℝ` | `□u = η^{αβ} ∂_α ∂_β u = -∂_t² u + ∑ a, ∂_a² u` |
| `kleinGordon` | `ℝ → (Spacetime → ℝ) → Spacetime → ℝ` | `kleinGordon m u = □u - m² u` |
| `rotationField` | `Fin 3 → Fin 3 → Spacetime → Spacetime` | components of `Ω_ab`: `(0, x_a e_b - x_b e_a)` |
| `rotation` | `Fin 3 → Fin 3 → (Spacetime → ℝ) → Spacetime → ℝ` | `Ω_ab = x_a ∂_b - x_b ∂_a` |
| `boostField` | `Fin 3 → Spacetime → Spacetime` | components of `L_a`: `(x_a, t e_a)` |
| `boost` | `Fin 3 → (Spacetime → ℝ) → Spacetime → ℝ` | `L_a = t ∂_a + x_a ∂_t` |
| `scalingField` | `Spacetime → Spacetime` | components of `S`: `p ↦ p`, i.e. `(t, x)` |
| `scaling` | `(Spacetime → ℝ) → Spacetime → ℝ` | `S = t ∂_t + ∑ a, x_a ∂_a` |

Scoped notation: `η` (`minkowskiMetric`), `∂ₜ` (`timeDeriv`), `∂ₓ[a]`
(`spaceDeriv a`), `∂[α]` (`partialDeriv α`), `□` (`wave`). With the scope open
these are tokens, so for example `η` cannot be used as a variable name there.
