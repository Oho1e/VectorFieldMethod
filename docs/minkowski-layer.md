# The Minkowski coordinate layer

Files: `VectorFieldMethod/Minkowski/{Spacetime,Derivative,WaveOperator,VectorFields,Computations}.lean`,
all imported by `VectorFieldMethod.lean`. Every declaration is in the namespace
`VectorFieldMethod.Minkowski`; the notations are scoped there.

The operators act on functions `u : Spacetime → F` with values in an arbitrary
real normed space `F` (`{F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]`,
an implicit argument inferred from `u`), so that the same definitions serve real
fields (`F = ℝ`), complex fields (`F = ℂ`) and, later, spinor fields. The
coordinate functions, the metric and the component fields are real and do not
depend on `F`.

## Public interface

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
| `kleinGordon` | `ℝ → (Spacetime → F) → Spacetime → F` | `kleinGordon m u = □u - m² u` |
| `rotationField` | `Fin 3 → Fin 3 → Spacetime → Spacetime` | components of `Ω_ab`: `(0, x_a e_b - x_b e_a)` |
| `rotation` | `Fin 3 → Fin 3 → (Spacetime → F) → Spacetime → F` | `Ω_ab = x_a ∂_b - x_b ∂_a` |
| `boostField` | `Fin 3 → Spacetime → Spacetime` | components of `L_a`: `(x_a, t e_a)` |
| `boost` | `Fin 3 → (Spacetime → F) → Spacetime → F` | `L_a = t ∂_a + x_a ∂_t` |
| `scalingField` | `Spacetime → Spacetime` | components of `S`: `p ↦ p`, i.e. `(t, x)` |
| `scaling` | `(Spacetime → F) → Spacetime → F` | `S = t ∂_t + ∑ a, x_a ∂_a` |

Scoped notation: `η` (`minkowskiMetric`), `∂ₜ` (`timeDeriv`), `∂ₓ[a]`
(`spaceDeriv a`), `∂[α]` (`partialDeriv α`), `□` (`dAlembertian`).

## Conventions

* Signature `(-, +, +, +)`; `α : Fin 4` with `0` the time index and `Fin.succ a`
  the spatial index `a : Fin 3`; mathematical spatial indices `1, 2, 3` are the
  Lean indices `0, 1, 2`; spatial indices are raised and lowered without
  changing the value, `x_a = x^a`.
* `□ = -∂_t² + Δ`. Compared with LeFloch–Ma: their `□ = ∂_t² - Δ` is `-□` here;
  their Klein–Gordon operator `□u + m²u` is `-(□u - m²u) = -kleinGordon m u`.
* Constant functions are written `fun _ ↦ c`, including in results of the
  operators. The Kronecker delta `δ_ab` is written `if a = b then 1 else 0`.
* Real coefficients (`η α β`, `m ^ 2`, `timeCoord p`, `spaceCoord a p`) act on
  values in `F` by scalar multiplication `•`. For `F = ℝ` this is the product
  `*` definitionally (`smul_eq_mul`), so for example
  `□ u p = ∑ α, ∑ β, η α β * ∂[α] (∂[β] u) p` holds by `rfl` for real `u`.

## Definitions

### `Spacetime`

*Formula.* `ℝ^{1+3} = ℝ_t × ℝ³_x`.

*Implementation.* `abbrev Spacetime : Type := ℝ × EuclideanSpace ℝ (Fin 3)`.

*Reasons.* The split into time and space is built into the type, so
`t = p.1` and `x = p.2` need no index bookkeeping, and the spatial factor
carries the Euclidean structure that the vector field method uses on `ℝ³`
(`‖x‖ = r`, inner product, `EuclideanSpace.single`). The product of normed
spaces is a normed space, so `fderiv`, `ContDiff`, and the second-derivative
symmetry theorems apply directly. It is an `abbrev` so that all instances of
the product are found without unfolding.

*Caveat.* The norm on the product is the max norm `max |t| ‖x‖`, and there is
no inner product on `Spacetime`. `‖p‖` is not a spacetime distance and is never
used as one. (Norms on `Spacetime` only matter through the topology, which is
the usual one.)

*Alternatives considered.*
* `EuclideanSpace ℝ (Fin 4)`: carries a Euclidean inner product and norm on
  spacetime, which invites confusing them with the Minkowski form, and every
  time/space split has to go through `Fin` index arithmetic.
* `Fin 4 → ℝ`: sup norm, no Euclidean structure on the spatial part.
* `WithLp 2 (ℝ × EuclideanSpace ℝ (Fin 3))`: again an unwanted Euclidean inner
  product on spacetime.
* A custom `structure`: would need all normed-space instances to be
  transported by hand.

### `timeCoord`, `spaceCoord a`, `radius`

*Formula.* `t(p) = p.1`, `x_a(p) = p.2 a`, `r(p) = ‖p.2‖`.

*Implementation.* Plain `def`s (not `abbrev`), so that `simp` lemmas about
`∂ₜ timeCoord`, `boost a (spaceCoord b)`, ... are keyed on the names. The
unfolding lemmas `timeCoord_apply`, `spaceCoord_apply`, `radius_apply` are not
`simp`. `radius_sq : radius p ^ 2 = ∑ a, spaceCoord a p ^ 2` (from
`EuclideanSpace.real_norm_sq_eq`) is the interface for computations: `r` is not
differentiable at `x = 0`, so every derivative of an expression in `r` goes
through `r²`.

### `minkowskiMetric` (`η`)

*Formula.* `η_{αβ} = diag(-1, 1, 1, 1)`; `η^{αβ}` is the inverse matrix.

*Implementation.* `Matrix.diagonal (Fin.cons (-1) fun _ ↦ 1)`, with
`minkowskiMetric_mul_self : η * η = 1`, `inv_minkowskiMetric : η⁻¹ = η`,
`transpose_minkowskiMetric`, and the entries `minkowskiMetric_zero_zero`,
`_zero_succ`, `_succ_zero`, `_succ_succ` (the last one is the Kronecker delta on
spatial indices). Because `η⁻¹ = η`, the inverse metric is not a separate
definition: `□` is written with the entries of `minkowskiMetric`, and its
docstring says that these are the entries of `η^{αβ}`.

*Alternatives considered.*
* `Matrix.indefiniteDiagonal`: indexed by `p ⊕ q` with the `+1` entries first,
  which does not match the `Fin 4` indexing with time at `0`; reindexing it
  would add an equivalence to every index computation.
* A bilinear or quadratic form (`LinearMap.BilinForm`, `QuadraticForm`): more
  structure than needed now; `□` and later the energy-momentum tensor only need
  the coefficients. It can be added on top of the matrix later.
* A literal matrix `!![-1, 0, 0, 0; ...]`: less structural; `Fin.cons` lets
  proofs split into the time index and the spatial indices with `Fin.cases`.

### `derivAlong`

*Formula.* For a vector field `V = V^α ∂_α` with components
`V(p) = (V⁰(p), (V¹(p), V²(p), V³(p)))`, `(V u)(p) = V^α(p) ∂_α u(p) = Du(p)(V(p))`.

*Implementation.* `derivAlong V u = fun p ↦ fderiv ℝ u p (V p)` with
`V : Spacetime → Spacetime` the component field and `u : Spacetime → F`. Every
first-order operator of the layer is `derivAlong` of a named component field,
and all operators are plain functions `(Spacetime → F) → Spacetime → F`.

*Reasons.* One operator means one set of lemmas: linearity, smoothness
(`contDiff_derivAlong : C^n` field and `C^{n+1}` function give `C^n`),
locality (`derivAlong_congr_of_eventuallyEq`), values on the coordinates
(`derivAlong_timeCoord`, `derivAlong_spaceCoord`), and computing through a
`HasFDerivAt` (`derivAlong_eq_of_hasFDerivAt`). Representing vector fields by
component functions `E → E` is also Mathlib's convention in
`Mathlib.Analysis.Calculus.VectorField`, so `VectorField.lieBracket ℝ V W`
(`= DW(V) - DV(W)`) can be used for commutators later.

*Linearity.* `fderiv` is `0` at points where `u` is not differentiable, so
`derivAlong V (u + v) p = derivAlong V u p + derivAlong V v p` is false in
general; `derivAlong_add` assumes `DifferentiableAt ℝ u p` and
`DifferentiableAt ℝ v p`. Homogeneity `derivAlong_smul` holds for `c : ℝ` without
hypotheses (`fderiv_const_smul_field`: for `c ≠ 0` the map `u ↦ c • u` preserves
differentiability, and `c = 0` is trivial). `derivAlong_const_mul` is the same
statement with the product written pointwise, `fun q ↦ c * u q`; it is about
`*` and is stated for real-valued `u` only.

*Values in `F`.* The value space `F` is a real normed space, with no inner
product or complex structure assumed: `fderiv ℝ` only uses the real linear
structure, and complex or spinor fields are then functions into `ℂ` or `ℂ⁴`
viewed as real normed spaces. Statements that need more structure on `F` will
assume it where they are made.

*Commutation with continuous linear maps.* For `T : F →L[ℝ] G`,
`derivAlong_clm_comp : derivAlong V (T ∘ u) p = T (derivAlong V u p)` at a point
where `u` is differentiable (chain rule, `T` being its own derivative). The same
holds for `timeDeriv`, `spaceDeriv`, `partialDeriv` (`*_clm_comp` in
`Derivative.lean`) and `rotation`, `boost`, `scaling` (`VectorFields.lean`).
These lemmas reduce statements about `F`-valued fields to their components (real
and imaginary parts, spinor components) and embed real computations into `F`
(`Complex.ofRealCLM`, `ContinuousLinearMap.toSpanSingleton ℝ w`).

*Alternatives considered.*
* `lineDeriv ℝ u p v` (Gateaux derivative): it agrees with
  `fderiv ℝ u p v` for differentiable `u`, but the `C^n` API, the symmetry of
  second derivatives (`IsSymmSndFDerivAt`) and the chain rules are all stated
  for `fderiv`, so using `lineDeriv` would add a conversion at every step.
* The notation class `LineDeriv` with `∂_{v}`
  (`Mathlib.Analysis.Distribution.DerivNotation`): its instances are for
  Schwartz functions, test functions and distributions, not for plain functions
  `Spacetime → ℝ`; it fits a later distributional layer, not this one.
* Vector fields as derivations, or as sections of the tangent bundle
  (manifold API): much heavier, and nothing in the vector field method needs a
  manifold structure on `ℝ^{1+3}`.

### `timeField`, `spaceField a`, `coordField α` and `timeDeriv`, `spaceDeriv a`, `partialDeriv α`

*Formula.* `∂_t`, `∂_a`, `∂_α` with `∂_0 = ∂_t`, `∂_{a+1} = ∂_a`.

*Implementation.* `timeField = fun _ ↦ (1, 0)`,
`spaceField a = fun _ ↦ (0, EuclideanSpace.single a 1)`, `coordField α` by
`Fin.cases timeField spaceField α`, and `timeDeriv = derivAlong timeField`,
etc. Hence, by `rfl`,
* `timeDeriv_apply : ∂ₜ u p = fderiv ℝ u p (1, 0)`,
* `spaceDeriv_apply : ∂ₓ[a] u p = fderiv ℝ u p (0, EuclideanSpace.single a 1)`,
* `partialDeriv_zero : ∂[0] = ∂ₜ`, `partialDeriv_succ : ∂[a.succ] = ∂ₓ[a]`.

Since `simp` rewrites `Fin.succ 0` to `1`, there are also `partialDeriv_one`,
`partialDeriv_two`, `partialDeriv_three`.

*Reasons.* Most formulas use `∂_t` and `∂_a` separately; `∂_α` is needed for
index sums such as `η^{αβ} ∂_α ∂_β`. Defining all three as `derivAlong` of
constant fields makes `∂[0] = ∂ₜ` and `∂[a.succ] = ∂ₓ[a]` definitional.

*Main lemmas.* Linearity (`*_smul`, `*_add`); values on constants and
coordinates (`timeDeriv_timeCoord : ∂ₜ timeCoord = fun _ ↦ 1`,
`spaceDeriv_spaceCoord : ∂ₓ[a] (spaceCoord b) = fun _ ↦ if a = b then 1 else 0`,
...); smoothness for a general order `n : ℕ∞ω`
(`contDiff_partialDeriv : ContDiff ℝ (n + 1) u → ContDiff ℝ n (∂[α] u)`) with
`C^∞` corollaries (`contDiff_infty_partialDeriv`; they hold because
`∞ + 1 = ∞` definitionally); symmetry of second derivatives
(`partialDeriv_comm_apply` for `u` that is `C²` at `p`, from
`ContDiffAt.isSymmSndFDerivAt`, and `partialDeriv_comm` for `u` that is `C²`).
`partialDeriv_partialDeriv_apply` identifies `∂_α ∂_β u (p)` with the second
Fréchet derivative `D²u(p) e_α e_β`.

### `dAlembertian` (`□`) and `kleinGordon`

*Formula.* `□u = η^{αβ} ∂_α ∂_β u = -∂_t² u + ∑ a, ∂_a² u`; Klein–Gordon:
`□u - m² u`.

*Implementation.*
`dAlembertian u = fun p ↦ ∑ α, ∑ β, η α β • ∂[α] (∂[β] u) p` (the entries of `η` are
those of `η^{αβ}`, see above; the real entry acts on the value in `F` by `•`),
with the expansion
`dAlembertian_eq : □ u p = -∂ₜ (∂ₜ u) p + ∑ a, ∂ₓ[a] (∂ₓ[a] u) p`, and
`kleinGordon m u = fun p ↦ □ u p - m ^ 2 • u p`.

*Reasons.* The index form is the one used in the energy-momentum computations
of the vector field method, and `dAlembertian_eq` gives the explicit form. Second
derivatives are iterated first-order operators, so every lemma about `∂_α`
applies to them.

*Lemmas.* `dAlembertian_smul`, `kleinGordon_smul` (no hypothesis); `dAlembertian_add`,
`kleinGordon_add` for `u`, `v` that are `C²` at the point (via
`partialDeriv_partialDeriv_add`, which uses that the first derivatives agree
near the point); the function-level corollaries
`dAlembertian_add_of_contDiff : □ (u + v) = □ u + □ v` and
`kleinGordon_add_of_contDiff : kleinGordon m (u + v) = kleinGordon m u + kleinGordon m v`
for `u`, `v` of class `C²`;
`contDiff_dAlembertian : ContDiff ℝ (n + 2) u → ContDiff ℝ n (□ u)` and
`contDiff_kleinGordon`, with `C^∞` corollaries; `dAlembertian_const`, `dAlembertian_timeCoord`,
`dAlembertian_spaceCoord` (all `0`); and the commutation with continuous linear
maps `dAlembertian_clm_comp : □ (T ∘ u) p = T (□ u p)` and
`kleinGordon_clm_comp` for `u` that is `C²` at `p` (via
`partialDeriv_partialDeriv_clm_comp`, again using that the first derivatives
agree near the point).

*Alternatives considered.*
* Defining `□` directly as `-∂_t² + ∑ ∂_a²`: loses the index form; it is the
  lemma `dAlembertian_eq` instead.
* Writing `η⁻¹` in the definition: then every computation would first rewrite
  with `inv_minkowskiMetric`.
* Mathlib's Laplacian (`Mathlib.Analysis.InnerProductSpace.Laplacian`,
  `Laplacian.laplacian`): it is the trace of the second derivative with respect
  to an inner product, which `Spacetime` does not have (and the Minkowski form
  is indefinite). Relating `∑ a, ∂_a²` to the Laplacian of the spatial factor
  can be done later if needed.
* `iteratedFDeriv ℝ 2 u p ![e_α, e_β]`: equivalent for `C²` functions, but it
  would separate `□` from the first-order operators.

### `rotationField`, `rotation`; `boostField`, `boost`; `scalingField`, `scaling`

*Formulas.*
* `Ω_ab = x_a ∂_b - x_b ∂_a`, component field `p ↦ (0, x_a e_b - x_b e_a)`;
* `L_a = t ∂_a + x_a ∂_t`, component field `p ↦ (x_a, t e_a)`;
* `S = t ∂_t + ∑ a, x_a ∂_a`, component field `p ↦ (t, x) = p`.

*Implementation.* Each operator is `derivAlong` of its component field. The
lemmas `rotationField_eq`, `boostField_eq`, `scalingField_eq` write the fields
as combinations of `timeField` and `spaceField`, and `rotation_eq`, `boost_eq`,
`scaling_eq` give the defining formulas (for instance
`boost a u p = timeCoord p • ∂ₓ[a] u p + spaceCoord a p • ∂ₜ u p`) without any
hypothesis, since `fderiv ℝ u p` is linear.

*Reasons.* Writing the components explicitly keeps the definitions
`rfl`-close to `fderiv` and makes their values on the coordinates immediate.
`Ω_ab` is defined for all `a b : Fin 3`; `rotation_swap : Ω_ba = -Ω_ab` and
`rotation_self : Ω_aa = 0` show that only the three with `a < b` are
independent. Together with the four translations this gives the 11 vector
fields.

*Alternatives considered.*
* Indexing the rotations by pairs `a < b` only: awkward to use in sums and
  in index formulas such as `Ω_ab x_c = δ_bc x_a - δ_ac x_b`.
* Generating the fields from the Lie algebra of the Poincaré group: much more
  infrastructure than needed for the coordinate layer.

## `simp` policy

`@[simp]` is only on

* values of the operators on the coordinate functions and on constants
  (`timeDeriv_timeCoord`, `spaceDeriv_spaceCoord`, `boost_timeCoord`,
  `rotation_spaceCoord`, `scaling_spaceCoord`, `dAlembertian_const`,
  `derivAlong_timeCoord`, ...);
* `partialDeriv_zero`, `partialDeriv_succ`, `partialDeriv_one`,
  `partialDeriv_two`, `partialDeriv_three`.

The unfolding lemmas to `fderiv` (`*_apply`) are ordinary lemmas. The
coordinate smoothness lemmas (`contDiff_timeCoord`, `contDiff_spaceCoord`,
`differentiable_*`) are tagged `@[fun_prop]`.

## Checked computations

Each is a named theorem.

| Statement | Lean name | File |
| --- | --- | --- |
| `∂_t t = 1`, `∂_t x_b = 0`, `∂_a t = 0`, `∂_a x_b = δ_ab` | `timeDeriv_timeCoord`, `timeDeriv_spaceCoord`, `spaceDeriv_timeCoord`, `spaceDeriv_spaceCoord` | `Derivative.lean` |
| `□(t² - r²) = -8`, `□(t²) = -2`, `□(x_a²) = 2` | `dAlembertian_timeCoord_sq_sub_radius_sq`, `dAlembertian_timeCoord_sq`, `dAlembertian_spaceCoord_sq` | `Computations.lean` |
| `L_a t = x_a`, `L_a x_b = t δ_ab` | `boost_timeCoord`, `boost_spaceCoord` | `VectorFields.lean` |
| `L_a (t² - r²) = 0` | `boost_timeCoord_sq_sub_radius_sq` | `Computations.lean` |
| `Ω_ab x_c = δ_bc x_a - δ_ac x_b`, `Ω_ba = -Ω_ab` | `rotation_spaceCoord`, `rotation_swap` | `VectorFields.lean` |
| `Ω_ab (r²) = 0` | `rotation_radius_sq` | `Computations.lean` |
| `S t = t`, `S x_a = x_a` | `scaling_timeCoord`, `scaling_spaceCoord` | `VectorFields.lean` |
| `S (t² - r²) = 2 (t² - r²)` | `scaling_timeCoord_sq_sub_radius_sq` | `Computations.lean` |

These computations are for real-valued functions (`F = ℝ`). The computations with
`t² - r²` go through the general first-derivative
formulas `derivAlong_timeCoord_sq`, `derivAlong_spaceCoord_sq`,
`derivAlong_radius_sq` and `derivAlong_timeCoord_sq_sub_radius_sq`
(`V (t² - r²) = 2 t V⁰ - 2 ∑ a, x_a Vᵃ`).

The section "Sanity checks" at the end of `Computations.lean` contains
`example`s (not named theorems) that check the generalization to `F`:
`□ (fun p ↦ ((timeCoord p ^ 2 : ℝ) : ℂ)) = fun _ ↦ -2` and the corresponding
Klein–Gordon value for a complex-valued function (via `Complex.ofRealCLM` and
`dAlembertian_clm_comp`, `kleinGordon_clm_comp`);
`□ (fun p ↦ timeCoord p ^ 2 • w) = fun _ ↦ (-2 : ℝ) • w` for `w` in any real
normed space; and, for `F = ℝ`, that `□`, `kleinGordon`, `rotation_eq`,
`boost_eq`, `scaling_eq` reduce to the forms with `*`.

## Notation and tokens

The notations `η`, `∂ₜ`, `∂ₓ[a]`, `∂[α]`, `□` are scoped in
`VectorFieldMethod.Minkowski`. Opening the scope makes them tokens: `η` can
then not be used as a variable name, and `η.transpose` lexes as an identifier
rather than as the notation followed by a projection (write
`Matrix.transpose η`). There is no notation for the rotations, boosts and
scaling: tokens such as `Ω[`, `L[` or `S` would clash with Mathlib's
`Ω[S⁄R]` (Kähler differentials), list indexing `L[i]`, and every identifier
`S`.
