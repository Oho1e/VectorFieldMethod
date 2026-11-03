# The hyperboloidal Sobolev inequality on ℝ³

Files: `VectorFieldMethod/Analysis/LocalSobolev.lean` and
`VectorFieldMethod/Analysis/HyperboloidalSobolev.lean`, both imported by
`VectorFieldMethod.lean`. Every declaration is in the namespace
`VectorFieldMethod.EuclideanSobolev`. The statement-by-statement correspondence
between the mathematics and the Lean code is in
`docs/statements/euclidean-sobolev.md`.

This is the part of the Klainerman–Sobolev inequality on hyperboloids that only
involves `ℝ³`. The passage from `ℝ³` to the hyperboloid is described below; it
is formalized in `VectorFieldMethod/Minkowski/KlainermanSobolev.lean` (namespace
`VectorFieldMethod.Minkowski`; statements in
`docs/statements/klainerman-sobolev.md`).

## Notation

* `ℝ³` is `EuclideanSpace ℝ (Fin 3)` with Lebesgue measure. Spatial indices
  `a, b ∈ {1, 2, 3}` are the Lean indices `0, 1, 2`, and
  `∂_a w (x) = Dw(x) e_a` is `fderiv ℝ w x (EuclideanSpace.single a 1)`.
* For `s > 0`, `φ_s(x) = √(s² + |x|²)`.
* `Λ_a w = φ_s ∂_a w` is `hyperboloidalWeightedDeriv s a w`. It depends on `s`.
* `‖·‖` without subscript is the `L²` norm over `ℝ³`. In Lean all `L²` norms are
  `eLpNorm _ 2 _`, with values in `ℝ≥0∞`; they may be `∞`, and the inequalities
  below then hold trivially. No integrability, boundedness or support assumption
  is made.

## What is proved

**Theorem 1** (`exists_abs_le_eLpNorm_ball`, local embedding `H² ⊂ L^∞`). There
is an absolute constant `C` such that for every ball `B = B(x₀, ρ)` of `ℝ³`
(`ρ > 0`) and every function `f` which is `C²` on `B`,

    |f(x₀)| ≤ C (ρ^{-3/2} ‖f‖_{L²(B)} + ρ^{-1/2} ‖Df‖_{L²(B)} + ρ^{1/2} ‖D²f‖_{L²(B)}),

where `Df` and `D²f = iteratedFDeriv ℝ 2 f` carry their operator norms. The
powers of `ρ` make the inequality invariant under dilations. The proposition
`LocalSobolevBound` is this statement, and `localSobolevBound_holds` proves it.

**Theorem 2** (`exists_hyperboloidalSobolev`). There is an absolute constant `C`
such that for all `s > 0`, all `w ∈ C²(ℝ³)` and all `x₀ ∈ ℝ³`,

    φ_s(x₀)^{3/2} |w(x₀)| ≤ C (‖w‖ + ∑_a ‖Λ_a w‖ + ∑_{a,b} ‖Λ_a Λ_b w‖).

The right-hand side has `1 + 3 + 9 = 13` terms: the sum over `(a, b)` runs over
all nine ordered pairs. The local version `exists_hyperboloidalSobolev_ball` has
the same left-hand side and `L²` norms over the ball `B(x₀, φ_s(x₀)/3)` only.
The reductions `exists_hyperboloidalSobolev_ball_of_localSobolevBound` and
`exists_hyperboloidalSobolev_of_localSobolevBound` derive both versions from
`LocalSobolevBound`.

The proofs give `C = 2 |B(0, 1)|^{-1/2}` in Theorem 1 and fifteen times that
constant in Theorem 2; the statements only assert existence.

## From ℝ³ to the hyperboloid (formalized in `KlainermanSobolev.lean`)

Work in Minkowski spacetime `ℝ^{1+3}` with coordinates `(t, x)` and the
conventions of the coordinate layer `VectorFieldMethod.Minkowski`
(`docs/minkowski-layer.md`). The boosts are `L_a = t ∂_a + x_a ∂_t`. For `s > 0`
the hyperboloid is `H_s = {(t, x) : t = φ_s(x)} = {t² - |x|² = s², t > 0}`, and
the restriction of a spacetime function `v` to `H_s` is the function on `ℝ³`

    v|_{H_s}(x) = v(φ_s(x), x).

**Lemma.** If `v` is `C¹`, then `Λ_a (v|_{H_s}) = (L_a v)|_{H_s}` for every `a`.

*Proof.* By the chain rule, `∂_a (v|_{H_s})(x) = (∂_t v)(φ_s(x), x) ∂_a φ_s(x) +
(∂_a v)(φ_s(x), x)`, and `∂_a φ_s(x) = x_a / φ_s(x)`. Multiplying by `φ_s(x)`,
which is the value of `t` at the point `(φ_s(x), x)` of `H_s`, gives
`Λ_a (v|_{H_s})(x) = (x_a ∂_t v + t ∂_a v)(φ_s(x), x) = (L_a v)|_{H_s}(x)`. ∎

**Iteration.** For an ordered multi-index `J = (a₁, …, a_k)` put
`Λ^J = Λ_{a₁} ⋯ Λ_{a_k}` and `L^J = L_{a₁} ⋯ L_{a_k}`. If `u` is `C^k`, then
`Λ^J (u|_{H_s}) = (L^J u)|_{H_s}`, with the indices in the same order: apply the
lemma to `v = L_{a₂} ⋯ L_{a_k} u`, which is `C¹`, and induct. The order matters,
since `[L_a, L_b] = x_a ∂_b - x_b ∂_a` is a rotation, which is nonzero for
`a ≠ b`; this is why Theorem 2 sums over ordered pairs.

**Consequence.** Let `u` be `C²` near `H_s` and `w = u|_{H_s}`; then `w` is `C²`
on `ℝ³`, because `φ_s` is smooth for `s > 0`. Define the flat `L²` norm on `H_s`
by

    ‖v‖²_{L²_f(H_s)} = ∫_{ℝ³} |v(φ_s(x), x)|² dx,

using Lebesgue measure `dx` on `ℝ³` rather than the induced measure of `H_s`.
Then `‖Λ^J w‖ = ‖L^J u‖_{L²_f(H_s)}`, and at the point `(t, x₀) ∈ H_s` one has
`t = φ_s(x₀)` and `w(x₀) = u(t, x₀)`. Theorem 2 therefore gives

    sup_{H_s} t^{3/2} |u| ≤ C ∑_{|J| ≤ 2} ‖L^J u‖_{L²_f(H_s)},

where `J` runs over the 13 ordered multi-indices of length at most 2.

**Remarks.**

* `C` is an absolute constant: it does not depend on `s`, on `u` or on the
  point.
* No support assumption is needed. In the literature the inequality is often
  stated for functions supported in a cone such as `{|x| < t - 1}`; the proof
  here works on the ball `B(x₀, φ_s(x₀)/3)` whatever the support is.
* `Λ_a` depends on `s` through the weight `φ_s`, while `L_a` does not.

The lemma, its iteration for `|J| ≤ 2`, the regularity of `w` and the
consequence are formalized in `VectorFieldMethod/Minkowski/KlainermanSobolev.lean`,
where `v|_{H_s}` is `restrictHyperboloid s v` and "`u` is `C²` near `H_s`" means
that `u` is `C²` on an open set `U` containing `H_s`:

* `hyperboloidalWeightedDeriv_restrictHyperboloid_apply`: the lemma, at a point
  `x`, for `s ≠ 0` and `v` differentiable at `(φ_s(x), x)`;
* `hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_restrictHyperboloid`:
  the iteration for `|J| = 2`, `Λ_a Λ_b w = (L_a L_b u)|_{H_s}`;
* `contDiff_restrictHyperboloid`: `w ∈ C²(ℝ³)`;
* `exists_klainermanSobolev_hyperboloid`: the consequence, with an absolute
  constant `C`.

## Proofs

### Theorem 1

The proof averages Taylor's formula along the segments issued from `x₀`; it uses
neither polar coordinates nor cut-off functions. Write `|B|` for the volume of
`B = B(x₀, ρ)`.

1. *Taylor along a segment* (`eq_sub_add_integral_of_contDiffOn_ball`). For
   `y ∈ B`, the fundamental theorem of calculus applied to
   `ψ(t) = t Df(x₀ + t(y - x₀))(y - x₀) - f(x₀ + t(y - x₀))`, whose derivative
   is `t D²f(x₀ + t(y - x₀))(y - x₀, y - x₀)`, gives
   `f(x₀) = f(y) - Df(y)(y - x₀) + ∫₀¹ t D²f(x₀ + t(y - x₀))(y - x₀, y - x₀) dt`.
   Hence (`enorm_le_of_contDiffOn_ball`)
   `|f(x₀)| ≤ |f(y)| + ρ ‖Df(y)‖ + ρ² ∫₀¹ t ‖D²f(x₀ + t(y - x₀))‖ dt`.
2. *Averaging* (`measure_ball_mul_enorm_le`). Integrate over `y ∈ B`. By
   Cauchy–Schwarz, `∫_B ‖g‖ ≤ |B|^{1/2} ‖g‖_{L²(B)}`, which bounds the first two
   terms of `|B| |f(x₀)|` by `|B|^{1/2} (‖f‖_{L²(B)} + ρ ‖Df‖_{L²(B)})`.
3. *The second-order term* (`lintegral_ball_lintegral_Ioc_le`). Exchange the
   integrals in `y` and `t` (Tonelli, for nonnegative measurable functions; no
   integrability is needed). For fixed `t ∈ (0, 1]` the homothety
   `y ↦ x₀ + t(y - x₀)` maps `B` into itself and multiplies volumes by `t³`
   (`setLIntegral_ball_comp_homothety_le`), so Cauchy–Schwarz in `y` gives
   `∫_B ‖D²f(x₀ + t(y - x₀))‖ dy ≤ t^{-3/2} |B|^{1/2} ‖D²f‖_{L²(B)}`
   (`eLpNorm_comp_homothety_le`). Since `∫₀¹ t · t^{-3/2} dt = 2`, the
   second-order term is at most `2 ρ² |B|^{1/2} ‖D²f‖_{L²(B)}`.
4. *Conclusion* (`exists_abs_le_eLpNorm_ball`). Divide by
   `|B| = ρ³ |B(0, 1)|`.

In step 3, another classical approach first changes variables `z = t(y - x₀)`,
exchanges the integrals a second time and applies Cauchy–Schwarz against the
weight `|z|^{-1}`, which requires `∫_{B(0, ρ)} |z|^{-2} dz ≤ Cρ`. Applying
Cauchy–Schwarz in `y` for each fixed `t` instead needs only one exchange of
integrals, no singular weight, and the elementary integral `∫₀¹ t^{-1/2} dt = 2`.

### Theorem 2

Let `φ₀ = φ_s(x₀)` and `ρ = φ₀/3`, and apply Theorem 1 to `w` on
`B = B(x₀, ρ)`.

* `φ_s` is 1-Lipschitz (`sqrt_sq_add_norm_sq_le_add`; algebraic proof), so
  `φ₀ ≤ (3/2) φ_s` on `B` (`sqrt_sq_add_norm_sq_le_of_mem_ball`).
* `‖Dw(x)‖ ≤ ∑_a |∂_a w(x)|` and `‖D²w(x)‖ ≤ ∑_{a,b} |∂_a ∂_b w(x)|`, by expanding
  in the standard basis (`norm_le_sum_norm_apply_single`). Hence
  `φ₀ ‖Dw‖ ≤ (3/2) ∑_a |Λ_a w|` on `B` (`mul_norm_fderiv_le`).
* `Λ_a Λ_b w = φ_s² ∂_a ∂_b w + x_a ∂_b w`
  (`hyperboloidalWeightedDeriv_hyperboloidalWeightedDeriv_apply`), where
  `∂_a ∂_b w(x) = D²w(x)(e_a, e_b)` with the outer derivative in the direction
  `a`. Since `|x_a| ≤ φ_s`, this gives
  `φ₀² ‖D²w‖ ≤ (9/4) ∑_{a,b} (|Λ_a Λ_b w| + |Λ_b w|)` on `B`
  (`sq_mul_norm_iteratedFDeriv_le`).
* Multiplying Theorem 1 by `φ₀^{3/2}`, the three coefficients become `3^{3/2}`,
  `√3 φ₀` and `φ₀²/√3`; the two previous bounds absorb the powers of `φ₀` and
  give the local version. The global version follows since `L²` norms over `B`
  are at most `L²` norms over `ℝ³` (`eLpNorm_mono_measure`).
