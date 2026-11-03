# Commutators of the Minkowski vector fields: statements

Layer: `VectorFieldMethod/Minkowski/`, files `Commutators.lean` (commutators of the vector fields)
and `WaveCommutators.lean` (commutators with $`\Box`$ and the Klein–Gordon operator). They build on
the Minkowski coordinate layer, documented in [`minkowski.md`](minkowski.md), whose conventions,
notation and definitions (`derivAlong`, the component fields `timeField`, `spaceField`,
`coordField`, `rotationField`, `boostField`, `scalingField`, the operators `∂ₜ`, `∂ₓ[a]`, `∂[α]`,
`rotation`, `boost`, `scaling`, `□`, `kleinGordon`) are used here without change. All declarations
are in the namespace `VectorFieldMethod.Minkowski`. The links below point to commit
[`d3ad61d`](https://github.com/Oho1e/VectorFieldMethod/tree/d3ad61dc2447af2599860c695e03b3c37b718008), the last commit that changes
the Lean files of this layer. How to read the entries: [`README.md`](README.md).

## Notation and conventions

**Indices and fields.** As in [`minkowski.md`](minkowski.md), the mathematical spatial index
$`a \in \{1, 2, 3\}`$ is the Lean index $`a - 1`$ of `Fin 3` (likewise for $`b, c, d`$), and a
spacetime index $`\alpha \in \{0, 1, 2, 3\}`$ is the same element of `Fin 4`. A vector field is given by its
component field $`V : \mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$, and acts on
$`u : \mathbb{R}^{1+3} \to F`$ ($`F`$ a real normed space) by $`(Vu)(p) = Du(p)\,V(p)`$
(`derivAlong V u p`). The component fields of $`\partial_t, \partial_a, \partial_\alpha`$ are
constant, those of $`\Omega_{ab}`$, $`L_a`$, $`S`$ are linear:
$`\Omega_{ab}(t, x) = (0, x^a e_b - x^b e_a)`$, $`L_a(t, x) = (x^a, t e_a)`$, $`S(t, x) = (t, x)`$.
$`E_\alpha`$ denotes the value of the constant field $`\partial_\alpha`$: $`E_0 = (1, 0)`$,
$`E_a = (0, e_a)`$ (Lean `coordField α 0`).

**Commutators.** For operators $`X, Y`$ acting on functions, $`[X, Y]u = X(Yu) - Y(Xu)`$. For
component fields $`V, W`$, $`[V, W]`$ is the Lie bracket
```math
[V, W](p) = DW(p)\,V(p) - DV(p)\,W(p),
```
which is Mathlib's `VectorField.lieBracket ℝ V W` (written `lieBracket ℝ V W`, the files have
`open VectorField`); its sign convention makes $`[V, W]u = V(Wu) - W(Vu)`$ for $`C^2`$ functions
$`u`$. The definition, quoted from Mathlib
([`Mathlib/Analysis/Calculus/VectorField.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Calculus/VectorField.lean#L59),
at the Mathlib commit pinned in `lake-manifest.json`; `𝕜` is the field of scalars, here
$`\mathbb{R}`$, and `E` the vector space, here `Spacetime`):

```lean
def lieBracket (V W : E → E) (x : E) : E :=
  fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)
```

**Kronecker delta.** $`\delta_{ab}`$ is written `if a = b then (1 : ℝ) else 0` in Lean, a real number
that multiplies component fields and values in $`F`$ by `•`.

**Forms of the statements.** Equalities between operators, such as
$`[L_a, L_b] = \Omega_{ab}`$, are stated twice: at a point $`p`$ where $`u`$ is $`C^k`$ (names
ending in `_apply`, hypothesis `ContDiffAt ℝ k u p`, which means that $`u`$ is $`C^k`$ on a
neighbourhood of $`p`$), and as equalities of functions for $`u \in C^k(\mathbb{R}^{1+3})`$ (same
name without `_apply`, hypothesis `ContDiff ℝ k u`). Vanishing commutators $`[X, Y] = 0`$ are stated
as commutation relations $`X(Yu) = Y(Xu)`$ (names with `_comm`). Constant functions and fields are
written `fun _ ↦ c`.

**Second derivatives.** $`D^2u(p)(v, w)`$ is `fderiv ℝ (fderiv ℝ u) p v w`, the derivative at $`p`$
in the direction $`v`$ of $`q \mapsto Du(q)\,w`$. For $`u`$ of class $`C^2`$ near $`p`$ it is
symmetric, and $`\partial_\alpha \partial_\beta u(p) = D^2u(p)(E_\alpha, E_\beta)`$
(`partialDeriv_partialDeriv_apply` in `Derivative.lean`).

## Context

The `variable` lines of the two files; their only hypotheses are that $`F`$ is a real normed space.

[`Commutators.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L57):

```lean
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V W : Spacetime → Spacetime} {u : Spacetime → F} {p : Spacetime}
```

[`WaveCommutators.lean`](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L57):

```lean
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : Spacetime → Spacetime} {u : Spacetime → F} {p : Spacetime}
```

## Definitions

The layer introduces no new definitions; it uses Mathlib's Lie bracket `VectorField.lieBracket`
(quoted above) and the definitions of the Minkowski coordinate layer.

## Main theorems: commutator of two vector fields

### The commutator of two vector fields is the Lie bracket (at a point)

- **Math.** Let $`V, W : \mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$ be differentiable at
  $`p \in \mathbb{R}^{1+3}`$, and let $`u : \mathbb{R}^{1+3} \to F`$ be $`C^2`$ on a neighbourhood
  of $`p`$. Then
  ```math
  V(Wu)(p) - W(Vu)(p) = \big([V, W]u\big)(p) = Du(p)\,\big(DW(p)\,V(p) - DV(p)\,W(p)\big).
  ```
- **Hypotheses.** $`F`$ is a real normed space; $`V`$ and $`W`$ are differentiable at $`p`$; $`u`$
  is $`C^2`$ at $`p`$ (`ContDiffAt ℝ 2 u p`).
- **Lean.** `VectorFieldMethod.Minkowski.derivAlong_derivAlong_sub_derivAlong_derivAlong_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L64)

```lean
theorem derivAlong_derivAlong_sub_derivAlong_derivAlong_apply (hV : DifferentiableAt ℝ V p)
    (hW : DifferentiableAt ℝ W p) (hu : ContDiffAt ℝ 2 u p) :
    derivAlong V (derivAlong W u) p - derivAlong W (derivAlong V u) p =
      derivAlong (lieBracket ℝ V W) u p
```

- **Notes.** This is Mathlib's `VectorField.fderiv_apply_lieBracket`, rewritten with `derivAlong`:
  $`V(Wu)(p) = D^2u(p)(V(p), W(p)) + Du(p)\,DW(p)\,V(p)`$, and the second-order terms cancel by the
  symmetry of $`D^2u(p)`$. The hypotheses are needed because `fderiv` is $`0`$ where a function is
  not differentiable (see the README).

### The commutator of two vector fields is the Lie bracket

- **Math.** Let $`V, W : \mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$ be differentiable and
  $`u \in C^2(\mathbb{R}^{1+3}, F)`$. Then $`V(Wu) - W(Vu) = [V, W]u`$ on $`\mathbb{R}^{1+3}`$.
- **Hypotheses.** $`F`$ is a real normed space; $`V`$ and $`W`$ are differentiable everywhere;
  $`u`$ is $`C^2`$ (`ContDiff ℝ 2 u`).
- **Lean.** `VectorFieldMethod.Minkowski.derivAlong_derivAlong_sub_derivAlong_derivAlong`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L73)

```lean
theorem derivAlong_derivAlong_sub_derivAlong_derivAlong (hV : Differentiable ℝ V)
    (hW : Differentiable ℝ W) (hu : ContDiff ℝ 2 u) :
    derivAlong V (derivAlong W u) - derivAlong W (derivAlong V u) =
      derivAlong (lieBracket ℝ V W) u
```

## Main theorems: commutation relations of the Minkowski vector fields

Each entry gives the Lie bracket of the component fields (an equality of maps
$`\mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$, no hypotheses) and the resulting relation between the
operators, at a point and as an equality of functions. The operator relations follow from the
entry above, since all component fields are smooth.

### $`[\partial_t, L_a] = \partial_a`$

- **Math.** For $`a \in \{1, 2, 3\}`$, $`[\partial_t, L_a] = \partial_a`$ as component fields:
  $`[(1, 0), (x^a, t e_a)] = (0, e_a)`$. Hence, for $`u`$ that is $`C^2`$ near $`p`$,
  ```math
  \partial_t (L_a u)(p) - L_a(\partial_t u)(p) = \partial_a u(p),
  ```
  and $`\partial_t L_a u - L_a \partial_t u = \partial_a u`$ on $`\mathbb{R}^{1+3}`$ for
  $`u \in C^2`$.
- **Hypotheses.** Field identity: none. Operator identities: $`F`$ is a real normed space; $`u`$
  is $`C^2`$ at $`p`$ (`ContDiffAt ℝ 2 u p`), resp. $`u`$ is $`C^2`$ (`ContDiff ℝ 2 u`).
- **Lean.** `VectorFieldMethod.Minkowski.lieBracket_timeField_boostField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L192);
  `VectorFieldMethod.Minkowski.timeDeriv_boost_sub_boost_timeDeriv_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L315);
  `VectorFieldMethod.Minkowski.timeDeriv_boost_sub_boost_timeDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L323)

```lean
theorem lieBracket_timeField_boostField (a : Fin 3) :
    lieBracket ℝ timeField (boostField a) = spaceField a

theorem timeDeriv_boost_sub_boost_timeDeriv_apply (a : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    ∂ₜ (boost a u) p - boost a (∂ₜ u) p = ∂ₓ[a] u p

theorem timeDeriv_boost_sub_boost_timeDeriv (a : Fin 3) (hu : ContDiff ℝ 2 u) :
    ∂ₜ (boost a u) - boost a (∂ₜ u) = ∂ₓ[a] u
```

### $`[\partial_b, L_a] = \delta_{ab}\, \partial_t`$

- **Math.** For $`a, b \in \{1, 2, 3\}`$, $`[\partial_b, L_a] = \delta_{ab}\, \partial_t`$ as
  component fields. Hence, for $`u`$ that is $`C^2`$ near $`p`$,
  ```math
  \partial_b (L_a u)(p) - L_a(\partial_b u)(p) = \delta_{ab}\, \partial_t u(p),
  ```
  and the same identity of functions for $`u \in C^2`$.
- **Hypotheses.** Field identity: none. Operator identities: $`F`$ is a real normed space; $`u`$
  is $`C^2`$ at $`p`$, resp. $`u`$ is $`C^2`$.
- **Lean.** `VectorFieldMethod.Minkowski.lieBracket_spaceField_boostField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L199);
  `VectorFieldMethod.Minkowski.spaceDeriv_boost_sub_boost_spaceDeriv_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L328);
  `VectorFieldMethod.Minkowski.spaceDeriv_boost_sub_boost_spaceDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L336)

```lean
theorem lieBracket_spaceField_boostField (a b : Fin 3) :
    lieBracket ℝ (spaceField b) (boostField a) = (if a = b then (1 : ℝ) else 0) • timeField

theorem spaceDeriv_boost_sub_boost_spaceDeriv_apply (a b : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    ∂ₓ[b] (boost a u) p - boost a (∂ₓ[b] u) p = (if a = b then (1 : ℝ) else 0) • ∂ₜ u p

theorem spaceDeriv_boost_sub_boost_spaceDeriv (a b : Fin 3) (hu : ContDiff ℝ 2 u) :
    ∂ₓ[b] (boost a u) - boost a (∂ₓ[b] u) = (if a = b then (1 : ℝ) else 0) • ∂ₜ u
```

- **Notes.** The Lean arguments are in the order `a b`, with `∂ₓ[b]` the translation and `boost a`
  the boost, as in the mathematical formula.

### $`[\partial_t, \Omega_{ab}] = 0`$

- **Math.** For $`a, b \in \{1, 2, 3\}`$, $`[\partial_t, \Omega_{ab}] = 0`$ as component fields.
  Hence, for $`u`$ that is $`C^2`$ near $`p`$, $`\partial_t(\Omega_{ab} u)(p) = \Omega_{ab}(\partial_t u)(p)`$,
  and $`\partial_t \Omega_{ab} u = \Omega_{ab} \partial_t u`$ on $`\mathbb{R}^{1+3}`$ for
  $`u \in C^2`$.
- **Hypotheses.** Field identity: none. Operator identities: $`F`$ is a real normed space; $`u`$
  is $`C^2`$ at $`p`$, resp. $`u`$ is $`C^2`$.
- **Lean.** `VectorFieldMethod.Minkowski.lieBracket_timeField_rotationField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L211);
  `VectorFieldMethod.Minkowski.timeDeriv_rotation_comm_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L341); `VectorFieldMethod.Minkowski.timeDeriv_rotation_comm`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L349)

```lean
theorem lieBracket_timeField_rotationField (a b : Fin 3) :
    lieBracket ℝ timeField (rotationField a b) = fun _ ↦ 0

theorem timeDeriv_rotation_comm_apply (a b : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    ∂ₜ (rotation a b u) p = rotation a b (∂ₜ u) p

theorem timeDeriv_rotation_comm (a b : Fin 3) (hu : ContDiff ℝ 2 u) :
    ∂ₜ (rotation a b u) = rotation a b (∂ₜ u)
```

### $`[\partial_c, \Omega_{ab}] = \delta_{ca}\, \partial_b - \delta_{cb}\, \partial_a`$

- **Math.** For $`a, b, c \in \{1, 2, 3\}`$,
  $`[\partial_c, \Omega_{ab}] = \delta_{ca}\, \partial_b - \delta_{cb}\, \partial_a`$ as component
  fields. Hence, for $`u`$ that is $`C^2`$ near $`p`$,
  ```math
  \partial_c (\Omega_{ab} u)(p) - \Omega_{ab}(\partial_c u)(p) = \delta_{ca}\, \partial_b u(p) - \delta_{cb}\, \partial_a u(p),
  ```
  and the same identity of functions for $`u \in C^2`$.
- **Hypotheses.** Field identity: none. Operator identities: $`F`$ is a real normed space; $`u`$
  is $`C^2`$ at $`p`$, resp. $`u`$ is $`C^2`$.
- **Lean.** `VectorFieldMethod.Minkowski.lieBracket_spaceField_rotationField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L218);
  `VectorFieldMethod.Minkowski.spaceDeriv_rotation_sub_rotation_spaceDeriv_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L354);
  `VectorFieldMethod.Minkowski.spaceDeriv_rotation_sub_rotation_spaceDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L366)

```lean
theorem lieBracket_spaceField_rotationField (a b c : Fin 3) :
    lieBracket ℝ (spaceField c) (rotationField a b) =
      (if c = a then (1 : ℝ) else 0) • spaceField b -
        (if c = b then (1 : ℝ) else 0) • spaceField a

theorem spaceDeriv_rotation_sub_rotation_spaceDeriv_apply (a b c : Fin 3)
    (hu : ContDiffAt ℝ 2 u p) :
    ∂ₓ[c] (rotation a b u) p - rotation a b (∂ₓ[c] u) p =
      (if c = a then (1 : ℝ) else 0) • ∂ₓ[b] u p -
        (if c = b then (1 : ℝ) else 0) • ∂ₓ[a] u p

theorem spaceDeriv_rotation_sub_rotation_spaceDeriv (a b c : Fin 3) (hu : ContDiff ℝ 2 u) :
    ∂ₓ[c] (rotation a b u) - rotation a b (∂ₓ[c] u) =
      (if c = a then (1 : ℝ) else 0) • ∂ₓ[b] u - (if c = b then (1 : ℝ) else 0) • ∂ₓ[a] u
```

### $`[\partial_t, S] = \partial_t`$ and $`[\partial_a, S] = \partial_a`$

- **Math.** For $`a \in \{1, 2, 3\}`$, $`[\partial_t, S] = \partial_t`$ and
  $`[\partial_a, S] = \partial_a`$ as component fields (hence $`[\partial_\alpha, S] = \partial_\alpha`$
  for every $`\alpha`$). Hence, for $`u`$ that is $`C^2`$ near $`p`$,
  ```math
  \partial_t (S u)(p) - S(\partial_t u)(p) = \partial_t u(p), \qquad \partial_a (S u)(p) - S(\partial_a u)(p) = \partial_a u(p),
  ```
  and the same identities of functions for $`u \in C^2`$.
- **Hypotheses.** Field identities: none. Operator identities: $`F`$ is a real normed space; $`u`$
  is $`C^2`$ at $`p`$, resp. $`u`$ is $`C^2`$.
- **Lean.** `VectorFieldMethod.Minkowski.lieBracket_timeField_scalingField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L232);
  `VectorFieldMethod.Minkowski.lieBracket_spaceField_scalingField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L239);
  `VectorFieldMethod.Minkowski.lieBracket_coordField_scalingField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L246);
  `VectorFieldMethod.Minkowski.timeDeriv_scaling_sub_scaling_timeDeriv_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L372);
  `VectorFieldMethod.Minkowski.timeDeriv_scaling_sub_scaling_timeDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L380);
  `VectorFieldMethod.Minkowski.spaceDeriv_scaling_sub_scaling_spaceDeriv_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L385);
  `VectorFieldMethod.Minkowski.spaceDeriv_scaling_sub_scaling_spaceDeriv`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L393)

```lean
theorem lieBracket_timeField_scalingField :
    lieBracket ℝ timeField scalingField = timeField

theorem lieBracket_spaceField_scalingField (a : Fin 3) :
    lieBracket ℝ (spaceField a) scalingField = spaceField a

theorem lieBracket_coordField_scalingField (α : Fin 4) :
    lieBracket ℝ (coordField α) scalingField = coordField α

theorem timeDeriv_scaling_sub_scaling_timeDeriv_apply (hu : ContDiffAt ℝ 2 u p) :
    ∂ₜ (scaling u) p - scaling (∂ₜ u) p = ∂ₜ u p

theorem timeDeriv_scaling_sub_scaling_timeDeriv (hu : ContDiff ℝ 2 u) :
    ∂ₜ (scaling u) - scaling (∂ₜ u) = ∂ₜ u

theorem spaceDeriv_scaling_sub_scaling_spaceDeriv_apply (a : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    ∂ₓ[a] (scaling u) p - scaling (∂ₓ[a] u) p = ∂ₓ[a] u p

theorem spaceDeriv_scaling_sub_scaling_spaceDeriv (a : Fin 3) (hu : ContDiff ℝ 2 u) :
    ∂ₓ[a] (scaling u) - scaling (∂ₓ[a] u) = ∂ₓ[a] u
```

### $`[L_a, L_b] = \Omega_{ab}`$

- **Math.** For $`a, b \in \{1, 2, 3\}`$, $`[L_a, L_b] = \Omega_{ab}`$ as component fields. Hence,
  for $`u`$ that is $`C^2`$ near $`p`$,
  ```math
  L_a(L_b u)(p) - L_b(L_a u)(p) = \Omega_{ab} u(p),
  ```
  and $`L_a L_b u - L_b L_a u = \Omega_{ab} u`$ on $`\mathbb{R}^{1+3}`$ for $`u \in C^2`$.
- **Hypotheses.** Field identity: none. Operator identities: $`F`$ is a real normed space; $`u`$
  is $`C^2`$ at $`p`$, resp. $`u`$ is $`C^2`$.
- **Lean.** `VectorFieldMethod.Minkowski.lieBracket_boostField_boostField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L253);
  `VectorFieldMethod.Minkowski.boost_boost_sub_boost_boost_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L400); `VectorFieldMethod.Minkowski.boost_boost_sub_boost_boost`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L408)

```lean
theorem lieBracket_boostField_boostField (a b : Fin 3) :
    lieBracket ℝ (boostField a) (boostField b) = rotationField a b

theorem boost_boost_sub_boost_boost_apply (a b : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    boost a (boost b u) p - boost b (boost a u) p = rotation a b u p

theorem boost_boost_sub_boost_boost (a b : Fin 3) (hu : ContDiff ℝ 2 u) :
    boost a (boost b u) - boost b (boost a u) = rotation a b u
```

- **Notes.** The sign is fixed by $`\Omega_{ab} = x^a \partial_b - x^b \partial_a`$ and
  $`L_a = t\,\partial_a + x^a \partial_t`$. The "Sanity checks" section of `Commutators.lean`
  verifies the identity on $`u = x^c`$, where both sides equal
  $`\delta_{bc}\, x^a - \delta_{ac}\, x^b`$, using only the values of $`L_a`$ and $`\Omega_{ab}`$ on
  the coordinates.

### $`[L_a, \Omega_{bc}] = \delta_{ab}\, L_c - \delta_{ac}\, L_b`$

- **Math.** For $`a, b, c \in \{1, 2, 3\}`$,
  $`[L_a, \Omega_{bc}] = \delta_{ab}\, L_c - \delta_{ac}\, L_b`$ as component fields. Hence, for
  $`u`$ that is $`C^2`$ near $`p`$,
  ```math
  L_a(\Omega_{bc} u)(p) - \Omega_{bc}(L_a u)(p) = \delta_{ab}\, L_c u(p) - \delta_{ac}\, L_b u(p),
  ```
  and the same identity of functions for $`u \in C^2`$.
- **Hypotheses.** Field identity: none. Operator identities: $`F`$ is a real normed space; $`u`$
  is $`C^2`$ at $`p`$, resp. $`u`$ is $`C^2`$.
- **Lean.** `VectorFieldMethod.Minkowski.lieBracket_boostField_rotationField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L263);
  `VectorFieldMethod.Minkowski.boost_rotation_sub_rotation_boost_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L413);
  `VectorFieldMethod.Minkowski.boost_rotation_sub_rotation_boost`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L424)

```lean
theorem lieBracket_boostField_rotationField (a b c : Fin 3) :
    lieBracket ℝ (boostField a) (rotationField b c) =
      (if a = b then (1 : ℝ) else 0) • boostField c -
        (if a = c then (1 : ℝ) else 0) • boostField b

theorem boost_rotation_sub_rotation_boost_apply (a b c : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    boost a (rotation b c u) p - rotation b c (boost a u) p =
      (if a = b then (1 : ℝ) else 0) • boost c u p -
        (if a = c then (1 : ℝ) else 0) • boost b u p

theorem boost_rotation_sub_rotation_boost (a b c : Fin 3) (hu : ContDiff ℝ 2 u) :
    boost a (rotation b c u) - rotation b c (boost a u) =
      (if a = b then (1 : ℝ) else 0) • boost c u - (if a = c then (1 : ℝ) else 0) • boost b u
```

### $`[\Omega_{ab}, \Omega_{cd}] = \delta_{bc}\, \Omega_{ad} - \delta_{ac}\, \Omega_{bd} - \delta_{bd}\, \Omega_{ac} + \delta_{ad}\, \Omega_{bc}`$

- **Math.** For $`a, b, c, d \in \{1, 2, 3\}`$,
  $`[\Omega_{ab}, \Omega_{cd}] = \delta_{bc}\, \Omega_{ad} - \delta_{ac}\, \Omega_{bd} - \delta_{bd}\, \Omega_{ac} + \delta_{ad}\, \Omega_{bc}`$
  as component fields. Hence, for $`u`$ that is $`C^2`$ near $`p`$,
  ```math
  \Omega_{ab}(\Omega_{cd} u)(p) - \Omega_{cd}(\Omega_{ab} u)(p) = \delta_{bc}\, \Omega_{ad} u(p) - \delta_{ac}\, \Omega_{bd} u(p) - \delta_{bd}\, \Omega_{ac} u(p) + \delta_{ad}\, \Omega_{bc} u(p),
  ```
  and the same identity of functions for $`u \in C^2`$.
- **Hypotheses.** Field identity: none. Operator identities: $`F`$ is a real normed space; $`u`$
  is $`C^2`$ at $`p`$, resp. $`u`$ is $`C^2`$.
- **Lean.** `VectorFieldMethod.Minkowski.lieBracket_rotationField_rotationField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L280);
  `VectorFieldMethod.Minkowski.rotation_rotation_sub_rotation_rotation_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L431);
  `VectorFieldMethod.Minkowski.rotation_rotation_sub_rotation_rotation`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L445)

```lean
theorem lieBracket_rotationField_rotationField (a b c d : Fin 3) :
    lieBracket ℝ (rotationField a b) (rotationField c d) =
      (if b = c then (1 : ℝ) else 0) • rotationField a d -
        (if a = c then (1 : ℝ) else 0) • rotationField b d -
        (if b = d then (1 : ℝ) else 0) • rotationField a c +
        (if a = d then (1 : ℝ) else 0) • rotationField b c

theorem rotation_rotation_sub_rotation_rotation_apply (a b c d : Fin 3)
    (hu : ContDiffAt ℝ 2 u p) :
    rotation a b (rotation c d u) p - rotation c d (rotation a b u) p =
      (if b = c then (1 : ℝ) else 0) • rotation a d u p -
        (if a = c then (1 : ℝ) else 0) • rotation b d u p -
        (if b = d then (1 : ℝ) else 0) • rotation a c u p +
        (if a = d then (1 : ℝ) else 0) • rotation b c u p

theorem rotation_rotation_sub_rotation_rotation (a b c d : Fin 3) (hu : ContDiff ℝ 2 u) :
    rotation a b (rotation c d u) - rotation c d (rotation a b u) =
      (if b = c then (1 : ℝ) else 0) • rotation a d u -
        (if a = c then (1 : ℝ) else 0) • rotation b d u -
        (if b = d then (1 : ℝ) else 0) • rotation a c u +
        (if a = d then (1 : ℝ) else 0) • rotation b c u
```

- **Notes.** In Lean, `a - b - c + d` is `((a - b) - c) + d`.

### $`[S, L_a] = 0`$ and $`[S, \Omega_{ab}] = 0`$

- **Math.** For $`a, b \in \{1, 2, 3\}`$, $`[S, L_a] = 0`$ and $`[S, \Omega_{ab}] = 0`$ as
  component fields. Hence, for $`u`$ that is $`C^2`$ near $`p`$,
  $`S(L_a u)(p) = L_a(S u)(p)`$ and $`S(\Omega_{ab} u)(p) = \Omega_{ab}(S u)(p)`$, and the same
  identities of functions for $`u \in C^2`$.
- **Hypotheses.** Field identities: none. Operator identities: $`F`$ is a real normed space; $`u`$
  is $`C^2`$ at $`p`$, resp. $`u`$ is $`C^2`$.
- **Lean.** `VectorFieldMethod.Minkowski.lieBracket_scalingField_boostField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L299);
  `VectorFieldMethod.Minkowski.lieBracket_scalingField_rotationField`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L306); `VectorFieldMethod.Minkowski.scaling_boost_comm_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L454);
  `VectorFieldMethod.Minkowski.scaling_boost_comm`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L462); `VectorFieldMethod.Minkowski.scaling_rotation_comm_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L467);
  `VectorFieldMethod.Minkowski.scaling_rotation_comm`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/Commutators.lean#L475)

```lean
theorem lieBracket_scalingField_boostField (a : Fin 3) :
    lieBracket ℝ scalingField (boostField a) = fun _ ↦ 0

theorem lieBracket_scalingField_rotationField (a b : Fin 3) :
    lieBracket ℝ scalingField (rotationField a b) = fun _ ↦ 0

theorem scaling_boost_comm_apply (a : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    scaling (boost a u) p = boost a (scaling u) p

theorem scaling_boost_comm (a : Fin 3) (hu : ContDiff ℝ 2 u) :
    scaling (boost a u) = boost a (scaling u)

theorem scaling_rotation_comm_apply (a b : Fin 3) (hu : ContDiffAt ℝ 2 u p) :
    scaling (rotation a b u) p = rotation a b (scaling u) p

theorem scaling_rotation_comm (a b : Fin 3) (hu : ContDiff ℝ 2 u) :
    scaling (rotation a b u) = rotation a b (scaling u)
```

- **Notes.** $`S`$ is the identity map and $`L_a`$, $`\Omega_{ab}`$ are linear, so
  $`[S, W](p) = W(p) - W(p) = 0`$ for $`W = L_a, \Omega_{ab}`$.

## Main theorems: commutators with the wave and Klein–Gordon operators

### Commutator of $`\Box`$ with a vector field with constant derivative

- **Math.** Let $`V : \mathbb{R}^{1+3} \to \mathbb{R}^{1+3}`$ have the same derivative, a linear
  map $`A`$, at every point (that is, $`V(q) = Aq + V(0)`$), let $`p \in \mathbb{R}^{1+3}`$ and let
  $`u : \mathbb{R}^{1+3} \to F`$ be $`C^3`$ on a neighbourhood of $`p`$. Then
  ```math
  V(\Box u)(p) - \Box(Vu)(p) = -\sum_{\alpha=0}^{3} \sum_{\beta=0}^{3} \eta^{\alpha\beta} \Big( D^2u(p)\big(E_\alpha, [\partial_\beta, V](p)\big) + D^2u(p)\big([\partial_\alpha, V](p), E_\beta\big) \Big),
  ```
  where $`[\partial_\beta, V](p) = A E_\beta`$ is the Lie bracket of component fields.
- **Hypotheses.** $`F`$ is a real normed space; $`V`$ has derivative $`A`$ at every point
  (`∀ q, HasFDerivAt V A q`); $`u`$ is $`C^3`$ at $`p`$ (`ContDiffAt ℝ 3 u p`).
- **Lean.** `VectorFieldMethod.Minkowski.derivAlong_dAlembertian_sub_dAlembertian_derivAlong_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L110)

```lean
theorem derivAlong_dAlembertian_sub_dAlembertian_derivAlong_apply
    {A : Spacetime →L[ℝ] Spacetime} (hV : ∀ q, HasFDerivAt V A q) (hu : ContDiffAt ℝ 3 u p) :
    derivAlong V (□ u) p - □ (derivAlong V u) p =
      -∑ α, ∑ β, η α β • (fderiv ℝ (fderiv ℝ u) p (coordField α 0)
          (lieBracket ℝ (coordField β) V p) +
        fderiv ℝ (fderiv ℝ u) p (lieBracket ℝ (coordField α) V p) (coordField β 0))
```

- **Notes.** `coordField α 0` is $`E_\alpha`$, and `η α β` is $`\eta^{\alpha\beta}`$ (equal to
  $`\eta_{\alpha\beta}`$). The proof follows the commutator method: since $`[\partial_\beta, V]`$
  is constant, $`V(\partial_\beta u) = \partial_\beta(Vu) - Du\,(A E_\beta)`$ on a neighbourhood of
  $`p`$, and applying the first entry of this file to $`\partial_\beta u`$ at $`p`$ gives
  $`V(\partial_\alpha \partial_\beta u)(p) = \partial_\alpha \partial_\beta (Vu)(p) - D^2u(p)(E_\alpha, A E_\beta) - D^2u(p)(A E_\alpha, E_\beta)`$;
  the formula is the sum of these identities with the coefficients $`\eta^{\alpha\beta}`$. The
  hypothesis on $`V`$ holds for the translations ($`A = 0`$) and for $`\Omega_{ab}`$, $`L_a`$,
  $`S`$ ($`A`$ is the field itself, `hasFDerivAt_of_isLinearMap`); the entries below apply the
  formula to these fields, and the "Sanity checks" section of `WaveCommutators.lean` states the
  hypothesis for the boost fields as an `example`.

### $`[\partial_\alpha, \Box] = 0`$

- **Math.** For $`\alpha \in \{0, 1, 2, 3\}`$ and $`u`$ that is $`C^3`$ on a neighbourhood of $`p`$,
  ```math
  \partial_\alpha(\Box u)(p) = \Box(\partial_\alpha u)(p),
  ```
  and $`\partial_\alpha \Box u = \Box \partial_\alpha u`$ on $`\mathbb{R}^{1+3}`$ for $`u \in C^3`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is $`C^3`$ at $`p`$
  (`ContDiffAt ℝ 3 u p`), resp. $`u`$ is $`C^3`$ (`ContDiff ℝ 3 u`).
- **Lean.** `VectorFieldMethod.Minkowski.partialDeriv_dAlembertian_comm_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L192);
  `VectorFieldMethod.Minkowski.partialDeriv_dAlembertian_comm`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L202)

```lean
theorem partialDeriv_dAlembertian_comm_apply (α : Fin 4) (hu : ContDiffAt ℝ 3 u p) :
    ∂[α] (□ u) p = □ (∂[α] u) p

theorem partialDeriv_dAlembertian_comm (α : Fin 4) (hu : ContDiff ℝ 3 u) :
    ∂[α] (□ u) = □ (∂[α] u)
```

- **Notes.** For $`\alpha = 0`$ this is $`\partial_t \Box u = \Box \partial_t u`$ (`∂[0] = ∂ₜ`),
  and for `α = Fin.succ a` it is $`\partial_a \Box u = \Box \partial_a u`$.

### $`[\Omega_{ab}, \Box] = 0`$

- **Math.** For $`a, b \in \{1, 2, 3\}`$ and $`u`$ that is $`C^3`$ on a neighbourhood of $`p`$,
  ```math
  \Omega_{ab}(\Box u)(p) = \Box(\Omega_{ab} u)(p),
  ```
  and $`\Omega_{ab} \Box u = \Box \Omega_{ab} u`$ on $`\mathbb{R}^{1+3}`$ for $`u \in C^3`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is $`C^3`$ at $`p`$, resp. $`u`$ is $`C^3`$.
- **Lean.** `VectorFieldMethod.Minkowski.rotation_dAlembertian_comm_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L207);
  `VectorFieldMethod.Minkowski.rotation_dAlembertian_comm`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L219)

```lean
theorem rotation_dAlembertian_comm_apply (a b : Fin 3) (hu : ContDiffAt ℝ 3 u p) :
    rotation a b (□ u) p = □ (rotation a b u) p

theorem rotation_dAlembertian_comm (a b : Fin 3) (hu : ContDiff ℝ 3 u) :
    rotation a b (□ u) = □ (rotation a b u)
```

### $`[L_a, \Box] = 0`$

- **Math.** For $`a \in \{1, 2, 3\}`$ and $`u`$ that is $`C^3`$ on a neighbourhood of $`p`$,
  ```math
  L_a(\Box u)(p) = \Box(L_a u)(p),
  ```
  and $`L_a \Box u = \Box L_a u`$ on $`\mathbb{R}^{1+3}`$ for $`u \in C^3`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is $`C^3`$ at $`p`$, resp. $`u`$ is $`C^3`$.
- **Lean.** `VectorFieldMethod.Minkowski.boost_dAlembertian_comm_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L224); `VectorFieldMethod.Minkowski.boost_dAlembertian_comm`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L236)

```lean
theorem boost_dAlembertian_comm_apply (a : Fin 3) (hu : ContDiffAt ℝ 3 u p) :
    boost a (□ u) p = □ (boost a u) p

theorem boost_dAlembertian_comm (a : Fin 3) (hu : ContDiff ℝ 3 u) :
    boost a (□ u) = □ (boost a u)
```

### $`[S, \Box] = -2\,\Box`$

- **Math.** For $`u`$ that is $`C^3`$ on a neighbourhood of $`p`$,
  ```math
  S(\Box u)(p) - \Box(S u)(p) = -2\, \Box u(p),
  ```
  and $`S \Box u - \Box S u = -2\, \Box u`$ on $`\mathbb{R}^{1+3}`$ for $`u \in C^3`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is $`C^3`$ at $`p`$, resp. $`u`$ is $`C^3`$.
- **Lean.** `VectorFieldMethod.Minkowski.scaling_dAlembertian_sub_dAlembertian_scaling_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L241);
  `VectorFieldMethod.Minkowski.scaling_dAlembertian_sub_dAlembertian_scaling`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L257)

```lean
theorem scaling_dAlembertian_sub_dAlembertian_scaling_apply (hu : ContDiffAt ℝ 3 u p) :
    scaling (□ u) p - □ (scaling u) p = (-2 : ℝ) • □ u p

theorem scaling_dAlembertian_sub_dAlembertian_scaling (hu : ContDiff ℝ 3 u) :
    scaling (□ u) - □ (scaling u) = (-2 : ℝ) • □ u
```

- **Notes.** `(-2 : ℝ) • □ u` is the function $`-2\,\Box u`$. The sign does not depend on the sign
  convention for $`\Box`$: with LeFloch–Ma's $`\Box = \partial_t^2 - \Delta`$ (which is $`-\Box`$
  here) the identity reads the same. The "Sanity checks" section of `WaveCommutators.lean` checks
  it on $`u = t^2 - r^2`$: from $`\Box(t^2 - r^2) = -8`$ and $`S(t^2 - r^2) = 2(t^2 - r^2)`$, both
  sides equal $`16`$.

### $`[\partial_\alpha, \mathrm{KG}_m] = 0`$, $`[\Omega_{ab}, \mathrm{KG}_m] = 0`$, $`[L_a, \mathrm{KG}_m] = 0`$

- **Math.** Let $`m \in \mathbb{R}`$, $`\mathrm{KG}_m u = \Box u - m^2 u`$, and let $`u`$ be
  $`C^3`$ on a neighbourhood of $`p`$. For $`Z = \partial_\alpha`$
  ($`\alpha \in \{0, 1, 2, 3\}`$), $`Z = \Omega_{ab}`$ and $`Z = L_a`$ ($`a, b \in \{1, 2, 3\}`$),
  ```math
  Z(\mathrm{KG}_m u)(p) = \mathrm{KG}_m(Z u)(p),
  ```
  and $`Z\, \mathrm{KG}_m u = \mathrm{KG}_m Z u`$ on $`\mathbb{R}^{1+3}`$ for $`u \in C^3`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is $`C^3`$ at $`p`$, resp. $`u`$ is $`C^3`$.
- **Lean.** `VectorFieldMethod.Minkowski.partialDeriv_kleinGordon_comm_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L264);
  `VectorFieldMethod.Minkowski.partialDeriv_kleinGordon_comm`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L271); `VectorFieldMethod.Minkowski.rotation_kleinGordon_comm_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L276);
  `VectorFieldMethod.Minkowski.rotation_kleinGordon_comm`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L283); `VectorFieldMethod.Minkowski.boost_kleinGordon_comm_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L288);
  `VectorFieldMethod.Minkowski.boost_kleinGordon_comm`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L295)

```lean
theorem partialDeriv_kleinGordon_comm_apply (α : Fin 4) (m : ℝ) (hu : ContDiffAt ℝ 3 u p) :
    ∂[α] (kleinGordon m u) p = kleinGordon m (∂[α] u) p

theorem partialDeriv_kleinGordon_comm (α : Fin 4) (m : ℝ) (hu : ContDiff ℝ 3 u) :
    ∂[α] (kleinGordon m u) = kleinGordon m (∂[α] u)

theorem rotation_kleinGordon_comm_apply (a b : Fin 3) (m : ℝ) (hu : ContDiffAt ℝ 3 u p) :
    rotation a b (kleinGordon m u) p = kleinGordon m (rotation a b u) p

theorem rotation_kleinGordon_comm (a b : Fin 3) (m : ℝ) (hu : ContDiff ℝ 3 u) :
    rotation a b (kleinGordon m u) = kleinGordon m (rotation a b u)

theorem boost_kleinGordon_comm_apply (a : Fin 3) (m : ℝ) (hu : ContDiffAt ℝ 3 u p) :
    boost a (kleinGordon m u) p = kleinGordon m (boost a u) p

theorem boost_kleinGordon_comm (a : Fin 3) (m : ℝ) (hu : ContDiff ℝ 3 u) :
    boost a (kleinGordon m u) = kleinGordon m (boost a u)
```

- **Notes.** $`[Z, \mathrm{KG}_m]u = [Z, \Box]u - m^2 (Zu - Zu) = [Z, \Box]u`$
  (`derivAlong_kleinGordon_sub_kleinGordon_derivAlong_apply`, for any component field $`V`$ and
  $`u`$ of class $`C^3`$ near $`p`$). The statements hold for LeFloch–Ma's Klein–Gordon operator
  $`-\mathrm{KG}_m`$ as well.

### $`[S, \mathrm{KG}_m] = -2\,\Box`$

- **Math.** Let $`m \in \mathbb{R}`$ and let $`u`$ be $`C^3`$ on a neighbourhood of $`p`$. Then
  ```math
  S(\mathrm{KG}_m u)(p) - \mathrm{KG}_m(S u)(p) = -2\, \Box u(p),
  ```
  and $`S\, \mathrm{KG}_m u - \mathrm{KG}_m S u = -2\, \Box u`$ on $`\mathbb{R}^{1+3}`$ for
  $`u \in C^3`$.
- **Hypotheses.** $`F`$ is a real normed space; $`u`$ is $`C^3`$ at $`p`$, resp. $`u`$ is $`C^3`$.
- **Lean.** `VectorFieldMethod.Minkowski.scaling_kleinGordon_sub_kleinGordon_scaling_apply`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L300);
  `VectorFieldMethod.Minkowski.scaling_kleinGordon_sub_kleinGordon_scaling`, [permalink](https://github.com/Oho1e/VectorFieldMethod/blob/d3ad61dc2447af2599860c695e03b3c37b718008/VectorFieldMethod/Minkowski/WaveCommutators.lean#L306)

```lean
theorem scaling_kleinGordon_sub_kleinGordon_scaling_apply (m : ℝ) (hu : ContDiffAt ℝ 3 u p) :
    scaling (kleinGordon m u) p - kleinGordon m (scaling u) p = (-2 : ℝ) • □ u p

theorem scaling_kleinGordon_sub_kleinGordon_scaling (m : ℝ) (hu : ContDiff ℝ 3 u) :
    scaling (kleinGordon m u) - kleinGordon m (scaling u) = (-2 : ℝ) • □ u
```

- **Notes.** The right-hand side is $`-2\,\Box u`$, not $`-2\,\mathrm{KG}_m u`$: the mass term
  commutes with $`S`$. With LeFloch–Ma's sign convention ($`\Box_{\mathrm{LM}} = -\Box`$,
  $`\mathrm{KG}_{\mathrm{LM}} = -\mathrm{KG}_m`$) the identity reads
  $`[S, \mathrm{KG}_{\mathrm{LM}}]u = -2\,\Box_{\mathrm{LM}} u`$.
