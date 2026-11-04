# VectorFieldMethod

Lean 4 formalization of the vector field method for hyperbolic PDEs.

## Goal

The vector field method (Klainerman) proves decay and global existence results
for wave-type equations using commuting vector fields, energy estimates and
weighted Sobolev (Klainerman–Sobolev) inequalities. This project aims to build
the foundational layer of that method in Lean 4 on top of
[Mathlib](https://github.com/leanprover-community/mathlib4), with every
unproved ingredient stated as an explicit hypothesis.

## Status

The library currently goes from the coordinate layer of Minkowski spacetime
`ℝ^{1+3}` up to the hyperboloidal energy estimate and the Klainerman–Sobolev
inequality on hyperboloids for the Klein–Gordon field. By layer (the mathematical statements of the main
definitions and theorems, next to their verbatim Lean statements, are in
[docs/statements/](docs/statements/)):

- **Minkowski coordinate layer** (`VectorFieldMethod/Minkowski/`: `Spacetime`,
  `Derivative`, `WaveOperator`, `VectorFields`, `Computations`): coordinates and
  metric, coordinate derivatives, the wave and Klein–Gordon operators, and the
  rotation, boost and scaling vector fields, with their basic lemmas.
  Statements: [minkowski.md](docs/statements/minkowski.md); design notes:
  [docs/minkowski-layer.md](docs/minkowski-layer.md).
- **Commutators** (`Minkowski/Commutators.lean`, `Minkowski/WaveCommutators.lean`):
  the commutator of two of the vector fields is the Lie bracket of their
  component fields, with all brackets computed; the translations, rotations and
  boosts commute with `□` and the Klein–Gordon operator, and `[S, □] = -2 □`.
  Statements: [commutators.md](docs/statements/commutators.md).
- **Energy-momentum tensor** (`Minkowski/EnergyMomentum.lean`): the
  energy-momentum tensor and the energy current of the Klein–Gordon field, and
  the divergence identity `∂_α P^α = -⟪□u - m² u, ∂_t u⟫`.
  Statements: [energy-momentum.md](docs/statements/energy-momentum.md).
- **Divergence theorems** (`VectorFieldMethod/ForMathlib/`): the divergence
  theorem below the graph of a `C¹` function, between two graphs (also for
  locally defined fields) and between two hyperboloids.
  Statements: [divergence.md](docs/statements/divergence.md).
- **Hyperboloidal energy identity** (`Minkowski/HyperboloidalEnergy.lean`,
  `Minkowski/HyperboloidalEnergyIdentity.lean`): the semi-hyperboloidal frame,
  the hyperboloidal energy, and the energy identity between two hyperboloids for
  a field that is `C²` near the region inside the cone `{|x| ≤ t - 1}`.
  Statements: [hyperboloidal-energy.md](docs/statements/hyperboloidal-energy.md).
- **Hyperboloidal energy estimate** (`Minkowski/HyperboloidalEnergyEstimate.lean`,
  `Analysis/SqrtGronwall.lean`): the foliation of the region between two
  hyperboloids, a square-root Grönwall inequality, and the energy estimate
  `E_m(s, u)^{1/2} ≤ E_m(s₀, u)^{1/2} + ∫_{s₀}^{s} ‖□u - m² u‖_{L²_f(H_{s'})} ds'`
  (flat `L²` norms on the hyperboloids).
  Statements: [hyperboloidal-energy-estimate.md](docs/statements/hyperboloidal-energy-estimate.md).
- **Sobolev inequalities on `ℝ³`** (`Analysis/LocalSobolev.lean`,
  `Analysis/HyperboloidalSobolev.lean`): the local Sobolev bound `H² ⊂ L^∞` on
  balls of `ℝ³` and the hyperboloidal (weighted) Sobolev inequality on `ℝ³`.
  Statements: [euclidean-sobolev.md](docs/statements/euclidean-sobolev.md);
  background: [docs/hyperboloidal-sobolev.md](docs/hyperboloidal-sobolev.md).
- **Klainerman–Sobolev inequality on hyperboloids**
  (`Minkowski/KlainermanSobolev.lean`): restriction to a hyperboloid, its
  relation with the boosts, and `sup_{H_s} t^{3/2} |u| ≤ C ∑_{|J| ≤ 2} ‖L^J u‖_{L²_f(H_s)}`.
  Statements: [klainerman-sobolev.md](docs/statements/klainerman-sobolev.md).

## Building

Requires [elan](https://github.com/leanprover/elan); the toolchain version is
read from `lean-toolchain` (Lean `v4.35.0`, Mathlib `v4.35.0`).

```bash
git clone https://github.com/Oho1e/VectorFieldMethod.git
cd VectorFieldMethod
lake exe cache get   # download prebuilt Mathlib (do not build Mathlib from source)
lake build
```

CI (`.github/workflows/build.yml`) builds every push and pull request with
warnings as errors, and fails if any file of the library contains `sorry`.

For Claude Code cloud sessions, see [docs/lean-cloud.md](docs/lean-cloud.md).
Contributor rules are in [CLAUDE.md](CLAUDE.md).

## License

Apache 2.0, see [LICENSE](LICENSE).
