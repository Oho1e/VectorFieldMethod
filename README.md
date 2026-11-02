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

Early stage: only the project infrastructure exists (Lake project, CI, cloud
setup). The library contains a placeholder module and no mathematics yet.

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
