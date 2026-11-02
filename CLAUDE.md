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
lake build VectorFieldMethod.Placeholder      # one module and its imports
lake env lean VectorFieldMethod/Placeholder.lean
```

The first form uses Lake's build cache; the second elaborates the file directly
(its imports must already be built). For quick experiments, put a scratch file
outside `VectorFieldMethod/` (e.g. `Scratch.lean`, not committed) and run
`lake env lean Scratch.lean`.

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

TBD.
