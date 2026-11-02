# Lean 4 + Mathlib in Claude Code cloud sessions

Cloud sessions start in a fresh VM whose default network policy may not reach
the Lean release server or the Mathlib olean cache, and in which compiling
Mathlib from source is not an option. Two pieces fix this; the design follows
[vidick/MIPRE-formalization](https://github.com/vidick/MIPRE-formalization/blob/main/docs/lean-cloud.md).

## The setup script: `.claude/cloud-setup.sh`

A cloud environment runs its setup script once and snapshots the VM; later
sessions start from the snapshot. Paste `.claude/cloud-setup.sh` into the
environment's **Setup script** field. It:

| Step | Result |
| --- | --- |
| clone (branch `BRANCH`, default `main`) | `/opt/warm/VectorFieldMethod` |
| elan | `$HOME/.elan` |
| toolchain from `lean-toolchain` | via elan, falling back to the GitHub release tarball |
| `lean`, `lake`, `elan` | wrappers in `/usr/local/bin` |
| Lake dependencies | shallow clones at the commits in `lake-manifest.json` |
| Mathlib oleans | `lake exe cache get` (legacy Azure host first if `cache.mathlib.org` is refused) |
| verification | `lake build --no-build Mathlib`; on success writes `.lake/lean-warm-manifest.json` |
| project modules | `lake build`, only if Mathlib verified and time remains |

Each step is logged with a timestamp to `/opt/warm/SETUP-REPORT.txt` (read it
first when something is missing); `/opt/warm/SETUP-STAMP` summarizes the run
(commit, toolchain, manifest hash, cache host used, whether Mathlib is
complete). The script is idempotent, keeps to a time budget (`DEADLINE`,
default 225 s), never compiles Mathlib, and always exits 0. Variables at the top
(`BRANCH`, `REPO_URL`, `WARM_DIR`, `BIN_DIR`, `DEADLINE`, `BUILD`) can be
edited in the pasted copy or set in the environment.

Measured on 2026-11-02 (4 vCPU VM, Lean/Mathlib v4.35.0, `cache.mathlib.org`
refused so the legacy host was used): two runs from clean directories took
131 s and 150 s (toolchain 36–49 s, dependency clones about 11 s, Mathlib cache
64–77 s); a third run, with elan already present but a slow cache download
(155 s), took 219 s. A rerun on a complete tree takes about 15 s. The warm tree
takes about 7 GB of disk.

## The SessionStart hook: `.claude/hooks/lean-warm.sh`

Registered in `.claude/settings.json`; does nothing unless
`CLAUDE_CODE_REMOTE=true`. At every session start it compares the checkout's
`lake-manifest.json` with `/opt/warm/VectorFieldMethod/.lake/lean-warm-manifest.json`
(and `lean-toolchain` with the warm clone's):

- **equal**: `.lake` in the checkout becomes a symlink to the warm `.lake`, so
  `lake build` only builds this repository's changed modules;
- **different** (the Mathlib pin moved since the snapshot): the warm tree is
  left alone, and `.claude/hooks/lean-cache-get.sh` runs in the background
  (shallow dependency clones, then `lake exe cache get`), logging to
  `/tmp/lean-warm-cache-get.log`. Wait for it to finish before `lake build`.

It prints one `lean-warm:` line, plus notes, e.g. when `cache.mathlib.org` is
refused by the network policy.

## One-time configuration on claude.ai

1. In claude.ai/code, open the environment settings (cloud icon above the
   message box, then the gear of the environment, or **Add cloud environment**).
2. **Network access**: Custom, keep the default package-manager list, and add

   ```text
   cache.mathlib.org
   lakecache.blob.core.windows.net
   releases.lean-lang.org
   lean-lang.org
   reservoir.lean-lang.org
   ```

   `cache.mathlib.org` is Mathlib's cache host since v4.35; the legacy
   `lakecache.blob.core.windows.net` still serves the same files and is the
   fallback (`MATHLIB_CACHE_DEBUG_USE_LEGACY=1`), but Mathlib intends to retire
   it. GitHub hosts need nothing: they go through a separate proxy.
3. **Setup script**: paste `.claude/cloud-setup.sh`, setting `BRANCH` if a
   feature branch pins a different toolchain or Mathlib than `main`.
4. Save. After a toolchain or Mathlib bump, re-save the setup script (any edit)
   so the snapshot is rebuilt.

## Rules in a cloud session

Never run `lake clean` (`.lake` is a symlink into the shared warm tree), never
`lake update` unless asked, and never `lake build` while Mathlib is
incomplete. See `CLAUDE.md`.
