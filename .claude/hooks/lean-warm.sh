#!/usr/bin/env bash
# SessionStart hook: reuse the warm Lean tree that .claude/cloud-setup.sh built
# under /opt/warm, so that a cloud session can run `lake build` at once.
#
# Runs only in Claude Code cloud sessions (CLAUDE_CODE_REMOTE=true).
#
# * If the checkout's lake-manifest.json and lean-toolchain are identical to
#   the warm clone's, the checkout's .lake becomes a symlink to the warm .lake
#   (Mathlib oleans included), so nothing is downloaded or compiled.
# * Otherwise (the Mathlib pin moved since the snapshot was built), the warm
#   tree is not touched and `lake exe cache get` runs in the background in the
#   checkout; its log path is printed.
#
# Fast, idempotent (also runs on resume/clear/compact) and always exits 0.
# Prints one `lean-warm:` line, which the session sees, plus notes if needed.

[ "${CLAUDE_CODE_REMOTE:-}" = "true" ] || exit 0
trap 'exit 0' EXIT

PROJ="${CLAUDE_PROJECT_DIR:-$(pwd)}"
WARM_DIR="${WARM_DIR:-/opt/warm}"
WARM_REPO="$WARM_DIR/VectorFieldMethod"
LOG="${TMPDIR:-/tmp}/lean-warm-cache-get.log"
PIDFILE="${TMPDIR:-/tmp}/lean-warm-cache-get.pid"
MARKER=".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"

say() { echo "lean-warm: $*"; }
note() { echo "lean-warm note: $*"; }

cd "$PROJ" 2>/dev/null || { say "cannot enter $PROJ"; exit 0; }
[ -f lakefile.toml ] || exit 0

if ! command -v lake >/dev/null 2>&1; then
  say "lake is not on PATH: the environment's setup script (.claude/cloud-setup.sh) has not run. See docs/lean-cloud.md."
  exit 0
fi

# Mirror the setup script's choice of Mathlib cache host: the legacy Azure host
# first unless cache.mathlib.org answers (404 for a file it cannot have).
cache_get_in_background() {
  if [ -f "$PIDFILE" ] && kill -0 "$(cat "$PIDFILE" 2>/dev/null)" 2>/dev/null; then
    say "a 'lake exe cache get' is already running (log: $LOG)"
    return
  fi
  local probe legacy_first=1
  probe=$(curl -s -o /dev/null -w '%{http_code}' --max-time 5 \
    "https://cache.mathlib.org/mathlib4-master/f/0000000000000000.ltar" 2>/dev/null)
  [ "$probe" = "404" ] && legacy_first=0
  nohup setsid bash "$(dirname "$0")/lean-cache-get.sh" "$PROJ" "$legacy_first" \
    > "$LOG" 2>&1 < /dev/null &
  echo "$!" > "$PIDFILE"
  say "started 'lake exe cache get' in the background (log: $LOG); wait for it before 'lake build', which would otherwise compile Mathlib"
  [ "$probe" = "404" ] || note "cache.mathlib.org is refused (HTTP ${probe:-none}); using the legacy cache host. Allow cache.mathlib.org in the environment's network settings."
}

consistent=0
if [ -f "$WARM_REPO/lake-manifest.json" ] && [ -f "$WARM_REPO/$MARKER" ] &&
   cmp -s lake-manifest.json "$WARM_REPO/lake-manifest.json" &&
   cmp -s lean-toolchain "$WARM_REPO/lean-toolchain"; then
  consistent=1
fi

if [ -L .lake ]; then
  if [ "$consistent" = 1 ] && [ "$(readlink .lake)" = "$WARM_REPO/.lake" ]; then
    say "$(lean --version 2>/dev/null | head -n1); .lake already linked to the warm tree"
    exit 0
  fi
  # A stale link (the pin moved): drop the link only, never the warm tree.
  rm -f .lake
fi

if [ "$consistent" = 1 ] && [ ! -e .lake ]; then
  ln -s "$WARM_REPO/.lake" .lake
  say "$(lean --version 2>/dev/null | head -n1); .lake linked to $WARM_REPO/.lake (Mathlib oleans ready)"
  exit 0
fi

if [ -f "$MARKER" ] && cmp -s lake-manifest.json .lake/lean-warm-manifest.json; then
  say "$(lean --version 2>/dev/null | head -n1); the checkout's own .lake has the Mathlib oleans for this manifest"
  exit 0
fi

if [ ! -d "$WARM_REPO" ]; then
  note "no warm tree at $WARM_REPO (setup script not run, or an older snapshot)"
elif [ "$consistent" = 0 ]; then
  note "lake-manifest.json or lean-toolchain differs from $WARM_REPO; not reusing the warm tree"
fi
cache_get_in_background
