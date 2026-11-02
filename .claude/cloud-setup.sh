#!/usr/bin/env bash
# Setup script for a Claude Code cloud environment working on VectorFieldMethod.
#
# Paste this file into the environment's "Setup script" field (see
# docs/lean-cloud.md). The platform runs it once on a fresh VM and snapshots
# the result; later sessions start from that snapshot. It:
#
#   1. clones this repository (public, branch $BRANCH) into /opt/warm,
#   2. installs elan and the toolchain named by the clone's lean-toolchain,
#   3. puts lean, lake and elan on PATH via wrappers in /usr/local/bin,
#   4. fetches the Lake dependencies (shallow) and the Mathlib olean cache,
#   5. checks that Mathlib is complete (marker .lake/lean-warm-manifest.json)
#      and, if time remains, builds this repository's own modules (Mathlib
#      itself is never compiled),
#
# and logs every step with a timestamp to /opt/warm/SETUP-REPORT.txt.
#
# Properties: safe to run repeatedly (each step skips work already done), never
# fails (always exits 0, so a network hiccup cannot block session start), and
# keeps to a time budget (DEADLINE, default 225 s) well under the platform's
# limit. Every setting below can also be overridden from the environment.

BRANCH="${BRANCH:-main}"
REPO_URL="${REPO_URL:-https://github.com/Oho1e/VectorFieldMethod.git}"
WARM_DIR="${WARM_DIR:-/opt/warm}"
BIN_DIR="${BIN_DIR:-/usr/local/bin}"
DEADLINE="${DEADLINE:-225}"   # seconds after start; later steps are cut short
BUILD="${BUILD:-1}"           # 1: build this repository's modules if time remains
export HOME="${HOME:-/root}"
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"

REPO_DIR="$WARM_DIR/VectorFieldMethod"
REPORT="$WARM_DIR/SETUP-REPORT.txt"
MARKER="$REPO_DIR/.lake/lean-warm-manifest.json"
STAMP="$WARM_DIR/SETUP-STAMP"
START=$(date +%s)
export PATH="$ELAN_HOME/bin:$PATH"
export GIT_TERMINAL_PROMPT=0

mkdir -p "$WARM_DIR" 2>/dev/null
[ -f "$REPORT" ] && mv -f "$REPORT" "$REPORT.prev" 2>/dev/null

elapsed() { echo $(( $(date +%s) - START )); }
remaining() { echo $(( DEADLINE - $(elapsed) )); }
log() {
  local line
  line="[$(date -u +%Y-%m-%dT%H:%M:%SZ) +$(elapsed)s] $*"
  echo "$line"
  echo "$line" >> "$REPORT" 2>/dev/null
}
# run TIMEOUT CMD...: run a command with a time limit, log its outcome and the
# tail of its output, and return its exit status.
run() {
  local limit=$1 out rc t0
  shift
  t0=$(date +%s)
  if [ "$limit" -le 0 ]; then
    log "  skipped (time budget spent): $*"
    return 124
  fi
  out=$(timeout "$limit" "$@" 2>&1)
  rc=$?
  log "  \$ $* -> exit $rc in $(( $(date +%s) - t0 ))s"
  [ -n "$out" ] && printf '%s\n' "$out" | tr '\r' '\n' | grep -v '^\s*$' | tail -n 5 \
    | sed 's/^/      /' | tee -a "$REPORT" 2>/dev/null
  return $rc
}

# HTTP status that cache.mathlib.org gives for a file it cannot have: 404 means
# the host answers; 403 or 000 means the network policy (or the network) refuses.
probe_cache_host() {
  curl -s -o /dev/null -w '%{http_code}' --max-time 10 \
    "https://cache.mathlib.org/mathlib4-master/f/0000000000000000.ltar" 2>/dev/null || true
}

step_repo() {
  log "STEP repo: $REPO_URL (branch $BRANCH) -> $REPO_DIR"
  if [ -d "$REPO_DIR/.git" ]; then
    run 60 git -C "$REPO_DIR" remote set-url origin "$REPO_URL"
    run 90 git -C "$REPO_DIR" fetch --depth 1 origin "$BRANCH" &&
      run 30 git -C "$REPO_DIR" reset --hard FETCH_HEAD
  else
    rm -rf "$REPO_DIR"
    run 120 git clone --depth 1 --branch "$BRANCH" --single-branch "$REPO_URL" "$REPO_DIR"
  fi
  if [ -f "$REPO_DIR/lean-toolchain" ]; then
    log "  commit $(git -C "$REPO_DIR" rev-parse HEAD 2>/dev/null), toolchain $(cat "$REPO_DIR/lean-toolchain")"
    return 0
  fi
  log "  ERROR: no lean-toolchain in $REPO_DIR; later steps are skipped"
  return 1
}

step_elan() {
  log "STEP elan: ELAN_HOME=$ELAN_HOME"
  if [ -x "$ELAN_HOME/bin/elan" ]; then
    log "  already installed: $("$ELAN_HOME/bin/elan" --version 2>&1)"
    return 0
  fi
  local tmp
  tmp=$(mktemp -d)
  if run 30 curl -sSfL -o "$tmp/elan-init.sh" \
      https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh; then
    run 60 bash "$tmp/elan-init.sh" -y --default-toolchain none --no-modify-path
  fi
  if [ ! -x "$ELAN_HOME/bin/elan" ]; then
    log "  falling back to the elan release tarball"
    run 60 curl -sSfL -o "$tmp/elan.tar.gz" \
      "https://github.com/leanprover/elan/releases/latest/download/elan-$(uname -m)-unknown-linux-gnu.tar.gz" &&
      run 30 tar -xzf "$tmp/elan.tar.gz" -C "$tmp" &&
      run 60 "$tmp/elan-init" -y --default-toolchain none --no-modify-path
  fi
  rm -rf "$tmp"
  [ -x "$ELAN_HOME/bin/elan" ] && log "  installed: $("$ELAN_HOME/bin/elan" --version 2>&1)"
  [ -x "$ELAN_HOME/bin/elan" ]
}

step_toolchain() {
  local tc ver dir tmp
  tc=$(tr -d '[:space:]' < "$REPO_DIR/lean-toolchain")
  log "STEP toolchain: $tc"
  run "$(remaining)" elan toolchain install "$tc"
  # Fallback: unpack the release tarball from GitHub where elan expects it.
  dir="$ELAN_HOME/toolchains/$(printf '%s' "$tc" | sed 's|/|--|g; s|:|---|g')"
  if [ ! -x "$dir/bin/lean" ] && [[ "$tc" == leanprover/lean4:v* ]]; then
    ver=${tc#leanprover/lean4:v}
    log "  falling back to the GitHub release tarball of Lean $ver"
    command -v zstd >/dev/null || run 90 bash -c 'apt-get install -y zstd || (apt-get update && apt-get install -y zstd)'
    tmp=$(mktemp -d)
    run "$(remaining)" curl -sSfL -o "$tmp/lean.tar.zst" \
      "https://github.com/leanprover/lean4/releases/download/v$ver/lean-$ver-linux.tar.zst" &&
      run 120 tar --use-compress-program=unzstd -xf "$tmp/lean.tar.zst" -C "$tmp" &&
      rm -rf "$dir" && mkdir -p "$(dirname "$dir")" && mv "$tmp/lean-$ver-linux" "$dir"
    rm -rf "$tmp"
  fi
  run 30 elan default "$tc"
  [ -x "$dir/bin/lean" ] && log "  $("$dir/bin/lean" --version 2>&1)"
  [ -x "$dir/bin/lean" ]
}

step_path() {
  log "STEP path: wrappers for lean, lake, elan in $BIN_DIR"
  mkdir -p "$BIN_DIR"
  local tool
  for tool in lean lake elan; do
    rm -f "$BIN_DIR/$tool"
    printf '#!/bin/sh\nexport ELAN_HOME="${ELAN_HOME:-%s}"\nexec "%s/bin/%s" "$@"\n' \
      "$ELAN_HOME" "$ELAN_HOME" "$tool" > "$BIN_DIR/$tool"
    chmod 755 "$BIN_DIR/$tool"
  done
  log "  $("$BIN_DIR/lake" --version 2>&1)"
}

# Clone every dependency of lake-manifest.json at its pinned commit, shallowly
# and in parallel. Lake accepts these clones as they are (right URL, right
# commit), which saves the full-history clone of Mathlib it would otherwise do.
step_deps() {
  log "STEP deps: shallow clones of the packages pinned in lake-manifest.json"
  local pkgdir="$REPO_DIR/.lake/packages" list name url rev dir pids=()
  list=$(python3 -c '
import json, sys
m = json.load(open(sys.argv[1]))
for p in m.get("packages", []):
    if p.get("type") == "git":
        print(p["name"], p["url"], p["rev"])
' "$REPO_DIR/lake-manifest.json" 2>/dev/null) || { log "  python3 unavailable; Lake will clone"; return 0; }
  mkdir -p "$pkgdir"
  while read -r name url rev; do
    [ -n "$name" ] || continue
    dir="$pkgdir/$name"
    if [ "$(git -C "$dir" rev-parse HEAD 2>/dev/null)" = "$rev" ]; then
      log "  $name: already at ${rev:0:12}"
      continue
    fi
    (
      rm -rf "$dir" && git init -q "$dir" &&
        git -C "$dir" remote add origin "$url" &&
        timeout "$(remaining)" git -C "$dir" fetch -q --depth 1 origin "$rev" &&
        git -C "$dir" checkout -q --detach FETCH_HEAD
    ) >/dev/null 2>&1 &
    pids+=("$!:$name:$rev")
  done <<< "$list"
  local entry
  for entry in "${pids[@]}"; do
    wait "${entry%%:*}"
    name=${entry#*:}; name=${name%%:*}
    if [ "$(git -C "$pkgdir/$name" rev-parse HEAD 2>/dev/null)" = "${entry##*:}" ]; then
      log "  $name: cloned at ${entry##*:}"
    else
      log "  $name: shallow clone FAILED (Lake will clone it)"
      rm -rf "${pkgdir:?}/$name"
    fi
  done
}

mathlib_oleans() {
  find "$REPO_DIR/.lake/packages/mathlib/.lake/build/lib" -name '*.olean' 2>/dev/null | wc -l
}

step_cache() {
  local probe order host
  probe=$(probe_cache_host)
  CACHE_PROBE=$probe
  rm -f "$MARKER"
  log "STEP cache: cache.mathlib.org probe answered ${probe:-nothing} (404 = reachable)"
  if [ "$probe" = "404" ]; then order="default legacy"; else order="legacy default"; fi
  for host in $order; do
    log "  trying the $host cache host"
    if [ "$host" = legacy ]; then
      (cd "$REPO_DIR" && MATHLIB_CACHE_DEBUG_USE_LEGACY=1 run "$(remaining)" lake exe cache get)
    else
      (cd "$REPO_DIR" && run "$(remaining)" lake exe cache get)
    fi && { CACHE_HOST=$host; break; }
  done
  log "  Mathlib oleans in place: $(mathlib_oleans)"
}

# Mark the warm tree complete only once Lake confirms that every Mathlib module
# is up to date: `--no-build` fails instead of building anything. The marker is
# a copy of the manifest; the SessionStart hook links to the warm tree only if
# it equals the session checkout's manifest.
step_verify() {
  log "STEP verify: Mathlib complete without compiling anything"
  if (cd "$REPO_DIR" && run "$(remaining)" lake build --no-build Mathlib); then
    cp "$REPO_DIR/lake-manifest.json" "$MARKER" && MATHLIB_OK=yes
    log "  complete; wrote $MARKER"
  else
    log "  Mathlib oleans incomplete; the warm tree is not marked complete"
  fi
}

step_build() {
  log "STEP build: this repository's modules (never Mathlib)"
  if [ "$BUILD" != 1 ]; then log "  disabled (BUILD=$BUILD)"; return 0; fi
  if [ "${MATHLIB_OK:-}" != yes ]; then log "  skipped: Mathlib incomplete (building would compile it)"; return 0; fi
  (cd "$REPO_DIR" && run "$(remaining)" lake build) && BUILT=yes
}

write_stamp() {
  {
    echo "date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "branch: $BRANCH"
    echo "commit: $(git -C "$REPO_DIR" rev-parse HEAD 2>/dev/null)"
    echo "toolchain: $(cat "$REPO_DIR/lean-toolchain" 2>/dev/null)"
    echo "manifest-sha256: $(sha256sum "$REPO_DIR/lake-manifest.json" 2>/dev/null | cut -d' ' -f1)"
    echo "default-cache-probe: ${CACHE_PROBE:-}"
    echo "cache-host-used: ${CACHE_HOST:-none}"
    echo "mathlib-oleans: $(mathlib_oleans)"
    echo "mathlib-complete: ${MATHLIB_OK:-no}"
    echo "project-built: ${BUILT:-no}"
    echo "script-sha256: $(sha256sum "$0" 2>/dev/null | cut -d' ' -f1)"
    echo "seconds: $(elapsed)"
  } > "$STAMP" 2>/dev/null
}

main() {
  log "cloud-setup.sh start: branch=$BRANCH warm=$WARM_DIR elan=$ELAN_HOME bin=$BIN_DIR deadline=${DEADLINE}s"
  if command -v flock >/dev/null; then
    exec 9> "$WARM_DIR/.setup.lock"
    flock -w 30 9 || { log "another run holds $WARM_DIR/.setup.lock; giving up"; return 0; }
  fi
  step_repo || return 0
  step_elan || { log "ERROR: elan not installed; stopping"; return 0; }
  step_toolchain || log "ERROR: toolchain not installed; continuing anyway"
  step_path
  step_deps
  step_cache
  step_verify
  step_build
}

trap 'write_stamp; log "cloud-setup.sh done in $(elapsed)s (always exits 0)"; exit 0' EXIT
main
