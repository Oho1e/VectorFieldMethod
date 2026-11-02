#!/usr/bin/env bash
# Background helper of lean-warm.sh: make the checkout's own .lake complete
# without compiling anything. Usage: lean-cache-get.sh PROJECT_DIR LEGACY_FIRST
#
# 1. Clone each dependency pinned in lake-manifest.json shallowly at its
#    commit (Lake accepts such clones and skips its full-history clone).
# 2. Run `lake exe cache get`, trying the legacy Azure cache host first when
#    LEGACY_FIRST=1 (cache.mathlib.org refused) and the default host otherwise.
# 3. On success, record the manifest in .lake/lean-warm-manifest.json.

cd "$1" || exit 0
legacy_first="${2:-1}"
pkgdir=.lake/packages
mkdir -p "$pkgdir"

python3 -c '
import json
for p in json.load(open("lake-manifest.json")).get("packages", []):
    if p.get("type") == "git":
        print(p["name"], p["url"], p["rev"])
' 2>/dev/null | while read -r name url rev; do
  dir="$pkgdir/$name"
  [ "$(git -C "$dir" rev-parse HEAD 2>/dev/null)" = "$rev" ] && continue
  # Leave an existing clone to Lake: it fetches the new commit itself.
  [ -e "$dir" ] && continue
  echo "lean-warm: shallow clone of $name at $rev"
  ( git init -q "$dir" && git -C "$dir" remote add origin "$url" &&
      git -C "$dir" fetch -q --depth 1 origin "$rev" &&
      git -C "$dir" checkout -q --detach FETCH_HEAD ) || rm -rf "$dir"
done

if [ "$legacy_first" = 1 ]; then
  MATHLIB_CACHE_DEBUG_USE_LEGACY=1 lake exe cache get || lake exe cache get
else
  lake exe cache get || MATHLIB_CACHE_DEBUG_USE_LEGACY=1 lake exe cache get
fi
rc=$?
[ "$rc" = 0 ] && cp lake-manifest.json .lake/lean-warm-manifest.json
echo "lean-warm: cache get finished with exit $rc"
exit 0
