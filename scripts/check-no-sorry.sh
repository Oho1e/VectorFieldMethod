#!/usr/bin/env bash
# Fail if any Lean file of the library mentions `sorry` as a whole word.
# Checks VectorFieldMethod.lean and every .lean file under VectorFieldMethod/.
# Comments are not exempt: rephrase a comment rather than write the word.
set -euo pipefail
cd "$(dirname "$0")/.."

files=(VectorFieldMethod.lean)
while IFS= read -r -d '' f; do files+=("$f"); done \
  < <(find VectorFieldMethod -name '*.lean' -print0)

if grep -nwH 'sorry' "${files[@]}"; then
  echo "error: 'sorry' found in the files listed above." >&2
  exit 1
fi
echo "No sorry in ${#files[@]} Lean file(s)."
