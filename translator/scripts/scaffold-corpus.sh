#!/usr/bin/env bash
# File: translator/scripts/scaffold-corpus.sh
#
# Print the profile U scaffold of every corpus entry's declaration, read
# from corpus/manifest.json, and have Agda scope-check it: the acceptance
# criterion of issue M2-3 ("every corpus entry's kernel term prints and
# re-parses").  Run from translator/ inside the Nix shell, after
# `make lean-cache`, since most entries import Mathlib; `make
# scaffold-corpus` does both steps' second half.  Name entry ids as
# arguments to check only those.  One row per entry: id, constants,
# scaffold bytes, seconds to print, seconds to scope-check, and the
# result.  Exits 1 if any entry fails to print or to scope-check.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
lake_cmd="${LAKE:-lake}"
agda_cmd="${AGDA:-agda}"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

"$lake_cmd" build lean2agda > /dev/null
entries=$(python3 -c '
import json, sys
wanted = set(sys.argv[1:])
for e in json.load(open("../corpus/manifest.json")):
    if not wanted or e["id"] in wanted:
        print(e["id"], e["lean_module"], e["lean_name"])' "$@")

# Seconds between two `date +%s%N` readings, to a tenth.
seconds() { local tenths=$(( ($2 - $1) / 100000000 )); printf '%d.%d' $((tenths / 10)) $((tenths % 10)); }

failed=0
printf '| id | constants | bytes | print s | scope s | result |\n| --- | --- | --- | --- | --- | --- |\n'
while read -r id module name; do
  out="$scratch/$id"
  start=$(date +%s%N)
  if ! "$lake_cmd" exe lean2agda --out "$out" "$module" -- "$name" > "$scratch/$id.listing" 2> "$scratch/$id.err"; then
    printf '| %s | | | | | print failed: %s |\n' "$id" "$(head -c 200 "$scratch/$id.err" | tr '\n' ' ')"
    failed=1
    continue
  fi
  printed=$(date +%s%N)
  file=$(find "$out" -name '*.agda')
  if (cd "$out" && "$agda_cmd" --only-scope-checking "${file#"$out/"}" > "$scratch/$id.scope" 2>&1); then
    result=pass
  else
    result="scope-check failed: $(grep -m1 'error' "$scratch/$id.scope" | sed 's/.*error: //')"
    failed=1
  fi
  done_at=$(date +%s%N)
  printf '| %s | %s | %s | %s | %s | %s |\n' "$id" "$(grep -vc '^#' "$scratch/$id.listing")" \
    "$(wc -c < "$file")" "$(seconds "$start" "$printed")" "$(seconds "$printed" "$done_at")" "$result"
done <<< "$entries"
exit "$failed"
