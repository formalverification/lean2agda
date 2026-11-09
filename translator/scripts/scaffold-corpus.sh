#!/usr/bin/env bash
# File: translator/scripts/scaffold-corpus.sh
#
# Print the profile U scaffold of every corpus entry's declaration, read
# from corpus/manifest.json, as a tree of modules (issue M2-8), and run
# the refusal loop over it module by module (agda_check.py --refusals):
# the acceptance criterion of issue M2-3 ("every corpus entry's kernel
# term prints and re-parses"), since Agda parses and scope-checks a module
# of a tree only once the modules it imports type-check.  Run from
# translator/ inside the Nix shell, after `make lean-cache`, since most
# entries import Mathlib; `make scaffold-corpus` does both steps' second
# half.  Name entry ids as arguments to check only those; JOBS sets the
# loop's parallelism.  One row per entry: id, constants, modules, scaffold
# bytes, seconds to print, seconds for the loop, and the summed count of
# declarations that checked.  Exits 1 if any entry fails to print or the
# loop cannot place an error of Agda's.
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
printf '| id | constants | modules | bytes | print s | check s | result |\n| --- | --- | --- | --- | --- | --- | --- |\n'
while read -r id module name; do
  out="$scratch/$id"
  start=$(date +%s%N)
  if ! "$lake_cmd" exe lean2agda --out "$out" "$module" -- "$name" > "$scratch/$id.listing" 2> "$scratch/$id.err"; then
    printf '| %s | | | | | | print failed: %s |\n' "$id" "$(head -c 200 "$scratch/$id.err" | tr '\n' ' ')"
    failed=1
    continue
  fi
  printed=$(date +%s%N)
  if python3 ../scripts/python/agda_check.py --refusals --agda "$agda_cmd" -j "${JOBS:-4}" "$out" \
      > "$scratch/$id.check" 2>&1; then
    result=$(head -n 1 "$scratch/$id.check")
  else
    result="check failed: $(grep -m1 'agda_check:' "$scratch/$id.check" | head -c 200)"
    failed=1
  fi
  done_at=$(date +%s%N)
  modules=$(find "$out" -name '*.agda' | wc -l)
  bytes=$(find "$out" -name '*.agda' -exec cat {} + | wc -c)
  printf '| %s | %s | %s | %s | %s | %s | %s |\n' "$id" "$(grep -vc '^#' "$scratch/$id.listing")" \
    "$modules" "$bytes" "$(seconds "$start" "$printed")" "$(seconds "$printed" "$done_at")" "$result"
done <<< "$entries"
exit "$failed"
