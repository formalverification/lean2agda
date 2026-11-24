#!/usr/bin/env bash
# File: translator/scripts/goldens.sh
#
# The golden trees of issue M2-9 (docs/performance.md): for each line of
# tests/goldens.txt, or for the names given, translate the closure into a
# tree of modules, run the refusal loop over it (agda_check.py
# --refusals), check the loop's final state fresh (agda_check.py
# --fresh), and compare the golden directory this makes with
# tests/expected/scaffolds/NAME/ by `diff -r`.  The golden holds the
# loop's listings, the library file, refusals.txt when the translator
# refuses anything, and either the modules (form `tree`) or modules.txt,
# each module's SHA-256 digest, bytes and path (form `digest`).  Then
# scripts/python/refusal_report.py prints the tables and fails unless
# every tree passes: its final state checks and every refusal is
# classified by tests/refusal-classes.txt.
#
# Run from anywhere inside the Nix shell, after `make lean-cache`, since
# most closures import Mathlib; `make goldens` runs it.  Options, as
# follows:
#
#   --update        write each golden directory instead of comparing
#   --results DIR   keep each tree's work under DIR/NAME (the emitted
#                   tree, the listings, loop.txt, final.json,
#                   translate-seconds), and the tables in DIR/report.md
#
# JOBS sets each check's Agda processes (default 4).  The translator runs
# from a copy of its binary, so that a rebuild during a run cannot change
# it.  Exits 1 if a golden differs, a check fails, or the report fails.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
lake_cmd="${LAKE:-lake}"
agda_cmd="${AGDA:-agda}"
jobs="${JOBS:-4}"
update=
results=
while [[ $# -gt 0 ]]; do
  case "$1" in
    --update) update=1; shift ;;
    --results) results="$2"; shift 2 ;;
    --) shift; break ;;
    -*) echo "goldens.sh: unknown option $1" >&2; exit 2 ;;
    *) break ;;
  esac
done

# Every name asked for must be a golden, checked before anything runs.
listed=$(awk '!/^#/ && NF { print $1 }' tests/goldens.txt)
for wanted in "$@"; do
  if ! grep -qxF -- "$wanted" <<< "$listed"; then
    echo "goldens.sh: no golden named $wanted in tests/goldens.txt" >&2
    exit 2
  fi
done

scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
work="${results:-$scratch/results}"
mkdir -p "$work"
work=$(cd "$work" && pwd)

"$lake_cmd" build lean2agda > /dev/null
cp .lake/build/bin/lean2agda "$scratch/lean2agda"

# Seconds between two `date +%s%N` readings, to a tenth.
seconds() { local tenths=$(( ($2 - $1) / 100000000 )); printf '%d.%d' $((tenths / 10)) $((tenths % 10)); }

# The digest form's manifest: a line per module, sorted by path.
manifest() {
  (cd "$1" && find . -name '*.agda' -not -path './_build/*' | LC_ALL=C sort \
     | while read -r f; do printf '%s  %s  %s\n' "$(sha256sum < "$f" | cut -c1-64)" "$(wc -c < "$f")" "${f#./}"; done)
}

status=0
names=()
# The list is read on descriptor 3, so that no command inside the loop
# can read the rest of it from standard input.
while read -r name form args <&3; do
  [[ -z "$name" || "$name" == \#* ]] && continue
  if [[ $# -gt 0 ]] && ! printf '%s\n' "$@" | grep -qxF -- "$name"; then continue; fi
  names+=("$name")
  out="$work/$name"
  rm -rf "$out"
  mkdir -p "$out"
  read -r -a lean_args <<< "$args"
  start=$(date +%s%N)
  "$lake_cmd" env "$scratch/lean2agda" --out "$out/tree" "${lean_args[@]}" > /dev/null
  seconds "$start" "$(date +%s%N)" > "$out/translate-seconds"
  start=$(date +%s%N)
  python3 ../scripts/python/agda_check.py --refusals --messages --agda "$agda_cmd" -j "$jobs" \
    --listings "$out/listings" --keep "$out/kept" "$out/tree" > "$out/loop.txt" || status=1
  looped=$(date +%s%N)
  python3 ../scripts/python/agda_check.py --fresh --json --agda "$agda_cmd" -j "$jobs" \
    "$out/kept" > "$out/final.json" || status=1
  checked=$(date +%s%N)
  golden="$out/golden"
  mkdir -p "$golden"
  cp -r "$out/listings/." "$golden/"
  cp "$out/tree"/*.agda-lib "$golden/"
  if [[ -s "$out/tree/refusals.txt" ]]; then cp "$out/tree/refusals.txt" "$golden/"; fi
  case "$form" in
    tree) (cd "$out/tree" && find . -name '*.agda' -not -path './_build/*' -exec cp --parents -t "$golden" {} +) ;;
    digest) manifest "$out/tree" > "$golden/modules.txt" ;;
    *) echo "goldens.sh: $name: unknown form $form" >&2; exit 2 ;;
  esac
  expected="tests/expected/scaffolds/$name"
  if [[ -n "$update" ]]; then
    rm -rf "$expected"
    cp -r "$golden" "$expected"
    verdict=written
  elif diff -r "$expected" "$golden" > "$out/golden.diff"; then
    verdict=same
  else
    verdict=differs
    status=1
    head -n 40 "$out/golden.diff" >&2
  fi
  printf '%s: translated in %s s, loop %s s, final check %s s, golden %s\n' "$name" \
    "$(cat "$out/translate-seconds")" "$(seconds "$start" "$looped")" "$(seconds "$looped" "$checked")" "$verdict"
done 3< tests/goldens.txt

if [[ ${#names[@]} -eq 0 ]]; then
  echo "goldens.sh: tests/goldens.txt names no golden" >&2
  exit 2
fi
dirs=()
for n in "${names[@]}"; do dirs+=("$work/$n"); done
python3 ../scripts/python/refusal_report.py --classes tests/refusal-classes.txt "${dirs[@]}" \
  > "$work/report.md" || status=1
if [[ -z "$results" ]]; then cat "$work/report.md"; else echo "tables: $work/report.md"; fi
exit "$status"
