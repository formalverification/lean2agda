#!/usr/bin/env bash
# File: translator/tests/run.sh
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
lake_cmd="${LAKE:-lake}"
lean_cmd="${LEAN:-lean}"

# These targets compile against Lean only.  Lake may clone its pinned
# dependencies on a fresh checkout, but no Mathlib cache is needed.
"$lake_cmd" build lean2agda TranslatorTests Atlas.Graph naming-check-atlas
"$lake_cmd" env "$lean_cmd" tests/Check.lean

scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

NAMING_AGDA_TEST_DIR="$scratch" "$lake_cmd" env "$lean_cmd" tests/NamingAtlasFixture.lean
"$lake_cmd" exe naming-check-atlas "$scratch/atlas-valid.ndjson" > "$scratch/atlas-check.json"
grep -F '"constants":5' "$scratch/atlas-check.json" > /dev/null
for defect in truncated count duplicate trailing pin malformed; do
  if "$lake_cmd" exe naming-check-atlas "$scratch/atlas-$defect.ndjson" \
      > "$scratch/stdout" 2> "$scratch/stderr"; then
    echo "atlas checker accepted $defect input" >&2
    exit 1
  else
    [[ "$?" == 1 ]]
  fi
  grep -F 'naming-check-atlas:' "$scratch/stderr" > /dev/null
  [[ ! -s "$scratch/stdout" ]]
done

NAMING_AGDA_TEST_DIR="$scratch" "$lake_cmd" env "$lean_cmd" tests/Naming.lean
"$lake_cmd" env "$lean_cmd" tests/NamingGolden.lean > "$scratch/naming-init.txt"
tail -n +2 tests/expected/naming-init.txt > "$scratch/expected-naming-init.txt"
diff -u "$scratch/expected-naming-init.txt" "$scratch/naming-init.txt"
(cd "$scratch" && "${AGDA:-agda}" NamingLexical.agda && "${AGDA:-agda}" NamingImport.agda)

timeout 60 "$lake_cmd" exe lean2agda --stats Init.Data.Nat.Gcd -- Nat.gcd_self > "$scratch/gcd.txt"
tail -n +2 tests/expected/gcd-self.txt > "$scratch/expected-gcd.txt"
diff -u "$scratch/expected-gcd.txt" "$scratch/gcd.txt"

"$lake_cmd" exe lean2agda --profile U --out "$scratch/out with spaces" \
  TranslatorTests.Input.Consumer -- Fixtures.selected > "$scratch/selected.txt"
tail -n +2 tests/expected/selected.txt > "$scratch/expected-selected.txt"
diff -u "$scratch/expected-selected.txt" "$scratch/selected.txt"
diff -u "$scratch/selected.txt" "$scratch/out with spaces/closure.txt"

"$lake_cmd" exe lean2agda --stats --out "$scratch/stats" \
  Init.Data.Nat.Gcd -- Nat.gcd_self > "$scratch/gcd-out.txt"
diff -u "$scratch/gcd.txt" "$scratch/gcd-out.txt"
sed '/^# stats/,$d' "$scratch/gcd-out.txt" > "$scratch/listing.txt"
diff -u "$scratch/listing.txt" "$scratch/stats/closure.txt"

expect_failure() {
  local expected_status=$1 expected_message=$2 actual_status
  shift 2
  if "$lake_cmd" exe lean2agda "$@" > "$scratch/stdout" 2> "$scratch/stderr"; then
    echo "unexpected success: $*" >&2
    return 1
  else
    actual_status=$?
  fi
  if [[ "$actual_status" != "$expected_status" ]]; then
    cat "$scratch/stderr" >&2
    echo "expected status $expected_status, got $actual_status: $*" >&2
    return 1
  fi
  grep -F -- "$expected_message" "$scratch/stderr" > /dev/null
  [[ ! -s "$scratch/stdout" ]]
}

expect_failure 2 'at least one module is required'
expect_failure 2 'unsupported profile' --profile K Init
expect_failure 2 'unknown option' --wat Init
expect_failure 2 '--out needs a directory' --out
expect_failure 1 'unknown declaration' Init.Data.Nat.Gcd -- DoesNotExist
expect_failure 1 'DoesNotExist' DoesNotExist

"$lake_cmd" exe lean2agda --help > "$scratch/help.txt"
grep -F 'usage: lean2agda' "$scratch/help.txt" > /dev/null

echo 'translator golden and command-line tests passed'
