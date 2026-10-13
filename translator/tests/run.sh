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

PRINTING_AGDA_TEST_DIR="$scratch" "$lake_cmd" env "$lean_cmd" tests/Printing.lean
(cd "$scratch" && "${AGDA:-agda}" PrintingLexical.agda)

"$lake_cmd" env "$lean_cmd" tests/Inductives.lean
"$lake_cmd" env "$lean_cmd" tests/Scaffold.lean

# A scaffold (the profile U module --out writes) must scope-check (the
# acceptance criterion of issue M2-3) and type-check except for the
# refusals its golden listing names, which also counts the theorems the
# fallback unfolded; check_scaffold also compares the module with its
# golden file, and the declarations the translator refuses with the
# golden refused.txt, or requires them to be none.
check_refusals() {
  local name=$1 file relative
  shift
  "$lake_cmd" exe lean2agda --out "$scratch/scaffold-$name" "$@" > /dev/null
  file=$(find "$scratch/scaffold-$name" -name '*.agda')
  relative=${file#"$scratch/scaffold-$name/"}
  (cd "$scratch/scaffold-$name" && "${AGDA:-agda}" --only-scope-checking "$relative" > /dev/null)
  python3 ../scripts/python/scaffold_check.py --agda "${AGDA:-agda}" --messages "$file" \
    > "$scratch/refusals-$name.txt"
  tail -n +2 "tests/expected/scaffolds/$name.refusals.txt" | diff -u - "$scratch/refusals-$name.txt"
}

check_scaffold() {
  local name=$1
  check_refusals "$@"
  tail -n +2 "tests/expected/scaffolds/$name.agda" | diff -u - "$(find "$scratch/scaffold-$name" -name '*.agda')"
  if [[ -f "tests/expected/scaffolds/$name.refused.txt" ]]; then
    tail -n +2 "tests/expected/scaffolds/$name.refused.txt" | diff -u - "$scratch/scaffold-$name/refusals.txt"
  else
    [[ ! -s "$scratch/scaffold-$name/refusals.txt" ]]
  fi
}

check_scaffold list-reverse-reverse Init.Data.List.Lemmas -- List.reverse_reverse
check_scaffold nat-gcd-succ Init.Data.Nat.Gcd -- Nat.gcd_succ
check_scaffold nat-gcd-self Init.Data.Nat.Gcd -- Nat.gcd_self
check_scaffold printing TranslatorTests.Input.Printing -- PrintFixtures.alignedTop \
  PrintFixtures.alignedDeep PrintFixtures.withLet PrintFixtures.redex PrintFixtures.higher \
  PrintFixtures.strict PrintFixtures.pick PrintFixtures.greeting PrintFixtures.large \
  PrintFixtures.sorts PrintFixtures.doubling PrintFixtures.Pair.first PrintFixtures.Dependent.value
check_scaffold selected TranslatorTests.Input.Consumer -- Fixtures.selected
check_scaffold inductives TranslatorTests.Input.Inductives -- InductiveFixtures.Vec \
  InductiveFixtures.Same InductiveFixtures.Sized InductiveFixtures.Packed InductiveFixtures.Packed.width \
  InductiveFixtures.Packed.measured InductiveFixtures.Packed.value InductiveFixtures.Packed.fits \
  InductiveFixtures.Token InductiveFixtures.Rose InductiveFixtures.Rose.label InductiveFixtures.Rose.children \
  "InductiveFixtures.Stream'" InductiveFixtures.Term InductiveFixtures.Pair InductiveFixtures.Wide \
  InductiveFixtures.Bad
check_scaffold kinds TranslatorTests.Input.Kinds

# The acceptance criterion of issue M2-4: every inductive type of the
# closure of Init.Core's declarations is declared and checks.  They are
# the roots, so the definitions and theorems their types need stay
# postulates; the listing counts the data types and records.
INDUCTIVE_CLOSURE=Init.Core "$lake_cmd" env "$lean_cmd" scripts/InductiveTypes.lean \
  > "$scratch/init-core-inductives.txt"
mapfile -t init_core_inductives < "$scratch/init-core-inductives.txt"
check_refusals init-core-inductives Init.Core -- "${init_core_inductives[@]}"

# Every declaration of a module, mutual partial definitions included,
# makes a scaffold that scope-checks.
"$lake_cmd" exe lean2agda --out "$scratch/module-selection" TranslatorTests.Input.Printing > /dev/null
(cd "$scratch/module-selection" && "${AGDA:-agda}" --only-scope-checking \
  U/TranslatorTests/Input/Printing.agda > /dev/null)

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
NAMING_OUTPUT_DIR="$scratch/out with spaces" "$lake_cmd" env "$lean_cmd" tests/NamingSidecars.lean

"$lake_cmd" exe lean2agda --root CC.Constructive --out "$scratch/custom-root" \
  TranslatorTests.Input.Consumer -- Fixtures.selected > "$scratch/custom-root.txt"
diff -u "$scratch/selected.txt" "$scratch/custom-root.txt"
NAMING_ROOT=CC.Constructive NAMING_OUTPUT_DIR="$scratch/custom-root" \
  "$lake_cmd" env "$lean_cmd" tests/NamingSidecars.lean

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
expect_failure 2 '--root needs a Lean name' --root
expect_failure 2 '--root needs a Lean name' --root --stats Init
expect_failure 2 '--share needs a natural number' --share x Init
expect_failure 2 '--share needs a natural number' --share
expect_failure 1 'unknown declaration' Init.Data.Nat.Gcd -- DoesNotExist
expect_failure 1 'DoesNotExist' DoesNotExist

"$lake_cmd" exe lean2agda --help > "$scratch/help.txt"
grep -F 'usage: lean2agda' "$scratch/help.txt" > /dev/null

echo 'translator golden and command-line tests passed'
