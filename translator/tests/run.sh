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
"$lake_cmd" env "$lean_cmd" tests/Modules.lean

# A scaffold is a tree of modules, one per Lean module of the closure
# (issue M2-8).  check_listings runs scaffold_check's refusal loop over a
# tree with agda_check.py, module by module in dependency order, so that
# each module type-checks except for the refusals its listing names,
# which also counts the theorems the fallback unfolded; check_tree also
# compares the modules, the library file and the declarations the
# translator refuses (refusals.txt, when there are any) with the golden
# tree tests/expected/scaffolds/NAME/, beside the listings.  With KEEP
# set, the loop's final tree is copied there.
jobs=${AGDA_JOBS:-4}
check_listings() {
  local name=$1 out="$scratch/scaffold-$1" actual="$scratch/actual-$1"
  shift
  "$lake_cmd" exe lean2agda --out "$out" "$@" > /dev/null
  mkdir -p "$actual"
  python3 ../scripts/python/agda_check.py --refusals --messages --agda "${AGDA:-agda}" -j "$jobs" \
    --listings "$actual" ${KEEP:+--keep "$KEEP"} "$out" > /dev/null
}

check_tree() {
  local name=$1 out="$scratch/scaffold-$1" actual="$scratch/actual-$1"
  check_listings "$@"
  (cd "$out" && find . -name '*.agda' -not -path './_build/*' -exec cp --parents -t "$actual" {} +)
  cp "$out"/*.agda-lib "$actual/"
  if [[ -s "$out/refusals.txt" ]]; then cp "$out/refusals.txt" "$actual/"; fi
  diff -r "tests/expected/scaffolds/$name" "$actual"
}

check_tree list-reverse-reverse Init.Data.List.Lemmas -- List.reverse_reverse
check_tree nat-gcd-succ Init.Data.Nat.Gcd -- Nat.gcd_succ
check_tree nat-gcd-self Init.Data.Nat.Gcd -- Nat.gcd_self
check_tree printing TranslatorTests.Input.Printing -- PrintFixtures.alignedTop \
  PrintFixtures.alignedDeep PrintFixtures.withLet PrintFixtures.redex PrintFixtures.higher \
  PrintFixtures.strict PrintFixtures.pick PrintFixtures.greeting PrintFixtures.large \
  PrintFixtures.sorts PrintFixtures.doubling PrintFixtures.Pair.first PrintFixtures.Dependent.value
KEEP="$scratch/kept-selected" check_tree selected TranslatorTests.Input.Consumer -- Fixtures.selected
check_tree inductives TranslatorTests.Input.Inductives -- InductiveFixtures.Vec \
  InductiveFixtures.Same InductiveFixtures.Sized InductiveFixtures.Packed InductiveFixtures.Packed.width \
  InductiveFixtures.Packed.measured InductiveFixtures.Packed.value InductiveFixtures.Packed.fits \
  InductiveFixtures.Token InductiveFixtures.Rose InductiveFixtures.Rose.label InductiveFixtures.Rose.children \
  "InductiveFixtures.Stream'" InductiveFixtures.Term InductiveFixtures.Pair InductiveFixtures.Wide \
  InductiveFixtures.Bad
check_tree kinds TranslatorTests.Input.Kinds

# The driver of issue M2-8 (make check-output): the final tree of the
# loop over `selected` checks module by module, as it is.
python3 ../scripts/python/agda_check.py --agda "${AGDA:-agda}" -j "$jobs" "$scratch/kept-selected" > /dev/null

# A split changes no outcome: nat-gcd-self's tree cut into parts of at
# most 60 KB checks exactly what the uncut tree checks, so that what a
# part drops is dropped from the later parts that open it.
"$lake_cmd" exe lean2agda --split 60000 --out "$scratch/split" Init.Data.Nat.Gcd -- Nat.gcd_self > /dev/null
find "$scratch/split" -path '*~p2.agda' | grep -q .
python3 ../scripts/python/agda_check.py --refusals --agda "${AGDA:-agda}" -j "$jobs" \
  --listings "$scratch/split-listed" "$scratch/split" > /dev/null
diff -u tests/expected/scaffolds/nat-gcd-self/checked.txt "$scratch/split-listed/checked.txt"

# The acceptance criterion of issue M2-4: every inductive type of the
# closure of Init.Core's declarations is declared and checks.  They are
# the roots, so the definitions and theorems their types need stay
# postulates; the listings count the data types and records, and only
# they are compared.
INDUCTIVE_CLOSURE=Init.Core "$lake_cmd" env "$lean_cmd" scripts/InductiveTypes.lean \
  > "$scratch/init-core-inductives.txt"
mapfile -t init_core_inductives < "$scratch/init-core-inductives.txt"
check_listings init-core-inductives Init.Core -- "${init_core_inductives[@]}"
diff -r tests/expected/scaffolds/init-core-inductives "$scratch/actual-init-core-inductives"

# Every declaration of a module, mutual partial definitions included,
# makes a tree that the refusal loop gets through.
"$lake_cmd" exe lean2agda --out "$scratch/module-selection" TranslatorTests.Input.Printing > /dev/null
python3 ../scripts/python/agda_check.py --refusals --agda "${AGDA:-agda}" -j "$jobs" \
  "$scratch/module-selection" > /dev/null

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
expect_failure 2 '--split needs a natural number' --split x Init
expect_failure 2 '--split needs a natural number' --split
expect_failure 1 'unknown declaration' Init.Data.Nat.Gcd -- DoesNotExist
expect_failure 1 'DoesNotExist' DoesNotExist

"$lake_cmd" exe lean2agda --help > "$scratch/help.txt"
grep -F 'usage: lean2agda' "$scratch/help.txt" > /dev/null

echo 'translator golden and command-line tests passed'
