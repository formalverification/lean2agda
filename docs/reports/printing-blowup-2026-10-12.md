<!-- File: docs/reports/printing-blowup-2026-10-12.md -->

# Printed size and the sharing pass, 2026-10-12

How large the printer's output is for the three core-Lean corpus entries,
with and without the sharing pass, measured for issue [#17] on 2026-10-12;
[`printing.md`][printing] states the rules these numbers decided.  The
code is the translator at commit `12ac60c`, under Lean v4.33.1 and Agda
2.8.0, on a 20-thread Intel i9-12900H with 62 GB of memory, which other
sessions shared; the load averages are given with each run.

## Terms

+  **Bytes** are the UTF-8 bytes of every type and every value of the
   closure printed, each as `name : type` and a clause, auxiliary
   definitions included.  This is more than the scaffold prints, which is
   every type and the root's value only.
+  **Records** are the expression records of the entry's committed export,
   `corpus/<entry>/lean/term.ndjson`: lean4export writes one per distinct
   subterm, as it identifies them (LF-11 of
   [`lean-findings.md`][findings]: up to binder names and binder
   information).  They are the measure of "the `.olean` term size" here;
   [#44] is to use bytes of `.olean` instead.
+  **Distinct subterms** are counted per declaration, by structural
   equality that keeps binder names and information, so a subterm shared
   by two declarations counts twice; **printed nodes** are the expression
   nodes of the printed trees, a shared subterm's counted once.  Their
   worst ratio over a closure's declarations is the test of linearity: a
   pass that keeps it bounded keeps each declaration's text linear in its
   shared size.
+  **Repairs** are lambdas printed with the visibility of the type they
   are checked against, at the top of a value and below it.

## Size against the threshold

Produced by `cd translator && lake env lean scripts/PrintingBlowup.lean`
(load averages 0.62, 1.34, 2.79 before and 0.68, 1.33, 2.77 after; 10
seconds).  `off` is `--share 0`.
### list-reverse-reverse

41 constants; the export has 835 expression records in 56,062 bytes; the
declarations have 1,131 distinct subterms, counted per declaration.

| Threshold | Bytes | Bytes per record | Bytes over export bytes | Auxiliaries | Printed nodes | Worst nodes per distinct subterm | Repairs, top and deeper |
| --- | --- | --- | --- | --- | --- | --- | --- |
| off | 12401 | 14.9 | 0.22 | 0 | 2292 | 3.4 (`List.reverseAux_reverseAux_nil`) | 0, 1 |
| 64 | 12401 | 14.9 | 0.22 | 0 | 2292 | 3.4 (`List.reverseAux_reverseAux_nil`) | 0, 1 |
| 32 | 12401 | 14.9 | 0.22 | 0 | 2292 | 3.4 (`List.reverseAux_reverseAux_nil`) | 0, 1 |
| 16 | 12401 | 14.9 | 0.22 | 0 | 2292 | 3.4 (`List.reverseAux_reverseAux_nil`) | 0, 1 |
| 8 | 12401 | 14.9 | 0.22 | 0 | 2292 | 3.4 (`List.reverseAux_reverseAux_nil`) | 0, 1 |
| 4 | 12401 | 14.9 | 0.22 | 0 | 2292 | 3.4 (`List.reverseAux_reverseAux_nil`) | 0, 1 |
| 2 | 12607 | 15.1 | 0.22 | 2 | 2286 | 3.4 (`List.reverseAux_reverseAux_nil`) | 0, 1 |

### nat-gcd-succ

271 constants; the export has 8,131 expression records in 527,857 bytes;
the declarations have 14,279 distinct subterms, counted per declaration.

| Threshold | Bytes | Bytes per record | Bytes over export bytes | Auxiliaries | Printed nodes | Worst nodes per distinct subterm | Repairs, top and deeper |
| --- | --- | --- | --- | --- | --- | --- | --- |
| off | 270502 | 33.3 | 0.51 | 0 | 50897 | 23.5 (`_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary.eq_def`) | 25, 196 |
| 64 | 263380 | 32.4 | 0.50 | 3 | 49094 | 15.7 (`_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary.eq_def`) | 25, 196 |
| 32 | 257530 | 31.7 | 0.49 | 9 | 47578 | 13.0 (`WellFounded.Nat.fix_eq`) | 25, 196 |
| 16 | 259987 | 32.0 | 0.49 | 34 | 46303 | 13.0 (`WellFounded.Nat.fix_eq`) | 25, 192 |
| 8 | 269173 | 33.1 | 0.51 | 133 | 40614 | 8.8 (`WellFounded.Nat.fix_eq`) | 25, 192 |
| 4 | 303077 | 37.3 | 0.57 | 232 | 36741 | 8.1 (`WellFounded.Nat.fix_eq`) | 25, 192 |
| 2 | 341111 | 42.0 | 0.65 | 348 | 36031 | 8.0 (`WellFounded.Nat.fix_eq`) | 25, 192 |

### nat-gcd-self

334 constants; the export has 10,818 expression records in 684,821 bytes;
the declarations have 19,203 distinct subterms, counted per declaration.

| Threshold | Bytes | Bytes per record | Bytes over export bytes | Auxiliaries | Printed nodes | Worst nodes per distinct subterm | Repairs, top and deeper |
| --- | --- | --- | --- | --- | --- | --- | --- |
| off | 431486 | 39.9 | 0.63 | 0 | 84909 | 23.5 (`_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary.eq_def`) | 29, 198 |
| 64 | 424364 | 39.2 | 0.62 | 3 | 83106 | 22.3 (`Nat.modCore_eq`) | 29, 198 |
| 32 | 417558 | 38.6 | 0.61 | 15 | 81170 | 22.3 (`Nat.modCore_eq`) | 29, 198 |
| 16 | 419571 | 38.8 | 0.61 | 50 | 79509 | 22.3 (`Nat.modCore_eq`) | 29, 194 |
| 8 | 408741 | 37.8 | 0.60 | 218 | 61513 | 12.5 (`Nat.modCore_eq`) | 29, 194 |
| 4 | 456649 | 42.2 | 0.67 | 348 | 55973 | 11.2 (`Nat.modCore_eq`) | 29, 194 |
| 2 | 516798 | 47.8 | 0.75 | 528 | 54563 | 10.7 (`Nat.modCore_eq`) | 29, 194 |

The export file is 63 to 67 bytes a record; the printed text is 15 to 40
bytes a record with the pass off and at most 48 at any threshold, so it is
smaller than the export it came from at every threshold.  Without the
pass the printed trees have 2.0, 3.6 and 4.4 nodes per distinct subterm
overall, and 23.5 in the worst declaration (`Nat.gcd._unary.eq_def`):
these terms are not deeply shared.
The pass's effect on bytes is a U-shaped curve.  Small thresholds share
small subterms whose references cost as much as the subterms, since an
auxiliary's identifier repeats its owner's
(`~uprivate:Init:Data:Nat:Gcd:~n0:Nat:gcd:~uunary:eq~udef:~ushare:~n1`) and
it adds a type.  At 32, bytes are lowest for `nat-gcd-succ` and 2.2% above
the lowest for `nat-gcd-self` (408,741 at 8), with 9 and 15 auxiliaries
against 133 and 218 at 8; 32 is the default.  The worst ratio of
`nat-gcd-self` stays at 22.3 down to a threshold of 16 because
`Nat.modCore_eq` repeats open subterms, which the pass does not share.

## A shared term

The pass exists for terms that are shared, which the corpus entries are
not.  Two measurements, both in `make test-translator`, show the effect
there:

+  `PrintFixtures.doubling` (`tests/TranslatorTests/Input/Printing.lean`),
   `Nat.add` doubled ten times: its definitions print in 19,498 bytes with
   `--share 0` and in 1,288 bytes, with 6 auxiliary definitions, at 32.
+  The doubling of 2^20 leaves built in `tests/Printing.lean`: 42 distinct
   subterms, a printed tree of 2^22 − 3 nodes without the pass, and 100
   nodes with it at threshold 2 (19 auxiliaries of 5 nodes and a root of
   5).

## What Agda checks

`scripts/python/scaffold_check.py` type-checks a scaffold, turning a
refused definition into a postulate of its type and dropping a refused type
with its dependents (load averages 1.20, 1.36, 2.62 before, 1.17, 1.34,
2.57 after; times are the median of three runs).

| Scaffold | Bytes | Scope check | Agda runs | Last run | Refusals |
| --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | 6,123 | 0.05 s | 2 | 0.1 s | the root's value |
| `nat-gcd-succ` | 63,073 | 0.23 s | 7 | 0.4 s | the root's value, 5 types |
| `nat-gcd-self` | 84,449 | 0.31 s | 8 | 0.5 s | the root's value, 6 types |
| printing fixture | 68,258 | 0.22 s | 6 | 0.4 s | 1 value, 4 types |
| `Fixtures.selected` | 3,820 | 0.05 s | 1 | 0.1 s | none |

Printing every value of each closure, with every definition, theorem and
opaque constant as a root (load averages 0.65, 1.30, 2.74 before, 1.36,
1.41, 2.67 after), gives the following:

| Entry | Roots | Values printed | Checked | Refused | Behind a refused type | Agda runs, seconds |
| --- | --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | 21 | 21 | 17 | 4 | 0 | 5, 0.4 |
| `nat-gcd-succ` | 192 | 201 | 104 | 41 | 56 | 47, 24.7 |
| `nat-gcd-self` | 251 | 266 | 139 | 54 | 73 | 60, 43.5 |

Values printed include the type abbreviations and auxiliary definitions.
Every refusal in both tables is an `UnequalTerms`, a conversion Agda cannot
make without unfolding a definition or computing a recursor that the
scaffold postulates.  An earlier run of the same rules at thresholds off,
32, 16 and 8 refused the same declarations at each, with the last
successful run between 0.45 and 0.81 seconds.

## Every corpus entry

`make scaffold-corpus` (`translator/scripts/scaffold-corpus.sh`, added
after Copilot's review of the pull request) prints each entry of
`corpus/manifest.json` at the default threshold and has Agda scope-check
the scaffold.  The run below took 32 minutes 23 seconds, at load averages
3.82, 3.54, 3.27 before and 4.68, 7.43, 6.74 after, with other sessions
running.  Its first run, before commit `82964b5`, found
`real-sqrt-nonneg`'s scaffold unparsable: an implicit argument that was an
implicit Pi type printed as `{{…`, Agda's ASCII instance brace.

| Entry | Constants | Bytes | Print, s | Scope check, s |
| --- | --- | --- | --- | --- |
| `list-reverse-reverse` | 41 | 6,123 | 1.6 | 0.1 |
| `nat-gcd-self` | 334 | 84,449 | 1.6 | 0.9 |
| `nat-gcd-succ` | 271 | 63,073 | 1.6 | 0.9 |
| `lists-subset-refl` | 219 | 44,773 | 2.9 | 0.5 |
| `multiset-map-map` | 110 | 19,935 | 3.8 | 0.2 |
| `set-ext` | 26 | 3,978 | 2.4 | 0.1 |
| `finset-card-image` | 3,367 | 1,147,851 | 4.9 | 49.8 |
| `real-sqrt-nonneg` | 11,036 | 7,529,204 | 11.7 | 1,652.4 |
| `subgroup-card-dvd` | 6,918 | 3,040,759 | 3.1 | 186.5 |
| `order-hom-map-lfp` | 570 | 185,528 | 1.3 | 0.6 |
| `subtype-coe-eta` | 20 | 4,957 | 1.1 | 0.0 |
| `substructure-closure-le` | 1,879 | 692,061 | 1.8 | 6.0 |

Every entry passes.  Printing stays under 12 seconds, most of it loading
Mathlib's environment; the scope check grows faster than the module's
size, from 6 seconds for 0.7 MB to 28 minutes for 7.5 MB, in one module
each.

## The sort of `Prop`

With every sort whose level normalizes to zero printed as `Prop`, under
`--prop --type-in-type` (a probe, not committed), the scaffolds of
`nat-gcd-succ` and `nat-gcd-self` have 17 and 20 refusals instead of 6 and
7.  The 11 and 13 new ones, and the roots' own, are `UnequalSorts Prop !=
Set`: a universe-polymorphic constant printed with `Set` and instantiated
at `Prop`.  Profile U therefore uses `--type-in-type` alone.

## To rerun

Inside `nix develop`, from `translator/`:

```sh
lake env lean scripts/PrintingBlowup.lean
lake exe lean2agda --out out Init.Data.Nat.Gcd -- Nat.gcd_self
python3 ../scripts/python/scaffold_check.py --messages out/U/Init/Data/Nat/Gcd.agda
lake exe lean2agda Init.Data.Nat.Gcd -- Nat.gcd_self \
  | awk -F'\t' '$1=="definition"||$1=="theorem"||$1=="opaque" {print $3}' > roots.txt
lake exe lean2agda --out every Init.Data.Nat.Gcd -- $(cat roots.txt)
python3 ../scripts/python/scaffold_check.py every/U/Init/Data/Nat/Gcd.agda
```

From the repository root, after `make lean-cache`, `make scaffold-corpus`
gives the table of every corpus entry.

[#17]: https://github.com/formalverification/lean2agda/issues/17
[#44]: https://github.com/formalverification/lean2agda/issues/44
[printing]: ../translator/printing.md
[findings]: ../lean-findings.md
