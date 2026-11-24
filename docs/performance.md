<!-- File: docs/performance.md -->

# The performance baseline

What the profile U translation of the corpus and of four fragments of
Lean's `Init` costs, module by module, and what Agda accepts of it: the
baseline of issue [#23], Milestone 2's exit test, measured on 2026-11-22.
Every corpus entry of [`corpus/manifest.json`][manifest] and the modules
`Init.Prelude`, `Init.Core`, `Init.Data.Nat.Basic` and `Init.Data.Nat.Gcd`
were translated into trees of Agda modules ([`modules.md`][modules]), run
through the checker's refusal loop ([`printing.md`][printing-checks]),
checked again fresh in the loop's final state, and compared with goldens
under [`translator/tests/expected/scaffolds/`][goldens].  Thirteen of the
sixteen pass under the reading of "accepted" below: the four fragments
and nine of the twelve corpus entries.  The loops of the three largest
Mathlib closures stop before they end, and [#94] takes them.  The tables
give each tree's size and times, its values and what Agda refused of
them, by the issue whose work removes each refusal; `make goldens`
reproduces those that pass.

## What "accepted" means

(See also [#23], [#26], [#27], [#31], [#88] and [#89].)

Under profile U the checker turns a value Agda refuses into a postulate of
its type, and drops what a refused type takes with it, so a tree it
reports as checked is accepted by Agda in that state, not as the
translator emitted it.  Some refusals cannot go before Milestone 3, so
Milestone 2's exit criterion ("accepted by Agda under profile U") cannot
hold word for word.  William chose the following reading on 2026-11-22:

+  a tree passes when the loop's final state checks fresh in Agda and every
   refusal in its listings is classified to an issue other than [#23],
   with none unclassified;
+  a value dropped with a refused type is charged to that type's class;
+  a postulate the checker made is never counted as a checked value;
+  the tables count each class.

[`translator/tests/refusal-classes.txt`][classes] classifies each refusal
by Agda's error and the declaration's identifier (a glob may stand for
several), with a note saying why, and
[`scripts/python/refusal_report.py`][report-py] fails a tree with a
refusal no rule classifies, or with a module of its final state that does
not check.  The classes are as follows:

+  **[#27]**, definitional proof irrelevance: two proofs of one
   proposition compared (`h₆ != hc₂ of type c₀`), which Lean's kernel
   accepts and Agda does not under profile U, where every sort is `Set`.
+  **[#26]**, `K`-like reduction: `Eq.rec` on a proof of `a = a` that is a
   variable, which Agda reduces only on `Eq.refl` (`eq_of_heq`,
   `cast_eq`), and what stalls on `eq_of_heq` once it is a postulate.
+  **[#31]**, the equations the operation table gives up
   ([`nat-operations.md`][nat-operations]): the fuel equations of
   `Nat.div.go` and `Nat.modCore.go` and the lemmas resting on them, and
   `Nat.beq.eq_def`, the unfolding of `Nat.beq` at two variables, which
   this baseline found ([`nat-operations.md`][nat-operations] has the
   correction).  [#31] is closed: these are its documented cost under
   profile U.
+  **[#88]** (M3-11), `String`'s recursor, a postulate while `String` is
   bound to `BUILTIN STRING`: `String.noConfusion`,
   `String.ofByteArray.noConfusion` and `String.isValidUTF8`.
+  **[#89]** (M3-12), binder information, which Lean's kernel ignores when
   it compares two types and Agda does not: every `UnequalHiding`
   (`{a : α} → B` against `(a : α) → B`); a term with explicit binders
   checked where one of Lean's strict-implicit `⦃a b⦄` is expected once
   the expected type unfolds (`Monotone`, `Function.Injective`,
   `upperBounds`, `lowerBounds`, and `Set`'s order, which Mathlib takes
   from the Pi type's); and what stalls on one of those once it is a
   postulate.

A refusal's listing keeps the first line of Agda's message only.  To
classify one, its emitted declaration was put back into a copy of the
loop's final tree, whose interfaces the final check had written, and Agda
was run on its module alone, which gives the whole message in seconds.  A
message that names a value the loop had postulated was charged to that
value's class.  Every class above names the issue whose work removes it,
so a refusal that a later change removes, or one it adds, shows in the
goldens' listings and in the report.

## How it was measured

+  **The code** is this repository at its pull request's head: the
   translator at `5cfd6f5`, unchanged by the pull request, Lean v4.33.1
   and Agda 2.8.0 from the dev shell, Mathlib at its pinned tag
   ([`pinning.md`][pinning]).
+  **The machine** is a laptop, a 12th-generation Intel Core i9-12900H with
   20 threads and 62 GB of memory, which other sessions shared; the load
   averages ran from 1 to 5 while the passing trees were measured, and the
   dated report [`goldens-2026-11-22`][dated] gives each tree's.  The times
   are wall times and carry that noise; the counts do not.
+  **Each tree** was translated by a copy of the translator's binary
   (`lake env lean2agda --out DIR MODULE -- NAME`), so that no rebuild
   could change it mid-run; its loop ran with `agda_check.py --refusals
   --messages -j 4` under the checker's 8G heap bound, and its final state
   with `agda_check.py --fresh -j 4 --json`.  `make goldens` runs the same
   steps ([`goldens.sh`][goldens-sh]).
+  **Per module**, `Agda s` and `Agda MiB` are the final check's: the wall
   time and peak resident memory of that module's own Agda process,
   reading its imports' interfaces.  `Loop runs`, `Loop s` and `Loop MiB`
   are the refusal loop's: its Agda runs on the module over every pass,
   their seconds, and the largest of their peaks.  A module `M.~pN` is a
   part of a module cut at the split threshold, 1 MB.
+  **Values** are the definitions, theorems and opaque constants of
   Lean's printed with their values, recursors and the operation table's
   helpers not among them; **declarations** are the Agda module's, a data
   type or a record with its constructors being one.

## The trees

Every tree of `translator/tests/goldens.txt`, a row each:

| Tree | Constants | Modules | MB | Translate s | Translator refused | Values | Checked | Refused | Behind a refused type | Types refused | Loop Agda s | Loop MiB | Final wall s | Final MiB | Result |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | 41 | 6 | 0.02 | 1.3 | 0 | 21 | 21 | 0 | 0 | 0 | 1 | 56 | 0.3 | 55 | passes |
| `nat-gcd-self` | 334 | 8 | 0.62 | 1.3 | 0 | 266 | 260 | 6 (#26 1, #27 2, #31 3) | 0 | 0 | 90 | 224 | 4.4 | 235 | passes |
| `nat-gcd-succ` | 271 | 7 | 0.31 | 1.3 | 0 | 201 | 199 | 2 (#26 1, #31 1) | 0 | 0 | 16 | 221 | 3.3 | 241 | passes |
| `lists-subset-refl` | 219 | 9 | 0.17 | 1.6 | 0 | 141 | 136 | 5 (#26 4, #89 1) | 0 | 0 | 18 | 107 | 1.7 | 96 | passes |
| `multiset-map-map` | 110 | 10 | 0.12 | 1.8 | 0 | 66 | 65 | 1 (#26 1) | 0 | 0 | 3 | 97 | 1.3 | 101 | passes |
| `set-ext` | 26 | 4 | 0.01 | 1.5 | 0 | 11 | 11 | 0 | 0 | 0 | 0 | 54 | 0.2 | 53 | passes |
| `order-hom-map-lfp` | 570 | 25 | 0.48 | 1.9 | 0 | 351 | 340 | 11 (#26 1, #27 2, #31 1, #89 7) | 0 | 0 | 36 | 340 | 5.2 | 236 | passes |
| `subtype-coe-eta` | 20 | 4 | 0.02 | 1.5 | 0 | 11 | 9 | 2 (#26 1, #27 1) | 0 | 0 | 0 | 57 | 0.3 | 55 | passes |
| `substructure-closure-le` | 1,879 | 81 | 4.91 | 2.7 | 0 | 1,492 | 1,436 | 56 (#26 1, #27 13, #31 3, #89 39) | 0 | 0 | 1,370 | 8,490 | 47.8 | 526 | passes |
| `init-prelude` | 2,314 | 4 | 1.26 | 1.4 | 22 | 1,877 | 1,868 | 9 (#26 1, #27 4, #31 1, #88 3) | 0 | 0 | 326 | 2,166 | 34.3 | 1,537 | passes |
| `init-core` | 2,128 | 7 | 1.53 | 1.7 | 0 | 1,660 | 1,635 | 21 (#26 2, #27 16, #31 1, #88 2) | 4 (#27 4) | 1 | 442 | 2,292 | 20.0 | 1,367 | passes |
| `init-data-nat-basic` | 916 | 10 | 2.18 | 1.6 | 0 | 810 | 805 | 5 (#26 1, #27 1, #31 1, #89 2) | 0 | 0 | 60 | 823 | 17.6 | 587 | passes |
| `init-data-nat-gcd` | 808 | 9 | 3.31 | 1.4 | 0 | 696 | 688 | 8 (#26 1, #27 2, #31 5) | 0 | 0 | 274 | 620 | 20.4 | 584 | passes |

## The classes

Refused values by class, with the values behind a refused type:

| Class | `list-reverse-reverse` | `nat-gcd-self` | `nat-gcd-succ` | `lists-subset-refl` | `multiset-map-map` | `set-ext` | `order-hom-map-lfp` | `subtype-coe-eta` | `substructure-closure-le` | `init-prelude` | `init-core` | `init-data-nat-basic` | `init-data-nat-gcd` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| #26 | 0 | 1 | 1 | 4 | 1 | 0 | 1 | 1 | 1 | 1 | 2 | 1 | 1 |
| #27 | 0 | 2 | 0 | 0 | 0 | 0 | 2 | 1 | 13 | 4 | 16 + 4 behind | 1 | 2 |
| #31 | 0 | 3 | 1 | 0 | 0 | 0 | 1 | 0 | 3 | 1 | 1 | 1 | 5 |
| #88 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 3 | 2 | 0 | 0 |
| #89 | 0 | 0 | 0 | 1 | 0 | 0 | 7 | 0 | 39 | 0 | 0 | 2 | 0 |

## The `Init` fragments

One table per fragment, a row per emitted module, under the loop's
summary line.  `Init.Prelude`'s closure has 22 declarations the
translator itself refuses (`sorryAx`, eleven unsafe definitions, two
unsafe opaque constants and the eight unsafe compiler axioms;
[`printing.md`][printing-scaffold], The scaffold), which are not Agda's
refusals and are counted apart, as `Translator refused`.

### `Init.Prelude` (`init-prelude`)

4 modules, 18 Agda runs, 326.4 s in all, 327.0 s wall with -j 4

| Module | KB | Declarations | Values | Checked | Refused | Behind a refused type | Types refused | Loop runs | Loop s | Loop MiB | Agda s | Agda MiB |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `U.Init.Prelude.~p1` | 1,000 | 1,650 | 1,390 | 1,384 | 6 (#26 1, #27 4, #31 1) | 0 | 0 | 12 | 247.8 | 2166 | 20.6 | 1537 |
| `U.Init.Prelude.~p2` | 262 | 530 | 487 | 484 | 3 (#88 3) | 0 | 0 | 4 | 67.0 | 1785 | 11.6 | 1085 |
| `U.Init.Prelude` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 10.7 | 1006 | 1.0 | 291 |
| `U.Everything` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0.9 | 292 | 1.1 | 332 |

### `Init.Core` (`init-core`)

7 modules, 37 Agda runs, 441.5 s in all, 424.2 s wall with -j 4

| Module | KB | Declarations | Values | Checked | Refused | Behind a refused type | Types refused | Loop runs | Loop s | Loop MiB | Agda s | Agda MiB |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `U.Init.Prelude` | 508 | 864 | 665 | 657 | 8 (#26 1, #27 4, #31 1, #88 2) | 0 | 0 | 14 | 102.2 | 948 | 5.9 | 670 |
| `U.Init.Coe` | 1 | 2 | 0 | 0 | 0 | 0 | 0 | 1 | 8.8 | 659 | 0.3 | 156 |
| `U.Init.Core.~p2` | 21 | 18 | 18 | 18 | 0 | 0 | 0 | 1 | 9.2 | 663 | 0.5 | 187 |
| `U.Init.SizeOf` | 1 | 5 | 3 | 3 | 0 | 0 | 0 | 1 | 9.0 | 636 | 0.3 | 156 |
| `U.Init.Core.~p1` | 998 | 1,083 | 974 | 957 | 13 (#26 1, #27 12) | 4 (#27 4) | 1 | 18 | 296.9 | 2292 | 12.4 | 1367 |
| `U.Init.Core` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 14.8 | 1370 | 0.7 | 288 |
| `U.Everything` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0.7 | 232 | 0.6 | 226 |

### `Init.Data.Nat.Basic` (`init-data-nat-basic`)

10 modules, 15 Agda runs, 59.7 s in all, 55.0 s wall with -j 4

| Module | KB | Declarations | Values | Checked | Refused | Behind a refused type | Types refused | Loop runs | Loop s | Loop MiB | Agda s | Agda MiB |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `U.Init.Prelude` | 179 | 280 | 205 | 204 | 1 (#26 1) | 0 | 0 | 2 | 3.7 | 263 | 2.1 | 226 |
| `U.Init.Core` | 38 | 87 | 55 | 54 | 1 (#27 1) | 0 | 0 | 2 | 3.2 | 220 | 0.5 | 94 |
| `U.Init.Data.Zero` | 1 | 2 | 2 | 2 | 0 | 0 | 0 | 1 | 2.4 | 251 | 0.2 | 87 |
| `U.Init.Data.NeZero` | 2 | 4 | 2 | 2 | 0 | 0 | 0 | 1 | 0.6 | 98 | 0.2 | 90 |
| `U.Init.SimpLemmas` | 39 | 28 | 28 | 28 | 0 | 0 | 0 | 1 | 0.8 | 130 | 0.4 | 111 |
| `U.Init.SizeOf` | 1 | 4 | 2 | 2 | 0 | 0 | 0 | 1 | 2.3 | 244 | 0.2 | 88 |
| `U.Init.Data.Nat.Basic.~p1` | 998 | 330 | 330 | 329 | 1 (#31 1) | 0 | 0 | 2 | 12.9 | 654 | 6.3 | 587 |
| `U.Init.Data.Nat.Basic.~p2` | 919 | 189 | 186 | 184 | 2 (#89 2) | 0 | 0 | 3 | 26.5 | 823 | 7.2 | 576 |
| `U.Init.Data.Nat.Basic` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 6.9 | 596 | 0.5 | 153 |
| `U.Everything` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 | 0.5 | 164 | 0.6 | 189 |

### `Init.Data.Nat.Gcd` (`init-data-nat-gcd`)

9 modules, 94 Agda runs in 5 passes, 274.0 s in all, 276.8 s wall with -j 4

| Module | KB | Declarations | Values | Checked | Refused | Behind a refused type | Types refused | Loop runs | Loop s | Loop MiB | Agda s | Agda MiB |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `U.Init.Prelude` | 191 | 293 | 214 | 212 | 2 (#26 1, #31 1) | 0 | 0 | 24 | 44.5 | 283 | 2.0 | 220 |
| `U.Init.Core` | 36 | 76 | 50 | 48 | 2 (#27 2) | 0 | 0 | 15 | 14.3 | 269 | 0.5 | 94 |
| `U.Init.SimpLemmas` | 21 | 21 | 21 | 21 | 0 | 0 | 0 | 5 | 3.0 | 115 | 0.3 | 93 |
| `U.Init.Data.Nat.Basic` | 868 | 152 | 152 | 152 | 0 | 0 | 0 | 5 | 22.9 | 438 | 4.6 | 569 |
| `U.Init.WF` | 96 | 27 | 21 | 21 | 0 | 0 | 0 | 5 | 23.9 | 620 | 0.8 | 155 |
| `U.Init.Data.Nat.Div.Basic` | 974 | 50 | 50 | 46 | 4 (#31 4) | 0 | 0 | 25 | 82.9 | 539 | 4.8 | 576 |
| `U.Init.Data.Nat.Dvd` | 212 | 40 | 40 | 40 | 0 | 0 | 0 | 5 | 26.1 | 480 | 1.5 | 224 |
| `U.Init.Data.Nat.Gcd` | 908 | 149 | 148 | 148 | 0 | 0 | 0 | 5 | 31.5 | 537 | 5.2 | 584 |
| `U.Everything` | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 5 | 24.8 | 553 | 0.7 | 188 |

## The corpus entries

The three core-Lean entries and six Mathlib entries pass; their trees run
from 8 KB (`set-ext`) to 4.9 MB (`substructure-closure-le`, 81 modules),
and their per-module tables are in the dated report
[`goldens-2026-11-22`][dated].  The goldens of trees under 1 MB hold the
emitted modules; those of the larger trees and of the fragments hold each
module's SHA-256 digest and size (`modules.txt`) instead, beside the
listings, so that any change to a module still shows.  The three
core-Lean goldens are the ones `run.sh` already checked, byte for byte.
`substructure-closure-le` refuses 56 of its 1,492 values, 39 of them
[#89]'s: `Set`'s lattice instances, which Mathlib builds from the Pi
type's, compare `(i : α) → a i ≤ b i` with `Set`'s `{a : α} → a ∈ s → a ∈
t`, and once `Set.instDistribLattice` and `Set.instBoundedOrder` are
postulates, every proof about `Set`'s order that unfolds them stalls.

### The three largest closures

(See also [#94].)

The other three corpus entries do not pass: their loops stop with an
error, so no final state exists to check, and the modules that import the
one where each stopped were not reached.  The counts below are of what the
loop got through before it stopped; a value in a module it never reached
counts as unchecked.

| Tree | Constants | Modules | MB | Translate s | Values | Checked | Refused | Behind a refused type | Loop, until it stopped | Modules not reached |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `finset-card-image` | 3,367 | 125 | 37.28 | 7.4 | 3,849 | 3,656 | 116, 99 unclassified | 0 | 4,207 s wall, 242 Agda runs | 10 |
| `subgroup-card-dvd` | 6,918 | 322 | 56.88 | 6.8 | 7,139 | 6,407 | 274, 209 unclassified | 6 | 3,915 s wall, 628 Agda runs | 31 |
| `real-sqrt-nonneg` | 11,036 | 511 | 125.87 | 23.1 | 12,725 | 10,807 | 711, 620 unclassified | 285 | 11,868 s wall, 1,244 Agda runs | 42 |

The findings are as follows; [#94] (M2-15) takes them, and adds the three
trees to the goldens once they pass:

+  **A run past the time bound**.  All three stop at
   `Init.Data.List.Perm`, where one Agda run passes the checker's
   3,600 s per-run bound at 8,559 to 9,076 MiB, at the 8G heap bound; the
   checker names the declaration in progress and, by design, refuses
   nothing for a timeout, since the bound is no one declaration's.  The
   cause is `List.perm_inv_core`, a 343 KB proof whose metas Agda leaves
   unsolved and whose constraints it wakes again at every later
   declaration: the module, cut before `List.Perm.filterMap`, checks to
   its end in 61 s at 1.4 GiB and then reports the unsolved metas; cut
   after it, in 718 s at 2.3 GiB; under a 2G heap the full module
   exhausts it in 272 s.  `real-sqrt-nonneg` also stops in
   `Mathlib.Data.Real.Basic.~p2`, at a sharing auxiliary of
   `Real.ofCauchy_sup`.
+  **Unsolved metas**: 447 values are refused with
   `UnsolvedMetaVariables`, 416 of them the sharing pass's auxiliaries
   (`…:~ushare:~nN`, [`printing.md`][printing-sharing]).  None of the
   passing trees has one.  The likeliest cause, not yet tested, is that a
   subterm lifted into an auxiliary of its own loses the context from
   which Agda inferred its implicit arguments.
+  **`Real`'s type** is refused as `HeapExhausted`, with 285 values
   behind it: Agda exhausts the 8G heap in the record's own declaration,
   where the checker places a positivity check's blowup, as
   `ByteArray.IsValidUTF8`'s was before [#31]; which normal form grows has
   not been measured.
+  **The rest**: 479 `UnequalTerms` refusals and a handful of others
   (`WrongHidingInLambda`, `CannotEliminateWithPattern`, `CannotApply`)
   are not yet classified.

The heap and time bounds stayed as they are: a run that needs more is the
finding, and raising either to make a run pass would hide it.

## What moves the numbers

+  **The loop's passes**.  The driver checks a tree again, from a fresh
   copy, whenever a refusal names a theorem of another module, with that
   theorem transparent in its own module, and undoes the unfolding in the
   next pass when it was in vain ([`modules.md`][modules]).  Every pass
   rechecks every module, so `Init.Data.Nat.Gcd`'s five passes cost 277 s
   where `Init.Data.Nat.Basic`'s one costs 55 s.
+  **An unfolding in vain across modules**.  In
   `substructure-closure-le`'s closure, `Init.Data.Nat.Div.Basic` asks
   for three of `Init.Prelude`'s theorems (`Nat.div_rec_fuel_lemma`,
   `Nat.le_of_ble_eq_true`, `Nat.not_le_of_not_ble_eq_true`), all in
   vain, and the pass that holds them transparent checks `Init.Prelude`
   with them so.  A probe of that state, the loop's final text of the
   module with the three theorems transparent, ran 164 s, reached 8.29 GiB
   and exhausted the heap in `ByteArray.IsValidUTF8`'s positivity check:
   the blowup that [#31] removed within one module, reached across
   modules.  The next pass
   undoes the unfoldings and the final listings are right, but it is why
   that loop's largest process reached 8,490 MiB while its final state
   checks at 359 MiB.  A closure that holds both
   `ByteArray.IsValidUTF8` and `Init.Data.Nat.Div.Basic`'s fuel lemmas
   pays it in a pass of its loop.
+  **The heap bound**, 8G by default (`--heap`), which a run that needs
   more meets as a refusal, never as the system's out-of-memory killer.  It
   refuses nothing in the thirteen trees that pass; in the three largest it
   refuses `Real`'s type and two values, which is a finding, not a reason
   to raise it.
+  **The split threshold**, 1 MB by default (`--split`), which
   [`modules.md`][modules] chose: smaller parts make the loop cheaper and
   the final check dearer.
+  **The parallelism**, `-j`: a module waits for every module it imports,
   so `Init.Prelude`, every tree's root, always runs alone, and a chain
   of imports runs as one process at a time whatever `-j` is.

## The commands

From the repository's root inside `nix develop`, after `make lean-cache`,
as follows:

```sh
make goldens RESULTS=out              # all thirteen; tables in out/report.md
make goldens GOLDENS=init-core        # one, by its name in translator/tests/goldens.txt
make goldens-update GOLDENS=init-core # rewrite its golden after a change meant to move it
```

`RESULTS` keeps each tree's emitted modules, listings, loop report and
final check; without it they go to a scratch directory.  The tables of
this document are `out/report.md`'s, and the full per-module tables of
every tree, the three largest Mathlib closures' among them, are in the
dated report [`goldens-2026-11-22`][dated].

[#23]: https://github.com/formalverification/lean2agda/issues/23
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#31]: https://github.com/formalverification/lean2agda/issues/31
[#88]: https://github.com/formalverification/lean2agda/issues/88
[#89]: https://github.com/formalverification/lean2agda/issues/89
[#94]: https://github.com/formalverification/lean2agda/issues/94
[manifest]: ../corpus/manifest.json
[modules]: translator/modules.md
[printing-checks]: translator/printing.md#what-agda-checks-and-the-fallback
[goldens]: ../translator/tests/expected/scaffolds/
[goldens-sh]: ../translator/scripts/goldens.sh
[classes]: ../translator/tests/refusal-classes.txt
[report-py]: ../scripts/python/refusal_report.py
[nat-operations]: foundations/nat-operations.md
[pinning]: pinning.md
[printing-scaffold]: translator/printing.md#the-scaffold
[printing-sharing]: translator/printing.md#the-sharing-pass
[dated]: reports/goldens-2026-11-22.md
