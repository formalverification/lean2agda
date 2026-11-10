<!-- File: docs/translator/modules.md -->

# One module per Lean module

`lake exe lean2agda --out DIR` writes the profile U scaffold of a closure
as a tree of Agda modules, one per Lean source module of the closure,
each importing the modules whose constants it names, with a library file
and a module that imports them all; `scripts/python/agda_check.py`
checks such a tree one Agda process per module, in dependency order and
several at once, and records each module's time and peak memory.  Issue
[#22] implements both, in `translator/Lean2Agda/Core/Modules.lean` and
the driver.  The reason is Agda's time, which grew faster than a single
module: 6 s for 0.7 MB, 187 s for 3.0 MB and 28 minutes for 7.5 MB
([`printing-blowup`][report]), and lyphyser's single file ran Agda out of
memory ([`related-work.md`][related]).  The single-module scaffold is
retired: one emission path, and the goldens are trees.

## The tree

Each declaration belongs to its Lean source module
(`Declaration.sourceModule`), and a sharing auxiliary to its owner's
([`naming.md`][naming]).  The module of source module `M` sits at the
path of `M`'s names sidecar, `agdaModule root M`, so that
`Init.Data.Nat.Gcd` under the root `U` is `U/Init/Data/Nat/Gcd.agda`,
module `U.Init.Data.Nat.Gcd`, beside `U/Init/Data/Nat/Gcd.names.ndjson`.
It holds the items of the declarations its source module owns, ordered
as the scaffold orders them ([`printing.md`][printing]); a source module
none of whose declarations is emitted (every one refused) gets no file.

Inside a module the printer names a constant by its identifier; a
constant of another module it names by that module's path and the
identifier (`Naming.qualified`), and the module imports, plainly, exactly
the modules whose constants its items name, as follows:

```agda
{-# OPTIONS --type-in-type #-}
-- lean2agda, profile U: the scaffold of the closure of Fixtures:selected
-- Lean module TranslatorTests.Input.Consumer
module U.TranslatorTests.Input.Consumer where
import U.Init.Prelude
import U.TranslatorTests.Input.Base

Fixtures:selected : U.Init.Prelude.Nat
...
```

The rules behind that shape are as follows:

+  **Plain `import`, never `open import`**, so that the text Agda reads is
   the text the printer wrote and no two modules' identifiers can meet in
   one scope.  The cost is length: the tree of `Init.Data.Nat.Gcd`'s
   closure is 3.3 MB of text where the single module was 1.68 MB, the
   difference being `U.Init.Prelude.` and its kind before every foreign
   constant.  This session did not measure the names' share of Agda's
   time; the finished tree's check (below) is 2 s slower than the same
   declarations in one module, and that difference includes it.
+  **Exactly the modules named**: the import set of a module is computed
   from its items' printed references, and a reference that names
   neither an item of the module nor an item of another module stops the
   translator with an error.  A literal counts as a reference to `Nat` or
   `String` (`AgdaTerm.references`), whose builtin binding a module sees
   only through an import of the type's module, direct or not.
+  **Acyclic**: a Lean declaration refers only to its own module and to
   modules that module imports, and Lean's import graph is acyclic, so
   the emitted graph is too.  It is often a chain: in
   `Init.Data.Nat.Gcd`'s closure every module imports every earlier one.
+  **A projection from another module's record** goes through the
   record's projection function, which sits beside the record, so the
   form `U.M.R.f` is rare; Agda resolves it through a plain import all
   the same (probe of 2026-11-08: a record declared in a part, projected
   through the re-exporting module from another module).
+  **Refusals**: `refusals.txt` at the root lists every refused
   declaration as before, and each module's header counts those of its
   own source module.

## The split rule

A module whose items pass `--split BYTES` of printed text (1,000,000 by
default; `--split 0` never splits) is cut, in item order, into parts
`M.~p1`, `M.~p2`, …, at `U/Init/Core/~p1.agda` and so on, each part at
most the threshold unless one item alone is larger.  An item is never
cut, and a `mutual` block (a block of inductive types, or [#19]'s
recursors) is one item, so it lands whole in one part.  No Lean module
component encodes to `~p` followed by a digit, since the identifier
encoding escapes a `~` ([`naming.md`][naming]), so a part's path is never
a module's.

Inside one Lean module every identifier is unqualified, so a part
`open import`s the earlier parts whose identifiers its items name (the
one place an emitted module is opened: the identifiers of one Lean
module never clash), and imports plainly the other modules its own items
name.  The module `M` itself becomes a header that re-exports its parts,
`open import M.~pk public`, so that the qualified names other modules
print, `U.Init.Core.x`, still resolve; a probe of 2026-11-08 confirmed
that a re-exported record's fields, constructor and builtin binding all
reach a module that imports `M`.  A part opens only the parts it needs,
so two parts that need nothing of each other can check in parallel.

The threshold measures bytes of printed Agda, since that is what the
blowup report measured Agda's time against.  Its default, 1 MB, rests on
the measurements below: cutting further makes the refusal loop faster but
the check of a finished tree slower, since every module pays Agda's
start-up and the reading of its imports' interfaces.

## The library files

At the output root `lean2agda --out` writes, as follows:

+  `U.agda-lib` (the root's name; `lean2agda.agda-lib` for no root), with
   `name: U` and `include: .`, so that Agda run from the root resolves
   the imports.  It has no `depend:` line, since the profile U scaffold
   imports nothing outside the tree, and no `flags:` line, since every
   module states its own options.  A profile that needs a library adds
   its `depend:` line here.
+  `libraries`, naming that file by its absolute path, for a consumer
   outside the root: `agda --library-file=DIR/libraries -l U File.agda`.
   Agda reads a relative path in a libraries file against the directory
   it runs in, not against the file's (probe of 2026-11-08), so the path
   is absolute and the file is not portable; it is excluded from the
   goldens.
+  `U/Everything.agda`, module `U.Everything`, importing every module of
   the tree: the single Agda process that checks it all.  A closure with
   a Lean module whose path would be `U.Everything` stops the translator
   with an error.

A `DIR` that already holds a module this run does not write (one an
earlier, larger closure left) stops the translator before it writes
anything, since the driver reads every `.agda` file under `DIR` as part
of the tree; the translator deletes nothing there.  Running the same
closure into the same `DIR` again overwrites it.  Stale interfaces under
`DIR/_build` need no such care: Agda rechecks a module whose source or
imports changed.

## The driver

`scripts/python/agda_check.py DIR` reads the tree from its files (each
module's `module` line and `import` lines; a file must sit at the path its
module asks for, and the graph must be acyclic) and checks each module
with `agda <module>` from `DIR`, so that Agda writes the module's
interface under `DIR/_build` and every later module reads it instead of
checking the module again.  `make check-output OUT=DIR JOBS=N` runs it,
and `make check` runs it after `corpus-check` when `OUT` is set.  The
details are as follows:

+  **Scheduling**.  A module starts once every module it imports has
   checked, so no two Agda processes ever work on modules one of which
   imports the other, and no interface is written twice.  Up to `-j N`
   run at once (half the processors by default), the module that most
   others wait for first.  A module whose import failed is skipped, not
   run, since Agda would check the import again inside it.  The rule is
   one pure function, `launchable`; `simulate` replays it against given
   durations, which is how the tests show the ordering, and `execute`
   runs it with a thread per running Agda.
+  **Time** is the wall time of the module's own Agda process, from the
   injected clock; the summary adds the wall time of the whole run and
   the sum over the modules.
+  **Peak memory** is the maximum resident set size of the module's own
   Agda process, which `os.wait4` returns for that one child (`ru_maxrss`,
   KiB on Linux).  `resource.getrusage(RUSAGE_CHILDREN)` cannot give it
   under `-j`: its `ru_maxrss` is the largest of all the children waited
   for so far, so a small module would report the largest earlier one.
+  **The heap** is bounded, 8G by default (`--heap`, GHC's `-M`), and Agda
   names each declaration as it starts it (`-v tc.decl:5`), so that a
   module that exhausts the heap fails alone, reported as `heap` with the
   declaration Agda named last, instead of taking the machine down; [#19]
   met one such declaration, `ByteArray.IsValidUTF8`, whose positivity
   check normalizes an exponentially large type.
+  **Interfaces**.  Agda reuses an interface newer than its module, so a
   second run over an unchanged tree checks nothing; `--fresh` removes
   `DIR/_build` first, which every measurement below used.
+  **The report** is a table (module, result, seconds, peak MiB, size)
   and a summary line, or `--json`; the exit status is 1 unless every
   module checks.

## Refusals across modules

No tree checks whole yet: until the recursors and quotients compute
([#19], [#21]), every closure holds declarations Agda refuses.
`agda_check.py --refusals DIR` runs `scaffold_check.py`'s loop
([`printing.md`][printing]) on each module of a scratch copy of the tree,
in the same order and with the same parallelism, so that a module is
checked against the final text of the modules it imports.  The choice
was to have the driver call the checker per module rather than teach the
checker trees: the checker stays a function of one module, and the
scheduler stays in one place.

+  A declaration reduced to a postulate in module A is a postulate for
   every module that imports A, since A's final text is what Agda reads.
+  A declaration dropped in A is dropped from every module that names it,
   with what refers to it there, before Agda runs, and listed as
   `dropped`; Agda would otherwise meet it as a name out of scope.
   Identifiers are unique across a tree, so a dropped identifier named
   bare in a later part of A's own module, which opens the earlier parts,
   is found too.  An out-of-scope error that still reaches the loop is a
   defect of that drop, and the run fails rather than count it as a
   refusal; the first version of the drop missed the bare names, and a
   split run counted 25 declarations as checked that were not.
+  The fallback of [#20] makes a theorem transparent when a dependent's
   error names it.  Within a module the loop does that itself; across
   modules, and across the parts of a split module, the driver does it
   between passes over the tree.  When a pass ends with a refusal whose
   message names a theorem still opaque in a module the refused
   declaration's module imports, the driver checks the whole tree again
   from a fresh copy with that theorem transparent in its own module,
   under `-- theorem, unfolded for D`, and lists `unfolded T for D` in
   the dependent's module, where its `in vain` mark is decided as in one
   module.  Each pass adds a theorem, so the passes end; the summary line
   counts them when there are more than one, and each module's runs and
   seconds are summed over them.  A first version unfolded only within
   the module, and lost two kinds of unfolding: on `kinds` and on the
   quotients' `--without-rewrite` listing, an unfolding of an `Init`
   theorem, in vain in the single module too; and, in the review of
   [#84], on `kinds` cut with `--split 1`, the unfolding of `alias` for
   `useAlias`, which turned `useAlias` into a postulate.  Every golden
   tree now lists the counts and events of the single module it replaces
   (as of [#83]), and the harness checks `kinds` cut after every item
   against its uncut tree.
+  `--listings OUT` writes each module's listing beside its path
   (`OUT/U/Init/Core.checked.txt`) and the sums of their count lines to
   `OUT/checked.txt`; `--keep OUT` copies the final tree, which the
   default mode can then check and time without the loop (an `OUT`
   holding a module outside the tree is refused before the loop starts,
   for the same reason as the translator's `DIR`); `--types-only`
   restricts each module as `scaffold_check.py --types-only` does, keeping
   too whatever a kept declaration of another module names.

## Measurements

The acceptance run of [#22] is the closure of every declaration of
`Init.Data.Nat.Gcd` (135 roots, 797 declarations under the checker),
emitted with `lake exe lean2agda --out gcd Init.Data.Nat.Gcd` in 1.1 s:
nine modules from 21 KB to 974 KB, none past the default threshold, 3.3 MB
in all.  The single module of the base commit (`37e7feb`) is 1.68 MB.
Both were run on 2026-11-08 on a 20-processor machine that other sessions
were also using, so the times carry some noise; the counts do not.

| | single module (base) | tree, `-j 8` |
| --- | --- | --- |
| refusal loop: Agda runs | 120 | 128 |
| refusal loop: wall time | 922 s | 191 s |
| refusal loop: largest Agda process | 1,146 MiB | 441 MiB |
| declarations checked | 625 of 797 | 625 of 797 |
| final text checked once: wall time | 4.0 to 4.4 s | 6.1 to 6.3 s |
| final text checked once: largest process | 495 MiB | 224 MiB |

The two runs list the same events, so no refusal is an artifact of the
split into modules.  The loop is five times faster because each of its
runs checks one module against its imports' interfaces instead of the
whole closure up to the error: 7.7 s a run for the single module, 1.5 s
for the tree.  The finished tree, on the other hand, checks 2 s slower
than the same declarations in one module, and `-j 1` takes the same
6.2 s as `-j 8`: this closure's import graph is a chain, so nothing runs
in parallel, and each of the nine modules pays Agda's start-up and its
imports' interfaces.  Memory falls by half or more in both.

The per-module table of the finished tree (`agda_check.py --fresh -j 8`)
is as follows:

| module | seconds | peak MiB | KB |
| --- | --- | --- | --- |
| `U.Init.Prelude` | 2.2 | 181 | 137 |
| `U.Init.Core` | 0.6 | 95 | 29 |
| `U.Init.SimpLemmas` | 0.4 | 83 | 13 |
| `U.Init.Data.Nat.Basic` | 2.5 | 224 | 289 |
| `U.Init.WF` | 0.5 | 110 | 19 |
| `U.Init.Data.Nat.Div.Basic` | 0.7 | 119 | 42 |
| `U.Init.Data.Nat.Dvd` | 1.0 | 145 | 160 |
| `U.Init.Data.Nat.Gcd` | 0.5 | 104 | 24 |
| `U.Everything` | 0.3 | 102 | 0 |

The threshold was set from the same closure emitted three ways, each run
through the loop and then checked once (`--fresh -j 8`), as follows:

| `--split` | modules | loop: runs | loop: wall | finished: wall | finished: largest process |
| --- | --- | --- | --- | --- | --- |
| 1,000,000 (nothing cut) | 9 | 128 | 161 s | 6.4 s | 224 MiB |
| 250,000 | 22 | 141 | 92 s | 9.2 s | 181 MiB |
| 100,000 | 47 | 166 | 66 s | 17.1 s | 132 MiB |

All three check the same 625 declarations and list the same events.
Cutting smaller makes each run of the loop cheaper, and lets a few parts
run side by side (17.1 s of wall time against 19.7 s summed at 100 KB),
but every extra module costs the finished tree its start-up and its
imports' interfaces.  The finished tree is the product, so the default
stays at 1 MB, below the sizes where the blowup report saw Agda's time
turn superlinear (187 s for 3.0 MB); `--split 100000` is the setting for
a session that iterates on the refusal loop.  (The unsplit loop's 161 s
here and 191 s in the first table are two runs of one command on a
shared machine.)

The commands, from `translator/` in the dev shell, are as follows:

```sh
lake exe lean2agda --out gcd Init.Data.Nat.Gcd
python3 ../scripts/python/agda_check.py --refusals --messages -j 8 --listings listed --keep kept gcd
python3 ../scripts/python/agda_check.py --fresh -j 8 kept
```

## Verification

`make test` runs the following:

+  `translator/tests/Modules.lean`, on the two-module fixture
   `TranslatorTests.Input.Base` and `Consumer`: each constant in its
   source module's module, references to another module qualified and
   references inside one bare, the import sets exactly the modules named,
   an auxiliary definition beside its owner, the library file and
   `U.Everything`; and the split, with a threshold that falls inside the
   fixture's `mutual` block of `Tree` and `Forest`, which lands whole as
   the first item of the next part, each part opening only earlier parts;
+  the golden trees of `tests/expected/scaffolds/` (`printing.md`'s
   Verification), compared with `diff -r`: the modules, the library file,
   `refusals.txt` where the translator refuses anything, and the loop's
   listings; the final tree of `selected` checked by the default mode;
   and `nat-gcd-self` emitted with `--split 60000`, whose summed counts
   must equal the uncut tree's;
+  `scripts/python/tests/test_agda_check.py`: the tree's parsing, the
   graph and its cycles, `launchable`, `simulate` against an import
   diamond (no module starts before its imports end, at most `-j` at
   once, nothing past a failure), `execute` with threads, the measuring
   runner on real processes (a peak it must see, a failure, a timeout, a
   missing command), the report with a fake Agda, and the loop over a
   tree with a fake Agda, in which a module drops a declaration and the
   next module's user of it is dropped before Agda runs.

[#19]: https://github.com/formalverification/lean2agda/issues/19
[#20]: https://github.com/formalverification/lean2agda/issues/20
[#21]: https://github.com/formalverification/lean2agda/issues/21
[#22]: https://github.com/formalverification/lean2agda/issues/22
[#83]: https://github.com/formalverification/lean2agda/pull/83
[#84]: https://github.com/formalverification/lean2agda/pull/84
[naming]: naming.md
[printing]: printing.md
[related]: ../related-work.md
[report]: ../reports/printing-blowup-2026-10-12.md
