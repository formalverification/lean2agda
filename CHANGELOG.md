<!-- File: CHANGELOG.md -->

# Changelog

The translator's versions, newest first.  The version is the one line of
`translator/VERSION`, which `lean2agda --version` prints and the
provenance record of a generated library will carry; the scheme, and the
test that keeps this file, the file and the executable in agreement, are in
[`docs/translator/architecture.md`][map], "The version".  Each entry lists
the merged pull requests it covers, oldest first, one line each: what
changed, and its link.

## 0.1.0

The translator before its first generated library: the profile U scaffold
of a closure, with its names, sidecars and refusals, and the axiom atlas.
The entries are as follows:

+  The Lake package under `translator/`, pinning Lean v4.33.1, Mathlib at
   tag v4.33.1 and lean4export at tag v4.33.0 ([#64]).
+  The axiom atlas, version 0: one record per constant of the pinned
   Mathlib, with its exact axioms and tier, `lake exe atlas` ([#71]).
+  The command line, the environment loader, the dependency closure in
   dependency order, and the golden-test harness ([#73]).
+  Lean names as Agda identifiers and module paths, and the reverse-map
   sidecars ([#74]).
+  The expression printer, the sharing pass, and the profile U scaffold,
   checked by `scaffold_check.py` ([#77]).
+  Inductive types emitted as records and data types ([#80]).
+  Definitions, theorems in `opaque` blocks, opaque constants and axioms;
   the refusals of `sorryAx` and `unsafe`; the fallback that unfolds a
   theorem a dependent needs ([#81]).
+  The quotient's computation rules under profile U: `Quot.lift` and
   `Quot.ind` on `Quot.mk` as rewrite rules over `Eq`, and the checker's
   `--without-rewrite`, which shows where they fire ([#83]).
+  The engineering standards: the module map and its test, the `File:`
   header test, `lake test`, `translator/VERSION` with `--version`, and
   this file ([#25]).
+  Recursors defined by pattern matching on their constructors, one
   clause per rule of the kernel's and a `mutual` block for several; the
   printer's eta repair; the checker's heap bound and its markers, which
   charge an exhausted run to the declaration Agda died in ([#82]).
+  The scaffold as a tree of Agda modules, one per Lean module, with
   qualified references, exact imports, the split rule (`--split`),
   `U.agda-lib` and `U/Everything.agda`; `agda_check.py`, which checks a
   tree in dependency order with per-module time and peak memory, and
   runs the refusal loop over it, unfolding theorems across modules
   ([#84]).
+  The operation table under profile U (`--arithmetic agda`, the
   default; `lean` keeps Lean's definitions): Agda's builtins and Lean's
   own clauses in place of the recursive cores of the operations Lean's
   kernel accelerates on `Nat`, `Bool` bound to Agda's booleans, and
   `Nat.sub`'s equation at a successor as a rewrite rule, with two that
   make the rules confluent; the checker and the tree driver undo an
   unfolding made in vain ([#31]).

[#25]: https://github.com/formalverification/lean2agda/issues/25
[#31]: https://github.com/formalverification/lean2agda/issues/31
[#64]: https://github.com/formalverification/lean2agda/pull/64
[#71]: https://github.com/formalverification/lean2agda/pull/71
[#73]: https://github.com/formalverification/lean2agda/pull/73
[#74]: https://github.com/formalverification/lean2agda/pull/74
[#77]: https://github.com/formalverification/lean2agda/pull/77
[#80]: https://github.com/formalverification/lean2agda/pull/80
[#81]: https://github.com/formalverification/lean2agda/pull/81
[#82]: https://github.com/formalverification/lean2agda/pull/82
[#83]: https://github.com/formalverification/lean2agda/pull/83
[#84]: https://github.com/formalverification/lean2agda/pull/84

[map]: docs/translator/architecture.md
