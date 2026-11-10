<!-- File: docs/translator/architecture.md -->

# The translator's module map

Which file of the translator does what, in what order, on what data, in
the code as it stands.  The pipeline's stages, what each is for, which
issue builds it and where it stood are in [`../architecture.md`][pipeline],
the companion note of ADR 0001; this map names the files and definitions
that implement the stages built so far, and the rules each one implements
stay in the notes beside it ([`loading.md`][loading],
[`naming.md`][naming], [`printing.md`][printing] and
[`inductives.md`][inductives]).

The map is kept true by a test.  `scripts/python/standards_check.py`, run
by `make test` (`tests/test_standards_check.py`), fails on any of the
following:

+  a tracked `.lean` or `.sh` file under `translator/`, or a Python file
   the translator's harness runs (`agda_run.py` and `scaffold_check.py`),
   with no row in a table below whose first column is "File";
+  a row naming a file that does not exist, or a file with two rows;
+  a Lean file whose "Effects" cell begins with `pure` and whose code (its
   comments and strings aside) mentions an effect monad (`IO`, `EIO`,
   `BaseIO`, `CoreM`, `MetaM`, `TermElabM`, `CommandElabM`), or whose cell
   begins with `IO` and whose code mentions none;
+  a name in the pass order or the data types that the file its row names
   does not define;
+  a relative link of this document that names no file.

The same script checks that every tracked Lean, Python and shell file of
the repository opens with a `File:` header naming its own path.  A pull
request that adds a module adds its row here; one that renames a
definition the pass order names renames it here.

## Terms

+  The **environment** is Lean's `Environment`: every constant of the
   imported `.olean` modules, with its type, its value if it has one, and
   the module that declares it.
+  The **closure** of a set of root declarations is every constant they
   reach through types, values, constructors, recursors and their
   reduction rules, as a `Closure`: groups of declarations, each group a
   strongly connected component of the dependency graph, dependencies
   first.
+  The **shared closure** is the closure after the sharing pass: each
   declaration's large repeated closed subterms replaced by references to
   **auxiliary** definitions, which the closure then holds too, flagged
   `auxiliary`.
+  The **scaffold** is the Agda module the translator writes for a
   closure under profile U (`--type-in-type --rewriting`, postulates
   allowed); a **refusal** is a declaration the scaffold leaves out, with
   its reason.  A **computation rule** is a postulated equation the
   scaffold makes a rewrite rule, so that Agda reduces `Quot.lift` and
   `Quot.ind` on `Quot.mk` as Lean's kernel does.
+  A **sidecar** is the `.names.ndjson` file beside each module path,
   mapping every Agda identifier back to the Lean name it encodes.
+  **Pure** means a function of its arguments: no effect monad, so no
   file, process or clock.  The Lean kernel's `whnf` and `check`, which
   the printer and the sharing pass call, are pure in this sense; they
   return `Except`.

## The pass order

One run of `lake exe lean2agda [--out DIR] [--stats] MODULE... [-- DECL...]`,
from the command line to the files it writes, then the scaffold checker
that the harness (or a person) runs on the scaffold.  Each row is one
definition.  The rows from `addAuxiliaries` to `orderItems` run inside
`scaffold`, and `inductiveDecl` inside `scaffoldItem`; `ruleItem` follows
`scaffoldItem` for `Quot.lift` and `Quot.ind`.  Without `--out`
the run stops after the listing; with `--stats` it appends the counts.

| Definition | File | Consumes | Produces |
| --- | --- | --- | --- |
| `main` | `translator/Main.lean` | the arguments | the exit status: 0, 1 on a failure, 2 on a usage error |
| `parseArgs` | `translator/Lean2Agda/Core/CommandLine.lean` | the arguments, as strings | `Args`, or the usage error |
| `run` | `translator/Lean2Agda/Main.lean` | `Args` | standard output, and with `--out` the files below |
| `importEnvironment` | `translator/Lean2Agda/Main.lean` | the module names | the `Environment`, from the `.olean` files on `LEAN_PATH` |
| `selectRoots` | `translator/Lean2Agda/Core/Closure.lean` | the environment, the modules, the declarations named after `--` | the roots: those declarations, or every one the modules own |
| `dependencyClosure` | `translator/Lean2Agda/Core/Closure.lean` | the environment and the roots | the `Closure`, by `directDependencies` over `recursorIndex` and Lean's `SCC.scc` |
| `renderClosure` | `translator/Lean2Agda/Core/Render.lean` | the profile and the closure | the listing: standard output, and `closure.txt` with `--out` |
| `writeOutputs` | `translator/Lean2Agda/Main.lean` | the environment, `Args`, the directory, the closure, the listing | the files of `--out` |
| `shareClosure` | `translator/Lean2Agda/Core/Share.lean` | the environment, the threshold (`--share`), the closure | the shared closure, by `shareDeclaration` on each safe declaration |
| `moduleNameMaps` | `translator/Lean2Agda/Core/ReverseMap.lean` | the root (`--root`) and the shared closure | one `ModuleNames` per source module; `ModuleNames.render` writes each sidecar |
| `scaffold` | `translator/Lean2Agda/Core/Scaffold.lean` | the environment, the root, the shared closure | the `Scaffold`: its items in order, its counts, its refusals |
| `addAuxiliaries` | `translator/Lean2Agda/Core/Share.lean` | the environment and the shared closure | the environment with the auxiliary definitions added, checked by the kernel |
| `refuseDeclarations` | `translator/Lean2Agda/Core/Scaffold.lean` | the closure's declarations | the refused ones, each with its `Refusal` |
| `scaffoldItem` | `translator/Lean2Agda/Core/Scaffold.lean` | one kept declaration | its `ScaffoldItem`, by kind, through the printer's `Printer.type` and `Printer.clause` |
| `ruleItem` | `translator/Lean2Agda/Core/Scaffold.lean` | a quotient primitive's computation rule, from `quotRule?` | its `ScaffoldItem`: the rule's postulate and its `REWRITE` pragma |
| `inductiveDecl` | `translator/Lean2Agda/Core/Inductive.lean` | a block's `InductiveMember`s, from `blockMembers` | its `InductiveDecl`: `data` and `record` lines, shaped by `isAgdaRecord` and `agdaParamCount` |
| `breakCycles` | `translator/Lean2Agda/Core/Scaffold.lean` | the items | the items, a cyclic definition postulated |
| `orderItems` | `translator/Lean2Agda/Core/Scaffold.lean` | the items | the items, each after what it refers to |
| `Scaffold.render` | `translator/Lean2Agda/Core/Scaffold.lean` | the scaffold and `scaffoldComment`'s line | the module's text, written at `Scaffold.filePath` |
| `Scaffold.renderRefusals` | `translator/Lean2Agda/Core/Scaffold.lean` | the scaffold | `refusals.txt` |
| `Closure.stats` | `translator/Lean2Agda/Core/Stats.lean` | the closure, not the shared one | `Stats`; `Stats.render` appends them with `--stats` |
| `without_rewrites` | `scripts/python/scaffold_check.py` | a scaffold, parsed by `parse_module`, under `--without-rewrite` | the module without its `REWRITE` pragmas, its rules left to postulates that never fire |
| `check_module` | `scripts/python/scaffold_check.py` | a scaffold, parsed by `parse_module` | the checked module, each refusal and unfolding an event, rendered by `listing` |
| `check_file` | `scripts/python/agda_run.py` | one scratch copy of the module | Agda's verdict as a `FileRun`, through the injected `run_agda` |

The listing and `--stats` describe the closure as loaded; the sidecars and
the scaffold describe the shared closure, so that they cover the
auxiliary definitions.  The translator stamps no version into what it
writes (see "The version" below).

## The data types

The types that cross a file's boundary.  Each is immutable, as Lean's
structures are, and each Python one is a frozen dataclass.

| Type | File | Made by | Read by |
| --- | --- | --- | --- |
| `Args` | `translator/Lean2Agda/Core/CommandLine.lean` | `parseArgs` | `main`, `run`, `writeOutputs` |
| `Kind` | `translator/Lean2Agda/Core/Types.lean` | `Kind.ofConstantInfo` | `renderClosure`, `Stats.add`, the refusals |
| `Declaration` | `translator/Lean2Agda/Core/Types.lean` | `dependencyClosure`; `shareDeclaration` for an auxiliary | every pass after loading |
| `Closure` | `translator/Lean2Agda/Core/Types.lean` | `dependencyClosure`; `shareClosure` for the shared closure | `renderClosure`, `Closure.stats`, `moduleNameMaps`, `scaffold` |
| `Stats` | `translator/Lean2Agda/Core/Stats.lean` | `Closure.stats` | `run`, through `Stats.render` |
| `Root` | `translator/Lean2Agda/Core/Naming.lean` | `parseArgs`, from `--root` | `agdaModule`, `moduleNameMaps`, `scaffold` |
| `ModuleNames` | `translator/Lean2Agda/Core/ReverseMap.lean` | `moduleNameMaps`; `ModuleNames.parse` from a sidecar | `writeOutputs`, the naming tests |
| `ReverseMap` | `translator/Lean2Agda/Core/ReverseMap.lean` | `ReverseMap.build`, which refuses a collision | `ModuleNames.render`, `ReverseMap.lookup` |
| `AgdaTerm` | `translator/Lean2Agda/Core/Print.lean` | `printExpr` and the rest of the printer | `AgdaTerm.render`, `AgdaTerm.constants`, the emitters |
| `PrintCounts` | `translator/Lean2Agda/Core/Print.lean` | the printer, in `PrintM`'s state | `Scaffold`'s counts, the printing tests and `PrintingBlowup.lean` |
| `Printer` | `translator/Lean2Agda/Core/Print.lean` | `scaffold`, with the environment and a `Naming` | `Printer.type`, `Printer.clause`, `Printer.telescope`, `Printer.term` |
| `Scope` | `translator/Lean2Agda/Core/Print.lean` | `Scope.enter` and `enterTelescope` | the printer and `Inductive.lean`'s `dataLines` and `recordLines` |
| `Clause` | `translator/Lean2Agda/Core/Print.lean` | `Printer.clause` | `valueItem` in `Scaffold.lean` |
| `InductiveMember` | `translator/Lean2Agda/Core/Inductive.lean` | `blockMembers` | `inductiveDecl` |
| `InductiveDecl` | `translator/Lean2Agda/Core/Inductive.lean` | `inductiveDecl` | `inductiveItem` in `Scaffold.lean` |
| `ScaffoldItem` | `translator/Lean2Agda/Core/Scaffold.lean` | `scaffoldItem` | `breakCycles`, `orderItems`, `Scaffold.render` |
| `Refusal` | `translator/Lean2Agda/Core/Scaffold.lean` | `refuseDeclarations` | `Scaffold.renderRefusals` |
| `Scaffold` | `translator/Lean2Agda/Core/Scaffold.lean` | `scaffold` | `writeOutputs` |
| `Module` | `scripts/python/scaffold_check.py` | `parse_module`, from the scaffold's text | `check_module`, `types_only` |
| `State` | `scripts/python/scaffold_check.py` | `check_module`, by `step` | `listing` |
| `FileRun` | `scripts/python/agda_run.py` | `classify` | `check_module`; the corpus checker too |

Between the translator and what reads its output, the data are files, as
follows:

+  `closure.txt`: the listing, one tab-separated row per declaration
   (kind, source module, name) under a `# group N` line per group
   ([`loading.md`][loading]);
+  `<root>/<module path>.names.ndjson`: a sidecar, a header record (naming
   version 1, root, source, target path), one record per identifier, and
   a footer counting them ([`naming.md`][naming]);
+  `<root>/<module path>.agda`: the scaffold, at the path of its first
   root's sidecar ([`printing.md`][printing]);
+  `refusals.txt`: one line per refused declaration, kind, name and reason;
+  the scaffold checker's listing, on standard output, which the harness
   compares with `translator/tests/expected/scaffolds/*.refusals.txt`.

## The translator

The library `Lean2Agda`, its command line, and the Python the harness runs
on its output.  The rule is a pure core with IO at the edges: every file
under `Lean2Agda/Core/` is pure, and the edges are `translator/Main.lean`
and `translator/Lean2Agda/Main.lean`.

| File | Stage | Consumes | Produces | Effects | Rules |
| --- | --- | --- | --- | --- | --- |
| `translator/Main.lean` | command line | the arguments | the exit status, messages, `--version` | IO: the executable's root, with `main` | [`README.md`][translator-readme] |
| `translator/Lean2Agda/Main.lean` | load and write | `Args` | the environment; standard output; the files of `--out` | IO: the shell, `importEnvironment` and `writeOutputs` | [`loading.md`][loading] |
| `translator/Lean2Agda.lean` | library root | | the core, imported whole | pure | |
| `translator/Lean2Agda/Core/CommandLine.lean` | command line | the arguments | `Args`, the usage text | pure | [`README.md`][translator-readme] |
| `translator/Lean2Agda/Core/Types.lean` | load | `ConstantInfo` | `Kind`, `Declaration`, `Closure` | pure | [`loading.md`][loading] |
| `translator/Lean2Agda/Core/Closure.lean` | load | the environment, the roots | the closure in dependency order | pure | [`loading.md`][loading] |
| `translator/Lean2Agda/Core/Render.lean` | load | the closure | the listing | pure | [`loading.md`][loading] |
| `translator/Lean2Agda/Core/Stats.lean` | load | the closure | the counts by kind | pure | [`loading.md`][loading] |
| `translator/Lean2Agda/Core/Naming.lean` | emit: names | a Lean name, a root and a module | its Agda identifier and module path | pure | [`naming.md`][naming] |
| `translator/Lean2Agda/Core/ReverseMap.lean` | emit: names | the shared closure; a sidecar's text | the sidecars, rendered and parsed | pure | [`naming.md`][naming] |
| `translator/Lean2Agda/Core/Share.lean` | emit: sharing | the environment and the closure | the shared closure; the environment with its auxiliaries | pure | [`printing.md`][printing] |
| `translator/Lean2Agda/Core/InductiveShape.lean` | emit: inductives | an inductive type | record or data, the parameters kept, a field's binder | pure | [`inductives.md`][inductives] |
| `translator/Lean2Agda/Core/Print.lean` | emit: printer | a kernel expression | `AgdaTerm`, its text, a clause, `PrintCounts` | pure | [`printing.md`][printing] |
| `translator/Lean2Agda/Core/Inductive.lean` | emit: inductives | a block of inductive types | its Agda declaration | pure | [`inductives.md`][inductives] |
| `translator/Lean2Agda/Core/Scaffold.lean` | emit: scaffold | the shared closure | the scaffold, its quotient computation rules, and its refusals | pure | [`printing.md`][printing] |
| `scripts/python/scaffold_check.py` | check | a scaffold | its listing of refusals and unfoldings | IO in `check_module` and `main`; the rest pure | [`printing.md`][printing] |
| `scripts/python/agda_run.py` | check | a file and a directory | Agda's verdict, classified | IO in `run_agda`, `check_file` and `real_clock`; the rest pure | [`printing.md`][printing] |

`Printer.telescope`, `Printer.term` and `Naming.qualified` are called by
the tests and the measurement scripts only, today; they are the printer's
interface for the emitters to come.  `scripts/python/corpus_check.py` also
runs `agda_run.py`, on the corpus, which is not the translator's.

## The atlas

The axiom atlas ([`../../atlas/README.md`][atlas]): `lake exe atlas`
imports Mathlib when it runs and writes one NDJSON record per constant.

| File | Stage | Consumes | Produces | Effects | Rules |
| --- | --- | --- | --- | --- | --- |
| `translator/Atlas/Main.lean` | profile | the arguments, `lake-manifest.json` | the records file and its run file | IO: the executable, `atlas` | [`../../atlas/README.md`][atlas] |
| `translator/Atlas/Collect.lean` | profile | an imported environment | each constant's `Record`, in order | IO: reads the environment in `CoreM`, writes nothing | [`../../atlas/README.md`][atlas] |
| `translator/Atlas/Graph.lean` | profile | the constants | the dependency graph, the exact axiom sets, the value-graph count | pure | [`../../atlas/README.md`][atlas] |
| `translator/Atlas/Record.lean` | profile | a constant's axioms and flags | its tier and its NDJSON line | pure | [`../../atlas/README.md`][atlas] |
| `translator/Atlas/AutoDecl.lean` | profile | a constant's name | whether it is auto-generated, Batteries' test | pure | [`../../atlas/README.md`][atlas] |

## Tests

`make test-translator` runs `translator/tests/run.sh`, which builds the
package, runs `lake test` (the unit checks, below), and then the checks
that need Agda, a run's output, or a golden file.  `lake test` builds and
runs the executable `unittests`, whose root is `tests/UnitTests.lean`;
every check runs at each invocation, reads its fixtures when it runs,
and the executable exits 1 if any fails.  `lake test -- NAME...` runs the
named checks only.

| File | Run by | Checks |
| --- | --- | --- |
| `translator/tests/UnitTests.lean` | `lake test` | the driver: runs the checks below, or those named, and reports each |
| `translator/tests/Check.lean` | `lake test` (`check`) | the parser, root selection, dependencies, cycles, order, statistics, and the closure's axioms against `tests/atlas-gcd-self.json` and `Atlas.Graph` |
| `translator/tests/Inductives.lean` | `lake test` (`inductives`) | record or data, parameters kept, the declarations of core types and the fixtures, projections, sharing in constructor types |
| `translator/tests/Naming.lean` | `lake test` (`naming`) | identifiers, reverse maps, injectivity over samples and `Init`, module paths; writes `NamingLexical.agda` and `NamingImport.agda` to `NAMING_AGDA_TEST_DIR` |
| `translator/tests/Printing.lean` | `lake test` (`printing`) | the layout, binder names, constructors, telescopes, repairs, sharing; writes `PrintingLexical.agda` to `PRINTING_AGDA_TEST_DIR` |
| `translator/tests/Scaffold.lean` | `lake test` (`scaffold`) | each kind's item, refusals, `unsafe` and sharing, cycles, builtins, the quotient's computation rules against `Quot.liftBeta` and `Quot.indBeta` |
| `translator/tests/NamingAtlasFixture.lean` | `run.sh`, `lake env lean` | writes the NDJSON fixtures `naming-check-atlas` runs on, valid and defective, to `NAMING_AGDA_TEST_DIR` |
| `translator/tests/NamingGolden.lean` | `run.sh`, `lake env lean` | prints the names `Init.Data.Nat.Gcd` owns, diffed with `tests/expected/naming-init.txt` |
| `translator/tests/NamingSidecars.lean` | `run.sh`, `lake env lean` | the sidecars a run wrote to `NAMING_OUTPUT_DIR`, under `NAMING_ROOT`, against the closure's |
| `translator/tests/TranslatorTests/NamingAtlas.lean` | `run.sh`, `lake exe naming-check-atlas` | injectivity over an atlas's names; the root of that executable |
| `translator/tests/TranslatorTests/AtlasNames.lean` | `NamingAtlas.lean`, `NamingAtlasProbe.lean` | reads an atlas's population of names |
| `translator/tests/TranslatorTests.lean` | `lake build TranslatorTests` | the fixtures' root |
| `translator/tests/TranslatorTests/Input/Base.lean` | fixture | an axiom, a type and a structure, a mutual block, a definition |
| `translator/tests/TranslatorTests/Input/Consumer.lean` | fixture | a private, an opaque and a matching definition, a projection, an `initialize`, importing `Base` |
| `translator/tests/TranslatorTests/Input/Inductives.lean` | fixture | one inductive type per rule of [`inductives.md`][inductives] |
| `translator/tests/TranslatorTests/Input/Kinds.lean` | fixture | every kind the scaffold emits or refuses |
| `translator/tests/TranslatorTests/Input/Printing.lean` | fixture | every expression constructor and binder visibility, the repairs, a sharing blowup |
| `translator/tests/TranslatorTests/Input/Quotients.lean` | fixture | theorems that hold by `rfl` only through a quotient's computation rule |
| `translator/tests/run.sh` | `make test-translator` | `lake test`; Agda on the lexical files; the golden scaffolds and refusal listings through `scaffold_check.py`; the `quotients` scaffold with its rewrite rules removed; `Init.Core`'s inductive types; the golden listings and sidecars; `--version`; the command line's failures |

The fixture `Consumer.lean` declares an `initialize`, so it mentions `IO`;
the fixtures and tests carry no Effects cell, since every test does IO.

## Scripts

Run by hand, or by `run.sh` where the row says so; none is part of a
library.

| File | Run as | Purpose |
| --- | --- | --- |
| `translator/scripts/InductiveTypes.lean` | `lake env lean`; `run.sh` with `INDUCTIVE_CLOSURE=Init.Core` | the inductive types of a closure or of modules, one per line, as roots |
| `translator/scripts/PrintingBlowup.lean` | `lake env lean` | the printer's output size with and without sharing, for the dated report under `docs/reports/` |
| `translator/scripts/FlattenBenchmark.lean` | compiled by hand ([`../lean-findings.md`][findings]) | the cost of `Closure.declarations` against an explicit loop |
| `translator/scripts/NamingAtlasProbe.lean` | `lake exe naming-atlas-probe` | the atlas's name decoder against Mathlib's structured names; needs Mathlib's cache |
| `translator/scripts/Smoke.lean` | `make lean-smoke` | Mathlib's `.olean` files load |
| `translator/scripts/scaffold-corpus.sh` | `make scaffold-corpus` | every corpus entry's scaffold printed and scope-checked |

## The package

| File | Role |
| --- | --- |
| `translator/lakefile.toml` | the libraries `Lean2Agda`, `Atlas`, `TranslatorTests` and `UnitChecks`; the executables `lean2agda`, `atlas`, `unittests`, `naming-check-atlas` and `naming-atlas-probe`; the test driver; the requirements |
| `translator/VERSION` | the translator's version, one line |

## The version

`translator/VERSION` holds the translator's version, `MAJOR.MINOR.PATCH`,
as follows:

+  it stays below `1.0.0` until the first generated library is released
   (issue M5-6, [#48]), and is `1.0.0` from then;
+  it moves when a generated library must tell two translators apart:
   before a library is generated by a translator whose output differs from
   the last version's, the minor version goes up if what the translator
   emits or accepts changed, and the patch version otherwise;
+  between bumps, each pull request that changes the translator adds its
   line to the newest entry of `CHANGELOG.md`, at the repository's root,
   which has one entry per version, newest first; a bump opens a new
   entry.

No library is generated before Milestone 5, so every pull request so far
is under `0.1.0`.

`lean2agda --version` prints it.  `translator/Main.lean` reads the file at
build time with `include_str`, and the executable's `needs` names the
package's `[[input_file]]` target `version`, which Lake hashes, so that a
change to the file rebuilds the root and reaches `--version`: without it
Lake tracks no file `include_str` reads.  `run.sh` checks that the
executable's `--version` names the file's version, and the Python suite
that the file and the changelog's newest entry agree.

The version is not written into the scaffold, the sidecars or any other
output, since every golden file would change at every release.  It belongs
in the provenance record of a generated library (issue M5-5, [#47]), which
reads this file: the Lean version, the Mathlib revision, the translator's
version and the profile, in the library's `NOTICE` and README
([`../licensing.md`][licensing], "Generated libraries").

[#47]: https://github.com/formalverification/lean2agda/issues/47
[#48]: https://github.com/formalverification/lean2agda/issues/48

[pipeline]: ../architecture.md
[loading]: loading.md
[naming]: naming.md
[printing]: printing.md
[inductives]: inductives.md
[translator-readme]: ../../translator/README.md
[atlas]: ../../atlas/README.md
[findings]: ../lean-findings.md
[licensing]: ../licensing.md
