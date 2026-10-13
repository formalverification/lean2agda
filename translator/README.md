<!-- File: translator/README.md -->

# translator

The Lean 4 package that reads the elaborated Lean environment and emits
Agda.  Issue M1-3 created it as a Lake package, `lean2agda`, that
requires Mathlib and lean4export at pinned tags; issue M1-11 added the
axiom atlas; issue M2-1 added the translator's command line, the
environment loader and the golden-test harness; issue M2-2 added structured
name encoding, module paths, and reverse-map sidecars; issue M2-3 added the
expression printer, the sharing pass, and the profile U scaffold
(`../docs/translator/printing.md`); and issue M2-4 adds the inductive
types, as records and data types (`../docs/translator/inductives.md`).  The
architecture it implements is described in the Description section of
`../docs/GITHUB_PROJECT.md` and in `../docs/architecture.md`, the companion
note of ADR 0001 (`../docs/adr/0001-translation-architecture.md`).

## Layout

+  `lakefile.toml`: the package, its libraries `Lean2Agda` and `Atlas`,
   the executables `lean2agda` and `atlas`, and its two requirements,
   Mathlib (tag
   v4.33.1) and lean4export (tag v4.33.0).
+  `lake-manifest.json`: the commit each requirement resolved to,
   Mathlib's own dependencies included; committed, never edited by hand.
+  `lean-toolchain`: a symlink to `../lean-toolchain`, so that the flake,
   `elan` and Mathlib's cache tool read one pin.
+  `Lean2Agda.lean`: the translator library's root module.
+  `Lean2Agda/Core/`: pure declaration types, command-line parsing,
   dependency closure and ordering, diagnostic rendering, statistics,
   name encoding, module paths, reverse maps, the expression printer
   (`Print.lean`), the sharing pass (`Share.lean`), the inductive types'
   shapes (`InductiveShape.lean`) and declarations (`Inductive.lean`), and
   the scaffold (`Scaffold.lean`).
+  `Lean2Agda/Main.lean`: the IO shell, which loads compiled modules and
   writes the closure listing, the reverse-map sidecars, and the scaffold.
+  `tests/`: compiled Lean inputs, semantic checks, atlas and golden
   fixtures, the printer's checks (`Printing.lean`), the inductive types'
   checks (`Inductives.lean`), golden scaffolds (`expected/scaffolds/`),
   and the shell harness.
+  `Atlas/`: the axiom atlas (`../atlas/README.md`).  `Record.lean`
   and `Graph.lean` are the pure core (the record and its line, the
   dependency graph and the exact axiom sets), `AutoDecl.lean` is
   Batteries' test for auto-generated declarations, `Collect.lean`
   reads a constant's record from an environment, and `Main.lean` is
   the executable: it imports Mathlib when it runs, so the library
   imports Lean only and building it never needs Mathlib's modules.
+  `scripts/Smoke.lean`: a standalone check that Mathlib's `.olean`
   files load.
+  `scripts/InductiveTypes.lean`: the inductive types of a module's
   closure or of a set of modules, one name per line, as roots for a
   scaffold that declares them all.

What each pin is and how to move it is in `../docs/pinning.md`.

## Using it

Every command runs inside the Nix shell (`nix develop`, or
`nix develop --command ...`) and, for `lake`, from this directory.  A
fresh checkout needs the following, once:

```sh
lake update --keep-toolchain   # clone Mathlib and lean4export into .lake/packages/
lake exe cache get             # fetch Mathlib's prebuilt .olean files
lake build                     # build the libraries and executables
```

`lake update` is the only command that populates `.lake/packages/` the
first time; `lake build` without it stops with "missing manifest".
Always pass `--keep-toolchain`, or Lake may rewrite the repository's
`lean-toolchain` through the symlink (`../docs/pinning.md` says what
happens then).  Mathlib's post-update hook runs `lake exe cache get`
itself, so the second command finds nothing left to fetch unless the
first was interrupted; it resumes an interrupted fetch.  Never build
Mathlib from source: if the cache tool reports files missing for the
pinned tag, stop and say so.

The `.olean` files land under `.lake/packages/*/.lake/build/`
(gitignored, several gigabytes); the compressed downloads stay in
`~/.cache/mathlib/`, shared by every checkout on the machine.  The cache
tool downloads with the shell's `curl`.

From the repository root the same steps are `make lean-cache`,
`make lean-build` and `make lean-smoke`.  The last checks the cache:
`lake build --no-build Mathlib` compiles nothing and fails (status 3)
if Lake finds any Mathlib module out of date, and
`lake env lean scripts/Smoke.lean` then prints the axioms of one Mathlib
theorem and one core theorem.  The exporter runs as follows:

```sh
lake exe lean4export Mathlib.Data.Finset.Card -- Finset.card_image_of_injective > out.ndjson
```

The translator's command line is as follows:

```sh
lake exe lean2agda --profile U --out out Init.Data.Nat.Gcd -- Nat.gcd_self
lake exe lean2agda --stats Init.Data.Nat.Gcd -- Nat.gcd_self
```

It prints an ordered closure of Lean declarations.  `--out DIR` also
writes the listing to `DIR/closure.txt`, a `.names.ndjson` sidecar per
source module under the supplied `--root NAME` (default `U`), and the
profile U scaffold, an Agda module declaring the closure's constants with
their printed types; `--share N` sets the sharing pass's threshold.  The
naming API and sidecar schema are in [`naming.md`], and the printer, the
sharing pass and the scaffold in [`printing.md`].  `--stats` appends
counts to standard output.  Omit declarations after `--` to select all
declarations owned by the named modules.  Only profile U is available.
The closure API, dependencies, cycle handling, and output format are in
[`loading.md`].

Run `make test-translator` from the repository root, or
`bash tests/run.sh` here.  It builds core Lean fixtures, checks the pure
core, and diffs three golden outputs, including `Nat.gcd_self` and the
names owned by `Init.Data.Nat.Gcd`.  It also checks reverse maps and
generated lexical fixtures with Agda.  It needs
no Mathlib cache; Lake still clones the source dependencies named in the
manifest on a fresh checkout.  `make test` includes both this harness and
the Python suite; `make test-python` runs the Python suite alone.

The atlas runs as `lake exe atlas` (or `make atlas` from the root,
which also writes its report); `lake exe atlas --import MODULE --out
FILE` writes the records of a smaller environment.

`make test-naming-atlas ATLAS=atlas/mathlib-v4.33.1-0df444a.ndjson`, from
the repository root, checks injectivity over the atlas without loading
Mathlib.  The optional `lake exe naming-atlas-probe` compares the atlas
decoder with the original structured names in the pinned environment;
it needs the prebuilt Mathlib cache.

## Conventions

Conventions for everything that lands here are as follows:

+  a pure translation core with IO at the edges;
+  a `File:` header comment in every file;
+  small named definitions over large ones;
+  a golden test for every translation feature, under `tests/`.

[`loading.md`]: ../docs/translator/loading.md
[`naming.md`]: ../docs/translator/naming.md
[`printing.md`]: ../docs/translator/printing.md
