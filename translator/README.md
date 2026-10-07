<!-- File: translator/README.md -->

# translator

The Lean 4 package that reads the elaborated Lean environment and emits
Agda.  Issue M1-3 created it as a Lake package, `lean2agda`, that
requires Mathlib and lean4export at pinned tags; issue M2-1 adds the
command line, the environment loader and the golden-test harness.  The
architecture it implements is described in the Description section of
`../docs/GITHUB_PROJECT.md` and, once written, in `../docs/architecture.md`.

## Layout

+  `lakefile.toml`: the package, its one library `Lean2Agda`, and its
   two requirements, Mathlib (tag v4.33.1) and lean4export (tag
   v4.33.0).
+  `lake-manifest.json`: the commit each requirement resolved to,
   Mathlib's own dependencies included; committed, never edited by hand.
+  `lean-toolchain`: a symlink to `../lean-toolchain`, so that the flake,
   `elan` and Mathlib's cache tool read one pin.
+  `Lean2Agda.lean`: the library's root module, empty until M2-1.
+  `scripts/Smoke.lean`: a standalone check that Mathlib's `.olean`
   files load.

What each pin is and how to move it is in `../docs/pinning.md`.

## Using it

Every command runs inside the Nix shell (`nix develop`, or
`nix develop --command ...`) and, for `lake`, from this directory.  A
fresh checkout needs the following, once:

```sh
lake update --keep-toolchain   # clone Mathlib and lean4export into .lake/packages/
lake exe cache get             # fetch Mathlib's prebuilt .olean files
lake build                     # build the Lean2Agda library
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

## Conventions

Conventions for everything that lands here are as follows:

+  a pure translation core with IO at the edges;
+  a `File:` header comment in every file;
+  small named definitions over large ones;
+  a golden test for every translation feature, under `tests/`.
