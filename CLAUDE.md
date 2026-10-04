<!-- File: CLAUDE.md -->

# CLAUDE.md: lean2agda

Guidance for Claude Code working in this repository.  lean2agda is a
Lean 4 to Agda translator and the Agda libraries it produces: a
translator written in Lean over the elaborated Lean environment, a
corpus of Mathlib declarations translated by hand that the translator
must reproduce, an atlas of what every Mathlib declaration depends on,
and the documentation of what Lean's type theory has that Agda's does
not.  The roadmap is `docs/GITHUB_PROJECT.md`; read its Description
section before changing anything structural.

## Build, check, and test

+  Enter the toolchain with `nix develop`; `flake.lock` pins Agda 2.8.0
   with agda-stdlib 2.3 and cubical 0.9, the Lean toolchain named in
   `lean-toolchain`, Python 3, `gh`, and the github-project engine.
   Never assume a system Agda or Lean.  `nix develop .#agda` and
   `nix develop .#lean` are the single-tool shells.
+  `make doctor` prints the tool versions and fails if Agda cannot
   resolve the standard library and the cubical library.
+  Type-check one Agda file inside the shell with `agda path/File.agda`;
   the shell's `agda` is a wrapper that passes the project-local
   `--library-file`, so a bare system `agda` would see no libraries.
+  `make help` lists every target.  `make check`, `make test`,
   `make corpus-check` and `make atlas` are placeholders until the issues
   that implement them land (M1-6, M1-11, M2-1, M2-8); each says so.
+  Mathlib's prebuilt `.olean` files come from `lake exe cache get`
   inside `translator/` once the Lake package exists (M1-3); never
   rebuild Mathlib from source.
+  Do not commit generated artifacts: `*.agdai`, `.agda/`, `.lake/`,
   `result`, and anything the translator emits.  Generated libraries
   live in their own repositories (see the roadmap's Description).

## The roadmap file

`docs/GITHUB_PROJECT.md` is the single source of truth for project
STRUCTURE (milestones, labels, issue definitions, prose, dependency
graphs); GitHub owns STATE (issue numbers, open or closed, assignees).
Two commands move information between them, as follows:

+  `make populate` (file to GitHub) creates labels, milestones and
   issues and writes each new issue number back into the file.  It is
   idempotent.
+  `make update` (GitHub to file) rewrites only the regions between
   `<!-- BEGIN GENERATED -->` and `<!-- END GENERATED -->` markers;
   prose outside them is preserved byte for byte.

Edit prose in the file; edit the body of an already-created issue on
GitHub; never strip the `[MN-k]` prefix from an issue title on GitHub.
`make lint` checks the file's structure without network and must pass
before any pull request.  The committed skills `project-setup` and
`roadmap-upkeep` under `.claude/skills/` cover both workflows.

## Repository architecture

+  `translator/`: the Lean 4 package (a Lake project) that reads the
   elaborated environment and emits Agda; pure translation core, IO at
   the edges.
+  `corpus/`: Mathlib declarations translated by hand, one directory per
   entry with the Lean statement and exported term, the idiomatic Agda,
   and notes; the translator's test oracle.
+  `atlas/`: per-declaration records of axioms, computability and kernel
   features, as NDJSON, with their schema.
+  `scripts/python/`: stdlib-only Python for checking the corpus,
   reporting on the atlas and driving Agda; every pure function has a
   test.
+  `docs/`: the roadmap, the design records under `docs/adr/`, the
   foundational notes under `docs/foundations/`, and the engine's
   command reference `docs/HowToRun.md`.

## Conventions

+  Python follows the functional house style: total functions, `Result`
   values rather than exceptions for control flow, frozen dataclasses,
   type annotations everywhere, a `File:` header docstring in every
   file, and a test for every pure function.
+  Lean code keeps a pure core with IO at the edges, a `File:` header
   comment in every file, and small named definitions over large ones.
+  Agda in the corpus declares its flags in an `OPTIONS` pragma; the
   default is `--safe --cubical-compatible`, with `--safe --cubical
   --guardedness` for the cubical variants (see the gotcha below).
   Emitted Agda targets Agda 2.8.0.
+  Design decisions are ADRs under `docs/adr/`: a plain title, an
   executive summary, one section per decision area with Decision,
   Evidence and Status, a numbered decision log, reference-style links,
   and a companion note beside the component the record is about.
+  Markdown: `+` bullets in prose files, wrapped at about 80 columns;
   GitHub issue and PR bodies are not hard-wrapped, and issue numbers in
   them are written as reference links `[#N]`.  Two spaces after a
   sentence-ending period.  No em-dashes in prose (the roadmap's
   `### Milestone N — Title` headings and label entries are the engine's
   grammar, not prose).  American spelling.  Never bold punctuation.
+  Git identity is the human author's; provenance of AI-assisted
   changes goes in a line of the commit body, never in a trailer.

## Environment gotchas

+  lean4-nix lags Lean releases by about one version; `lean-toolchain`
   names the newest version it carries.  Pinning Mathlib means pinning
   the Mathlib tag that matches that Lean version, not master.
+  The Nix shellHook rewrites `.agda/libraries` on every entry; it is
   gitignored.  Set `AGDA_UNIMATH_ROOT`, `AGDA_TYPETOPOLOGY_ROOT` or
   `AGDA_ALGEBRAS_ROOT` before entering the shell to register those
   libraries too.
+  A file that imports the cubical library must enable `--guardedness`:
   the library's own `.agda-lib` flags include it, and Agda treats it as
   infective, so `{-# OPTIONS --safe --cubical #-}` alone fails with
   `InfectiveImport` on the first `Cubical.*` import.
+  In GitHub Actions, set `NO_ENV_PREFIX=1` on engine invocations: the
   engine strips `GH_TOKEN` by default, which is how Actions
   authenticates.
