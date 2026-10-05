<!-- File: translator/README.md -->

# translator

The Lean 4 package that reads the elaborated Lean environment and emits
Agda.  It does not exist yet: issue M1-3 creates the Lake project with
Mathlib as a pinned dependency, and issue M2-1 adds the command line,
the environment loader and the golden-test harness.  The architecture
it implements is described in the Description section of
`../docs/GITHUB_PROJECT.md` and, once written, in `../docs/architecture.md`.

Conventions for everything that lands here are as follows:

+  a pure translation core with IO at the edges;
+  a `File:` header comment in every file;
+  small named definitions over large ones;
+  a golden test for every translation feature, under `tests/`.
