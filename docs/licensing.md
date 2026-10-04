<!-- File: docs/licensing.md -->

# Licensing

Decided 2026-10-04 (issue M1-13).

## The translator and this repository

Apache License, Version 2.0 (`LICENSE`, with `NOTICE`).  The reasons are
as follows:

+  Lean, Mathlib, lean4export, lean2dk and lyphyser's lean2agda are
   Apache-2.0, so code adapted from any of them can be carried under the
   same terms;
+  the generated libraries must be Apache-2.0 in any case (below), and
   one license across the project is simpler to state and to audit.

The repository was created from the github-project template under MIT;
the switch happened before any release, so no MIT-licensed version was
ever published.

## Generated libraries

A library generated from Mathlib is a derived work of Mathlib, which is
Apache-2.0.  Every generated library repository carries the following:

+  `LICENSE`: the Apache License, Version 2.0;
+  `NOTICE`: Mathlib's copyright line, the lean2agda line, and the
   provenance record (Lean version, Mathlib revision, translator
   version, profile, date) that the pipeline writes;
+  a README section stating that statements and proofs originate in
   Mathlib and were translated mechanically, with the translator's
   version.

The same rule applies to any other Lean library translated later, with
that library's license in place of Mathlib's; a library under a license
incompatible with Apache-2.0 is not translated until the question is
settled with its authors.

## Code adapted from predecessors

Code adapted from another project keeps that project's copyright notice
in the file's header comment, names the source repository and commit,
and is listed in `NOTICE`.  Lean4Less and Predicativize declare no
license, so they are used as external tools and never copied; issue
M1-14 asks their authors for a license.
