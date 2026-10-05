<!-- File: scripts/python/README.md -->

# scripts/python

Stdlib-only Python for the project's plumbing, none of it written yet.
The planned scripts check the corpus (`corpus_check.py`, issue M1-6),
report on the atlas (`atlas_report.py`, issue M1-11), and drive Agda
over emitted modules (`agda_check.py`, issue M2-8).

House style, which applies to every file here, is as follows:

+  total functions, with `Result` values instead of exceptions for
   control flow;
+  frozen dataclasses and type annotations everywhere;
+  a `File:` header docstring stating the file's path and purpose;
+  a test for every pure function, under `tests/`, run by `make test`;
+  no third-party packages.
