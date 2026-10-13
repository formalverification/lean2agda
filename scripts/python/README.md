<!-- File: scripts/python/README.md -->

# scripts/python

Stdlib-only Python for the project's plumbing.  The scripts are as
follows:

+  `corpus_check.py` (issue M1-6): validates `corpus/manifest.json` and
   type-checks every translated corpus entry; run by `make corpus-check`.
   `corpus_manifest.py` holds the manifest's rules and `agda_run.py` the
   call to Agda, which issue M2-8's `agda_check.py` is to reuse.
+  `corpus_tables.py` (issue M1-10): prints the corpus's tables from the
   manifest and the entries' files (the coverage of the gap catalog's
   features, the matrix of entries against features, and the sizes of
   each export and Agda file), which `corpus/README.md` and
   `docs/foundations/gap-report-corpus.md` carry; run by
   `make corpus-tables`.
+  `atlas_report.py` (issue M1-11): reads the records `lake exe atlas`
   writes and writes the atlas's report under `docs/reports/`, checking
   them against `corpus/manifest.json`; run by `make atlas`.
+  `scaffold_check.py` (issue M2-3): type-checks a profile U scaffold
   that `lake exe lean2agda --out` writes, turning a refused definition
   into a postulate and dropping a refused type with its dependents until
   the rest checks, and lists the refusals; the translator's harness
   compares the listings with golden ones.
+  `agda_check.py` (issue M2-8) is planned.

`_utils/` is the utilities package, copied from agda-algebras (each
file's header says from where and what changed): `Result` and
`PipelineError` in `pipeline_types.py`, filesystem wrappers in
`file_ops.py`, and `run_command` in `command_runner.py`.  Use it rather
than calling `open`, `shutil` or `subprocess` directly, and put a new
general helper there.  One of its behaviors surprises: `is_ok` and
`is_err` are properties, not methods.  The copies in agda-algebras and
agda-native-air also have `unwrap` treat `Result.ok(None)` as an error;
this copy fixed that, with the other defects its files' headers name,
so a `Result` may hold `None` here.

House style, which applies to every file here, is as follows:

+  total functions, with `Result` values instead of exceptions for
   control flow;
+  frozen dataclasses and type annotations everywhere;
+  a `File:` header docstring stating the file's path and purpose;
+  a test for every pure function, under `tests/`, run by `make test`
   (`python3 -m unittest discover -s scripts/python/tests -t scripts/python`);
   a test never runs Agda, whose call is injected;
+  no third-party packages.
