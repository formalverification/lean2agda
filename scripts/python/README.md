<!-- File: scripts/python/README.md -->

# scripts/python

Stdlib-only Python for the project's plumbing.  The scripts are as
follows:

+  `corpus_check.py` (issue M1-6): validates `corpus/manifest.json` and
   type-checks every translated corpus entry; run by `make corpus-check`.
   `corpus_manifest.py` holds the manifest's rules and `agda_run.py` the
   call to Agda, which issue M2-8's `agda_check.py` is to reuse.
+  `atlas_report.py` (issue M1-11) and `agda_check.py` (issue M2-8) are
   planned.

`_utils/` is the utilities package, copied from agda-algebras (each
file's header says from where and what changed): `Result` and
`PipelineError` in `pipeline_types.py`, filesystem wrappers in
`file_ops.py`, and `run_command` in `command_runner.py`.  Use it rather
than calling `open`, `shutil` or `subprocess` directly, and put a new
general helper there.  Two of its behaviors surprise: `is_ok` and
`is_err` are properties, not methods, and `unwrap` treats
`Result.ok(None)` as an error, so a function whose `Result` may be
unwrapped returns a value, never `None`.

House style, which applies to every file here, is as follows:

+  total functions, with `Result` values instead of exceptions for
   control flow;
+  frozen dataclasses and type annotations everywhere;
+  a `File:` header docstring stating the file's path and purpose;
+  a test for every pure function, under `tests/`, run by `make test`
   (`python3 -m unittest discover -s scripts/python/tests -t scripts/python`);
   a test never runs Agda, whose call is injected;
+  no third-party packages.
