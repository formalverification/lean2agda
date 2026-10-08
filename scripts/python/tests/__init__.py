"""
File: scripts/python/tests/__init__.py

Description:
  The Python test suite, run from the repository root by `make test` as

    python3 -m unittest discover -s scripts/python/tests -t scripts/python

  The top-level directory scripts/python is put on sys.path, so the
  tests import the scripts (corpus_check, agda_run, ...) and the _utils
  package by their plain names.  No test runs Agda: the Agda call is
  injected, and the tests pass a fake runner and a fake clock.
"""
