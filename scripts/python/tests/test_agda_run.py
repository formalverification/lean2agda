"""
File: scripts/python/tests/test_agda_run.py

Description:
  Tests of agda_run.py.  The classification is tested on runner results
  built by hand, shaped like the ones command_runner returns (measured
  with Agda 2.8.0: errors on standard output, exit status 42), and
  check_file with a fake runner and a fake clock.
"""
from __future__ import annotations

import subprocess
import unittest
from pathlib import Path
from typing import Sequence

from _utils.pipeline_types import ErrorType, PipelineError, Result
from agda_run import FileRun, Outcome, check_file, classify, first_error, shorten_path

AGDA_FAILURE = """Checking Bad (/tmp/x/agda/Bad.agda).
/tmp/x/agda/Bad.agda:6.7-11: error: [UnequalTerms]
0 != 1 of type ℕ
when checking that the expression refl has type zero ≡ 1
"""


def failed(stdout: str) -> Result[subprocess.CompletedProcess, PipelineError]:
    return Result.err(PipelineError(ErrorType.COMMAND_FAILED, "Command failed with exit code 42",
                                    context={"return_code": 42, "stdout": stdout}))


def passed() -> Result[subprocess.CompletedProcess, PipelineError]:
    return Result.ok(subprocess.CompletedProcess(["agda", "Good.agda"], 0, "Checking Good\n", ""))


class TestShortenPath(unittest.TestCase):
    def test_drops_directories(self) -> None:
        self.assertEqual(shorten_path("/a/b/Bad.agda:6.7-11: error: [X]"), "Bad.agda:6.7-11: error: [X]")

    def test_leaves_a_line_without_a_path(self) -> None:
        self.assertEqual(shorten_path("error: [LibraryError]"), "error: [LibraryError]")


class TestFirstError(unittest.TestCase):
    def test_finds_the_error_line(self) -> None:
        self.assertEqual(first_error(AGDA_FAILURE), "Bad.agda:6.7-11: error: [UnequalTerms]")

    def test_bare_error(self) -> None:
        self.assertEqual(first_error("Checking X\nerror: [LibraryError] no such library\n"),
                         "error: [LibraryError] no such library")

    def test_none_without_an_error_line(self) -> None:
        self.assertIsNone(first_error("Checking Good (/tmp/Good.agda).\n"))

    def test_a_word_containing_error_is_not_an_error_line(self) -> None:
        self.assertIsNone(first_error("module NoErrors where\n"))


class TestClassify(unittest.TestCase):
    def test_pass(self) -> None:
        self.assertEqual(classify("Good.agda", passed(), 1.5),
                         FileRun("Good.agda", Outcome.PASS, 1.5, "", ""))

    def test_fail_names_the_first_error(self) -> None:
        run = classify("Bad.agda", failed(AGDA_FAILURE), 2.0)
        self.assertEqual(run.outcome, Outcome.FAIL)
        self.assertEqual(run.message, "Bad.agda:6.7-11: error: [UnequalTerms]")
        self.assertEqual(run.output, AGDA_FAILURE)

    def test_fail_without_output_uses_the_error_message(self) -> None:
        missing = Result.err(PipelineError(ErrorType.COMMAND_FAILED, "Command not found: agda"))
        run = classify("Bad.agda", missing, 0.0)
        self.assertEqual((run.outcome, run.message, run.output),
                         (Outcome.FAIL, "Command not found: agda", ""))

    def test_timeout(self) -> None:
        expired = Result.err(PipelineError(ErrorType.TIMEOUT, "Command timed out after 300 seconds",
                                           context={"stdout": "Checking Slow\n"}))
        run = classify("Slow.agda", expired, 300.2)
        self.assertEqual((run.outcome, run.message), (Outcome.TIMEOUT, "Command timed out after 300 seconds"))


class TestCheckFile(unittest.TestCase):
    def test_runs_agda_on_the_file_alone_and_times_it(self) -> None:
        calls: list[tuple[tuple[str, ...], Path, float]] = []

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
            calls.append((tuple(command), cwd, timeout))
            return passed()

        ticks = iter([10.0, 13.25])
        run = check_file(runner, lambda: next(ticks), "agda", Path("/c/e/agda"), "E.agda", 60.0)
        # No flags and no library options: the file's pragma decides.
        self.assertEqual(calls, [(("agda", "E.agda"), Path("/c/e/agda"), 60.0)])
        self.assertEqual(run, FileRun("E.agda", Outcome.PASS, 3.25, "", ""))


if __name__ == "__main__":
    unittest.main()
