"""
File: scripts/python/agda_run.py

Description:
  Run Agda on one file and classify what happened.

  Agda runs as `agda <file>` from a given directory, with no flags of
  this module's own: a file checks under the flags its OPTIONS pragma
  declares, and sees the libraries the Nix shell's agda wrapper
  registers (a file outside any .agda-lib project sees them through the
  `defaults` file the shell writes).  The call to Agda and the clock are
  injected, so the classification is tested without Agda.

  The corpus checker (corpus_check.py) runs every file of every
  translated entry through check_file; the driver of issue M2-8
  (agda_check.py) is meant to reuse it for emitted modules.

Design Principles:
  - The edge is check_file: one call of the runner, timed by the clock.
  - Everything it returns is a FileRun built by the pure classify.
  - Agda 2.8 prints its errors on standard output and exits with status
    42; standard error stays empty.  The output is therefore read from
    the error's "stdout" context, which command_runner keeps.
"""
from __future__ import annotations

import re
import subprocess
import time
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Callable, Optional, Sequence

from _utils.command_runner import run_command
from _utils.pipeline_types import ErrorType, PipelineError, Result

# The command, the directory it runs in, and the timeout in seconds.
Runner = Callable[
    [Sequence[str], Path, float],
    Result[subprocess.CompletedProcess, PipelineError],
]
Clock = Callable[[], float]


class Outcome(Enum):
    """How one run of Agda on one file ended."""

    PASS = "pass"
    FAIL = "fail"
    TIMEOUT = "timeout"


@dataclass(frozen=True)
class FileRun:
    """The result of checking one file.

    `message` is empty on a pass; otherwise it names the failure in one
    line.  `output` is Agda's whole output on a failure, for the reader
    of a CI log, and empty on a pass.
    """

    path: str
    outcome: Outcome
    seconds: float
    message: str
    output: str


def run_agda(
    command: Sequence[str], cwd: Path, timeout: float
) -> Result[subprocess.CompletedProcess, PipelineError]:
    """The real runner: command_runner, capturing text, with a timeout."""
    return run_command(
        list(command), cwd=cwd, capture_output=True, text=True, timeout=timeout
    )


# An Agda error line: "<path>:<range>: error: [Name]", or a bare
# "error: ..." when no file position applies.
_ERROR_LINE = re.compile(r"(^|: )error: ")
# A leading path ending in a .agda file name.
_PATH_PREFIX = re.compile(r"^(?:.*/)?([^/\s]+\.agda)(?=:)")


def shorten_path(line: str) -> str:
    """Drop the directory part of the .agda path an error line starts
    with, so that a table row does not carry an absolute path."""
    return _PATH_PREFIX.sub(r"\1", line, count=1)


def first_error(output: str) -> Optional[str]:
    """The first line of Agda's output that reports an error, shortened;
    None when no line does."""
    lines = (line.strip() for line in output.splitlines())
    return next(
        (shorten_path(line) for line in lines if _ERROR_LINE.search(line)), None
    )


def classify(
    path: str,
    result: Result[subprocess.CompletedProcess, PipelineError],
    seconds: float,
) -> FileRun:
    """Turn the runner's result into a FileRun."""
    if result.is_ok:
        return FileRun(path, Outcome.PASS, seconds, "", "")
    error = result.unwrap_err()
    output = str(error.context.get("stdout", ""))
    if error.error_type == ErrorType.TIMEOUT:
        return FileRun(path, Outcome.TIMEOUT, seconds, error.message, output)
    message = first_error(output) or error.message
    return FileRun(path, Outcome.FAIL, seconds, message, output)


def check_file(
    runner: Runner,
    clock: Clock,
    agda: str,
    cwd: Path,
    path: str,
    timeout: float,
) -> FileRun:
    """Run `agda path` in cwd through the runner and classify it."""
    start = clock()
    result = runner((agda, path), cwd, timeout)
    return classify(path, result, clock() - start)


def real_clock() -> float:
    """The clock check_file uses outside the tests."""
    return time.monotonic()
