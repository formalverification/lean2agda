"""
File: scripts/python/tests/test_command_runner.py

Description:
  Tests of the edits lean2agda made to _utils/command_runner.py: the
  timeout, which turns an expired command into an error value; the
  standard output kept in the error of a failed command; streaming that
  drains standard error while it reads standard output, so a command
  that fills the standard error pipe cannot deadlock it; and
  capture_output=False, which now leaves standard output uncaptured.
  They run the current Python interpreter as the command, never Agda.
"""
from __future__ import annotations

import logging
import sys
import tempfile
import threading
import unittest
from pathlib import Path

from _utils.command_runner import _as_text, run_command
from _utils.pipeline_types import ErrorType


class TestRunCommand(unittest.TestCase):
    def test_success_is_ok(self) -> None:
        result = run_command([sys.executable, "-c", "print('hi')"],
                             capture_output=True, text=True, timeout=30)
        self.assertTrue(result.is_ok)
        self.assertEqual(result.unwrap().stdout, "hi\n")

    def test_failure_keeps_stdout(self) -> None:
        result = run_command([sys.executable, "-c", "print('E: bad'); raise SystemExit(42)"],
                             capture_output=True, text=True, timeout=30)
        self.assertTrue(result.is_err)
        error = result.unwrap_err()
        self.assertEqual(error.error_type, ErrorType.COMMAND_FAILED)
        self.assertEqual(error.context["return_code"], 42)
        self.assertEqual(error.context["stdout"], "E: bad\n")

    def test_timeout_is_an_error_value(self) -> None:
        result = run_command([sys.executable, "-c", "import time; print('x', flush=True); time.sleep(30)"],
                             capture_output=True, text=True, timeout=0.5)
        self.assertTrue(result.is_err)
        error = result.unwrap_err()
        self.assertEqual(error.error_type, ErrorType.TIMEOUT)
        self.assertIn("0.5 seconds", error.message)

    def test_missing_command(self) -> None:
        result = run_command(["lean2agda-no-such-command"], capture_output=True, text=True)
        self.assertTrue(result.is_err)
        self.assertIn("Command not found", result.unwrap_err().message)


class TestStreaming(unittest.TestCase):
    """Run with logging off: the streamed lines would flood the output."""

    def setUp(self) -> None:
        logging.disable(logging.CRITICAL)

    def tearDown(self) -> None:
        logging.disable(logging.NOTSET)

    def test_a_full_stderr_pipe_does_not_deadlock(self) -> None:
        # A megabyte on standard error, far past the 64 KiB a Linux pipe
        # holds, before the command writes to standard output and exits.
        # Reading standard output to its end first waited forever here.
        child = "import sys; sys.stderr.write('e' * 1_000_000); sys.stderr.flush(); print('done')"
        results: list[object] = []
        worker = threading.Thread(
            target=lambda: results.append(run_command([sys.executable, "-c", child],
                                                      text=True, stream_output=True)),
            daemon=True,
        )
        worker.start()
        worker.join(timeout=60)
        self.assertFalse(worker.is_alive(), "run_command did not return: the pipes deadlocked")
        self.assertTrue(results[0].is_ok)  # type: ignore[attr-defined]

    def test_a_streamed_failure_is_an_error_value(self) -> None:
        r = run_command([sys.executable, "-c", "raise SystemExit(3)"], text=True, stream_output=True)
        self.assertTrue(r.is_err)
        self.assertEqual(r.unwrap_err().context["return_code"], 3)


class TestCaptureOutput(unittest.TestCase):
    def test_capture_output_false_leaves_stdout_uncaptured(self) -> None:
        r = run_command([sys.executable, "-c", "pass"], capture_output=False, text=True)
        self.assertIsNone(r.unwrap().stdout)

    def test_stdout_file_receives_the_output(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "sub" / "out.txt"
            r = run_command([sys.executable, "-c", "print('to the file')"], text=True, stdout_file=out)
            self.assertTrue(r.is_ok)
            self.assertEqual(out.read_text("utf-8"), "to the file\n")


class TestAsText(unittest.TestCase):
    def test_none_bytes_and_text(self) -> None:
        self.assertEqual(_as_text(None), "")
        self.assertEqual(_as_text(b"caf\xc3\xa9"), "café")
        self.assertEqual(_as_text("text"), "text")


if __name__ == "__main__":
    unittest.main()
