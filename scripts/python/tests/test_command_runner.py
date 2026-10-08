"""
File: scripts/python/tests/test_command_runner.py

Description:
  Tests of the two edits lean2agda made to _utils/command_runner.py: the
  timeout, which turns an expired command into an error value, and the
  standard output kept in the error of a failed command.  They run the
  current Python interpreter as the command, never Agda.
"""
from __future__ import annotations

import sys
import unittest

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


class TestAsText(unittest.TestCase):
    def test_none_bytes_and_text(self) -> None:
        self.assertEqual(_as_text(None), "")
        self.assertEqual(_as_text(b"caf\xc3\xa9"), "café")
        self.assertEqual(_as_text("text"), "text")


if __name__ == "__main__":
    unittest.main()
