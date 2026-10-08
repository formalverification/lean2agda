"""
File: scripts/python/_utils/command_runner.py

Description:
  Functional command execution utilities for the build pipeline.

Provenance:
  Copyright 2025-2026 William DeMeo and Contributors (agda-native-air);
  Copyright 2018-2026 The agda-algebras development team.  Licensed
  under the Apache License, Version 2.0.

  Adapted from formalverification/agda-native-air/ at SHA 664b919.
  Copied into lean2agda from ualib/agda-algebras, scripts/python/_utils/,
  at commit ee830be.  lean2agda added the timeout parameter, and keeps
  the captured standard output in the error of a failed command (Agda
  prints its errors there, not on standard error).  It also fixed two
  defects of the copy: streaming read standard output to its end before
  standard error, which deadlocks once the command fills the standard
  error pipe, and left both pipes open; and capture_output=False still
  captured standard output.  See NOTICE.
"""
from __future__ import annotations
import subprocess
import logging
import threading
from pathlib import Path
from typing import IO, Callable, List, Optional, Union

from .pipeline_types import Result, PipelineError, ErrorType

def run_command(
    command: List[str],
    cwd: Optional[Path] = None,
    capture_output: bool = False,
    text: bool = False,
    stdout_file: Optional[Path] = None,
    stream_output: bool = False,  # --- NEW: Parameter to enable live streaming
    timeout: Optional[float] = None,
) -> Result[subprocess.CompletedProcess, PipelineError]:
    """
    Runs a shell command and returns a Result object.
    Can either capture output or stream it live to the logger.

    Standard output is captured when capture_output is set, written to
    stdout_file when one is given, and otherwise inherited from this
    process; standard error is always captured.

    With a timeout (seconds; capturing mode only), a command still
    running when it expires is killed and the result is an error of type
    ErrorType.TIMEOUT, never an exception.
    """
    command_str = ' '.join(map(str, command))
    logging.debug(f"Running: {command_str}")

    try:
        # --- NEW: Logic to handle live streaming output ---
        if stream_output:
            # Use Popen for live output streaming; as a context manager it
            # closes both pipes and waits for the command on the way out.
            with subprocess.Popen(
                [str(arg) for arg in command],
                cwd=cwd,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding='utf-8'
            ) as process:
                # Log stdout and stderr line by line, draining standard error
                # on a thread while this one reads standard output.  Reading
                # one stream to its end before the other deadlocks as soon as
                # the command fills the other's pipe (64 KiB on Linux): the
                # command blocks writing it, and this process blocks waiting
                # for the first stream to close.
                drain = threading.Thread(
                    target=_log_lines, args=(process.stderr, logging.warning, "  ! "), daemon=True
                )
                drain.start()
                _log_lines(process.stdout, logging.info, "  > ")

                # Wait for the process to complete and get the return code
                process.wait()
                drain.join()
            if process.returncode != 0:
                 return Result.err(PipelineError(
                    error_type=ErrorType.COMMAND_FAILED,
                    message=f"Streamed command failed with exit code {process.returncode}",
                    context={"command": command_str, "return_code": process.returncode}
                ))
            # Return a CompletedProcess-like object on success
            return Result.ok(subprocess.CompletedProcess(
                args=command, returncode=0, stdout="", stderr=""
            ))

        # --- Original logic for capturing output ---
        else:
            stdout_target = subprocess.PIPE if capture_output else None
            if stdout_file:
                stdout_file.parent.mkdir(parents=True, exist_ok=True)
                stdout_target = open(stdout_file, "w", encoding="utf-8")

            process = subprocess.run(
                [str(arg) for arg in command],
                cwd=cwd, stdout=stdout_target, stderr=subprocess.PIPE,
                text=text, check=False, encoding='utf-8' if text else None,
                timeout=timeout
            )

            if process.stderr:
                logging.debug(f"Stderr for '{command_str}':\n{process.stderr}")
            if process.returncode != 0:
                return Result.err(PipelineError(
                    error_type=ErrorType.COMMAND_FAILED,
                    message=f"Command failed with exit code {process.returncode}",
                    context={
                        "command": command_str,
                        "return_code": process.returncode,
                        "stderr": process.stderr.strip() if process.stderr else "N/A",
                        "stdout": _as_text(process.stdout),
                        "cwd": str(cwd) if cwd else "N/A"
                    }
                ))
            return Result.ok(process)

    except subprocess.TimeoutExpired as e:
        return Result.err(PipelineError(
            error_type=ErrorType.TIMEOUT,
            message=f"Command timed out after {timeout:g} seconds",
            context={
                "command": command_str,
                "timeout": timeout,
                "stdout": _as_text(e.stdout),
                "cwd": str(cwd) if cwd else "N/A"
            },
            cause=e
        ))
    except FileNotFoundError as e:
        return Result.err(PipelineError(
            error_type=ErrorType.COMMAND_FAILED,
            message=f"Command not found: {command[0]}",
            cause=e
        ))
    except Exception as e:
        return Result.err(PipelineError(
            error_type=ErrorType.COMMAND_FAILED,
            message=f"An unexpected error occurred running command: {e}",
            cause=e
        ))
    finally:
        if not stream_output and stdout_file and 'stdout_target' in locals() and stdout_target:
            if not isinstance(stdout_target, int): # Not a PIPE
                 stdout_target.close()


def _as_text(output: Optional[Union[str, bytes]]) -> str:
    """Captured output as text: TimeoutExpired carries bytes even when
    the command ran in text mode, and an uncaptured stream is None."""
    if output is None:
        return ""
    if isinstance(output, bytes):
        return output.decode("utf-8", errors="replace")
    return output


def _log_lines(stream: Optional[IO[str]], log: Callable[[str], None], prefix: str) -> None:
    """Log each line of a text stream until it closes."""
    if stream is None:
        return
    for line in iter(stream.readline, ''):
        log(f"{prefix}{line.strip()}")
