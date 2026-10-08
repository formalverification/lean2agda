"""
File: scripts/python/tests/test_pipeline_types.py

Description:
  Tests of the pure helpers of _utils/pipeline_types.py, the Result type
  and the immutable records the package copied from agda-algebras
  carries.  Two of them pin defects of the copy that lean2agda fixed:
  a successful Result holding None now unwraps to None (it raised), and
  a literate Markdown file, M.lagda.md, now counts as an Agda file (its
  Path.suffix is .md).
"""
from __future__ import annotations

import unittest
from pathlib import Path

from _utils.pipeline_types import (
    CommandResult, ErrorType, FileMetadata, PipelineError, PipelineState,
    PipelineStatistics, ProcessedFile, ProcessingStage, Result,
    collect_errors, sequence_results,
)

ERROR = PipelineError(ErrorType.FILE_NOT_FOUND, "missing")
META = FileMetadata(Path("M.agda"), ProcessingStage.SOURCE, 0.5, 10, "abc")


def processed(name: str) -> ProcessedFile:
    return ProcessedFile(Path("src") / name, Path("build") / name, META)


class TestResult(unittest.TestCase):
    def test_ok_and_err(self) -> None:
        ok: Result[int, PipelineError] = Result.ok(1)
        err: Result[int, PipelineError] = Result.err(ERROR)
        self.assertTrue(ok.is_ok and not ok.is_err)
        self.assertTrue(err.is_err and not err.is_ok)
        self.assertEqual(ok.unwrap(), 1)
        self.assertEqual(err.unwrap_err(), ERROR)
        self.assertRaises(ValueError, err.unwrap)
        self.assertRaises(ValueError, ok.unwrap_err)
        self.assertRaises(ValueError, Result.err, None)

    def test_a_success_holding_none_unwraps_to_none(self) -> None:
        none: Result[None, PipelineError] = Result.ok(None)
        self.assertTrue(none.is_ok)
        self.assertIsNone(none.unwrap())
        self.assertIsNone(none.unwrap_or(None))
        self.assertEqual(Result.ok(0).unwrap(), 0)

    def test_unwrap_or(self) -> None:
        self.assertEqual(Result.ok(1).unwrap_or(2), 1)
        self.assertEqual(Result.err(ERROR).unwrap_or(2), 2)

    def test_map(self) -> None:
        self.assertEqual(Result.ok(2).map(lambda x: x * 3).unwrap(), 6)
        self.assertEqual(Result.err(ERROR).map(lambda x: x * 3).unwrap_err(), ERROR)
        # An exception raised by the function becomes the error value.
        failed = Result.ok(1).map(lambda x: x // 0)
        self.assertIsInstance(failed.unwrap_err(), ZeroDivisionError)

    def test_map_err(self) -> None:
        self.assertEqual(Result.err(ERROR).map_err(lambda e: e.message).unwrap_err(), "missing")
        self.assertEqual(Result.ok(1).map_err(lambda e: e.message).unwrap(), 1)

    def test_and_then_and_flat_map(self) -> None:
        half = lambda x: Result.ok(x // 2) if x % 2 == 0 else Result.err(ERROR)  # noqa: E731
        self.assertEqual(Result.ok(8).and_then(half).and_then(half).unwrap(), 2)
        self.assertEqual(Result.ok(6).flat_map(half).flat_map(half).unwrap_err(), ERROR)
        self.assertEqual(Result.err(ERROR).and_then(half).unwrap_err(), ERROR)


class TestSequences(unittest.TestCase):
    def test_sequence_results(self) -> None:
        self.assertEqual(sequence_results([Result.ok(1), Result.ok(None), Result.ok(3)]).unwrap(),
                         [1, None, 3])
        self.assertEqual(sequence_results([Result.ok(1), Result.err(ERROR)]).unwrap_err(), ERROR)
        self.assertEqual(sequence_results([]).unwrap(), [])

    def test_collect_errors(self) -> None:
        self.assertEqual(collect_errors([Result.ok(1), Result.err(ERROR), Result.ok(None)]),
                         ([1, None], [ERROR]))


class TestPipelineError(unittest.TestCase):
    def test_with_context_returns_a_new_error(self) -> None:
        richer = ERROR.with_context(path="x")
        self.assertEqual(richer.context, {"path": "x"})
        self.assertEqual(ERROR.context, {})

    def test_str(self) -> None:
        self.assertEqual(str(ERROR), "FILE_NOT_FOUND: missing")
        self.assertEqual(str(ERROR.with_context(path="x")),
                         "FILE_NOT_FOUND: missing | Context: path=x")


class TestFiles(unittest.TestCase):
    def test_advanced_to(self) -> None:
        later = META.advanced_to(ProcessingStage.DEPLOYED)
        self.assertEqual(later.stage, ProcessingStage.DEPLOYED)
        self.assertEqual((later.relative_path, later.file_size), (META.relative_path, 10))
        self.assertEqual(META.stage, ProcessingStage.SOURCE)

    def test_at_stage(self) -> None:
        moved = processed("M.agda").at_stage(ProcessingStage.SNAPSHOT, Path("snap/M.agda"))
        self.assertEqual(moved.current_path, Path("snap/M.agda"))
        self.assertEqual(moved.metadata.stage, ProcessingStage.SNAPSHOT)
        self.assertEqual(moved.source_path, Path("src/M.agda"))

    def test_is_agda_file(self) -> None:
        for name in ("M.agda", "M.lagda", "M.lagda.md"):
            self.assertTrue(processed(name).is_agda_file, name)
        for name in ("M.md", "M.agdai", "M.lagda.txt"):
            self.assertFalse(processed(name).is_agda_file, name)

    def test_module_name(self) -> None:
        self.assertEqual(processed("M.lagda.md").module_name, "M")
        self.assertEqual(processed("M.agda").module_name, "M")


class TestState(unittest.TestCase):
    def test_statistics(self) -> None:
        stats = PipelineStatistics().add_file(0.5).add_file(0.25).add_error()
        self.assertEqual((stats.files_processed, stats.total_processing_time,
                          stats.errors_encountered), (2, 0.75, 1))
        self.assertEqual(PipelineStatistics().files_processed, 0)

    def test_state_updates_return_new_values(self) -> None:
        start = PipelineState()
        state = (start.add_file(processed("M.agda"))
                      .add_artifact("macros", Path("macros.json"))
                      .advance_to_stage(ProcessingStage.PREPROCESSED))
        self.assertEqual(state.statistics.files_processed, 1)
        self.assertEqual(state.artifacts, {"macros": Path("macros.json")})
        self.assertEqual(state.stage, ProcessingStage.PREPROCESSED)
        self.assertEqual((start.processed_files, start.artifacts), ((), {}))
        self.assertEqual(state.files_at_stage(ProcessingStage.SOURCE), [processed("M.agda")])
        self.assertEqual(state.files_at_stage(ProcessingStage.DEPLOYED), [])


class TestCommandResult(unittest.TestCase):
    def test_success_and_failure(self) -> None:
        good = CommandResult(("true",), 0)
        bad = CommandResult(("false",), 1, stdout="out", stderr="err")
        self.assertTrue(good.success and not good.failed)
        self.assertTrue(bad.failed and not bad.success)
        self.assertEqual(good.to_result().unwrap(), good)
        error = bad.to_result().unwrap_err()
        self.assertEqual(error.error_type, ErrorType.COMMAND_FAILED)
        self.assertEqual(error.context, {"command": "false", "stderr": "err", "stdout": "out"})


if __name__ == "__main__":
    unittest.main()
