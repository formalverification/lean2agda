"""
File: scripts/python/tests/test_corpus_check.py

Description:
  Tests of corpus_check.py: the pure fold, counts and formatting, and
  check_corpus end to end on a temporary corpus with a fake runner (an
  injected stand-in for the agda call, never Agda itself) and a fake
  clock.
"""
from __future__ import annotations

import io
import json
import os
import subprocess
import tempfile
import unittest
from contextlib import redirect_stderr
from pathlib import Path
from typing import Any, Sequence
from unittest import mock

from _utils.pipeline_types import ErrorType, PipelineError, Result
from agda_run import FileRun, Outcome
from corpus_check import (
    Report, Row, Summary, check_corpus, exit_status, failure_detail,
    file_record, fold_files, format_details, format_json, format_seconds,
    format_summary, format_table, format_text, main, malformed_row,
    parse_args, planned_row, result_cell, summarize,
)
from corpus_manifest import AgdaFile, Entry

CC = ("--safe", "--cubical-compatible")
CU = ("--safe", "--cubical", "--guardedness")
ENTRY = Entry("set-ext", "set extensionality", "Set.ext", "Mathlib.Data.Set.Defs",
              ("propext", "Quot.sound"), "T1", ("axioms",),
              (AgdaFile("SetExt.agda", CC, "CC"), AgdaFile("SetExtCubical.agda", CU, "CU")),
              "translated", 8)
PASS_A = FileRun("SetExt.agda", Outcome.PASS, 1.25, "", "")
FAIL_B = FileRun("SetExtCubical.agda", Outcome.FAIL, 2.0,
                 "SetExtCubical.agda:3.1-53: error: [InfectiveImport]", "Checking ...\nerror text\n")
SLOW_B = FileRun("SetExtCubical.agda", Outcome.TIMEOUT, 300.0, "Command timed out after 300 seconds", "")


def row(result: str, **changes: Any) -> Row:
    base: dict[str, Any] = dict(id="e", status="translated", result=result, seconds=1.0,
                                detail="", problems=(), files=())
    base.update(changes)
    return Row(**base)


class TestFold(unittest.TestCase):
    def test_all_pass(self) -> None:
        self.assertEqual(fold_files(ENTRY, [PASS_A, PASS_A]),
                         Row("set-ext", "translated", "pass", 2.5, "", (), (PASS_A, PASS_A)))

    def test_first_failure_is_named_and_seconds_are_summed(self) -> None:
        folded = fold_files(ENTRY, [PASS_A, FAIL_B, SLOW_B])
        self.assertEqual(folded.result, "fail")
        self.assertEqual(folded.seconds, 303.25)
        self.assertEqual(folded.detail, "SetExtCubical.agda:3.1-53: error: [InfectiveImport]")

    def test_failure_detail(self) -> None:
        self.assertEqual(failure_detail(FAIL_B), FAIL_B.message)
        self.assertEqual(failure_detail(SLOW_B), "SetExtCubical.agda: Command timed out after 300 seconds")

    def test_planned_and_malformed_rows(self) -> None:
        self.assertEqual(planned_row(ENTRY), Row("set-ext", "translated", "skipped", None, "", (), ()))
        self.assertEqual(malformed_row("x", "planned", ("one", "two", "three")).detail, "one (and 2 more)")
        self.assertEqual(malformed_row("x", "planned", ("one",)).detail, "one")


class TestCounts(unittest.TestCase):
    ROWS = (row("pass"), row("fail"), row("skipped"), row("skipped"), row("malformed"))

    def test_summarize(self) -> None:
        self.assertEqual(summarize(self.ROWS), Summary(5, 2, 1, 1, 2, 1))

    def test_exit_status(self) -> None:
        self.assertEqual(exit_status(Report((row("pass"), row("skipped")), ())), 0)
        self.assertEqual(exit_status(Report((row("fail"),), ())), 1)
        self.assertEqual(exit_status(Report((row("malformed"),), ())), 1)
        self.assertEqual(exit_status(Report((row("pass"),), ("corpus/x/ is not ...",))), 1)

    def test_format_summary(self) -> None:
        self.assertEqual(format_summary(summarize(self.ROWS)),
                         "5 entries: 2 checked (1 passed, 1 failed), 2 planned, 1 malformed.")


class TestFormatting(unittest.TestCase):
    def test_format_seconds_and_result_cell(self) -> None:
        self.assertEqual(format_seconds(None), "-")
        self.assertEqual(format_seconds(4.83), "4.8")
        self.assertEqual(result_cell(row("pass")), "pass")
        self.assertEqual(result_cell(row("fail", detail="X.agda: boom")), "fail: X.agda: boom")

    def test_format_table(self) -> None:
        table = format_table([row("pass", id="a-long-id", seconds=4.83), row("skipped", id="b", seconds=None)])
        self.assertEqual(table.splitlines(), [
            "| id        | status     | result  | seconds |",
            "| --------- | ---------- | ------- | ------- |",
            "| a-long-id | translated | pass    | 4.8     |",
            "| b         | translated | skipped | -       |",
        ])

    def test_format_details(self) -> None:
        report = Report((row("malformed", id="m", problems=("p1", "p2")),
                         row("fail", id="f", files=(PASS_A, FAIL_B))), ("orphan",))
        self.assertEqual(format_details(report),
                         "corpus: orphan\nm: p1\nm: p2\n\n"
                         "--- f: agda/SetExtCubical.agda (fail)\nChecking ...\nerror text")
        self.assertEqual(format_details(Report((row("pass"),), ())), "")

    def test_format_text_ends_with_the_summary(self) -> None:
        text = format_text(Report((row("pass"),), ()))
        self.assertTrue(text.endswith("1 entry: 1 checked (1 passed, 0 failed), 0 planned, 0 malformed."))
        self.assertNotIn("\n\n\n", text)

    def test_json(self) -> None:
        self.assertEqual(file_record(PASS_A), {"path": "SetExt.agda", "outcome": "pass",
                                               "seconds": 1.25, "message": "", "output": ""})
        data = json.loads(format_json(Report((row("fail", files=(FAIL_B,)),), ("orphan",))))
        self.assertEqual(data["summary"]["failed"], 1)
        self.assertEqual(data["problems"], ["orphan"])
        self.assertEqual(data["entries"][0]["files"][0]["outcome"], "fail")


def write_corpus(root: Path, manifest: list[dict[str, Any]]) -> None:
    """A corpus with one translated entry whose two files exist."""
    (root / "manifest.json").write_text(json.dumps(manifest), "utf-8")
    entry_dir = root / "set-ext"
    for sub in ("agda", "lean"):
        (entry_dir / sub).mkdir(parents=True)
    (entry_dir / "agda" / "SetExt.agda").write_text("{-# OPTIONS --safe --cubical-compatible #-}\n", "utf-8")
    (entry_dir / "agda" / "SetExtCubical.agda").write_text(
        "{-# OPTIONS --safe --cubical --guardedness #-}\n", "utf-8")
    (entry_dir / "lean" / "Statement.lean").write_text("", "utf-8")
    (entry_dir / "lean" / "term.ndjson").write_text("{}\n", "utf-8")
    (entry_dir / "notes.md").write_text("", "utf-8")


RAW_ENTRY: dict[str, Any] = {
    "id": "set-ext", "theme": "set extensionality", "lean_name": "Set.ext",
    "lean_module": "Mathlib.Data.Set.Defs", "axioms": ["propext", "Quot.sound"], "tier": "T1",
    "features": ["axioms"],
    "agda_files": [{"path": "SetExt.agda", "flags": list(CC), "profile": "CC"},
                   {"path": "SetExtCubical.agda", "flags": list(CU), "profile": "CU"}],
    "status": "translated", "issue": 8,
}
PLANNED: dict[str, Any] = dict(RAW_ENTRY, id="nat-gcd-self", status="planned", agda_files=[])


class FakeRunner:
    """Stands in for the agda call: passes every file but the ones named
    in `failing`, and records what it was asked to run."""

    def __init__(self, failing: Sequence[str] = ()) -> None:
        self.failing = failing
        self.calls: list[tuple[tuple[str, ...], Path]] = []

    def __call__(self, command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
        self.calls.append((tuple(command), cwd))
        if command[-1] in self.failing:
            return Result.err(PipelineError(ErrorType.COMMAND_FAILED, "exit 42", context={
                "stdout": f"/x/{command[-1]}:1.1-2: error: [Boom]\n"}))
        return Result.ok(subprocess.CompletedProcess(list(command), 0, "", ""))


def clock() -> float:
    return 0.0


class TestCheckCorpus(unittest.TestCase):
    def test_checks_translated_entries_and_lists_planned_ones(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_corpus(root, [RAW_ENTRY, PLANNED])
            runner = FakeRunner()
            report = check_corpus(root, runner, clock, "agda", 60.0).unwrap()
            self.assertEqual([(r.id, r.result) for r in report.rows],
                             [("set-ext", "pass"), ("nat-gcd-self", "skipped")])
            self.assertEqual(runner.calls, [(("agda", "SetExt.agda"), root / "set-ext" / "agda"),
                                            (("agda", "SetExtCubical.agda"), root / "set-ext" / "agda")])
            self.assertEqual(report.problems, ())

    def test_a_failing_file_fails_its_entry(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_corpus(root, [RAW_ENTRY])
            report = check_corpus(root, FakeRunner(["SetExtCubical.agda"]), clock, "agda", 60.0).unwrap()
            self.assertEqual(report.rows[0].result, "fail")
            self.assertEqual(report.rows[0].detail, "SetExtCubical.agda:1.1-2: error: [Boom]")
            self.assertEqual(exit_status(report), 1)

    def test_malformed_entries_and_orphans_are_not_run(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_corpus(root, [dict(RAW_ENTRY, tier="T2"), dict(PLANNED, id="other")])
            (root / "stray").mkdir()
            (root / "set-ext" / "notes.md").unlink()
            runner = FakeRunner()
            report = check_corpus(root, runner, clock, "agda", 60.0).unwrap()
            self.assertEqual(report.rows[0].result, "malformed")
            self.assertEqual(report.problems, ("corpus/stray/ is not the id of any manifest entry",))
            self.assertEqual(runner.calls, [])

    def test_a_translated_entry_with_a_missing_file_is_malformed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_corpus(root, [RAW_ENTRY])
            (root / "set-ext" / "notes.md").unlink()
            report = check_corpus(root, FakeRunner(), clock, "agda", 60.0).unwrap()
            self.assertEqual(report.rows[0].problems, ("notes.md is missing",))

    def test_an_unusable_manifest_is_an_error(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.assertIn("File not found", check_corpus(root, FakeRunner(), clock, "agda", 1.0).unwrap_err())
            (root / "manifest.json").write_text("{}", "utf-8")
            self.assertEqual(check_corpus(root, FakeRunner(), clock, "agda", 1.0).unwrap_err(),
                             "the manifest is not a JSON array")


class TestCommandLine(unittest.TestCase):
    def test_defaults(self) -> None:
        args = parse_args([])
        self.assertEqual((args.agda, args.timeout, args.json), ("agda", 300.0, False))
        self.assertEqual(args.corpus.name, "corpus")

    def test_main_refuses_to_run_outside_the_shell(self) -> None:
        environment = {k: v for k, v in os.environ.items() if k != "AGDA_DIR"}
        with mock.patch.dict(os.environ, environment, clear=True), redirect_stderr(io.StringIO()) as err:
            self.assertEqual(main([]), 1)
        self.assertIn("AGDA_DIR is not set", err.getvalue())


if __name__ == "__main__":
    unittest.main()
