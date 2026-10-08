"""
File: scripts/python/corpus_check.py

Description:
  The corpus checker, run by `make corpus-check` inside the Nix shell.

  It reads corpus/manifest.json, validates it against the rules of
  corpus/SCHEMA.md (corpus_manifest.py), runs the shell's agda on every
  file of every translated entry from the entry's agda/ directory with a
  per-file timeout (agda_run.py), and prints one table row per entry
  (id, status, result, seconds), the problems and Agda's output for
  whatever failed, and a summary.  It exits with status 1 if a checked
  entry fails, an entry is malformed, or the corpus as a whole is not
  in order; planned entries are listed, never checked or failed.
  `--json` prints the same report as one JSON object, with a record for
  every file, for the driver of issue M2-8.

    python3 scripts/python/corpus_check.py [--json] [--agda AGDA]
                                           [--timeout SECONDS] [--corpus DIR]

Design Principles:
  - The checker passes Agda no flags and no library options of its own:
    each file checks under its OPTIONS pragma and sees the libraries the
    shell registers, and a file that omits a flag it needs (the cubical
    library's --guardedness) fails, as it should.
  - The report is built by pure functions from the entries and the file
    runs; check_corpus is the only function that reads the disk or runs
    Agda, through an injected runner and clock.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Sequence

from _utils.file_ops import read_text
from _utils.pipeline_types import Result
from agda_run import Clock, FileRun, Outcome, Runner, check_file, real_clock, run_agda
from corpus_manifest import (
    Entry, Item, Malformed, decode_manifest, entry_file_problems,
    gather_entry_files, orphan_problems,
)

DEFAULT_TIMEOUT: float = 300.0


@dataclass(frozen=True)
class Row:
    """One entry of the report.

    `result` is "pass", "fail", "skipped" (a planned entry, listed and
    not checked) or "malformed"; `detail` names the first failure or
    problem; `seconds` is the sum over the entry's files, None when
    nothing ran.
    """

    id: str
    status: str
    result: str
    seconds: Optional[float]
    detail: str
    problems: tuple[str, ...]
    files: tuple[FileRun, ...]


@dataclass(frozen=True)
class Summary:
    """Counts over the rows."""

    entries: int
    checked: int
    passed: int
    failed: int
    planned: int
    malformed: int


@dataclass(frozen=True)
class Report:
    """The rows, and the problems of the corpus as a whole."""

    rows: tuple[Row, ...]
    problems: tuple[str, ...]


# ---------------------------------------------------------------------------
# Pure: rows and the report
# ---------------------------------------------------------------------------

def failure_detail(run: FileRun) -> str:
    """Name a failed file and its first error; Agda's error lines already
    start with the file's name, which is then not repeated."""
    return run.message if run.message.startswith(run.path) else f"{run.path}: {run.message}"


def fold_files(entry: Entry, runs: Sequence[FileRun]) -> Row:
    """One row for a checked entry: it passes when every file passes,
    its seconds are the sum, and its detail names the first failure."""
    failures = [run for run in runs if run.outcome != Outcome.PASS]
    seconds = sum(run.seconds for run in runs)
    detail = failure_detail(failures[0]) if failures else ""
    return Row(entry.id, entry.status, "fail" if failures else "pass",
               seconds, detail, (), tuple(runs))


def planned_row(entry: Entry) -> Row:
    """The row of an entry that is listed and not checked."""
    return Row(entry.id, entry.status, "skipped", None, "", (), ())


def malformed_row(label: str, status: str, problems: Sequence[str]) -> Row:
    """The row of an entry that breaks a rule of corpus/SCHEMA.md."""
    more = f" (and {len(problems) - 1} more)" if len(problems) > 1 else ""
    return Row(label, status, "malformed", None, f"{problems[0]}{more}", tuple(problems), ())


def summarize(rows: Sequence[Row]) -> Summary:
    """Count the rows by result."""
    def count(result: str) -> int:
        return sum(1 for row in rows if row.result == result)
    return Summary(
        entries=len(rows),
        checked=count("pass") + count("fail"),
        passed=count("pass"),
        failed=count("fail"),
        planned=count("skipped"),
        malformed=count("malformed"),
    )


def exit_status(report: Report) -> int:
    """0 when nothing failed and everything is well formed, else 1."""
    summary = summarize(report.rows)
    return 1 if summary.failed or summary.malformed or report.problems else 0


def format_seconds(seconds: Optional[float]) -> str:
    """Seconds to one decimal, or '-' when nothing ran."""
    return "-" if seconds is None else f"{seconds:.1f}"


def result_cell(row: Row) -> str:
    """The result column: the result, with the first failure or problem."""
    return f"{row.result}: {row.detail}" if row.detail else row.result


def format_table(rows: Sequence[Row]) -> str:
    """A Markdown table, one row per entry, its columns padded to line up."""
    header = ("id", "status", "result", "seconds")
    body = [(row.id, row.status, result_cell(row), format_seconds(row.seconds)) for row in rows]
    widths = [max(len(cells[i]) for cells in [header, *body]) for i in range(len(header))]

    def line(cells: Sequence[str]) -> str:
        return "| " + " | ".join(c.ljust(w) for c, w in zip(cells, widths)) + " |"
    rule = "| " + " | ".join("-" * w for w in widths) + " |"
    return "\n".join([line(header), rule, *(line(cells) for cells in body)])


def format_details(report: Report) -> str:
    """Every problem of the corpus and of each malformed entry, and Agda's
    output for each file that failed; empty when there is none."""
    corpus = [f"corpus: {problem}" for problem in report.problems]
    malformed = [
        f"{row.id}: {problem}" for row in report.rows if row.result == "malformed"
        for problem in row.problems
    ]
    failures = [
        f"--- {row.id}: agda/{run.path} ({run.outcome.value})\n{run.output.rstrip() or run.message}"
        for row in report.rows for run in row.files if run.outcome != Outcome.PASS
    ]
    return "\n\n".join(part for part in ("\n".join(corpus + malformed), "\n\n".join(failures)) if part)


def format_summary(summary: Summary) -> str:
    """One line of counts."""
    noun = "entry" if summary.entries == 1 else "entries"
    return (f"{summary.entries} {noun}: {summary.checked} checked "
            f"({summary.passed} passed, {summary.failed} failed), "
            f"{summary.planned} planned, {summary.malformed} malformed.")


def format_text(report: Report) -> str:
    """The report as the terminal shows it: table, details, summary."""
    details = format_details(report)
    parts = [format_table(report.rows), details, format_summary(summarize(report.rows))]
    return "\n\n".join(part for part in parts if part)


def file_record(run: FileRun) -> dict[str, object]:
    """A file run as JSON."""
    return {"path": run.path, "outcome": run.outcome.value, "seconds": run.seconds,
            "message": run.message, "output": run.output}


def format_json(report: Report) -> str:
    """The report as one JSON object."""
    summary = summarize(report.rows)
    return json.dumps({
        "entries": [
            {"id": row.id, "status": row.status, "result": row.result,
             "seconds": row.seconds, "detail": row.detail,
             "problems": list(row.problems), "files": [file_record(f) for f in row.files]}
            for row in report.rows
        ],
        "problems": list(report.problems),
        "summary": {
            "entries": summary.entries, "checked": summary.checked,
            "passed": summary.passed, "failed": summary.failed,
            "planned": summary.planned, "malformed": summary.malformed,
        },
    }, indent=2, ensure_ascii=False)


# ---------------------------------------------------------------------------
# The edge
# ---------------------------------------------------------------------------

def check_entry(corpus: Path, entry: Entry, runner: Runner, clock: Clock,
                agda: str, timeout: float) -> Row:
    """The row of one well-formed entry: listed if planned; otherwise its
    directory is validated and, if that passes, every file is checked."""
    if entry.status == "planned":
        return planned_row(entry)
    entry_dir = corpus / entry.id
    gathered = gather_entry_files(entry_dir, entry)
    if gathered.is_err:
        return malformed_row(entry.id, entry.status, (str(gathered.unwrap_err()),))
    problems = entry_file_problems(entry, gathered.unwrap())
    if problems:
        return malformed_row(entry.id, entry.status, problems)
    runs = [check_file(runner, clock, agda, entry_dir / "agda", f.path, timeout)
            for f in entry.agda_files]
    return fold_files(entry, runs)


def row_of(corpus: Path, item: Item, runner: Runner, clock: Clock,
           agda: str, timeout: float) -> Row:
    """The row of a manifest item, well formed or not."""
    if isinstance(item, Malformed):
        return malformed_row(item.label, item.status, item.problems)
    return check_entry(corpus, item, runner, clock, agda, timeout)


def check_corpus(corpus: Path, runner: Runner, clock: Clock,
                 agda: str, timeout: float) -> Result[Report, str]:
    """Check the corpus in directory `corpus`; an error means the
    manifest itself could not be read or used."""
    text = read_text(corpus / "manifest.json")
    if text.is_err:
        return Result.err(str(text.unwrap_err()))
    decoded = decode_manifest(text.unwrap())
    if decoded.is_err:
        return Result.err(decoded.unwrap_err())
    items = decoded.unwrap()
    directories = [p.name for p in corpus.iterdir() if p.is_dir()]
    rows = tuple(row_of(corpus, item, runner, clock, agda, timeout) for item in items)
    return Result.ok(Report(rows, orphan_problems(directories, items)))


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    """The command line."""
    parser = argparse.ArgumentParser(
        description="Type-check every translated corpus entry under its declared flags.")
    parser.add_argument("--corpus", type=Path,
                        default=Path(__file__).resolve().parents[2] / "corpus",
                        help="the corpus directory (default: the repository's corpus/)")
    parser.add_argument("--agda", default="agda",
                        help="the agda to run (default: agda, the Nix shell's wrapper)")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT,
                        help=f"seconds allowed per file (default: {DEFAULT_TIMEOUT:g})")
    parser.add_argument("--json", action="store_true",
                        help="print the report as JSON instead of a table")
    return parser.parse_args(argv)


def main(argv: Sequence[str]) -> int:
    """Parse the arguments, check the corpus, print the report."""
    args = parse_args(argv)
    # The libraries the corpus imports are the ones the Nix shell's agda
    # wrapper registers in $AGDA_DIR; a host agda would read
    # ~/.config/agda and check against whatever is installed there.
    if "AGDA_DIR" not in os.environ:
        print("corpus-check: AGDA_DIR is not set; run inside the Nix shell "
              "(nix develop), whose agda sees the pinned libraries", file=sys.stderr)
        return 1
    result = check_corpus(args.corpus, run_agda, real_clock, args.agda, args.timeout)
    if result.is_err:
        print(f"corpus-check: {result.unwrap_err()}", file=sys.stderr)
        return 1
    report = result.unwrap()
    print(format_json(report) if args.json else format_text(report))
    return exit_status(report)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
