"""
File: scripts/python/standards_check.py

Description:
  Check the translator's engineering standards (issue M2-11) against the
  tree: that the module map, docs/translator/architecture.md, describes
  every file it must and only files that exist; that every tracked Lean,
  Python and shell file opens with a `File:` header naming its own path;
  and that the translator's version and the changelog agree.

    python3 scripts/python/standards_check.py [ROOT]

  It prints one line per problem and exits 1 if there is any, 0 if
  none; the Python suite runs the same checks on the repository
  (tests/test_standards_check.py), so `make test` fails when the map
  falls behind the tree.

  What the map must cover: every tracked `.lean` and `.sh` file under
  translator/, and the Python the translator's harness runs,
  TRANSLATOR_PYTHON below.  Its rows are the rows of every Markdown table
  whose first header cell is "File", one file per row, named by its path
  from the repository root in backticks.  Beyond coverage the map is
  checked as follows:

  - a Lean file whose row's "Effects" cell begins with "pure" must use no
    effect monad (EFFECT_MONADS) outside its comments and strings, and
    one whose cell begins with "IO" must use one, so that the map's
    account of the pure core and its edges stays true;
  - every name in the first cell of a table whose first header cell is
    "Definition" or "Type" must be defined, by `def`, `structure`,
    `inductive`, `abbrev` or `class`, in the file its row's "File" cell
    names, so that the pass order and the data types name what the code
    has;
  - every relative link of the document must name an existing file.

  It also checks that translator/VERSION holds one version,
  MAJOR.MINOR.PATCH, and that CHANGELOG.md's newest entry (its first
  `## ` heading) is that version; translator/tests/run.sh checks that
  `lean2agda --version` prints it.

Design Principles:
  - Everything is a pure function of the document's text, the list of
    tracked files and their texts; the edges are tracked_files (git
    ls-files through command_runner), read_sources (file_ops) and main.
  - A problem is a line of text naming the file and what is wrong; the
    checks return tuples of them, empty when the tree is as the map says.
"""
from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from functools import reduce
from pathlib import Path
from typing import Callable, Mapping, Optional, Sequence

from _utils.command_runner import run_command
from _utils.file_ops import read_text
from _utils.pipeline_types import PipelineError, Result, sequence_results

MAP_PATH: str = "docs/translator/architecture.md"
VERSION_PATH: str = "translator/VERSION"
CHANGELOG_PATH: str = "CHANGELOG.md"

# The Python the translator's harness (translator/tests/run.sh) runs: the
# scaffold checker and the module it imports.  The rest of scripts/python
# (the corpus checker, the atlas report, the tables, _utils) serves the
# corpus and the atlas, not the translator.  A new script the harness runs
# joins this tuple and gets a row.
TRANSLATOR_PYTHON: tuple[str, ...] = (
    "scripts/python/agda_run.py",
    "scripts/python/scaffold_check.py",
)

# The monads in which a Lean function can do more than compute.  `ST`,
# which `runST` makes pure, is not among them.
EFFECT_MONADS: tuple[str, ...] = (
    "IO", "EIO", "BaseIO", "CoreM", "MetaM", "TermElabM", "CommandElabM",
)

HEADER_SUFFIXES: tuple[str, ...] = (".lean", ".py", ".sh")

# A `File:` header sits on one of a file's first lines: after the `/-` of
# a Lean comment, the `"""` of a Python docstring, or a shell's `#!` line.
HEADER_LINES: int = 5


@dataclass(frozen=True)
class Table:
    """A Markdown table: its header cells and its rows of cells."""

    header: tuple[str, ...]
    rows: tuple[tuple[str, ...], ...]


@dataclass(frozen=True)
class MapRow:
    """One row of the map: the file it describes and its other cells."""

    path: str
    cells: Mapping[str, str]


@dataclass(frozen=True)
class DefinitionRow:
    """One row of the pass order or the data types: names and their file."""

    names: tuple[str, ...]
    path: str


# ---------------------------------------------------------------------------
# Markdown
# ---------------------------------------------------------------------------

_CELL_SPLIT = re.compile(r"(?<!\\)\|")
_RULE_CELL = re.compile(r"^:?-{3,}:?$")
_CODE = re.compile(r"`([^`]+)`")
_INLINE_LINK = re.compile(r"\]\(([^)\s]+)\)")
_REFERENCE_LINK = re.compile(r"^\[[^\]]+\]:\s*(\S+)", re.MULTILINE)


def split_row(line: str) -> tuple[str, ...]:
    """The cells of one table line, stripped, without the outer pipes."""
    inner = line.strip()
    inner = inner[1:] if inner.startswith("|") else inner
    inner = inner[:-1] if inner.endswith("|") and not inner.endswith("\\|") else inner
    return tuple(cell.strip() for cell in _CELL_SPLIT.split(inner))


def is_rule(cells: tuple[str, ...]) -> bool:
    """Whether a table line is the rule under the header."""
    return bool(cells) and all(_RULE_CELL.match(cell) for cell in cells)


def _blocks(lines: tuple[str, ...]) -> tuple[tuple[str, ...], ...]:
    """Maximal runs of consecutive lines that begin with a pipe."""
    def step(acc: tuple[tuple[str, ...], ...], line: str) -> tuple[tuple[str, ...], ...]:
        if not line.lstrip().startswith("|"):
            return acc if not acc or not acc[-1] else acc + ((),)
        if not acc:
            return ((line,),)
        return acc[:-1] + (acc[-1] + (line,),)
    return tuple(block for block in reduce(step, lines, ()) if block)


def parse_tables(text: str) -> tuple[Table, ...]:
    """Every table of a Markdown text: a header line, a rule, and rows.
    Lines inside fenced code blocks are skipped."""
    def unfenced(acc: tuple[tuple[str, ...], bool], line: str) -> tuple[tuple[str, ...], bool]:
        kept, fenced = acc
        if line.lstrip().startswith("```"):
            return kept + ("",), not fenced
        return (kept + ("" if fenced else line,), fenced)
    lines, _ = reduce(unfenced, text.splitlines(), ((), False))
    return tuple(
        Table(split_row(block[0]), tuple(split_row(line) for line in block[2:]))
        for block in _blocks(lines)
        if len(block) >= 2 and is_rule(split_row(block[1]))
    )


def code_spans(cell: str) -> tuple[str, ...]:
    """The backticked spans of a cell, in order."""
    return tuple(_CODE.findall(cell))


def map_rows(tables: tuple[Table, ...]) -> tuple[MapRow, ...]:
    """The rows of the tables whose first header cell is "File"; a row's
    file is the first backticked span of its first cell."""
    return tuple(
        MapRow(spans[0], dict(zip(table.header, row)))
        for table in tables if table.header and table.header[0] == "File"
        for row in table.rows
        for spans in (code_spans(row[0]),) if spans
    )


def definition_rows(tables: tuple[Table, ...]) -> tuple[DefinitionRow, ...]:
    """The rows of the tables whose first header cell is "Definition" or
    "Type" and which have a "File" column."""
    return tuple(
        DefinitionRow(code_spans(row[0]), paths[0])
        for table in tables
        if table.header and table.header[0] in ("Definition", "Type") and "File" in table.header
        for row in table.rows
        for paths in (code_spans(dict(zip(table.header, row)).get("File", "")),) if paths
    )


def relative_links(text: str) -> tuple[str, ...]:
    """The targets of the inline and reference links that name a file of
    the repository: not a URL, not an anchor alone; anchors dropped."""
    targets = tuple(_INLINE_LINK.findall(text)) + tuple(_REFERENCE_LINK.findall(text))
    return tuple(sorted({
        t.split("#", 1)[0] for t in targets
        if not re.match(r"^[a-z]+:", t) and not t.startswith("#")
    }))


# ---------------------------------------------------------------------------
# Lean source
# ---------------------------------------------------------------------------

_CHAR_LITERAL = re.compile(r"'(\\.|[^\\'\n])'")


def lean_code(source: str) -> str:
    """A Lean source with its comments and string and character literals
    blanked out, so that a token in a docstring is not taken for code.
    Block comments nest, as Lean's do."""
    # A scanner over positions, with a while loop: the state (position
    # and comment depth) changes by a varying step, and recursion per
    # character would exceed Python's stack on any real file.
    chunks: list[str] = []
    i, depth = 0, 0
    while i < len(source):
        if depth > 0:
            step = 2 if source.startswith(("/-", "-/"), i) else 1
            depth += 1 if source.startswith("/-", i) else -1 if source.startswith("-/", i) else 0
            chunks.append("\n" if source[i] == "\n" else " ")
            i += step
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            chunks.append('""')
            i = _string_end(source, i + 1)
        elif (m := _CHAR_LITERAL.match(source, i)) is not None and not _ident_char(source, i - 1):
            chunks.append("' '")
            i = m.end()
        else:
            chunks.append(source[i])
            i += 1
    return "".join(chunks)


def _ident_char(source: str, i: int) -> bool:
    """Whether position i holds a character that continues an identifier,
    so that a quote after it is a prime (`x'`), not a character literal."""
    return 0 <= i < len(source) and (source[i].isalnum() or source[i] in "_'!?.")


def _string_end(source: str, i: int) -> int:
    """The index just past the closing quote of a string opened before i."""
    while i < len(source):
        if source[i] == "\\":
            i += 2
        elif source[i] == '"':
            return i + 1
        else:
            i += 1
    return len(source)


def uses_effects(source: str) -> bool:
    """Whether a Lean source's code mentions an effect monad."""
    pattern = r"(?<![\w.])(?:" + "|".join(EFFECT_MONADS) + r")(?![\w'])"
    return re.search(pattern, lean_code(source)) is not None


def defines(source: str, name: str) -> bool:
    """Whether a Lean or Python source defines `name`."""
    pattern = r"(?:^|\s)(?:def|abbrev|structure|inductive|class)\s+" + re.escape(name) + r"(?![\w.'?!])"
    return re.search(pattern, source, re.MULTILINE) is not None


# ---------------------------------------------------------------------------
# The checks
# ---------------------------------------------------------------------------

def required_paths(tracked: tuple[str, ...]) -> tuple[str, ...]:
    """The files the map must cover, sorted."""
    translator = (p for p in tracked if p.startswith("translator/") and p.endswith((".lean", ".sh")))
    return tuple(sorted(set(translator) | set(TRANSLATOR_PYTHON)))


def coverage_problems(required: tuple[str, ...], rows: tuple[MapRow, ...],
                      exists: Callable[[str], bool]) -> tuple[str, ...]:
    """A file the map must cover with no row; a row naming a file that does
    not exist; a file with two rows."""
    mapped = tuple(row.path for row in rows)
    missing = tuple(f"{p}: no row in {MAP_PATH}" for p in required if p not in mapped)
    absent = tuple(f"{p}: {MAP_PATH} has a row for it, but it does not exist"
                   for p in sorted(set(mapped)) if not exists(p))
    twice = tuple(f"{p}: {MAP_PATH} has {mapped.count(p)} rows for it"
                  for p in sorted(set(mapped)) if mapped.count(p) > 1)
    return missing + absent + twice


def effect_problems(rows: tuple[MapRow, ...], sources: Mapping[str, str]) -> tuple[str, ...]:
    """A Lean row whose Effects cell disagrees with the code it describes."""
    def problem(row: MapRow) -> Optional[str]:
        cell = row.cells.get("Effects", "")
        source = sources.get(row.path)
        if not row.path.endswith(".lean") or source is None or not cell:
            return None
        claim = re.match(r"(pure|IO)\b", cell)
        if claim is None:
            return f"{row.path}: the Effects cell must begin with pure or IO"
        effectful = uses_effects(source)
        if claim.group(1) == "pure" and effectful:
            return f"{row.path}: the map says pure, and the code uses an effect monad"
        if claim.group(1) == "IO" and not effectful:
            return f"{row.path}: the map says IO, and the code uses no effect monad"
        return None
    return tuple(p for p in map(problem, rows) if p is not None)


def definition_problems(rows: tuple[DefinitionRow, ...], sources: Mapping[str, str]) -> tuple[str, ...]:
    """A name the pass order or the data types give a file that does not
    define it."""
    return tuple(
        f"{row.path}: the map names {name}, which the file does not define"
        if row.path in sources else f"{row.path}: the map names it for {name}, and it does not exist"
        for row in rows for name in row.names
        if row.path not in sources or not defines(sources[row.path], name)
    )


def link_problems(links: tuple[str, ...], document: str,
                  exists: Callable[[str], bool]) -> tuple[str, ...]:
    """A relative link of the document that names no existing file."""
    base = Path(document).parent
    return tuple(f"{document}: the link {link} names no file"
                 for link in links if not exists(_normalize(base / link)))


def _normalize(path: Path) -> str:
    """A relative path with `..` and `.` resolved textually."""
    parts = reduce(lambda acc, part: acc[:-1] if part == ".." and acc else
                   acc if part == "." else acc + (part,), path.parts, ())
    return "/".join(parts)


def map_problems(document: str, tracked: tuple[str, ...], sources: Mapping[str, str],
                 exists: Callable[[str], bool]) -> tuple[str, ...]:
    """Every problem of the map, given its text and the tree."""
    tables = parse_tables(document)
    rows = map_rows(tables)
    return (coverage_problems(required_paths(tracked), rows, exists)
            + effect_problems(rows, sources)
            + definition_problems(definition_rows(tables), sources)
            + link_problems(relative_links(document), MAP_PATH, exists))


def header_problem(path: str, source: str) -> Optional[str]:
    """A file whose first lines carry no `File:` header naming its path."""
    found = re.findall(r"File:\s*(\S+)", "\n".join(source.splitlines()[:HEADER_LINES]))
    if not found:
        return f"{path}: no File: header in its first {HEADER_LINES} lines"
    if found[0] != path:
        return f"{path}: its File: header names {found[0]}"
    return None


def header_problems(sources: Mapping[str, str]) -> tuple[str, ...]:
    """Every tracked Lean, Python and shell file without a correct header."""
    return tuple(p for p in (header_problem(path, sources[path])
                             for path in sorted(sources) if path.endswith(HEADER_SUFFIXES))
                 if p is not None)


_VERSION = re.compile(r"^(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)$")


def newest_entry(changelog: str) -> Optional[str]:
    """The version of the changelog's first `## ` heading, if any."""
    headings = [line[3:].split() for line in changelog.splitlines() if line.startswith("## ")]
    return headings[0][0] if headings and headings[0] else None


def version_problems(version: str, changelog: str) -> tuple[str, ...]:
    """A VERSION file that is not one version, or that the changelog's
    newest entry does not name."""
    lines = version.splitlines()
    if len(lines) != 1 or not _VERSION.match(lines[0]):
        return (f"{VERSION_PATH}: must hold one line, MAJOR.MINOR.PATCH",)
    newest = newest_entry(changelog)
    if newest != lines[0]:
        return (f"{CHANGELOG_PATH}: its newest entry is {newest}, and {VERSION_PATH} says {lines[0]}",)
    return ()


# ---------------------------------------------------------------------------
# The edges
# ---------------------------------------------------------------------------

def tracked_files(root: Path) -> Result[tuple[str, ...], PipelineError]:
    """The files git tracks under root, by path from root.  Generated
    files (`.lake`, `.agda`) are never tracked, so none enters a check."""
    return run_command(["git", "ls-files", "-z"], cwd=root, capture_output=True, text=True).map(
        lambda done: tuple(p for p in done.stdout.split("\0") if p))


def read_sources(root: Path, paths: Sequence[str]) -> Result[dict[str, str], PipelineError]:
    """The texts of the given files that exist, by path."""
    present = tuple(p for p in paths if (root / p).is_file())
    return sequence_results([read_text(root / p) for p in present]).map(
        lambda texts: dict(zip(present, texts)))


def named_paths(document: str) -> tuple[str, ...]:
    """The files the map's rows name, whether or not git tracks them yet,
    so that a new module's row is checked before the module is added."""
    tables = parse_tables(document)
    return tuple(row.path for row in map_rows(tables)) + tuple(row.path for row in definition_rows(tables))


def check_tree(root: Path) -> Result[tuple[str, ...], PipelineError]:
    """Every problem of the map, the headers and the version in the tree
    at root."""
    def with_texts(tracked: tuple[str, ...], texts: list[str]) -> Result[tuple[str, ...], PipelineError]:
        document, version, changelog = texts
        wanted = tuple(sorted(set(p for p in tracked if p.endswith(HEADER_SUFFIXES))
                              | set(TRANSLATOR_PYTHON) | set(named_paths(document))))
        exists: Callable[[str], bool] = lambda p: (root / p).exists()
        return read_sources(root, wanted).map(
            lambda sources: map_problems(document, tracked, sources, exists)
            + header_problems({p: t for p, t in sources.items() if p in tracked})
            + version_problems(version, changelog))
    return tracked_files(root).and_then(lambda tracked: sequence_results(
        [read_text(root / p) for p in (MAP_PATH, VERSION_PATH, CHANGELOG_PATH)]).and_then(
        lambda texts: with_texts(tracked, texts)))


def main(argv: Optional[list[str]] = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if len(args) > 1:
        print("usage: standards_check.py [ROOT]", file=sys.stderr)
        return 2
    root = Path(args[0]) if args else Path(__file__).resolve().parents[2]
    result = check_tree(root)
    if result.is_err:
        print(f"standards_check: {result.unwrap_err()}", file=sys.stderr)
        return 2
    problems = result.unwrap()
    for problem in problems:
        print(problem)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
