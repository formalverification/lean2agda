"""
File: scripts/python/scaffold_check.py

Description:
  Type-check a profile U scaffold, the Agda module that
  `lake exe lean2agda --out DIR` writes for a closure, and report which
  declarations Agda refuses.

  Agda stops at the first error in a module, and a scaffold holds
  hundreds of declarations, some of which cannot check until the
  emitters of issues M2-4 to M2-7 supply the definitional unfolding they
  need.  The checker therefore runs Agda on a scratch copy of the module
  repeatedly.  When Agda refuses the clause of a definition, the
  definition becomes a postulate of its type, so that what uses it still
  checks; when Agda refuses a declaration's type, the declaration and
  everything that refers to it are dropped.  It stops when the rest
  checks, and prints one line per refusal and per dropped declaration,
  in the order Agda met them, after a line counting what checked.

    python3 scripts/python/scaffold_check.py [--agda AGDA]
        [--timeout SECONDS] [--messages] MODULE.agda

  The listing is deterministic, so a test compares it with an expected
  one; `--messages` adds the first line of each error message.  The
  number of Agda runs and their times go to standard error.

Design Principles:
  - The module is never edited in place: the checker writes its copies
    under a temporary directory, at the path the module's name asks for.
  - Splitting the module, locating an error, and each step of the loop
    are pure functions over immutable values; check_module is the only
    function that writes files or runs Agda, through agda_run's injected
    runner and clock.
  - A declaration is a block of lines between blank lines, as
    Scaffold.render in translator/Lean2Agda/Core/Scaffold.lean writes
    them; its first word (after `postulate` or `data`) is its name.
"""
from __future__ import annotations

import argparse
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from _utils.file_ops import ensure_dir_exists, read_text, write_text
from _utils.pipeline_types import ErrorType, PipelineError, Result
from agda_run import Clock, FileRun, Outcome, Runner, check_file, real_clock, run_agda

DEFAULT_TIMEOUT: float = 600.0

# Identifiers in printed Agda are separated by whitespace and these
# delimiters; a dot never occurs in the scaffold's names.
_TOKEN = re.compile(r"[^\s(){}⦃⦄;]+")
# "<path>:<line>.<column>-<end>: error: [Name]", where the end is a
# column or a line.column.
_ERROR = re.compile(r":(\d+)\.\d+-(?:\d+\.)?\d+: error: \[(\w+)\]")
_MODULE = re.compile(r"^module (\S+) where$", re.MULTILINE)


@dataclass(frozen=True)
class Item:
    """One declaration: its kind ("postulate", "data" or "definition"),
    the names it declares, and its text."""

    kind: str
    names: tuple[str, ...]
    text: str


@dataclass(frozen=True)
class Module:
    """A scaffold: its name, its header (options, comment, module line),
    and its declarations."""

    name: str
    header: str
    items: tuple[Item, ...]


@dataclass(frozen=True)
class Refusal:
    """Agda's first error: the line it points at, its name, and the first
    line of its message."""

    line: int
    error: str
    message: str


@dataclass(frozen=True)
class Event:
    """What the checker did to a declaration: "refused type",
    "refused value" or "dropped"."""

    action: str
    name: str
    error: str
    message: str


@dataclass(frozen=True)
class State:
    """The declarations as they stand, which are still in the module, and
    what has happened so far."""

    items: tuple[Item, ...]
    alive: tuple[bool, ...]
    events: tuple[Event, ...]


def parse_item(text: str) -> Item:
    """Classify a block by its first line and collect its names; a data
    type also declares the constructors on its indented lines."""
    lines = text.split("\n")
    words = lines[0].split()
    if words[0] == "postulate":
        return Item("postulate", (words[1],), text)
    if words[0] == "data":
        constructors = tuple(line.split()[0] for line in lines[1:] if line.startswith("  "))
        return Item("data", (words[1],) + constructors, text)
    return Item("definition", (words[0],), text)


def parse_module(text: str) -> Result[Module, PipelineError]:
    """Split a scaffold at its blank lines: the first block is the header."""
    blocks = text.rstrip("\n").split("\n\n")
    match = _MODULE.search(blocks[0])
    if match is None or len(blocks) < 2:
        return Result.err(PipelineError(ErrorType.PARSING_ERROR, "not a scaffold module"))
    return Result.ok(Module(match.group(1), blocks[0], tuple(parse_item(b) for b in blocks[1:])))


def references(items: tuple[Item, ...]) -> tuple[frozenset[int], ...]:
    """For each item, the other items whose names its text mentions."""
    owner = {name: i for i, item in enumerate(items) for name in item.names}
    return tuple(
        frozenset(owner[t] for t in _TOKEN.findall(item.text) if t in owner and owner[t] != i)
        for i, item in enumerate(items)
    )


def render(module: Module, state: State) -> tuple[str, tuple[tuple[int, int], ...]]:
    """The module's text with the live items, and for each live item its
    index and first line."""
    live = tuple(i for i, a in enumerate(state.alive) if a)
    header_lines = module.header.count("\n") + 1
    starts = _starts(tuple(state.items[i].text.count("\n") + 1 for i in live), header_lines + 2)
    text = "\n\n".join((module.header,) + tuple(state.items[i].text for i in live)) + "\n"
    return text, tuple(zip(live, starts))


def _starts(heights: tuple[int, ...], first: int) -> tuple[int, ...]:
    """The first line of each block, given their heights and one blank
    line between blocks."""
    if not heights:
        return ()
    return (first,) + _starts(heights[1:], first + heights[0] + 1)


def parse_refusal(output: str) -> Optional[Refusal]:
    """The first error of Agda's output and the line of message after it."""
    lines = output.splitlines()
    found = next(((i, m) for i, line in enumerate(lines) if (m := _ERROR.search(line))), None)
    if found is None:
        return None
    i, match = found
    message = next((line.strip() for line in lines[i + 1:] if line.strip()), "")
    return Refusal(int(match.group(1)), match.group(2), message)


def locate(layout: tuple[tuple[int, int], ...], line: int) -> Optional[tuple[int, int]]:
    """The live item containing the line, as (index, line within it)."""
    before = tuple((i, start) for i, start in layout if start <= line)
    return (before[-1][0], line - before[-1][1]) if before else None


def dependents(index: int, refs: tuple[frozenset[int], ...], alive: tuple[bool, ...]) -> tuple[int, ...]:
    """The live items that refer to `index`, directly or through each
    other, in module order, `index` first."""
    def grow(found: frozenset[int]) -> frozenset[int]:
        more = found | frozenset(i for i, r in enumerate(refs) if alive[i] and r & found)
        return found if more == found else grow(more)
    return (index,) + tuple(sorted(grow(frozenset((index,))) - {index}))


def step(state: State, index: int, offset: int, refusal: Refusal) -> State:
    """Apply one refusal.  A definition refused below its signature line
    keeps its signature as a postulate; anything else is dropped with
    its dependents."""
    item = state.items[index]
    if item.kind == "definition" and offset > 0:
        signature = item.text.split("\n")[0]
        items = state.items[:index] + (Item("postulate", item.names, "postulate " + signature),) \
            + state.items[index + 1:]
        event = Event("refused value", item.names[0], refusal.error, refusal.message)
        return State(items, state.alive, state.events + (event,))
    gone = dependents(index, references(state.items), state.alive)
    alive = tuple(a and i not in gone for i, a in enumerate(state.alive))
    first = Event("refused type", item.names[0], refusal.error, refusal.message)
    rest = tuple(Event("dropped", state.items[i].names[0], "", "") for i in gone[1:])
    return State(state.items, alive, state.events + (first,) + rest)


def listing(state: State, messages: bool) -> str:
    """The report: what checked, then one line per event."""
    total = len(state.items)
    lines = (f"checked {sum(state.alive)} of {total} declarations",) + tuple(
        " ".join(w for w in (e.action, e.error, e.name) if w)
        + (f" | {e.message}" if messages and e.message else "")
        for e in state.events
    )
    return "\n".join(lines) + "\n"


@dataclass(frozen=True)
class Checked:
    """The final state, the number of Agda runs, their total time, and
    the time of the last run, which checked what remained."""

    state: State
    runs: int
    seconds: float
    last: float


def check_module(
    runner: Runner, clock: Clock, agda: str, module: Module, timeout: float, scratch: Path
) -> Result[Checked, PipelineError]:
    """Run Agda on copies of the module under `scratch` until the
    remaining declarations check.  Each round removes or rewrites one
    declaration, so there are at most twice as many rounds as
    declarations."""
    relative = Path(*module.name.split(".")).with_suffix(".agda")
    made = ensure_dir_exists((scratch / relative).parent)
    if made.is_err:
        return Result.err(made.unwrap_err())
    state = State(module.items, tuple(True for _ in module.items), ())
    runs, seconds = 0, 0.0
    for _ in range(2 * len(module.items) + 1):
        text, layout = render(module, state)
        written = write_text(scratch / relative, text)
        if written.is_err:
            return Result.err(written.unwrap_err())
        run: FileRun = check_file(runner, clock, agda, scratch, str(relative), timeout)
        runs, seconds = runs + 1, seconds + run.seconds
        if run.outcome == Outcome.PASS:
            return Result.ok(Checked(state, runs, seconds, run.seconds))
        refusal = parse_refusal(run.output)
        place = locate(layout, refusal.line) if refusal else None
        if run.outcome == Outcome.TIMEOUT or refusal is None or place is None:
            return Result.err(PipelineError(ErrorType.AGDA_ERROR,
                                            f"cannot place Agda's failure: {run.message}"))
        state = step(state, place[0], place[1], refusal)
    return Result.err(PipelineError(ErrorType.AGDA_ERROR, "the checker did not converge"))


def main(argv: Optional[list[str]] = None) -> int:
    """Parse arguments, run the checker, and print its listing."""
    parser = argparse.ArgumentParser(description="Type-check a profile U scaffold.")
    parser.add_argument("module", type=Path)
    parser.add_argument("--agda", default="agda")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT)
    parser.add_argument("--messages", action="store_true")
    args = parser.parse_args(argv)
    with tempfile.TemporaryDirectory(prefix="scaffold-check-") as scratch:
        outcome = read_text(args.module).and_then(parse_module).and_then(
            lambda m: check_module(run_agda, real_clock, args.agda, m, args.timeout, Path(scratch)))
    if outcome.is_err:
        print(f"scaffold_check: {outcome.unwrap_err()}", file=sys.stderr)
        return 1
    result = outcome.unwrap()
    print(listing(result.state, args.messages), end="")
    print(f"scaffold_check: {result.runs} runs, {result.seconds:.1f} s in all, "
          f"{result.last:.1f} s for the last", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
