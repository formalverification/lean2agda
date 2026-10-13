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
  in the order Agda met them, after a line counting what checked: the
  declarations, and the data types and records the inductive types
  became.

    python3 scripts/python/scaffold_check.py [--agda AGDA]
        [--timeout SECONDS] [--messages] [--types-only] MODULE.agda

  The listing is deterministic, so a test compares it with an expected
  one; `--messages` adds the first line of each error message.
  `--types-only` checks the data types and records alone, with the
  declarations they mention, directly or through each other: what
  Agda's positivity checker sees, in a module a fraction of the size,
  since Agda's time grows faster than a module.  The number of Agda runs
  and their times go to standard error.

Design Principles:
  - The module is never edited in place: the checker writes its copies
    under a temporary directory, at the path the module's name asks for.
  - Splitting the module, locating an error, and each step of the loop
    are pure functions over immutable values; check_module is the only
    function that writes files or runs Agda, through agda_run's injected
    runner and clock.
  - A declaration is a block of lines between blank lines, as
    Scaffold.render in translator/Lean2Agda/Core/Scaffold.lean writes
    them: a postulate, a definition, a data type with its constructors
    on the lines under it, a record with its constructor and fields, a
    mutual block of data types and records, each possibly after or
    before a pragma line.  The names a block declares are the ones its
    users can mention: a record's fields are mentioned as `R.f`, which
    names the record.
"""
from __future__ import annotations

import argparse
import re
import sys
import tempfile
from dataclasses import dataclass
from functools import reduce
from itertools import accumulate, groupby
from operator import itemgetter
from pathlib import Path
from typing import Callable, Optional

from _utils.file_ops import ensure_dir_exists, read_text, write_text
from _utils.pipeline_types import ErrorType, PipelineError, Result
from agda_run import Clock, FileRun, Outcome, Runner, check_file, real_clock, run_agda

DEFAULT_TIMEOUT: float = 600.0

# Identifiers in printed Agda are separated by whitespace and these
# delimiters.  A dot never occurs in the scaffold's names: it separates a
# record from its field in a projection `R.f`, which mentions `R`.
_TOKEN = re.compile(r"[^\s(){}⦃⦄;.]+")
# "<path>:<line>.<column>-<end>: error: [Name]", where the end is a
# column or a line.column.
_ERROR = re.compile(r":(\d+)\.\d+-(?:\d+\.)?\d+: error: \[(\w+)\]")
_MODULE = re.compile(r"^module (\S+) where$", re.MULTILINE)


@dataclass(frozen=True)
class Item:
    """One declaration: its kind ("postulate", "data", "record",
    "mutual", "definition" or "pragma"), the names it declares, its text,
    and the data types and records among those names."""

    kind: str
    names: tuple[str, ...]
    text: str
    types: tuple[str, ...] = ()


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


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def declared_types(lines: tuple[str, ...]) -> tuple[str, ...]:
    """The types that the lines of a data type, a record or a mutual block
    declare, one per `data T` or `record T` line."""
    return tuple(words[1] for words in (line.split() for line in lines)
                 if words and words[0] in ("data", "record"))


def declared_names(lines: tuple[str, ...]) -> tuple[str, ...]:
    """The types and constructors that the lines of a data type, a record
    or a mutual block declare: each `data T` or `record T` line names a
    type; under a data type, each line one step deeper names a
    constructor; under a record, its `constructor` line does, and its
    fields, mentioned only as `T.f`, name nothing."""
    def step(acc: tuple[tuple[str, ...], Optional[tuple[str, int]]],
             line: str) -> tuple[tuple[str, ...], Optional[tuple[str, int]]]:
        names, current = acc
        words = line.split()
        if words and words[0] in ("data", "record"):
            return names + (words[1],), (words[0], _indent(line))
        if not words or current is None or _indent(line) != current[1] + 2:
            return acc
        if current[0] == "data":
            return names + (words[0],), current
        return (names + (words[1],), current) if words[0] == "constructor" else acc
    return reduce(step, lines, ((), None))[0]


def parse_item(text: str) -> Item:
    """Classify a block by its first line that is not a pragma and collect
    the names it declares."""
    lines = tuple(line for line in text.split("\n") if not line.startswith("{-#"))
    if not lines:
        return Item("pragma", (), text)
    words = lines[0].split()
    if words[0] == "postulate":
        return Item("postulate", (words[1],), text)
    if words[0] in ("data", "record", "mutual"):
        return Item(words[0], declared_names(lines), text, declared_types(lines))
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


def reach(start: frozenset[int], successors: Callable[[int], frozenset[int]]) -> frozenset[int]:
    """Everything reachable from `start` through `successors`, `start`
    included.  A loop over a frontier, not a recursion: a chain of
    references can be thousands of declarations long, and each one is
    visited once."""
    found, frontier = start, start
    while frontier:
        frontier = frozenset().union(*(successors(i) for i in frontier)) - found
        found = found | frontier
    return found


def types_only(module: Module) -> Module:
    """The module's data types, records and mutual blocks, and the
    declarations they mention, directly or through each other, in the
    module's order."""
    refs = references(module.items)
    keep = reach(frozenset(i for i, item in enumerate(module.items) if item.types), lambda i: refs[i])
    return Module(module.name, module.header, tuple(item for i, item in enumerate(module.items) if i in keep))


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
    line between blocks.  A running sum, not recursion: a scaffold of a
    few thousand declarations would exhaust Python's stack."""
    return tuple(accumulate((h + 1 for h in heights[:-1]), initial=first)) if heights else ()


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
    pairs = sorted((i, j) for j, r in enumerate(refs) if alive[j] for i in r)
    users = {i: frozenset(j for _, j in group) for i, group in groupby(pairs, key=itemgetter(0))}
    return (index,) + tuple(sorted(reach(frozenset((index,)), lambda i: users.get(i, frozenset())) - {index}))


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
    """The report: what checked, declarations and the data types and
    records among them, then one line per event."""
    total = len(state.items)
    types = sum(len(item.types) for item in state.items)
    checked_types = sum(len(item.types) for item, alive in zip(state.items, state.alive) if alive)
    lines = (f"checked {sum(state.alive)} of {total} declarations, "
             f"{checked_types} of {types} data types and records",) + tuple(
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
    parser.add_argument("--types-only", action="store_true")
    args = parser.parse_args(argv)
    with tempfile.TemporaryDirectory(prefix="scaffold-check-") as scratch:
        outcome = read_text(args.module).and_then(parse_module).map(
            lambda m: types_only(m) if args.types_only else m).and_then(
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
