"""
File: scripts/python/scaffold_check.py

Description:
  Type-check a profile U scaffold, the Agda module that
  `lake exe lean2agda --out DIR` writes for a closure, and report which
  declarations Agda refuses and which theorems had to unfold.

  Agda stops at the first error in a module, and a scaffold holds
  hundreds of declarations, some of which cannot check until the
  emitters of issues M2-5 and M2-7 supply the definitional unfolding
  they need.  The checker therefore runs Agda on a scratch copy of the
  module repeatedly, and at each error does one of three things.  When
  the error's message names a theorem, which the scaffold keeps in an
  `opaque` block, the theorem is re-emitted as a transparent
  definition, so that what needed it to unfold can see its value: the
  fallback of issue M2-6, counted and named in the listing.  Otherwise,
  when Agda refuses the clause of a declaration, the declaration becomes
  a postulate of its type, so that what uses it still checks; and when
  Agda refuses a declaration's type, the declaration and everything that
  refers to it are dropped.  It stops when the rest checks, and prints
  one line per event, in the order Agda met them, after two lines
  counting what checked (the declarations, and the data types and
  records the inductive types became) and what unfolded.  An unfolding
  is in vain when the declaration it was made for is refused all the
  same, and the listing says so.

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
    them: comment lines naming its kind, if any, then a postulate, a
    definition, an opaque block with its signature and clause indented
    under the keyword, a data type with its constructors on the lines
    under it, a record with its constructor and fields, or a mutual
    block of data types and records, each possibly after or before a
    pragma line.  The names a block declares are the ones its users can
    mention: a record's fields are mentioned as `R.f`, which names the
    record.
"""
from __future__ import annotations

import argparse
import re
import sys
import tempfile
from dataclasses import dataclass
from functools import reduce
from itertools import accumulate, groupby, takewhile
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
# The lines of an opaque block are indented under its keyword.
_INDENT = "  "


@dataclass(frozen=True)
class Item:
    """One declaration: its kind ("postulate", "data", "record",
    "mutual", "definition", "opaque" or "pragma"), the label of the
    comment lines heading it ("theorem", "opaque constant", "cyclic
    definition, postulated", or empty), the names it declares, the index
    of its signature line, its text, and the data types and records among
    those names."""

    kind: str
    label: str
    names: tuple[str, ...]
    signature: int
    text: str
    types: tuple[str, ...] = ()


@dataclass(frozen=True)
class Module:
    """A scaffold: its name, its header (options, comments, module line),
    and its declarations."""

    name: str
    header: str
    items: tuple[Item, ...]


@dataclass(frozen=True)
class Refusal:
    """Agda's first error: the line it points at, its name, the first
    line of its message, and the message proper, before the lines saying
    what Agda was checking."""

    line: int
    error: str
    message: str
    detail: str = ""


@dataclass(frozen=True)
class Event:
    """What the checker did to a declaration: "unfolded" (a theorem, for
    the dependent that needed it), "refused type", "refused value" or
    "dropped"."""

    action: str
    name: str
    error: str
    message: str
    dependent: str = ""


@dataclass(frozen=True)
class State:
    """The declarations as they stand, which are still in the module, and
    what has happened so far."""

    items: tuple[Item, ...]
    alive: tuple[bool, ...]
    events: tuple[Event, ...]


def is_theorem(item: Item) -> bool:
    """A theorem still in its opaque block, which the fallback may unfold."""
    return item.kind == "opaque" and item.label == "theorem"


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
    """Classify a block by its first line that is neither a comment nor a
    pragma and collect the names it declares: a data type, a record or a
    mutual block declares its types and constructors, and an opaque block
    declares the name on its signature line."""
    raw = text.split("\n")
    first = next((i for i, line in enumerate(raw) if not (line.startswith("--") or line.startswith("{-#"))), None)
    if first is None:
        return Item("pragma", "", (), 0, text)
    label = " ".join(line[2:].strip() for line in raw[:first] if line.startswith("--"))
    lines = tuple(line for line in raw[first:] if not line.startswith("{-#"))
    words = lines[0].split()
    if words[0] == "postulate":
        return Item("postulate", label, (words[1],), first, text)
    if words[0] in ("data", "record", "mutual"):
        return Item(words[0], label, declared_names(lines), first, text, declared_types(lines))
    if words[0] == "opaque":
        return Item("opaque", label, (lines[1].split()[0],), first + 1, text)
    return Item("definition", label, (words[0],), first, text)


def parse_module(text: str) -> Result[Module, PipelineError]:
    """Split a scaffold at its blank lines: the first block is the header."""
    blocks = text.rstrip("\n").split("\n\n")
    match = _MODULE.search(blocks[0])
    if match is None or len(blocks) < 2:
        return Result.err(PipelineError(ErrorType.PARSING_ERROR, "not a scaffold module"))
    return Result.ok(Module(match.group(1), blocks[0], tuple(parse_item(b) for b in blocks[1:])))


def code(item: Item) -> str:
    """The item's text without its comment lines, whose words are not
    references."""
    return "\n".join(line for line in item.text.split("\n") if not line.startswith("--"))


def references(items: tuple[Item, ...]) -> tuple[frozenset[int], ...]:
    """For each item, the other items whose names its code mentions."""
    owner = {name: i for i, item in enumerate(items) for name in item.names}
    return tuple(
        frozenset(owner[t] for t in _TOKEN.findall(code(item)) if t in owner and owner[t] != i)
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
    """The first error of Agda's output, the line of message after it,
    and the message proper: the lines up to the first that says what
    Agda was checking."""
    lines = output.splitlines()
    found = next(((i, m) for i, line in enumerate(lines) if (m := _ERROR.search(line))), None)
    if found is None:
        return None
    i, match = found
    after = tuple(line.strip() for line in lines[i + 1:] if line.strip())
    detail = " ".join(takewhile(lambda line: not line.startswith("when "), after))
    return Refusal(int(match.group(1)), match.group(2), after[0] if after else "", detail)


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


def unfoldable(items: tuple[Item, ...], alive: tuple[bool, ...], index: int, refusal: Refusal) -> Optional[int]:
    """The first theorem the error's message names that is still opaque
    and alive, other than the refused declaration itself."""
    owner = {name: i for i, item in enumerate(items) for name in item.names}
    return next((i for i in (owner.get(t) for t in _TOKEN.findall(refusal.detail))
                 if i is not None and i != index and alive[i] and is_theorem(items[i])), None)


def transparent(item: Item, dependent: str) -> Item:
    """A theorem re-emitted as a transparent definition, under a comment
    naming the declaration that needed it to unfold."""
    body = tuple(line[len(_INDENT):] for line in item.text.split("\n")[item.signature:])
    label = f"theorem, unfolded for {dependent}"
    return Item("definition", label, item.names, 1, "\n".join((f"-- {label}",) + body))


def postulated(item: Item) -> Item:
    """A declaration with a value reduced to a postulate of its type,
    keeping the comment that labels it."""
    signature = item.text.split("\n")[item.signature].strip()
    comment = (f"-- {item.label}",) if item.label else ()
    return Item("postulate", item.label, item.names, len(comment), "\n".join(comment + (f"postulate {signature}",)))


def step(state: State, index: int, offset: int, refusal: Refusal) -> State:
    """Apply one refusal.  A theorem the message names is made
    transparent; otherwise a declaration refused below its signature
    keeps its signature as a postulate, and anything else is dropped
    with its dependents."""
    item = state.items[index]
    theorem = unfoldable(state.items, state.alive, index, refusal)
    if theorem is not None:
        unfolded = transparent(state.items[theorem], item.names[0])
        items = state.items[:theorem] + (unfolded,) + state.items[theorem + 1:]
        event = Event("unfolded", unfolded.names[0], refusal.error, refusal.message, item.names[0])
        return State(items, state.alive, state.events + (event,))
    if item.kind in ("definition", "opaque") and offset > item.signature:
        items = state.items[:index] + (postulated(item),) + state.items[index + 1:]
        event = Event("refused value", item.names[0], refusal.error, refusal.message)
        return State(items, state.alive, state.events + (event,))
    gone = dependents(index, references(state.items), state.alive)
    alive = tuple(a and i not in gone for i, a in enumerate(state.alive))
    first = Event("refused type", item.names[0], refusal.error, refusal.message)
    rest = tuple(Event("dropped", state.items[i].names[0], "", "") for i in gone[1:])
    return State(state.items, alive, state.events + (first,) + rest)


def theorems(items: tuple[Item, ...]) -> int:
    """How many of the items are theorems, opaque, unfolded or postulated."""
    return sum(1 for item in items if item.label.startswith("theorem"))


def in_vain(events: tuple[Event, ...], index: int) -> bool:
    """Whether the unfolding at `index` was made for a declaration that
    was refused all the same: the first later event that is not another
    unfolding for it refuses it."""
    dependent = events[index].dependent
    later = (e for e in events[index + 1:] if not (e.action == "unfolded" and e.dependent == dependent))
    following = next(later, None)
    return following is not None and following.name == dependent and following.action.startswith("refused")


def listing(state: State, messages: bool) -> str:
    """The report: what checked, declarations and the data types and
    records among them, what unfolded and how much of it in vain, then
    one line per event."""
    total = len(state.items)
    types = sum(len(item.types) for item in state.items)
    checked_types = sum(len(item.types) for item, alive in zip(state.items, state.alive) if alive)
    vain = tuple(e.action == "unfolded" and in_vain(state.events, i) for i, e in enumerate(state.events))
    unfolded = sum(1 for e in state.events if e.action == "unfolded")
    lines = (f"checked {sum(state.alive)} of {total} declarations, "
             f"{checked_types} of {types} data types and records",
             f"unfolded {unfolded} of {theorems(state.items)} theorems, {sum(vain)} in vain") + tuple(
        " ".join(w for w in (e.action, e.error, e.name) if w)
        + (f" for {e.dependent}" if e.dependent else "")
        + (", in vain" if vain[i] else "")
        + (f" | {e.message}" if messages and e.message else "")
        for i, e in enumerate(state.events)
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
    remaining declarations check.  Each round unfolds one theorem or
    removes or rewrites one declaration, so there are at most as many
    rounds as theorems plus twice the declarations."""
    relative = Path(*module.name.split(".")).with_suffix(".agda")
    made = ensure_dir_exists((scratch / relative).parent)
    if made.is_err:
        return Result.err(made.unwrap_err())
    state = State(module.items, tuple(True for _ in module.items), ())
    runs, seconds = 0, 0.0
    for _ in range(2 * len(module.items) + theorems(module.items) + 1):
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
