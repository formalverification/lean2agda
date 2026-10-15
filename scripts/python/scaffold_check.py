"""
File: scripts/python/scaffold_check.py

Description:
  Type-check a profile U scaffold, the Agda module that
  `lake exe lean2agda --out DIR` writes for a closure, and report which
  declarations Agda refuses and which theorems had to unfold.

  Agda stops at the first error in a module, and a scaffold holds
  hundreds of declarations, some of which cannot check until the
  emitter of issue M2-7 supplies the definitional unfolding they need.  The checker therefore runs Agda on a scratch copy of the
  module repeatedly, and at each error does one of three things.  When
  the error's message names a theorem, which the scaffold keeps in an
  `opaque` block, the theorem is re-emitted as a transparent
  definition, so that what needed it to unfold can see its value: the
  fallback of issue M2-6, counted and named in the listing.  Otherwise,
  when Agda refuses the clause of a declaration, or its termination
  checker refuses a recursor block, the declaration becomes a postulate
  of its type, or one postulate per member of the block, so that what
  uses it still checks; and when Agda refuses a declaration's type, the
  declaration and everything that refers to it are dropped.  It stops
  when the rest checks, and prints one line per event, in the order Agda
  met them, after three lines counting what checked (the declarations,
  and the data types and records the inductive types became), what
  unfolded, and how many of the recursors are still defined by pattern
  matching.  An unfolding
  is in vain when the declaration it was made for is refused or dropped
  all the same, which the first later event at or beyond that
  declaration decides, and the listing says so.

    python3 scripts/python/scaffold_check.py [--agda AGDA]
        [--timeout SECONDS] [--heap SIZE] [--messages] [--types-only]
        MODULE.agda

  Agda runs with its heap bounded, 8G by default (`--heap`, GHC's
  `-M`), and names each declaration as it starts and ends it
  (`-v tc.decl:5`): a run that exhausts the heap or the time bound is
  charged to the declaration Agda named last, which is refused like any
  other, its value postulated or, for a type, the declaration dropped
  with what refers to it.  Agda's positivity check normalizes the types
  of a data type's constructors and a record's fields, and the normal
  form of some of Lean's compiled definitions is exponentially large.

  The listing is deterministic, so a test compares it with an expected
  one; `--messages` adds the first line of each error message.
  `--types-only` checks the data types and records and their recursors
  alone, with the declarations their types mention, directly or through
  each other, as postulates of their types: what Agda's positivity and
  termination checkers see, in a module a fraction of the size, since
  Agda's time grows faster than a module, and a theorem's proof can be
  tens of megabytes.  The number of Agda runs
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
    definition (one clause, or a recursor's clauses), an opaque block
    with its signature and clause indented under the keyword, a data
    type with its constructors on the lines under it, a record with its
    constructor and fields, a mutual block of data types and records, or
    a mutual block of recursors with their signatures first, each
    possibly after or before a pragma line.  The names a block declares
    are the ones its users can mention: a record's fields are mentioned
    as `R.f`, which names the record.
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from functools import reduce
from itertools import accumulate, groupby, takewhile
from operator import itemgetter
from pathlib import Path
from typing import Callable, Optional, Sequence

from _utils.file_ops import ensure_dir_exists, read_text, write_text
from _utils.pipeline_types import ErrorType, PipelineError, Result
from agda_run import Clock, FileRun, Outcome, Runner, check_file, real_clock, run_agda

DEFAULT_TIMEOUT: float = 600.0
DEFAULT_HEAP: str = "8G"

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
# The label of a recursor block, and the error of Agda's termination
# checker, which points at a block's first line, not at a clause.
_RECURSOR = "recursor"
_TERMINATION = "TerminationIssue"
# What a run that ran out of heap or time is charged with.  GHC's runtime
# exits with 251 when the heap is exhausted.
_HEAP = "HeapExhausted"
_TIME = "Timeout"
_HEAP_EXIT = "exit code 251"
# "Checking X." and "Checked X.", which `-v tc.decl:5` prints.
_CHECKING = re.compile(r"^Check(?:ing|ed) (\S+)\.$", re.MULTILINE)


@dataclass(frozen=True)
class Item:
    """One declaration: its kind ("postulate", "data", "record",
    "mutual", "definition", "opaque" or "pragma"), the label of the
    comment lines heading it ("theorem", "opaque constant", "cyclic
    definition, postulated", "recursor", or empty), the names it
    declares, the index of its signature line (of its last one, in a
    mutual block of definitions), its text, and the data types and
    records among those names."""

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


def signature_names(lines: tuple[str, ...]) -> tuple[str, ...]:
    """The definitions that the signature lines of a mutual block declare,
    `  f : T` one step under the keyword."""
    return tuple(words[0] for words in (line.split() for line in lines if _indent(line) == len(_INDENT))
                 if len(words) > 1 and words[1] == ":")


def parse_item(text: str) -> Item:
    """Classify a block by its first line that is neither a comment nor a
    pragma and collect the names it declares: a data type, a record or a
    mutual block of them declares its types and constructors, a mutual
    block of definitions the names on its signature lines, a block of
    postulates the name of each, and an opaque block the name on its
    signature line."""
    raw = text.split("\n")
    first = next((i for i, line in enumerate(raw) if not (line.startswith("--") or line.startswith("{-#"))), None)
    if first is None:
        return Item("pragma", "", (), 0, text)
    label = " ".join(line[2:].strip() for line in raw[:first] if line.startswith("--"))
    lines = tuple(line for line in raw[first:] if not line.startswith("{-#"))
    words = lines[0].split()
    if words[0] == "postulate":
        return Item("postulate", label, tuple(line.split()[1] for line in lines if line.startswith("postulate ")),
                    first, text)
    if words[0] == "mutual" and not declared_types(lines):
        names = signature_names(lines)
        return Item("mutual", label, names, first + len(names), text)
    if words[0] in ("data", "record", "mutual"):
        return Item(words[0], label, declared_names(lines), first, text, declared_types(lines))
    if words[0] == "opaque":
        return Item("opaque", label, (lines[1].split()[0],), first + 1, text)
    return Item("definition", label, (words[0],), first, text)


def parse_module(text: str) -> Result[Module, PipelineError]:
    """Split a scaffold at its blank lines: the first block is the header,
    and a scaffold whose every declaration was refused has nothing after
    it."""
    blocks = text.rstrip("\n").split("\n\n")
    match = _MODULE.search(blocks[0])
    if match is None:
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
    """The module's data types, records and mutual blocks, their
    recursors, and the declarations they mention, directly or through
    each other, in the module's order, every value but a recursor's
    postulated, so that only its signature is mentioning anything."""
    starts = frozenset(i for i, item in enumerate(module.items) if item.types or item.label == _RECURSOR)
    items = tuple(postulated(item) if has_value(item) and i not in starts else item
                  for i, item in enumerate(module.items))
    refs = references(items)
    keep = reach(starts, lambda i: refs[i])
    return Module(module.name, module.header, tuple(item for i, item in enumerate(items) if i in keep))


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


def capped(runner: Runner, heap: str) -> Runner:
    """The runner, with Agda's heap bounded and each declaration named as
    Agda starts and ends it."""
    def run(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
        return runner((command[0], "+RTS", f"-M{heap}", "-RTS", "-v", "tc.decl:5", *command[1:]), cwd, timeout)
    return run


def parse_exhaustion(run: FileRun) -> Optional[tuple[str, Refusal]]:
    """For a run that exhausted Agda's heap or time, the declaration Agda
    named last and the refusal it is charged with; None for any other
    run, or one that named no declaration."""
    error = _TIME if run.outcome == Outcome.TIMEOUT else _HEAP if run.message.endswith(_HEAP_EXIT) else None
    names = _CHECKING.findall(run.output)
    return (names[-1], Refusal(0, error, run.message, "")) if error and names else None


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


def has_value(item: Item) -> bool:
    """A declaration with clauses below its signatures: a definition, an
    opaque block, or a mutual block of definitions."""
    return item.kind in ("definition", "opaque") or (item.kind == "mutual" and not item.types)


def postulated(item: Item, label: Optional[str] = None) -> Item:
    """A declaration with a value reduced to a postulate of its type, or
    of each type of a mutual block, under the comment that labels it or
    the one given."""
    lines = item.text.split("\n")
    signatures = (tuple(line.strip() for line in lines[item.signature - len(item.names) + 1:item.signature + 1])
                  if item.kind == "mutual" else (lines[item.signature].strip(),))
    label = item.label if label is None else label
    comment = (f"-- {label}",) if label else ()
    return Item("postulate", label, item.names, len(comment),
                "\n".join(comment + tuple(f"postulate {s}" for s in signatures)))


def step(state: State, index: int, offset: int, refusal: Refusal) -> State:
    """Apply one refusal.  A theorem the message names is made
    transparent; otherwise a declaration refused below its signature, or
    by the termination checker, which points at its first line, keeps
    its signature as a postulate, and anything else is dropped with its
    dependents."""
    item = state.items[index]
    theorem = unfoldable(state.items, state.alive, index, refusal)
    if theorem is not None:
        unfolded = transparent(state.items[theorem], item.names[0])
        items = state.items[:theorem] + (unfolded,) + state.items[theorem + 1:]
        event = Event("unfolded", unfolded.names[0], refusal.error, refusal.message, item.names[0])
        return State(items, state.alive, state.events + (event,))
    if has_value(item) and refusal.error == _TERMINATION:
        label = f"{item.label}, refused by the termination checker" if item.label else "refused by the termination checker"
        items = state.items[:index] + (postulated(item, label),) + state.items[index + 1:]
        event = Event("refused value", item.names[0], refusal.error, refusal.message)
        return State(items, state.alive, state.events + (event,))
    if has_value(item) and (offset > item.signature or refusal.error in (_HEAP, _TIME)):
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


def recursors(items: tuple[Item, ...], alive: tuple[bool, ...]) -> tuple[int, int, int]:
    """How many recursors the items declare, how many of them are live
    and still defined by pattern matching, and how many the termination
    checker refused."""
    labelled = tuple((item, a) for item, a in zip(items, alive) if item.label.startswith(_RECURSOR))
    return (sum(len(item.names) for item, _ in labelled),
            sum(len(item.names) for item, a in labelled if a and item.kind != "postulate"),
            sum(len(item.names) for item, _ in labelled if item.label.endswith("termination checker")))


def in_vain(events: tuple[Event, ...], index: int, position: dict[str, int]) -> bool:
    """Whether the unfolding at `index` was made for a declaration that
    was refused or dropped all the same.  The first later event at or
    beyond that declaration in module order decides, since an event at an
    earlier declaration says nothing about it; further unfoldings for it
    are passed over too."""
    dependent = events[index].dependent
    later = (e for e in events[index + 1:]
             if not (e.action == "unfolded" and e.dependent == dependent)
             and position[e.name] >= position[dependent])
    following = next(later, None)
    return following is not None and following.name == dependent


def listing(state: State, messages: bool) -> str:
    """The report: what checked, declarations and the data types and
    records among them, what unfolded and how much of it in vain, the
    recursors still defined by pattern matching and those the termination
    checker refused, then one line per event."""
    total = len(state.items)
    types = sum(len(item.types) for item in state.items)
    checked_types = sum(len(item.types) for item, alive in zip(state.items, state.alive) if alive)
    position = {name: i for i, item in enumerate(state.items) for name in item.names}
    vain = tuple(e.action == "unfolded" and in_vain(state.events, i, position) for i, e in enumerate(state.events))
    unfolded = sum(1 for e in state.events if e.action == "unfolded")
    declared, defined, unterminated = recursors(state.items, state.alive)
    lines = (f"checked {sum(state.alive)} of {total} declarations, "
             f"{checked_types} of {types} data types and records",
             f"unfolded {unfolded} of {theorems(state.items)} theorems, {sum(vain)} in vain",
             f"defined {defined} of {declared} recursors by pattern matching, "
             f"{unterminated} refused by the termination checker") + tuple(
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
        refusal = parse_refusal(run.output) if run.outcome == Outcome.FAIL else None
        place = locate(layout, refusal.line) if refusal else None
        exhausted = parse_exhaustion(run) if refusal is None else None
        if exhausted is not None:
            owner = {name: i for i, item in enumerate(state.items) if state.alive[i] for name in item.names}
            refusal, place = exhausted[1], ((owner[exhausted[0]], 0) if exhausted[0] in owner else None)
        if refusal is None or place is None:
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
    parser.add_argument("--heap", default=DEFAULT_HEAP)
    parser.add_argument("--messages", action="store_true")
    parser.add_argument("--types-only", action="store_true")
    args = parser.parse_args(argv)
    with tempfile.TemporaryDirectory(prefix="scaffold-check-") as scratch:
        outcome = read_text(args.module).and_then(parse_module).map(
            lambda m: types_only(m) if args.types_only else m).and_then(
            lambda m: check_module(capped(run_agda, args.heap), real_clock, args.agda, m, args.timeout,
                                   Path(scratch)))
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
