"""
File: scripts/python/refusal_report.py

Description:
  The tables of issue M2-9 (docs/performance.md): for each emitted tree
  that `translator/scripts/goldens.sh` translated and checked, one row per
  emitted module with its size, its values, how many of them checked,
  how many Agda refused by class, how many stood behind a refused type,
  and the Agda time and peak memory of the refusal loop and of the final
  check; a row per tree; and the classes counted over every tree.

  A tree passes, under the reading of "accepted" that issue M2-9 took for
  Milestone 2's exit criterion, when every module of the loop's final
  state checks fresh in Agda and every refusal in its listings is
  classified to an issue other than M2-9's, with none unclassified.  A
  value the loop reduced to a postulate is refused, never checked; a
  value dropped with a refused type is charged to that type's class.
  The exit status is 1 unless every tree passes.

  The classes file holds one rule per line, `#N ERROR IDENTIFIER`: the
  issue the refusal belongs to, Agda's error as the listing names it,
  and the Agda identifier as the listing names it, which may be a glob
  (`*`, `?`, `[...]`); text after the identifier is a note, and a line
  that begins with `#` followed by a space is a comment.  The first rule
  that matches an event classifies it.

  Each RESULT directory holds what goldens.sh writes for one tree: the
  emitted tree under `tree/` (its modules, `closure.txt` and
  `refusals.txt`), the loop's listings under `listings/`, the loop's
  report `loop.txt`, the final check's JSON `final.json`, and
  `translate-seconds`.

    python3 scripts/python/refusal_report.py --classes FILE RESULT...

Design Principles:
  - Every function but the edge (read_result, main) is pure; the tree's
    declarations are parsed with scaffold_check's parser, so that a
    value means what the checker means by one (has_value, recursors
    left out), and a module's references with agda_check's.
  - A value counts once per name it declares: a mutual block of
    definitions refused is that many values, as its postulates are.
  - The refused types a dropped value stands behind are found by its
    references through the whole tree, since a module lists the values
    an imported module's refusal took from it first, without the type.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from fnmatch import fnmatchcase
from pathlib import Path
from typing import Mapping, Optional, Sequence

from _utils.file_ops import read_text
from _utils.pipeline_types import Result
from agda_check import Tree, build_tree, module_files, named, parse_source, topological
from scaffold_check import code, has_value, parse_module

# The issue this report is the test of: no refusal may be charged to it.
OWN_ISSUE = "#23"
# The label of a recursor block, which is not a value.
_RECURSOR = "recursor"
_RULE = re.compile(r"^(#[0-9]+)\s+(\S+)\s+(\S+)(?:\s+(.*))?$")
_EVENT = re.compile(r"^(refused value|refused type) (\S+) (\S+)$")
_DROPPED = re.compile(r"^dropped (\S+)$")
_UNFOLDED = re.compile(r"^unfolded (\S+) (\S+) for (\S+)(, in vain)?$")
_DECLARATIONS = re.compile(r"^checked [0-9]+ of ([0-9]+) declarations")
_ROW = re.compile(r"^(\S+)\s+([0-9]+)\s+([0-9.]+)\s+([0-9]+)\s")


@dataclass(frozen=True)
class Rule:
    """One line of the classes file."""

    issue: str
    error: str
    pattern: str
    note: str = ""


@dataclass(frozen=True)
class Event:
    """One event line of a listing: its action ("refused value", "refused
    type", "dropped" or "unfolded"), Agda's error, the declaration, and
    for an unfolding the dependent and whether it was in vain."""

    action: str
    error: str
    name: str
    dependent: str = ""
    vain: bool = False


@dataclass(frozen=True)
class LoopRow:
    """A module's row of the loop's report."""

    runs: int
    seconds: float
    peak_mib: int


@dataclass(frozen=True)
class FinalRow:
    """A module's row of the final check: its result, seconds and peak."""

    result: str
    seconds: float
    peak_kib: int


@dataclass(frozen=True)
class Declared:
    """What a module declares: each value's first name and how many names
    it declares, and for every name the identifiers its item names."""

    values: Mapping[str, int]
    refs: Mapping[str, frozenset[str]]


@dataclass(frozen=True)
class TreeRun:
    """One tree as goldens.sh leaves it, read: the tree, each module's
    text and listing, the loop's rows and summary, the final check's
    rows and wall time, the translation's seconds, the closure's
    constants and the declarations the translator refused."""

    name: str
    tree: Tree
    texts: Mapping[str, str]
    listings: Mapping[str, str]
    loop: Mapping[str, LoopRow]
    loop_summary: str
    final: Mapping[str, FinalRow]
    final_wall: float
    translate_seconds: float
    constants: int
    translator_refusals: int
    lean: frozenset[str]


@dataclass(frozen=True)
class ModuleReport:
    """One module's row."""

    name: str
    size: int
    declarations: int
    values: int
    refused: Mapping[str, int]
    behind: Mapping[str, int]
    types_refused: int
    unclassified: tuple[str, ...]
    loop: Optional[LoopRow]
    final: Optional[FinalRow]
    listed: bool = True

    @property
    def checked(self) -> int:
        """The values Agda accepted: none in a module the loop never
        listed, which it did not reach."""
        if not self.listed:
            return 0
        return self.values - sum(self.refused.values()) - sum(self.behind.values())


@dataclass(frozen=True)
class TreeReport:
    """One tree's rows and what it passes on."""

    name: str
    modules: tuple[ModuleReport, ...]
    result: TreeRun

    @property
    def unclassified(self) -> tuple[str, ...]:
        return tuple(u for m in self.modules for u in m.unclassified)

    @property
    def final_passes(self) -> bool:
        return all(m.final is not None and m.final.result == "pass" for m in self.modules)

    @property
    def unlisted(self) -> tuple[str, ...]:
        return tuple(m.name for m in self.modules if not m.listed)

    @property
    def passes(self) -> bool:
        return self.final_passes and not self.unclassified and not self.unlisted


# ---------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------

def parse_rules(text: str) -> Result[tuple[Rule, ...], str]:
    """The classes file's rules; an error for a line that is not a rule
    or a comment, or a rule charged to this report's own issue."""
    rules: list[Rule] = []
    for number, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped == "#" or stripped.startswith("# "):
            continue
        match = _RULE.match(stripped)
        if match is None:
            return Result.err(f"line {number}: not a rule: {stripped}")
        if match.group(1) == OWN_ISSUE:
            return Result.err(f"line {number}: a refusal cannot be charged to {OWN_ISSUE}, whose test this is")
        rules.append(Rule(match.group(1), match.group(2), match.group(3), match.group(4) or ""))
    return Result.ok(tuple(rules))


def parse_event(line: str) -> Optional[Event]:
    """An event line of a listing, without its message; None for a count
    line."""
    head = line.split(" | ", 1)[0]
    refused = _EVENT.match(head)
    if refused:
        return Event(refused.group(1), refused.group(2), refused.group(3))
    dropped = _DROPPED.match(head)
    if dropped:
        return Event("dropped", "", dropped.group(1))
    unfolded = _UNFOLDED.match(head)
    if unfolded:
        return Event("unfolded", unfolded.group(1), unfolded.group(2), unfolded.group(3),
                     unfolded.group(4) is not None)
    return None


def parse_listing(text: str) -> tuple[Event, ...]:
    """The events of a listing, in order."""
    return tuple(e for e in map(parse_event, text.splitlines()) if e is not None)


def declarations(listing: str) -> int:
    """The declarations a listing's first count line says the module has."""
    match = _DECLARATIONS.match(listing)
    return int(match.group(1)) if match else 0


def parse_loop(text: str) -> tuple[dict[str, LoopRow], str]:
    """The loop report's rows by module, and its summary line (modules,
    runs, passes, seconds)."""
    lines = text.splitlines()
    summary = next((line for line in lines if " modules, " in line and " Agda runs" in line), "")
    rows = {m.group(1): LoopRow(int(m.group(2)), float(m.group(3)), int(m.group(4)))
            for m in map(_ROW.match, lines) if m is not None}
    return rows, summary


def parse_final(text: str) -> Result[tuple[dict[str, FinalRow], float], str]:
    """The final check's rows by module, and its wall time."""
    try:
        data = json.loads(text)
        rows = {m["name"]: FinalRow(m["result"], float(m["seconds"]), int(m["peak_kib"]))
                for m in data["modules"]}
        return Result.ok((rows, float(data["wall_seconds"])))
    except (ValueError, KeyError, TypeError) as e:
        return Result.err(f"final.json: {e}")


def sidecar_identifiers(text: str) -> tuple[str, ...]:
    """The Agda identifiers a names sidecar maps to Lean names."""
    def agda(line: str) -> Optional[str]:
        try:
            record = json.loads(line)
        except ValueError:
            return None
        return record.get("agda") if isinstance(record, dict) else None
    return tuple(a for a in map(agda, text.splitlines()) if isinstance(a, str))


def declared(text: str, modules: frozenset[str], lean: frozenset[str]) -> Declared:
    """A module's values and references, from its emitted text.  A value
    is a Lean constant's, named in the tree's sidecars (`lean`); the
    operation table's helpers and rewrite rules, which no Lean constant
    has, are not values."""
    parsed = parse_module(text)
    if parsed.is_err:
        return Declared({}, {})
    module = parsed.unwrap()
    values = {item.names[0]: len(item.names) for item in module.items
              if item.names and has_value(item) and not item.label.startswith(_RECURSOR)
              and item.names[0] in lean}
    refs = {name: named(code(item), modules, module.name) for item in module.items for name in item.names}
    return Declared(values, refs)


# ---------------------------------------------------------------------------
# Classes and counts
# ---------------------------------------------------------------------------

def classify(event: Event, rules: Sequence[Rule]) -> Optional[str]:
    """The issue of the first rule that matches a refusal."""
    return next((r.issue for r in rules if r.error == event.error and fnmatchcase(event.name, r.pattern)), None)


def roots_behind(name: str, refs: Mapping[str, frozenset[str]], roots: frozenset[str]) -> frozenset[str]:
    """The refused types that `name` reaches through its references,
    itself included."""
    seen: set[str] = set()
    found: set[str] = set()
    stack = [name]
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        if current in roots:
            found.add(current)
        stack.extend(n for n in refs.get(current, frozenset()) if n not in seen)
    return frozenset(found)


def bump(counts: Mapping[str, int], key: str, by: int) -> dict[str, int]:
    """`counts` with `by` added at `key`."""
    return {**counts, key: counts.get(key, 0) + by}


def module_report(name: str, size: int, declared_count: int, values: Mapping[str, int], events: Sequence[Event],
                  rules: Sequence[Rule], type_class: Mapping[str, str],
                  behind_classes: Mapping[str, str], loop: Optional[LoopRow],
                  final: Optional[FinalRow], listed: bool = True) -> ModuleReport:
    """One module's counts: its refused values by class, its values behind
    a refused type by that type's class, its refused types, and every
    refusal no rule classifies."""
    refused: dict[str, int] = {}
    behind: dict[str, int] = {}
    unclassified: list[str] = []
    types_refused = 0
    for e in events:
        if e.action == "refused value":
            issue = classify(e, rules)
            if issue is None:
                unclassified.append(f"{name}: refused value {e.error} {e.name}")
            if e.name in values:
                refused = bump(refused, issue or "unclassified", values[e.name])
        elif e.action == "refused type":
            types_refused += 1
            if type_class.get(e.name) is None:
                unclassified.append(f"{name}: refused type {e.error} {e.name}")
        if e.action in ("refused type", "dropped") and e.name in values:
            behind = bump(behind, behind_classes.get(e.name, "unattributed"), values[e.name])
    unattributed = [f"{name}: {e.name} stands behind no refused type" for e in events
                    if e.action in ("refused type", "dropped") and e.name in values
                    and e.name not in behind_classes]
    return ModuleReport(name, size, declared_count, sum(values.values()), refused, behind, types_refused,
                        tuple(unclassified + unattributed), loop, final, listed)


def tree_report(result: TreeRun, rules: Sequence[Rule]) -> TreeReport:
    """Every module's row of one tree, in the tree's dependency order."""
    modules = frozenset(result.tree.modules)
    decls = {m: declared(result.texts.get(m, ""), modules, result.lean) for m in result.tree.modules}
    events = {m: parse_listing(result.listings.get(m, "")) for m in result.tree.modules}
    refused_types = {e.name: e for es in events.values() for e in es if e.action == "refused type"}
    type_class = {n: issue for n, e in refused_types.items() if (issue := classify(e, rules)) is not None}
    behind_names = [e.name for es in events.values() for e in es if e.action in ("refused type", "dropped")]
    refs: dict[str, frozenset[str]] = {}
    if behind_names:
        for d in decls.values():
            refs.update(d.refs)
    roots = frozenset(refused_types)
    def charged(n: str) -> Optional[str]:
        reached = roots_behind(n, refs, roots)
        classes = sorted({type_class.get(r, "unclassified") for r in reached})
        return "+".join(classes) if classes else None
    behind_classes = {n: c for n in behind_names if (c := charged(n)) is not None}
    order = topological(result.tree.graph)
    rows = tuple(module_report(m, result.tree.modules[m].size, declarations(result.listings.get(m, "")),
                               decls[m].values, events[m], rules, type_class,
                               behind_classes, result.loop.get(m), result.final.get(m),
                               bool(result.listings.get(m))) for m in order)
    return TreeReport(result.name, rows, result)


# ---------------------------------------------------------------------------
# Tables
# ---------------------------------------------------------------------------

def by_class(counts: Mapping[str, int]) -> str:
    """A total with its classes: `3 (#26 1, #27 2)`, or `0`."""
    total = sum(counts.values())
    if not total:
        return "0"
    return f"{total} (" + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) + ")"


def _mib(kib: int) -> int:
    return round(kib / 1024)


def _summed(reports: Sequence[ModuleReport], field: str) -> dict[str, int]:
    total: dict[str, int] = {}
    for m in reports:
        for k, v in getattr(m, field).items():
            total = bump(total, k, v)
    return total


def module_table(report: TreeReport) -> str:
    """The rows of a tree, one per emitted module."""
    head = ("| Module | KB | Declarations | Values | Checked | Refused | Behind a refused type | Types refused "
            "| Loop runs | Loop s | Loop MiB | Agda s | Agda MiB |\n"
            "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |\n")
    def row(m: ModuleReport) -> str:
        loop = (f"{m.loop.runs} | {m.loop.seconds:.1f} | {m.loop.peak_mib}" if m.loop else "| |")
        final = (f"{m.final.seconds:.1f} | {_mib(m.final.peak_kib)}" if m.final else "|")
        return (f"| `{m.name}` | {m.size / 1000:,.0f} | {m.declarations:,} | {m.values:,} | {m.checked:,} "
                f"| {by_class(m.refused)} "
                f"| {by_class(m.behind)} | {m.types_refused} | {loop} | {final} |")
    return head + "\n".join(map(row, report.modules)) + "\n"


def tree_row(report: TreeReport) -> str:
    """A tree's row of the summary table."""
    ms = report.modules
    r = report.result
    values = sum(m.values for m in ms)
    checked = sum(m.checked for m in ms)
    peak = max((m.final.peak_kib for m in ms if m.final), default=0)
    loop_peak = max((m.loop.peak_mib for m in ms if m.loop), default=0)
    loop_seconds = sum(m.loop.seconds for m in ms if m.loop)
    verdict = ("passes" if report.passes else "modules the loop did not reach" if report.unlisted
               else "unclassified refusals" if report.final_passes else "final state refused")
    return (f"| `{report.name}` | {r.constants:,} | {len(ms)} | {sum(m.size for m in ms) / 1e6:,.2f} "
            f"| {r.translate_seconds:.1f} | {r.translator_refusals} | {values:,} | {checked:,} "
            f"| {by_class(_summed(ms, 'refused'))} | {by_class(_summed(ms, 'behind'))} "
            f"| {sum(m.types_refused for m in ms)} | {loop_seconds:,.0f} | {loop_peak:,} "
            f"| {r.final_wall:.1f} | {_mib(peak):,} | {verdict} |")


SUMMARY_HEAD = ("| Tree | Constants | Modules | MB | Translate s | Translator refused | Values | Checked "
                "| Refused | Behind a refused type | Types refused | Loop Agda s | Loop MiB "
                "| Final wall s | Final MiB | Result |\n"
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |\n")


def class_table(reports: Sequence[TreeReport]) -> str:
    """The refused values and the values behind a refused type, by class,
    each tree a column."""
    classes = sorted({k for r in reports for m in r.modules for k in (*m.refused, *m.behind)})
    head = ("| Class | " + " | ".join(f"`{r.name}`" for r in reports) + " |\n"
            + "| --- |" + " --- |" * len(reports) + "\n")
    def cell(r: TreeReport, k: str) -> str:
        refused = _summed(r.modules, "refused").get(k, 0)
        behind = _summed(r.modules, "behind").get(k, 0)
        return f"{refused}" + (f" + {behind} behind" if behind else "")
    return head + "\n".join(f"| {k} | " + " | ".join(cell(r, k) for r in reports) + " |" for k in classes) + "\n"


def render(reports: Sequence[TreeReport]) -> str:
    """The summary, the classes, then each tree's modules and its loop."""
    parts = ["## Summary\n\n" + SUMMARY_HEAD + "\n".join(map(tree_row, reports)) + "\n",
             "## Classes\n\n" + class_table(reports)]
    for r in reports:
        problems = "".join(f"+  {u}\n" for u in r.unclassified)
        parts.append(f"## `{r.name}`\n\n{r.result.loop_summary}\n\n" + module_table(r)
                     + (f"\nUnclassified:\n\n{problems}" if problems else ""))
    return "\n".join(parts)


# ---------------------------------------------------------------------------
# The edge
# ---------------------------------------------------------------------------

def read_result(directory: Path) -> Result[TreeRun, str]:
    """One tree's directory, as goldens.sh writes it."""
    tree_dir = directory / "tree"
    sources = []
    texts: dict[str, str] = {}
    for p in module_files(tree_dir):
        text = read_text(tree_dir / p)
        if text.is_err:
            return Result.err(str(text.unwrap_err()))
        source = parse_source(p.as_posix(), text.unwrap())
        if source.is_err:
            return Result.err(source.unwrap_err())
        sources.append(source.unwrap())
        texts[source.unwrap().name] = text.unwrap()
    built = build_tree(sources)
    if built.is_err:
        return Result.err(f"{directory}: {built.unwrap_err()}")
    tree = built.unwrap()
    listings = {m: read_text(directory / "listings" / Path(s.path).with_suffix(".checked.txt")).unwrap_or("")
                for m, s in tree.modules.items()}
    loop, summary = parse_loop(read_text(directory / "loop.txt").unwrap_or(""))
    final = parse_final(read_text(directory / "final.json").unwrap_or("{}"))
    rows, wall = final.unwrap() if final.is_ok else ({}, 0.0)
    lean = frozenset(identifiers for p in sorted(tree_dir.rglob("*.names.ndjson"))
                     for identifiers in sidecar_identifiers(read_text(p).unwrap_or("")))
    seconds = read_text(directory / "translate-seconds").unwrap_or("0").strip() or "0"
    closure = read_text(tree_dir / "closure.txt").unwrap_or("")
    refusals = read_text(tree_dir / "refusals.txt").unwrap_or("")
    return Result.ok(TreeRun(directory.name, tree, texts, listings, loop, summary, rows, wall, float(seconds),
                             sum(1 for line in closure.splitlines() if line and not line.startswith("#")),
                             sum(1 for line in refusals.splitlines() if line and not line.startswith("#")),
                             lean))


def main(argv: Sequence[str]) -> int:
    """Read the classes and every tree, print the tables, and fail unless
    every tree passes."""
    parser = argparse.ArgumentParser(description="Tabulate checked trees and classify their refusals.")
    parser.add_argument("--classes", type=Path, required=True)
    parser.add_argument("results", type=Path, nargs="+")
    args = parser.parse_args(argv)
    rules = read_text(args.classes).map_err(str).and_then(parse_rules)
    if rules.is_err:
        print(f"refusal_report: {args.classes}: {rules.unwrap_err()}", file=sys.stderr)
        return 1
    reports = []
    for d in args.results:
        read = read_result(d)
        if read.is_err:
            print(f"refusal_report: {read.unwrap_err()}", file=sys.stderr)
            return 1
        reports.append(tree_report(read.unwrap(), rules.unwrap()))
    print(render(reports), end="")
    failing = [r for r in reports if not r.passes]
    for r in failing:
        why = (f"{len(r.unlisted)} modules the loop did not reach" if r.unlisted
               else "its final state did not check" if not r.final_passes
               else f"{len(r.unclassified)} unclassified")
        print(f"refusal_report: {r.name}: {why}", file=sys.stderr)
    return 1 if failing else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
