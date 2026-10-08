"""
File: scripts/python/atlas_report.py

Description:
  The report of the axiom atlas (issue M1-11), run by `make atlas` after
  `lake exe atlas` has written the records.

  It reads the atlas, one NDJSON record per constant of the environment
  of `import Mathlib` (atlas/README.md), with the run file the program
  writes beside it, and writes a Markdown report: the denominator, the
  tiers T0 to T3 overall, by kind, by module directory and by top-level
  namespace, each with and without auto-generated declarations; every
  T3 constant; the constants whose axioms Lean's `#print axioms`
  under-reports; the agreement with the axioms corpus/manifest.json
  records; the comparison with the two published counts; and the run's
  time and memory.  It also writes the tiers of every module as a
  tab-separated table beside the records, too long for the report.

    python3 scripts/python/atlas_report.py [ATLAS.ndjson] [--out REPORT.md]
        [--modules MODULES.tsv] [--manifest corpus/manifest.json]

  The atlas defaults to the one `lake exe atlas` writes for the pin in
  translator/lake-manifest.json.  The run file is read from beside the
  atlas and the module table written there, each named after the atlas
  as `lake exe atlas` names the run file (`--out FILE.ndjson` gives
  `FILE.run.json`); the report defaults to
  docs/reports/atlas-<the atlas's name>.md.

  It exits with status 1 if the atlas is malformed or disagrees with the
  corpus manifest about an entry's axioms.

Design Principles:
  - Parsing is total: a malformed line is an error value naming the
    line, never an exception.
  - Every count is a pure function of the parsed records; the report is
    a pure function of the counts, so tests build small atlases by hand.
  - main reads the files and writes the outputs; nothing else does.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import textwrap
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Mapping, Optional, Sequence

from _utils.file_ops import load_json, read_bytes, read_text, write_text
from _utils.pipeline_types import Result
from corpus_manifest import Entry, decode_manifest, tier_of

TIERS: tuple[str, ...] = ("T0", "T1", "T2", "T3")
KINDS: tuple[str, ...] = (
    "theorem", "definition", "inductive", "constructor", "recursor",
    "opaque", "axiom", "quotient",
)
class StringList:
    """Marks a field whose value must be a JSON array of strings."""


RECORD_FIELDS: tuple[tuple[str, type], ...] = (
    ("name", str), ("module", str), ("kind", str), ("axioms", StringList),
    ("tier", str), ("lean_omits", StringList), ("noncomputable", bool),
    ("unsafe", bool), ("partial", bool), ("private", bool),
    ("internal", bool), ("auto", bool),
)
# How many top-level namespaces the report lists by name.
TOP_NAMESPACES: int = 40
# The label of declarations that sit in no namespace, such as `mul_comm`.
ROOT: str = "(root)"
# A component of a printed name: quoted segments and characters other
# than the dot.
_COMPONENT = re.compile(r"(?:«[^»]*»|[^.«])+")


# ---------------------------------------------------------------------------
# Values
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Header:
    """The atlas's first line: what was imported, at which pins."""

    version: int
    lean: str
    lean_commit: str
    mathlib: str
    mathlib_commit: str
    imports: tuple[str, ...]
    constants: int


@dataclass(frozen=True, slots=True)
class Record:
    """One constant, as the atlas records it (atlas/README.md)."""

    name: str
    module: str
    kind: str
    axioms: tuple[str, ...]
    tier: str
    lean_omits: tuple[str, ...]
    noncomputable: bool
    unsafe: bool
    partial: bool
    private: bool
    internal: bool
    auto: bool


@dataclass(frozen=True)
class End:
    """The atlas's last line: the number of records, and the population
    and classical count of Mendoza-Smith's method."""

    records: int
    value_graph_population: int
    value_graph_classical: int


@dataclass(frozen=True)
class Atlas:
    """A whole atlas file."""

    header: Header
    records: tuple[Record, ...]
    end: End


@dataclass(frozen=True)
class Run:
    """The run file: seconds per phase, and peak memory in KiB."""

    import_seconds: float
    graph_seconds: float
    records_seconds: float
    total_seconds: float
    peak_rss_kib: Optional[int]


@dataclass(frozen=True)
class TierCounts:
    """How many constants fall in each tier."""

    t0: int = 0
    t1: int = 0
    t2: int = 0
    t3: int = 0

    @property
    def total(self) -> int:
        return self.t0 + self.t1 + self.t2 + self.t3

    def of(self, tier: str) -> int:
        """The count of one tier, by its name."""
        return {"T0": self.t0, "T1": self.t1, "T2": self.t2, "T3": self.t3}[tier]


@dataclass(frozen=True)
class Agreement:
    """One corpus entry beside the atlas: the axioms the manifest records,
    the exact axioms, and Lean's (the exact ones less `lean_omits`)."""

    id: str
    lean_name: str
    manifest_module: str
    atlas_module: Optional[str]
    manifest_axioms: tuple[str, ...]
    atlas_axioms: Optional[tuple[str, ...]]
    lean_axioms: Optional[tuple[str, ...]]

    @property
    def agrees(self) -> bool:
        """The constant is in the atlas, in the module the manifest names,
        with the same set of axioms."""
        return (self.atlas_axioms is not None
                and self.atlas_module == self.manifest_module
                and set(self.atlas_axioms) == set(self.manifest_axioms))


# ---------------------------------------------------------------------------
# Pure: parsing
# ---------------------------------------------------------------------------

def field_errors(obj: Mapping[str, object], fields: Sequence[tuple[str, type]]) -> tuple[str, ...]:
    """The fields that are missing or of the wrong JSON type.  A Boolean
    is not accepted where a number is wanted, though Python's bool is an
    int, and a `StringList` field must hold strings only."""
    def wrong(value: object, kind: type) -> bool:
        if kind is StringList:
            return not isinstance(value, list) or not all(isinstance(x, str) for x in value)
        return not isinstance(value, kind) or (kind is int and isinstance(value, bool))
    def name_of(kind: type) -> str:
        return "list of strings" if kind is StringList else kind.__name__
    return tuple(
        f"field {name} is missing" if name not in obj else f"field {name} is not a {name_of(kind)}"
        for name, kind in fields if name not in obj or wrong(obj[name], kind)
    )


def decode_atlas(raw: bytes) -> Result[str, str]:
    """The atlas's bytes as text; Lean writes UTF-8."""
    try:
        return Result.ok(raw.decode("utf-8"))
    except UnicodeDecodeError as e:
        return Result.err(f"not UTF-8 text (byte {e.start}: {e.reason})")


def parse_object(line: str) -> Result[dict, str]:
    """One line as a JSON object.  Nesting too deep for the parser's stack
    is malformed input like any other, not a crash."""
    try:
        value = json.loads(line)
    except json.JSONDecodeError as e:
        return Result.err(f"not JSON ({e.msg})")
    except RecursionError:
        return Result.err("not JSON (nested too deeply to parse)")
    return Result.ok(value) if isinstance(value, dict) else Result.err("not a JSON object")


def parse_header(line: str) -> Result[Header, str]:
    """The first line, `{"atlas": {...}}`."""
    def build(obj: dict) -> Result[Header, str]:
        inner = obj.get("atlas")
        if not isinstance(inner, dict):
            return Result.err("the first line is not the atlas header {\"atlas\": {...}}")
        errors = field_errors(inner, (
            ("version", int), ("lean", str), ("lean_commit", str), ("mathlib", str),
            ("mathlib_commit", str), ("imports", StringList), ("constants", int)))
        if errors:
            return Result.err(f"header: {'; '.join(errors)}")
        return Result.ok(Header(inner["version"], inner["lean"], inner["lean_commit"],
                                inner["mathlib"], inner["mathlib_commit"],
                                tuple(inner["imports"]), inner["constants"]))
    return parse_object(line).and_then(build)


def parse_end(line: str) -> Result[End, str]:
    """The last line, `{"end": {...}}`; a file without it was cut short."""
    def build(obj: dict) -> Result[End, str]:
        inner = obj.get("end")
        graph = inner.get("value_graph") if isinstance(inner, dict) else None
        if not isinstance(inner, dict) or not isinstance(graph, dict):
            return Result.err("the last line is not the end line {\"end\": {...}}; "
                              "the file was cut short")
        errors = (field_errors(inner, (("records", int),))
                  + field_errors(graph, (("population", int), ("classical", int))))
        if errors:
            return Result.err(f"end line: {'; '.join(errors)}")
        return Result.ok(End(inner["records"], graph["population"], graph["classical"]))
    return parse_object(line).and_then(build)


def parse_record(line: str) -> Result[Record, str]:
    """One record line; its tier must be the one its axioms imply."""
    def build(obj: dict) -> Result[Record, str]:
        errors = field_errors(obj, RECORD_FIELDS)
        if errors:
            return Result.err("; ".join(errors))
        axioms, omits = tuple(obj["axioms"]), tuple(obj["lean_omits"])
        if obj["tier"] != tier_of(axioms):
            return Result.err(f"tier {obj['tier']} is not the tier its axioms imply, {tier_of(axioms)}")
        if not set(omits) <= set(axioms):
            return Result.err("lean_omits names an axiom that axioms lacks")
        return Result.ok(Record(
            obj["name"], obj["module"], obj["kind"], axioms, obj["tier"], omits,
            obj["noncomputable"], obj["unsafe"], obj["partial"], obj["private"],
            obj["internal"], obj["auto"]))
    return parse_object(line).and_then(build)


def first_error(results: Iterable[tuple[int, Result[Record, str]]]) -> Optional[str]:
    """The first failed line, as 'line N: why', or None."""
    return next((f"line {n}: {r.unwrap_err()}" for n, r in results if r.is_err), None)


def parse_atlas(text: str) -> Result[Atlas, str]:
    """A whole atlas: the header, the records, the end line, and as many
    records as the end line and the header say."""
    lines = text.splitlines()
    if len(lines) < 2:
        return Result.err("the atlas has fewer than two lines")
    header, end = parse_header(lines[0]), parse_end(lines[-1])
    if header.is_err:
        return Result.err(f"line 1: {header.unwrap_err()}")
    if end.is_err:
        return Result.err(f"line {len(lines)}: {end.unwrap_err()}")
    parsed = [(n, parse_record(line)) for n, line in enumerate(lines[1:-1], start=2)]
    error = first_error(parsed)
    if error is not None:
        return Result.err(error)
    records = tuple(r.unwrap() for _, r in parsed)
    counts = {len(records), end.unwrap().records, header.unwrap().constants}
    if len(counts) != 1:
        return Result.err(f"{len(records)} records, but the end line says {end.unwrap().records} "
                          f"and the header {header.unwrap().constants}")
    return Result.ok(Atlas(header.unwrap(), records, end.unwrap()))


def parse_run(data: object) -> Result[Run, str]:
    """The run file's object."""
    if not isinstance(data, dict):
        return Result.err("the run file is not a JSON object")
    seconds = ("import_seconds", "graph_seconds", "records_seconds", "total_seconds")
    bad = [k for k in seconds if not isinstance(data.get(k), (int, float)) or isinstance(data.get(k), bool)]
    peak = data.get("peak_rss_kib")
    if bad or not (peak is None or (isinstance(peak, int) and not isinstance(peak, bool))):
        return Result.err(f"the run file lacks a number for {', '.join(bad) or 'peak_rss_kib'}")
    return Result.ok(Run(*(float(data[k]) for k in seconds), peak))


# ---------------------------------------------------------------------------
# Pure: names and modules
# ---------------------------------------------------------------------------

def name_components(name: str) -> tuple[str, ...]:
    """The components of a name as Lean prints it: split at the dots that
    are not inside «...», which quotes a component that is not an
    identifier."""
    return tuple(_COMPONENT.findall(name))


def user_name(record: Record) -> str:
    """The name without the `_private.<module>.0.` prefix of a private
    declaration."""
    prefix = f"_private.{record.module}.0."
    return record.name[len(prefix):] if record.private and record.name.startswith(prefix) else record.name


def namespace_of(record: Record) -> str:
    """The top-level namespace: the first component of the user name, or
    ROOT for a name of one component."""
    components = name_components(user_name(record))
    return components[0] if len(components) > 1 else ROOT


def root_of(module: str) -> str:
    """The module's first component: Mathlib, Init, Lean, Std, ..."""
    return name_components(module)[0]


def directory_of(module: str) -> str:
    """The module's first two components, its directory in Mathlib."""
    return ".".join(name_components(module)[:2])


def is_mathlib(record: Record) -> bool:
    """Declared in a module of Mathlib's own, `Mathlib` or `Mathlib.*`."""
    return root_of(record.module) == "Mathlib"


def lean_axioms(record: Record) -> tuple[str, ...]:
    """The axioms Lean's `collectAxioms` gives the constant."""
    return tuple(a for a in record.axioms if a not in record.lean_omits)


# ---------------------------------------------------------------------------
# Pure: counting
# ---------------------------------------------------------------------------

def tier_counts(tiers: Iterable[str]) -> TierCounts:
    """Count tier names."""
    c = Counter(tiers)
    return TierCounts(c["T0"], c["T1"], c["T2"], c["T3"])


def count_records(records: Iterable[Record]) -> TierCounts:
    """The tiers of the records."""
    return tier_counts(r.tier for r in records)


def grouped(records: Iterable[Record], key: Callable[[Record], str]) -> dict[str, TierCounts]:
    """The tiers of the records in each group, by the group's key."""
    c = Counter((key(r), r.tier) for r in records)
    keys = sorted({k for k, _ in c})
    return {k: TierCounts(c[(k, "T0")], c[(k, "T1")], c[(k, "T2")], c[(k, "T3")]) for k in keys}


def largest(groups: Mapping[str, TierCounts], n: int) -> tuple[tuple[str, TierCounts], ...]:
    """The n largest groups, largest first, ties by name."""
    return tuple(sorted(groups.items(), key=lambda kv: (-kv[1].total, kv[0]))[:n])


def rest(groups: Mapping[str, TierCounts], shown: Iterable[str]) -> TierCounts:
    """The sum of the groups not shown."""
    hidden = [c for k, c in groups.items() if k not in set(shown)]
    return TierCounts(*(sum(c.of(t) for c in hidden) for t in TIERS))


def depends_on_choice(record: Record) -> bool:
    """Classical.choice is among the exact axioms."""
    return "Classical.choice" in record.axioms


def agreements(entries: Sequence[Entry], by_name: Mapping[str, Record]) -> tuple[Agreement, ...]:
    """Each corpus entry beside its atlas record, if the atlas has one."""
    def one(e: Entry) -> Agreement:
        r = by_name.get(e.lean_name)
        return Agreement(e.id, e.lean_name, e.lean_module, r.module if r else None,
                         e.axioms, r.axioms if r else None, lean_axioms(r) if r else None)
    return tuple(one(e) for e in entries)


# ---------------------------------------------------------------------------
# Pure: formatting
# ---------------------------------------------------------------------------

def num(n: int) -> str:
    """A count with thousands separators."""
    return f"{n:,}"


def pct(part: int, whole: int) -> str:
    """A share to one decimal, '<0.1' for a share that is not zero but
    would print as one, or a dash when the whole is empty."""
    if not whole:
        return "-"
    share = 100 * part / whole
    return "<0.1" if 0 < share < 0.05 else f"{share:.1f}"


def table(header: Sequence[str], rows: Sequence[Sequence[str]], right: Sequence[bool]) -> str:
    """A Markdown table; `right` says which columns are numbers."""
    rule = ["---:" if r else "---" for r in right]
    return "\n".join("| " + " | ".join(cells) + " |" for cells in [list(header), rule, *map(list, rows)])


def tier_cells(c: TierCounts) -> list[str]:
    """Total, then each tier as 'count (percent)'."""
    return [num(c.total)] + [f"{num(c.of(t))} ({pct(c.of(t), c.total)})" for t in TIERS]


def tier_table(rows: Sequence[tuple[str, TierCounts]], label: str) -> str:
    """Rows of tier counts with percentages of each row's total."""
    return table([label, "constants", "T0 (%)", "T1 (%)", "T2 (%)", "T3 (%)"],
                 [[name, *tier_cells(c)] for name, c in rows], [False] + [True] * 5)


def group_table(rows: Sequence[tuple[str, TierCounts]], label: str) -> str:
    """Rows of tier counts, compact: the constructive share is T0 and T1."""
    return table([label, "constants", "T0", "T1", "T2", "T3", "T0+T1 (%)"],
                 [[name, num(c.total), *(num(c.of(t)) for t in TIERS),
                   pct(c.t0 + c.t1, c.total)] for name, c in rows],
                 [False] + [True] * 6)


def code(s: str) -> str:
    """Inline code."""
    return f"`{s}`"


def modules_tsv(records: Iterable[Record]) -> str:
    """Every module's tiers, all constants and those not auto-generated,
    as tab-separated values with a header line."""
    recs = tuple(records)
    every, manual = grouped(recs, lambda r: r.module), grouped((r for r in recs if not r.auto), lambda r: r.module)
    head = "\t".join(["module", "constants", *TIERS, "not_auto", *(f"not_auto_{t}" for t in TIERS)])
    def row(m: str) -> str:
        a, b = every[m], manual.get(m, TierCounts())
        return "\t".join([m, str(a.total), *(str(a.of(t)) for t in TIERS),
                          str(b.total), *(str(b.of(t)) for t in TIERS)])
    return "\n".join([head, *(row(m) for m in sorted(every))]) + "\n"


# ---------------------------------------------------------------------------
# The published counts (docs/related-work.md, "Mathlib measurements")
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Count:
    """How many constants of a population depend on Classical.choice:
    what was counted, at which Mathlib revision, and where the number
    comes from ("published", "measured" once outside `make atlas`, or
    "this atlas").  A published count may state no population, only a
    percentage."""

    what: str
    revision: str
    population: Optional[int]
    classical: int
    source: str
    percent: Optional[str] = None


# Mathlib pull request 35685 (R. Brasca), an open draft on a custom Lean
# fork.  Its body's master figure was entered on 2026-08-25 at 09:41 UTC
# (the body's edit history, GitHub GraphQL userContentEdits); master was
# then 661ab0b (09:28 UTC), on Lean v4.34.0-rc2, 429 commits past the tag
# v4.33.1.  The measured rows are the script in the body, run verbatim
# with `lake env lean` in a Mathlib checkout at each commit, under the
# Lean its lean-toolchain names, with Mathlib's cache for the commit
# (2026-10-08); its totals include the script's own 25 constants.
PR_COUNTS: tuple[Count, ...] = (
    Count("Pull request 35685, master", "661ab0b", None, 446_045, "published", "57.5"),
    Count("Pull request 35685, its branch", "custom Lean fork", 775_824, 430_049, "published"),
    Count("Pull request 35685's script", "661ab0b", 775_887, 446_081, "measured"),
    Count("Pull request 35685's script", "v4.33.1 (0df444a)", 771_154, 437_486, "measured"),
)

# Mendoza-Smith (arXiv 2606.28572) at Mathlib 9f0aee2, master of
# 2026-03-28 on Lean v4.29.0-rc8, which its repository's
# scripts/setup_mathlib.sh pins; v4.33.1 is 3,558 commits later.  The
# measured row is atlas/probes/ValueGraph.lean run the same way.
MS_COUNTS: tuple[Count, ...] = (
    Count("Mendoza-Smith", "9f0aee2", 471_260, 171_522, "published"),
    Count("Mendoza-Smith's method", "9f0aee2", 471_261, 171_523, "measured"),
)

# Mendoza-Smith's classical count with its restrictions lifted, by
# atlas/probes/ValueGraph.lean: the label, then the count at 9f0aee2 and
# at v4.33.1 (0df444a).
ABLATION: tuple[tuple[str, int, int], ...] = (
    ("none (the method)", 171_523, 184_823),
    ("edges from types", 173_127, 187_150),
    ("edges out of the other kinds", 190_336, 203_128),
    ("paths through internal names", 254_586, 275_391),
    ("types and other kinds", 191_131, 204_071),
    ("types and internal names", 257_699, 278_832),
    ("other kinds and internal names", 282_568, 305_632),
    ("all three (the exact count)", 283_651, 306_754),
)


def atlas_counts(atlas: Atlas) -> tuple[Count, Count, Count, Count]:
    """This atlas's four counts: the whole environment, exactly and by
    Lean's collectAxioms; Mendoza-Smith's method; and the exact count on
    Mendoza-Smith's population."""
    recs, end, h = atlas.records, atlas.end, atlas.header
    pin = f"{h.mathlib} ({h.mathlib_commit[:7]})"
    named = [r for r in recs if not r.internal]
    return (
        Count("Whole environment, exact", pin, len(recs),
              sum(depends_on_choice(r) for r in recs), "this atlas"),
        Count("Whole environment, Lean's `collectAxioms`", pin, len(recs),
              sum("Classical.choice" in lean_axioms(r) for r in recs), "this atlas"),
        Count("Mendoza-Smith's method", pin, end.value_graph_population,
              end.value_graph_classical, "this atlas"),
        Count("Mendoza-Smith's population, exact", pin, len(named),
              sum(depends_on_choice(r) for r in named), "this atlas"),
    )


def count_row(c: Count) -> list[str]:
    """A count as a row of the comparison table."""
    population = "not stated" if c.population is None else num(c.population)
    share = c.percent or (pct(c.classical, c.population) if c.population else "-")
    return [c.what, c.source, c.revision, population, num(c.classical), share]


def comparison_rows(atlas: Atlas) -> list[list[str]]:
    """The comparison table: each published count, the same method
    measured at its revision and at the pin, and this atlas's counts."""
    exact, lean, method, named = atlas_counts(atlas)
    return [count_row(c) for c in (*PR_COUNTS, exact, lean, *MS_COUNTS, method, named)]


# ---------------------------------------------------------------------------
# Pure: the report
# ---------------------------------------------------------------------------

# The width prose is wrapped to, as in the repository's Markdown files.
WIDTH: int = 72
# A space before what Markdown would read as the start of a block if a
# line began with it: a list marker, a heading, a quotation or a link
# definition.  wrap never breaks a line there.
_BEFORE_BLOCK = re.compile(r" (?=(?:[+*-]|\d+[.)])(?: |$)|#|>|\[[^\]]*\]:)")
# Stands for a space the wrapping must not break at.
_GLUE: str = "\x00"
SINGULARS: Mapping[str, str] = {
    "inductive": "inductive type", "opaque": "opaque constant", "quotient": "quotient constant",
}
PLURALS: Mapping[str, str] = {
    "theorem": "theorems", "definition": "definitions", "inductive": "inductive types",
    "constructor": "constructors", "recursor": "recursors", "opaque": "opaque constants",
    "axiom": "axioms", "quotient": "quotient constants",
}


def wrap(text: str, first: str = "", rest: str = "", width: int = WIDTH) -> str:
    """Fill the text to the width, never breaking a word, at a hyphen, or
    where the next line would start a Markdown block."""
    lines = textwrap.wrap(_BEFORE_BLOCK.sub(_GLUE, text), width, initial_indent=first,
                          subsequent_indent=rest, break_long_words=False,
                          break_on_hyphens=False)
    return "\n".join(lines).replace(_GLUE, " ")


def para(text: str) -> str:
    """A paragraph."""
    return wrap(text)


def bullet(text: str) -> str:
    """A bullet in the house style: a plus and two spaces, continuation
    lines indented three."""
    return wrap(text, "+  ", "   ")


def counted(n: int, kind: str) -> str:
    """'1 theorem', '1 opaque constant', '3 inductive types'."""
    return f"{num(n)} {SINGULARS.get(kind, kind) if n == 1 else PLURALS.get(kind, kind + 's')}"


def series(items: Sequence[str]) -> str:
    """'none', 'a', 'a and b', 'a, b and c'."""
    if not items:
        return "none"
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " and " + items[-1]


def beside(atlas: Path, suffix: str) -> Path:
    """A file beside the atlas, named after it as `lake exe atlas` names
    the run file (Atlas/Main.lean, `runFile`): the atlas's name up to its
    last dot, then the suffix."""
    return atlas.with_name(f"{atlas.stem}.{suffix}")


def report_path(repo: Path, atlas: Path) -> Path:
    """The report's default path, named after the atlas, so that the
    report of an atlas written with --out never overwrites the pin's."""
    return repo / "docs" / "reports" / f"atlas-{atlas.stem}.md"


def pinned_stem(manifest: str) -> Result[str, str]:
    """The same name from the text of translator/lake-manifest.json, as
    `lake exe atlas` derives its default output (Atlas/Main.lean)."""
    try:
        packages = json.loads(manifest).get("packages", [])
    except (json.JSONDecodeError, AttributeError):
        return Result.err("lake-manifest.json is not a JSON object")
    found = [p for p in packages if isinstance(p, dict) and p.get("name") == "mathlib"]
    if not found or not isinstance(found[0].get("inputRev"), str) or not isinstance(found[0].get("rev"), str):
        return Result.err("lake-manifest.json pins no mathlib with an inputRev and a rev")
    return Result.ok(f"mathlib-{found[0]['inputRev']}-{found[0]['rev'][:7]}")


def without_auto(records: Iterable[Record]) -> tuple[Record, ...]:
    """The records that are not auto-generated."""
    return tuple(r for r in records if not r.auto)


def blocks(*parts: str) -> str:
    """Blocks separated by blank lines."""
    return "\n\n".join(p for p in parts if p)


def section_intro(h: Header, atlas_file: str, report_file: str) -> str:
    return blocks(
        f"<!-- File: {report_file} -->",
        f"# Axiom atlas of Mathlib {h.mathlib}",
        para(f"Generated by `make atlas` from `{atlas_file}` by "
             "`scripts/python/atlas_report.py`; do not edit it by hand.  Issue M1-11 "
             "([#11]) produced the atlas; `atlas/README.md` describes its records."),
    )


def section_denominator(atlas: Atlas, mathlib: Sequence[Record]) -> str:
    h, recs = atlas.header, atlas.records
    modules = {r.module for r in recs}
    ml_modules = {r.module for r in mathlib}
    private = [r for r in mathlib if r.private]
    roots = grouped(recs, lambda r: root_of(r.module))
    root_rows = sorted(roots.items(), key=lambda kv: (-kv[1].total, kv[0]))
    return blocks(
        "## The denominator",
        "\n".join([
            bullet(f"**The environment**.  `import {', '.join(h.imports)}` at Mathlib {h.mathlib} "
                   f"(commit `{h.mathlib_commit[:7]}`), under Lean v{h.lean} (commit "
                   f"`{h.lean_commit[:7]}`), holds {num(len(recs))} constants declared in "
                   f"{num(len(modules))} modules.  The atlas records every one of them."),
            bullet(f"**This report's denominator** is the {num(len(mathlib))} constants declared "
                   f"in Mathlib's own {num(len(ml_modules))} modules (`Mathlib` and `Mathlib.*`), "
                   "auto-generated and private ones included.  The other "
                   f"{num(len(recs) - len(mathlib))} come from Lean (`Init`, `Std`, `Lean`, "
                   "`Lake`) and Mathlib's other dependencies; a count below includes them "
                   "only where it says so."),
            bullet("**Auto-generated** means Batteries' `isAutoDecl`, the test of the linter "
                   "framework Mathlib's `#lint` runs: names with macro scopes or an internal "
                   "component (`_proof_1`), reserved names (`eq_1`, `eq_def`), names ending "
                   "in a `match_`, `proof_` or `unsafe_` component, a constructor's `injEq` "
                   "and `noConfusion`, an inductive type's `casesOn`, `recOn`, `below` and "
                   "the like, and a structure's projections to its parents.  It does not "
                   "hold of a recursor `rec`, a constructor, or a structure's own fields.  "
                   "It judges a private name by the name it was written with; Lean's own "
                   "`isAutoDeclOrPrivate_Internal` counts every private declaration as "
                   f"generated.  Of Mathlib's {num(len(private))} private constants, "
                   f"{num(sum(r.auto for r in private))} are auto-generated by Batteries' "
                   f"test and {num(sum(not r.auto for r in private))} are not."),
            bullet("**The tiers** follow `corpus/SCHEMA.md` (\"Tiers from axioms\"): T0 no "
                   "axiom, T1 `propext` or `Quot.sound` only, T2 `Classical.choice`, T3 any "
                   "other axiom (`sorryAx`, `Lean.ofReduceBool`, the compiler's `lcProof`, "
                   "an axiom `native_decide` generates)."),
            bullet("**The axioms** of a constant are exact: those reachable from it along "
                   "the edges `Lean.collectAxioms` follows (the constants its type and value "
                   "use, and an inductive type's constructors).  At this Lean version "
                   "`#print axioms` leaves some out; a section below counts where."),
        ]),
        para("The constants of the environment by the first component of their module "
             "are as follows:"),
        group_table(root_rows, "module root"),
    )


def section_tiers(recs: Sequence[Record], mathlib: Sequence[Record]) -> str:
    rows = [
        ("Mathlib", count_records(mathlib)),
        ("Mathlib, without auto-generated", count_records(without_auto(mathlib))),
        ("Whole environment", count_records(recs)),
        ("Whole environment, without auto-generated", count_records(without_auto(recs))),
    ]
    return blocks("## Tiers", tier_table(rows, "scope"))


def section_kinds(mathlib: Sequence[Record]) -> str:
    def rows(rs: Sequence[Record]) -> list[tuple[str, TierCounts]]:
        g = grouped(rs, lambda r: r.kind)
        return [(k, g[k]) for k in KINDS if k in g]
    return blocks(
        "## Mathlib by kind",
        "All constants:", tier_table(rows(mathlib), "kind"),
        "Without auto-generated:", tier_table(rows(without_auto(mathlib)), "kind"),
    )


def section_directories(mathlib: Sequence[Record], modules_file: str) -> str:
    def rows(rs: Sequence[Record]) -> list[tuple[str, TierCounts]]:
        return sorted(grouped(rs, lambda r: directory_of(r.module)).items())
    return blocks(
        "## Mathlib by module directory",
        para("Modules are grouped by their first two components.  The tiers of each of "
             f"the {num(len({r.module for r in mathlib}))} modules are in `{modules_file}`, "
             "which `make atlas` writes beside the records and which is not committed."),
        "All constants:", group_table(rows(mathlib), "directory"),
        "Without auto-generated:", group_table(rows(without_auto(mathlib)), "directory"),
    )


def section_namespaces(mathlib: Sequence[Record]) -> str:
    def rows(rs: Sequence[Record]) -> list[tuple[str, TierCounts]]:
        groups = grouped(rs, namespace_of)
        named = {k: v for k, v in groups.items() if k != ROOT}
        top = largest(named, TOP_NAMESPACES)
        shown = [k for k, _ in top]
        return ([(code(k), c) for k, c in top]
                + [("no namespace", groups.get(ROOT, TierCounts())),
                   (f"the other {num(len(named) - len(shown))} namespaces", rest(named, shown))])
    ns = {namespace_of(r) for r in mathlib} - {ROOT}
    return blocks(
        "## Mathlib by top-level namespace",
        para("The namespace of a constant is the first component of its name, with a "
             "private name's prefix `_private.<module>.0.` removed; a name of one component, "
             f"such as `mul_comm`, is in no namespace.  Mathlib's constants use {num(len(ns))} "
             f"top-level namespaces; the {TOP_NAMESPACES} largest are listed."),
        "All constants:", group_table(rows(mathlib), "namespace"),
        "Without auto-generated:", group_table(rows(without_auto(mathlib)), "namespace"),
    )


def t3_safety(recs: Sequence[Record]) -> str:
    """Which T3 constants are not `unsafe`, and whether any theorem is T3."""
    t3 = [r for r in recs if r.tier == "T3"]
    safe = [code(r.name) for r in t3 if not r.unsafe]
    theorems = sum(r.kind == "theorem" for r in t3)
    rest_ = ("" if not safe else f"; the other is {safe[0]}" if len(safe) == 1
             else f"; the other {num(len(safe))} are {series(safe)}")
    thm = ("No theorem is T3." if not theorems
           else f"{counted(theorems, 'theorem')} {'is' if theorems == 1 else 'are'} T3.")
    return (f"Of the {num(len(t3))}, {num(len(t3) - len(safe))} are `unsafe`{rest_}.  {thm}  "
            "(`docs/lean-findings.md`, LF-2, has what this rules out.)")


def section_t3(recs: Sequence[Record], mathlib: Sequence[Record]) -> str:
    standard = {"propext", "Quot.sound", "Classical.choice"}
    t3 = [r for r in mathlib if r.tier == "T3"]
    causes = Counter(a for r in recs if r.tier == "T3" for a in r.axioms if a not in standard)
    return blocks(
        "## T3",
        para(f"The whole environment has {num(sum(r.tier == 'T3' for r in recs))} T3 "
             "constants.  The axioms other than the standard three that put them there, "
             "with the number of constants that depend on each (the axiom itself among "
             "them), are as follows:"),
        table(["axiom", "constants"],
              [[code(a), num(n)] for a, n in sorted(causes.items(), key=lambda kv: (-kv[1], kv[0]))],
              [False, True]),
        para(t3_safety(recs)),
        para(f"Mathlib's {num(len(t3))} T3 constants are as follows:"),
        table(["constant", "module", "kind", "other axioms"],
              [[code(r.name), code(r.module), r.kind,
                ", ".join(code(a) for a in r.axioms if a not in standard)] for r in t3],
              [False] * 4),
    )


def section_print_axioms(recs: Sequence[Record], mathlib: Sequence[Record]) -> str:
    short = [r for r in recs if r.lean_omits]
    ml_short = [r for r in mathlib if r.lean_omits]
    missing = Counter(a for r in short for a in r.lean_omits)
    moves = Counter((tier_of(lean_axioms(r)), r.tier) for r in ml_short)
    lean_ml = tier_counts(tier_of(lean_axioms(r)) for r in mathlib)
    kinds = Counter(r.kind for r in ml_short)
    by_axiom = [f"`{a}` for {num(n)}" for a, n in sorted(missing.items(), key=lambda kv: (-kv[1], kv[0]))]
    by_kind = [counted(n, k) for k, n in sorted(kinds.items(), key=lambda kv: (-kv[1], kv[0]))]
    standard = {"propext", "Quot.sound", "Classical.choice"}
    hidden = sum(any(a not in standard for a in r.lean_omits) for r in short)
    hatch = ("Every axiom Lean leaves out here is one of the standard three, though the "
             "same mechanism can hide `sorryAx` (`docs/lean-findings.md`, LF-1, has a "
             "two-file reproduction)." if not hidden else
             f"For {num(hidden)} of them Lean leaves out an axiom other than the standard "
             "three, a trust escape hatch (`docs/lean-findings.md`, LF-1).")
    return blocks(
        "## Where `#print axioms` falls short",
        para("`Lean.collectAxioms`, which `#print axioms` calls, caches the axioms of a "
             "constant it reaches while one of that constant's own dependencies is still "
             "being visited, counting that dependency as having none.  The cycles where "
             "this happens are an inductive type and its constructors (a constructor's type "
             "mentions its type, and the type depends on its constructors) and mutually "
             "recursive definitions such as the `_unsafe_rec` companions of mutual `partial "
             "def`s.  Each `.olean` stores a table of the axioms of "
             "its exported declarations computed this way, and an importing module trusts "
             "it (Lean issue [15226]; pull request [15385], open, would fix it for "
             "inductive types only).  The atlas computes reachability over the same edges "
             "instead, and records in `lean_omits` what Lean leaves out.  Lean never "
             "reports an axiom the atlas does not; the program checks that for every "
             "constant."),
        print_axioms_findings(short, ml_short, by_axiom, by_kind, hatch, lean_ml, moves),
    )


def print_axioms_findings(short: Sequence[Record], ml_short: Sequence[Record],
                          by_axiom: Sequence[str], by_kind: Sequence[str], hatch: str,
                          lean_ml: TierCounts, moves: Mapping[tuple[str, str], int]) -> str:
    """The counts of what Lean leaves out, or one sentence when it leaves
    nothing out, as on a small environment or once Lean's cache is fixed."""
    if not short:
        return bullet("Lean's `collectAxioms` gives every constant of this environment its "
                      "full axiom set.")
    changed = [[a, b, num(n)] for (a, b), n in sorted(moves.items()) if a != b]
    tiers = (f"With Lean's axiom sets, Mathlib's tiers would be T0 {num(lean_ml.t0)}, "
             f"T1 {num(lean_ml.t1)}, T2 {num(lean_ml.t2)} and T3 {num(lean_ml.t3)}.  ")
    return blocks(
        "\n".join([
            bullet(f"{num(len(short))} constants of the environment, {num(len(ml_short))} of "
                   "them in Mathlib, get an incomplete axiom set from Lean.  The axiom left "
                   f"out is {series(by_axiom)} of them."),
            *([bullet(f"Mathlib's {num(len(ml_short))} are {series(by_kind)}.")] if ml_short else []),
            bullet(hatch),
            bullet(tiers + ("The Mathlib constants whose tier changes are as follows:" if changed
                            else "No Mathlib constant changes tier.")),
        ]),
        table(["tier by Lean", "exact tier", "Mathlib constants"], changed,
              [False, False, True]) if changed else "",
    )


def section_corpus(agrees: Sequence[Agreement]) -> str:
    def axioms(axs: Optional[tuple[str, ...]]) -> str:
        return "-" if axs is None else (", ".join(code(a) for a in sorted(axs)) or "none")
    bad = [a for a in agrees if not a.agrees]
    verdict = (f"The atlas agrees with all {len(agrees)} entries of `corpus/manifest.json`: "
               "each constant is in the module the manifest names, with the axioms the "
               "manifest records, which `#print axioms` printed.") if not bad else (
               f"The atlas disagrees with {len(bad)} of the {len(agrees)} entries of "
               "`corpus/manifest.json`, and `make atlas` fails until they are reconciled.")
    return blocks(
        "## Agreement with the corpus",
        para(verdict),
        table(["entry", "constant", "module", "manifest", "atlas", "agrees"],
              [[a.id, code(a.lean_name), code(a.atlas_module or "-"), axioms(a.manifest_axioms),
                axioms(a.atlas_axioms), "yes" if a.agrees else "**no**"] for a in agrees],
              [False] * 6),
    )


def section_comparison(atlas: Atlas, mathlib: Sequence[Record]) -> str:
    exact, lean, method, named = atlas_counts(atlas)
    pr_at, pr_pin = PR_COUNTS[2], PR_COUNTS[3]
    ms, ms_at = MS_COUNTS
    imported_at = (pr_at.population or 0) - 25
    grown = imported_at - (exact.population or 0)
    ml_named = [r for r in mathlib if not r.internal]
    ml_choice = sum(depends_on_choice(r) for r in mathlib)
    manual = without_auto(mathlib)
    gap = named.classical - method.classical
    return blocks(
        "## Comparison with the published counts",
        para("Each row counts the constants of a population that depend on "
             "`Classical.choice`.  A published row is as its source gives it; a measured "
             "row ran once, outside `make atlas`, at the revision named, as the notes "
             "below say; the other rows are this atlas's."),
        table(["count", "source", "revision", "population", "Classical.choice", "%"],
              comparison_rows(atlas), [False, False, False, True, True, True]),
        "### Mathlib pull request 35685",
        "\n".join([
            bullet("**What it counts**.  Every constant of the environment of `import "
                   "Mathlib`, as this atlas's whole environment does: Lean's core, "
                   "Batteries, Mathlib and Mathlib's other dependencies, auto-generated and "
                   "private constants included.  A constant counts when the script's own "
                   "walk reaches `Classical.choice` along the constants its type and value "
                   "use and an inductive type's constructors, the edges of "
                   "`Lean.collectAxioms`."),
            bullet("**Which revision**.  The body's edit history shows the master figure "
                   "entered on 2026-08-25 at 09:41 UTC, when Mathlib's master was "
                   "`661ab0b`, on Lean v4.34.0-rc2, 429 commits ahead of the tag v4.33.1.  "
                   "The branch figure is of a Mathlib built on a custom Lean and a "
                   "custom Batteries; this atlas has nothing to compare it with."),
            bullet("**Reproduced**.  The script, run verbatim at `661ab0b` under Lean "
                   f"v4.34.0-rc2 with Mathlib's cache for that commit, printed "
                   f"{num(pr_at.classical)} of {num(pr_at.population or 0)}: "
                   f"{num(pr_at.classical - 446_045)} more than published, and the same "
                   "57.5 percent.  Its total includes the 25 constants the script "
                   "declares itself; the figure was entered 13 minutes after `661ab0b` was "
                   "committed and may have been measured at an earlier master."),
            bullet("**The difference from this atlas**.  Run at "
                   f"{exact.revision}, the script prints {num(pr_pin.classical)} of "
                   f"{num(pr_pin.population or 0)}; this atlas counts {num(exact.classical)} "
                   f"of {num(exact.population or 0)} exactly, and Lean's `collectAxioms` "
                   f"{num(lean.classical)}.  Between the two revisions the environment "
                   f"grows by {num(grown)} constants ({num(imported_at)} against "
                   f"{num(exact.population or 0)}, the script's own left out) and the "
                   f"script's count by {num(pr_at.classical - pr_pin.classical)}.  The "
                   "script's walk caches a constant reached through a cycle much as "
                   "`Lean.collectAxioms` does, so it falls short of the exact count: "
                   "run beside the atlas's search in one scratch file, it missed 141 "
                   "choice-dependent constants at v4.33.1 and 146 at `661ab0b`.  (The walk "
                   "is the pull request's code, which this repository does not copy.)"),
        ]),
        "### Mendoza-Smith",
        "\n".join([
            bullet("**What it counts**.  In the paper's repository "
                   "(`scripts/build_decl_graph.py`), its \"Mathlib declarations\" are every "
                   "constant of the environment of `import Lean` and `import Mathlib` "
                   "whose name is not internal: Lean's core and Mathlib's other "
                   "dependencies are included, and constants with a component that begins "
                   "with an underscore (`_proof_1`, `_private`) are not.  A declaration is "
                   "classical when `Classical.choice` is reachable from it in a graph "
                   "whose only edges run from the value of a definition or theorem to the "
                   "non-internal constants the value uses (`src/lean/kernel_graph.py`)."),
            bullet("**Which revision**.  Mathlib `9f0aee2`, master of 2026-03-28 on Lean "
                   "v4.29.0-rc8, which the repository's `scripts/setup_mathlib.sh` pins; "
                   "v4.33.1 is 3,558 commits later."),
            bullet("**Reproduced**.  `atlas/probes/ValueGraph.lean`, which implements the "
                   "method, run at `9f0aee2` under Lean v4.29.0-rc8 with Mathlib's cache "
                   f"for that commit, gives {num(ms_at.classical)} of "
                   f"{num(ms_at.population or 0)}: one more of each than published.  The "
                   "cause of the difference of one was not found; the paper's graph file "
                   "is not published."),
            bullet(f"**The difference from this atlas**.  At {method.revision} the method "
                   f"gives {num(method.classical)} of {num(method.population or 0)} "
                   f"({pct(method.classical, method.population or 0)} percent); the "
                   f"population has grown by {num((method.population or 0) - (ms_at.population or 0))} "
                   "since `9f0aee2`.  The exact count on the same population is "
                   f"{num(named.classical)} ({pct(named.classical, named.population or 0)} "
                   f"percent): the method misses {num(gap)} constants that depend on "
                   "`Classical.choice`.  Lifting its three restrictions, alone and "
                   "together, shows where they are, as follows:"),
        ]),
        table(["restrictions lifted", "classical at 9f0aee2", "classical at v4.33.1"],
              [[label, num(a) if a else "-", num(b)] for label, a, b in ABLATION],
              [False, True, True]),
        para("Paths through internal names matter most: a proof that reaches "
             "`Classical.choice` only through an auxiliary lemma (`_proof_1`) or a private "
             "declaration does not make its theorem classical.  The method's \"constructive\" "
             "therefore means that no path through public definitions and theorems reaches "
             "the axiom, and its classical count is a lower bound on dependence on "
             "`Classical.choice`, not a count of it."),
        "### Against this report's denominator",
        para("Neither published count is of Mathlib's own constants.  Of the "
             f"{num(len(mathlib))} constants declared in Mathlib's modules, "
             f"{num(ml_choice)} ({pct(ml_choice, len(mathlib))} percent) depend on "
             f"`Classical.choice`; of the {num(len(manual))} that are not auto-generated, "
             f"{num(sum(depends_on_choice(r) for r in manual))} "
             f"({pct(sum(depends_on_choice(r) for r in manual), len(manual))} percent).  "
             f"Mendoza-Smith's population holds {num(len(ml_named))} of Mathlib's constants, "
             f"of which {num(sum(depends_on_choice(r) for r in ml_named))} depend on it."),
    )


def section_run(run: Run, size: int, digest: str, atlas_file: str) -> str:
    peak = "not reported" if run.peak_rss_kib is None else f"{run.peak_rss_kib / 1024 / 1024:.1f} GiB"
    return blocks(
        "## Reproducing the atlas",
        para("`make atlas` runs `lake exe atlas` in `translator/` and then this report's "
             "generator.  The run that wrote these records took the following:"),
        "\n".join([
            bullet(f"{run.import_seconds:.0f} s to import Mathlib, {run.graph_seconds:.0f} s "
                   "for the dependency graphs and the exact axiom sets, and "
                   f"{run.records_seconds:.0f} s for the records, Lean's `collectAxioms` of "
                   f"each constant among them: {run.total_seconds:.0f} s in all;"),
            bullet(f"a peak resident memory of {peak}."),
        ]),
        para(f"The records, `{atlas_file}`, are {num(size)} bytes, with SHA-256 `{digest}`."),
    )


REFERENCES: str = """
[#11]: https://github.com/formalverification/lean2agda/issues/11
[15226]: https://github.com/leanprover/lean4/issues/15226
[15385]: https://github.com/leanprover/lean4/pull/15385
"""


def render_report(atlas: Atlas, run: Run, agrees: Sequence[Agreement],
                  size: int, digest: str, atlas_file: str, modules_file: str,
                  report_file: str) -> str:
    """The whole report."""
    recs = atlas.records
    mathlib = tuple(r for r in recs if is_mathlib(r))
    return blocks(
        section_intro(atlas.header, atlas_file, report_file),
        section_denominator(atlas, mathlib),
        section_tiers(recs, mathlib),
        section_kinds(mathlib),
        section_directories(mathlib, modules_file),
        section_namespaces(mathlib),
        section_t3(recs, mathlib),
        section_print_axioms(recs, mathlib),
        section_corpus(agrees),
        section_comparison(atlas, mathlib),
        section_run(run, size, digest, atlas_file),
        REFERENCES.strip(),
    ) + "\n"


# ---------------------------------------------------------------------------
# The edge
# ---------------------------------------------------------------------------

def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    repo = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description="Write the report of the axiom atlas.")
    parser.add_argument("atlas", type=Path, nargs="?", default=None,
                        help="the atlas (default: atlas/mathlib-<tag>-<commit>.ndjson, "
                             "named after the pin in translator/lake-manifest.json)")
    parser.add_argument("--out", type=Path, default=None,
                        help="the report (default: docs/reports/atlas-<the atlas's name>.md)")
    parser.add_argument("--modules", type=Path, default=None,
                        help="the per-module table (default: beside the atlas, <its name>.modules.tsv)")
    parser.add_argument("--manifest", type=Path, default=repo / "corpus" / "manifest.json",
                        help="the corpus manifest (default: corpus/manifest.json)")
    return parser.parse_args(argv)


def relative(path: Path) -> str:
    """A path as the report names it: relative to the repository root
    when it lies inside it."""
    repo = Path(__file__).resolve().parents[2]
    try:
        return str(path.resolve().relative_to(repo))
    except ValueError:
        return str(path)


def main(argv: Sequence[str]) -> int:
    """Read the atlas, the run file and the manifest; write the report and
    the module table; fail if the corpus disagrees."""
    args = parse_args(argv)
    repo = Path(__file__).resolve().parents[2]
    if args.atlas is None:
        stem = read_text(repo / "translator" / "lake-manifest.json").map_err(str).and_then(pinned_stem)
        if stem.is_err:
            print(f"atlas-report: {stem.unwrap_err()}", file=sys.stderr)
            return 1
        args.atlas = repo / "atlas" / f"{stem.unwrap()}.ndjson"
    raw = read_bytes(args.atlas)
    if raw.is_err:
        print(f"atlas-report: {raw.unwrap_err()}", file=sys.stderr)
        return 1
    parsed = decode_atlas(raw.unwrap()).and_then(parse_atlas)
    if parsed.is_err:
        print(f"atlas-report: {args.atlas}: {parsed.unwrap_err()}", file=sys.stderr)
        return 1
    atlas = parsed.unwrap()
    run = load_json(beside(args.atlas, "run.json")).map_err(str).and_then(parse_run)
    manifest = read_text(args.manifest).map_err(str).and_then(decode_manifest)
    for what, result in (("run file", run), ("manifest", manifest)):
        if result.is_err:
            print(f"atlas-report: {what}: {result.unwrap_err()}", file=sys.stderr)
            return 1
    entries = [e for e in manifest.unwrap() if isinstance(e, Entry)]
    if len(entries) != len(manifest.unwrap()):
        print("atlas-report: the manifest has malformed entries; `make corpus-check` names them",
              file=sys.stderr)
        return 1
    by_name = {r.name: r for r in atlas.records}
    agrees = agreements(entries, by_name)
    out = args.out or report_path(repo, args.atlas)
    modules = args.modules or beside(args.atlas, "modules.tsv")
    digest = hashlib.sha256(raw.unwrap()).hexdigest()
    report = render_report(atlas, run.unwrap(), agrees, len(raw.unwrap()), digest,
                           relative(args.atlas), relative(modules), relative(out))
    written = write_text(out, report).and_then(
        lambda _: write_text(modules, modules_tsv(r for r in atlas.records if is_mathlib(r))))
    if written.is_err:
        print(f"atlas-report: {written.unwrap_err()}", file=sys.stderr)
        return 1
    print(f"atlas-report: wrote {relative(out)} and {relative(modules)}")
    disagreeing = [a.id for a in agrees if not a.agrees]
    if disagreeing:
        print(f"atlas-report: the atlas disagrees with the corpus about {', '.join(disagreeing)}",
              file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
