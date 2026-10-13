"""
File: scripts/python/corpus_tables.py

Description:
  The corpus's tables, generated from corpus/manifest.json and the files
  of each entry, for corpus/README.md and the gap report of issue M1-10
  (docs/foundations/gap-report-corpus.md).  There are three, as follows:

  - coverage: for each feature of the gap catalog, the entries whose
    manifest object lists it, and how many (corpus/README.md, Coverage);
  - matrix: the entries against the features, one row per entry, after a
    key to its column headings;
  - sizes: for each translated entry, the bytes of its exported kernel
    term (lean/term.ndjson, or the size its sidecar records) and, for
    each Agda file, its lines, its lines of code and its bytes.

  Run by `make corpus-tables`, which prints all three:

    python3 scripts/python/corpus_tables.py [--table coverage|matrix|sizes|all]
                                            [--corpus DIR]

Design Principles:
  - The tables count what the manifest says.  Its features follow the
    schema's closure rule (corpus/SCHEMA.md, Features: the declaration,
    the definitions it unfolds, and the lemmas it cites), so a feature
    one shared lemma brings in counts for every entry whose closure
    reaches that lemma.  Which uses come from the declaration itself is
    the gap report's reading of each entry's notes, not a field of the
    manifest, and nothing here guesses it.
  - Every function but the edge (read_entries, read_sizes, main) is pure;
    the sizes are computed from the EntryFiles that corpus_manifest's
    gather_entry_files reads, so that "lines of code" means the same
    tokens the checker reads pragmas with.
"""
from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from itertools import accumulate
from pathlib import Path
from typing import Mapping, Sequence

from _utils.file_ops import read_text
from _utils.pipeline_types import Result, sequence_results
from corpus_manifest import (
    FEATURES, Entry, EntryFiles, Item, decode_manifest, gather_entry_files, term_problems, tokens,
)

# The matrix's column headings, one per feature, short enough that the
# thirteen columns fit a page; the matrix prints this key above itself, as
# a table, which no Markdown wrapper re-flows.
ABBREVIATIONS: Mapping[str, str] = {
    "impredicative-prop": "imp",
    "proof-irrelevance": "pi",
    "k-and-uip": "K",
    "large-elimination": "elim",
    "quotients": "quot",
    "axioms": "ax",
    "universe-levels": "lvl",
    "structure-eta": "eta",
    "literals": "lit",
    "trust-escape-hatches": "hatch",
    "decidable-and-noncomputable": "dec",
    "nested-and-mutual-inductives": "mut",
    "projections-and-let": "proj",
}
TABLES: tuple[str, ...] = ("coverage", "matrix", "sizes")
MARK: str = "✓"
# The token kinds of corpus_manifest.tokens that are code rather than
# whitespace or a comment; the OPTIONS pragma counts as code.
CODE_KINDS: frozenset[str] = frozenset({"pragma", "string", "other"})


@dataclass(frozen=True)
class AgdaSize:
    """One Agda file of an entry: its name and profile, its lines (as
    `wc -l` counts them), its lines of code, and its bytes."""

    path: str
    profile: str
    lines: int
    code: int
    bytes: int


@dataclass(frozen=True)
class EntrySize:
    """A translated entry's export and Agda files.  `sidecar` says whether
    the export's size is the one lean/term.sidecar.json records (an export
    over 1 MB) rather than the size of a committed lean/term.ndjson."""

    id: str
    export_bytes: int
    sidecar: bool
    agda: tuple[AgdaSize, ...]


# ---------------------------------------------------------------------------
# Pure tables
# ---------------------------------------------------------------------------

def entries_of(items: Sequence[Item]) -> Result[tuple[Entry, ...], str]:
    """The manifest's entries, or which are malformed: the tables are only
    as good as the manifest, so a malformed entry stops them."""
    bad = tuple(item.label for item in items if not isinstance(item, Entry))
    if bad:
        return Result.err(f"malformed entries ({', '.join(bad)}); run make corpus-check")
    return Result.ok(tuple(item for item in items if isinstance(item, Entry)))


def coverage(entries: Sequence[Entry]) -> tuple[tuple[str, tuple[str, ...]], ...]:
    """For each feature, in the catalog's order, the ids of the entries
    that list it, in the manifest's order."""
    return tuple(
        (feature, tuple(e.id for e in entries if feature in e.features)) for feature in FEATURES
    )


def ticked(ids: Sequence[str]) -> str:
    """Ids in backquotes, separated by commas."""
    return ", ".join(f"`{i}`" for i in ids)


def conjoined(ids: Sequence[str]) -> str:
    """Ids in backquotes as a list in a sentence: `a`, `a` and `b`, or
    `a`, `b`, and `c`."""
    quoted = [f"`{i}`" for i in ids]
    if len(quoted) < 3:
        return " and ".join(quoted)
    return ", ".join(quoted[:-1]) + ", and " + quoted[-1]


def entries_cell(ids: Sequence[str], all_ids: Sequence[str]) -> str:
    """The entries that exercise a feature, named the short way: by their
    ids, as every entry, or as every entry but the few that do not, when
    those are at most half as many as the ones that do."""
    if not ids:
        return "none"
    missing = tuple(i for i in all_ids if i not in ids)
    if not missing:
        return "every entry"
    if 2 * len(missing) <= len(ids):
        return f"every entry but {conjoined(missing)}"
    return ticked(ids)


def format_coverage(entries: Sequence[Entry]) -> str:
    """The coverage table: one row per feature, with its entries and their
    count."""
    all_ids = tuple(e.id for e in entries)
    rows = tuple(
        f"| `{feature}` | {entries_cell(ids, all_ids)} | {len(ids)} |"
        for feature, ids in coverage(entries)
    )
    return "\n".join(("| Feature | Entries | Count |", "| --- | --- | --- |") + rows)


def matrix_key() -> str:
    """The matrix's column headings, spelled out, as a table."""
    rows = tuple(f"| `{ABBREVIATIONS[f]}` | `{f}` |" for f in FEATURES)
    return "\n".join(("| Column | Feature |", "| --- | --- |") + rows)


def format_matrix(entries: Sequence[Entry]) -> str:
    """The entries against the features: each entry's issue and tier, a
    mark where the manifest lists the feature, the count of each row and
    each column, and the key.  The issue prints as a reference link,
    [#N], which the Markdown file that carries the table defines."""
    head = "| Entry | Issue | Tier | " + " | ".join(ABBREVIATIONS[f] for f in FEATURES) + " | Features |"
    rule = "| --- | --- | --- | " + " | ".join("---" for _ in FEATURES) + " | --- |"
    rows = tuple(
        f"| `{e.id}` | [#{e.issue}] | {e.tier} | "
        + " | ".join(MARK if f in e.features else "" for f in FEATURES)
        + f" | {len(e.features)} |"
        for e in entries
    )
    totals = "| Entries | | | " + " | ".join(str(len(ids)) for _, ids in coverage(entries)) + " | |"
    return "\n".join((matrix_key(), "", head, rule) + rows + (totals,))


def code_lines(text: str) -> int:
    """The lines of an Agda file that hold code: a token other than
    whitespace or a comment, the OPTIONS pragma included."""
    found = tuple(tokens(text))
    starts = accumulate((lexeme.count("\n") for _, lexeme in found), initial=0)
    return len({line for (kind, _), line in zip(found, starts) if kind in CODE_KINDS})


def agda_size(path: str, profile: str, text: str) -> AgdaSize:
    """The size of one Agda file from its text."""
    return AgdaSize(path, profile, text.count("\n"), code_lines(text), len(text.encode("utf-8")))


def sidecar_bytes(text: str) -> Result[int, str]:
    """The export size a sidecar records."""
    try:
        data = json.loads(text)
    except json.JSONDecodeError as e:
        return Result.err(f"lean/term.sidecar.json is not valid JSON: {e}")
    size = data.get("bytes") if isinstance(data, dict) else None
    if isinstance(size, int) and not isinstance(size, bool):
        return Result.ok(size)
    return Result.err("lean/term.sidecar.json has no integer field bytes")


def export_bytes(files: EntryFiles) -> Result[tuple[int, bool], str]:
    """The export's size, and whether a sidecar records it."""
    if files.sidecar is not None:
        return sidecar_bytes(files.sidecar).map(lambda size: (size, True))
    if files.term_bytes is not None:
        return Result.ok((files.term_bytes, False))
    return Result.err("lean/ holds neither term.ndjson nor term.sidecar.json")


def entry_size(entry: Entry, files: EntryFiles) -> Result[EntrySize, str]:
    """A translated entry's sizes from what its directory holds.  The
    export's files must pass the checker's own rules first (both files, a
    sidecar for an export of 1 MB or less, a bad sidecar, an oversized
    term.ndjson), so that no size is printed for what make corpus-check
    calls malformed."""
    problems = term_problems(files.term_bytes, files.sidecar)
    if problems:
        return Result.err(f"{entry.id}: {problems[0]}")
    sources = dict(files.sources)
    missing = tuple(f.path for f in entry.agda_files if f.path not in sources)
    if missing:
        return Result.err(f"{entry.id}: agda/{missing[0]} is listed but missing")
    agda = tuple(agda_size(f.path, f.profile, sources[f.path]) for f in entry.agda_files)
    return export_bytes(files).map_err(lambda e: f"{entry.id}: {e}").map(
        lambda found: EntrySize(entry.id, found[0], found[1], agda)
    )


def format_sizes(sizes: Sequence[EntrySize]) -> str:
    """The sizes table: one row per Agda file, the entry and its export
    on the first row of each entry."""
    def rows(size: EntrySize) -> tuple[str, ...]:
        export = f"{size.export_bytes:,}" + (" (sidecar)" if size.sidecar else "")
        return tuple(
            (f"| `{size.id}` | {export} | " if i == 0 else "| | | ")
            + f"`{a.path}` | {a.profile} | {a.lines} | {a.code} | {a.bytes:,} |"
            for i, a in enumerate(size.agda)
        )
    head = ("| Entry | Export bytes | Agda file | Profile | Lines | Code lines | Agda bytes |",
            "| --- | --- | --- | --- | --- | --- | --- |")
    return "\n".join(head + sum((rows(s) for s in sizes), ()))


def marker(table: str) -> str:
    """The comment that heads a generated table in a Markdown file, naming
    the command that regenerates it."""
    return f"<!-- Generated by python3 scripts/python/corpus_tables.py --table {table} -->"


def carries(text: str, generated: str) -> bool:
    """Whether a Markdown text carries a generated block as it is: the
    block's marker (its first line) occurs exactly once, and from there to
    a blank line, or to the end, the text is the block."""
    mark = generated.split("\n", 1)[0]
    if text.count(mark) != 1:
        return False
    at = text[text.index(mark):]
    return at.rstrip("\n") == generated or at.startswith(generated + "\n\n")


# ---------------------------------------------------------------------------
# The edge
# ---------------------------------------------------------------------------

def read_entries(corpus: Path) -> Result[tuple[Entry, ...], str]:
    """The well-formed entries of corpus/manifest.json."""
    return (
        read_text(corpus / "manifest.json")
        .map_err(str)
        .and_then(decode_manifest)
        .and_then(entries_of)
    )


def read_size(corpus: Path, entry: Entry) -> Result[EntrySize, str]:
    """A translated entry's sizes, read from its directory."""
    return gather_entry_files(corpus / entry.id, entry).map_err(str).and_then(
        lambda files: entry_size(entry, files)
    )


def read_sizes(corpus: Path, entries: Sequence[Entry]) -> Result[tuple[EntrySize, ...], str]:
    """The sizes of every translated entry."""
    return sequence_results(
        [read_size(corpus, e) for e in entries if e.status == "translated"]
    ).map(tuple)


def render(table: str, corpus: Path, entries: Sequence[Entry]) -> Result[str, str]:
    """One table, headed by its marker."""
    if table == "coverage":
        body: Result[str, str] = Result.ok(format_coverage(entries))
    elif table == "matrix":
        body = Result.ok(format_matrix(entries))
    else:
        body = read_sizes(corpus, entries).map(format_sizes)
    return body.map(lambda text: f"{marker(table)}\n\n{text}")


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    """The command line."""
    parser = argparse.ArgumentParser(description="Print the corpus's tables from its manifest.")
    parser.add_argument("--table", choices=TABLES + ("all",), default="all",
                        help="which table to print (default: all three)")
    parser.add_argument("--corpus", type=Path, default=Path("corpus"),
                        help="the corpus directory (default: corpus)")
    return parser.parse_args(argv)


def main(argv: Sequence[str]) -> int:
    """Parse the arguments, read the corpus, print the tables."""
    args = parse_args(argv)
    chosen = TABLES if args.table == "all" else (args.table,)
    result = read_entries(args.corpus).and_then(
        lambda entries: sequence_results([render(t, args.corpus, entries) for t in chosen])
    )
    if result.is_err:
        print(f"corpus-tables: {result.unwrap_err()}", file=sys.stderr)
        return 1
    print("\n\n".join(result.unwrap()))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
