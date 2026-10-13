"""
File: scripts/python/tests/test_corpus_tables.py

Description:
  Tests of corpus_tables.py: every pure table function, the edge
  (read_entries, read_sizes, main) on a temporary corpus, and one
  consistency check against the repository: the coverage table in
  corpus/README.md is the one corpus_tables.py prints from
  corpus/manifest.json.
"""
from __future__ import annotations

import io
import json
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

from corpus_manifest import FEATURES, AgdaFile, Entry, EntryFiles, Malformed
from corpus_tables import (
    ABBREVIATIONS, AgdaSize, EntrySize, agda_size, carries, code_lines, conjoined, coverage,
    entries_cell, entries_of, entry_size, export_bytes, format_coverage, format_matrix,
    format_sizes, main, marker, matrix_key, read_entries, read_sizes, render,
    sidecar_bytes, ticked,
)

REPO = Path(__file__).resolve().parents[3]
CC = ("--safe", "--cubical-compatible")
CU = ("--safe", "--cubical", "--guardedness")
SIDECAR = json.dumps({"bytes": 1_234_567, "sha256": "0" * 64, "command": "lake exe lean4export M -- n"})


def entry(ident: str, features: tuple[str, ...], tier: str = "T1",
          files: tuple[AgdaFile, ...] = (AgdaFile("A.agda", CC, "CC"),),
          status: str = "translated") -> Entry:
    """A well-formed entry with the given id, features, tier, files and status."""
    axioms = {"T0": (), "T1": ("propext",), "T2": ("propext", "Classical.choice")}[tier]
    return Entry(ident, "a theme", "N.n", "M", axioms, tier, features, files, status, 7)


A = entry("a", ("axioms", "k-and-uip"))
B = entry("b", ("k-and-uip",), tier="T0")
C = entry("c", ("k-and-uip", "quotients"), tier="T2")
FILES = EntryFiles(
    sources=(("A.agda", "{-# OPTIONS --safe --cubical-compatible #-}\nmodule A where\n"),),
    present=("A.agda",), has_statement=True, has_notes=True, term_bytes=56_062, sidecar=None,
)
A_BYTES = len(FILES.sources[0][1].encode("utf-8"))


class TestCoverage(unittest.TestCase):
    def test_entries_of(self) -> None:
        self.assertEqual(entries_of((A, B)).unwrap(), (A, B))
        bad = Malformed("x", "planned", ("broken",))
        self.assertIn("malformed entries (x)", entries_of((A, bad)).unwrap_err())

    def test_coverage_follows_the_catalog_and_the_manifest(self) -> None:
        found = dict(coverage((A, B, C)))
        self.assertEqual(tuple(dict(coverage((A,)))), FEATURES)
        self.assertEqual(found["k-and-uip"], ("a", "b", "c"))
        self.assertEqual(found["quotients"], ("c",))
        self.assertEqual(found["literals"], ())

    def test_ticked_and_conjoined(self) -> None:
        self.assertEqual(ticked(("a", "b")), "`a`, `b`")
        self.assertEqual(conjoined(("a",)), "`a`")
        self.assertEqual(conjoined(("a", "b")), "`a` and `b`")
        self.assertEqual(conjoined(("a", "b", "c")), "`a`, `b`, and `c`")

    def test_entries_cell(self) -> None:
        everyone = ("a", "b", "c", "d")
        self.assertEqual(entries_cell((), everyone), "none")
        self.assertEqual(entries_cell(everyone, everyone), "every entry")
        self.assertEqual(entries_cell(("a", "b", "c"), everyone), "every entry but `d`")
        self.assertEqual(entries_cell(("a", "b"), everyone), "`a`, `b`")

    def test_format_coverage(self) -> None:
        lines = format_coverage((A, B, C)).splitlines()
        self.assertEqual(lines[:2], ["| Feature | Entries | Count |", "| --- | --- | --- |"])
        self.assertEqual(len(lines), 2 + len(FEATURES))
        self.assertIn("| `k-and-uip` | every entry | 3 |", lines)
        self.assertIn("| `quotients` | `c` | 1 |", lines)
        self.assertIn("| `literals` | none | 0 |", lines)


class TestMatrix(unittest.TestCase):
    def test_every_feature_has_one_short_heading(self) -> None:
        self.assertEqual(tuple(ABBREVIATIONS), FEATURES)
        self.assertEqual(len(set(ABBREVIATIONS.values())), len(FEATURES))

    def test_matrix_key_spells_out_every_heading(self) -> None:
        key = matrix_key().splitlines()
        self.assertEqual(key[:2], ["| Column | Feature |", "| --- | --- |"])
        self.assertEqual(key[2:], [f"| `{ABBREVIATIONS[f]}` | `{f}` |" for f in FEATURES])

    def test_format_matrix(self) -> None:
        key, matrix = format_matrix((A, C)).split("\n\n")
        self.assertEqual(key, matrix_key())
        head, rule, row_a, row_c, totals = matrix.splitlines()
        self.assertTrue(head.startswith("| Entry | Issue | Tier | imp | pi | K |"))
        self.assertTrue(row_a.startswith("| `a` | [#7] | T1 |  |  | ✓ |"))
        self.assertTrue(row_a.endswith("| 2 |"))
        self.assertTrue(row_c.startswith("| `c` | [#7] | T2 |  |  | ✓ |  | ✓ |"))
        self.assertTrue(totals.startswith("| Entries | | | 0 | 0 | 2 | 0 | 1 | 1 |"))
        self.assertEqual(head.count("|"), row_a.count("|"))
        self.assertEqual(head.count("|"), totals.count("|"))


class TestSizes(unittest.TestCase):
    def test_code_lines(self) -> None:
        text = "\n".join((
            "{-# OPTIONS --safe #-}",
            "",
            "-- a line comment",
            "{- a block {- nested -}",
            "   comment -}",
            "module M where",
            "  x : String  -- trailing",
            '  x = "not -- a comment"',
            "",
        ))
        self.assertEqual(code_lines(text), 4)
        self.assertEqual(code_lines(""), 0)

    def test_agda_size(self) -> None:
        text = "{-# OPTIONS --safe #-}\n-- é\nmodule M where\n"
        self.assertEqual(agda_size("M.agda", "K", text), AgdaSize("M.agda", "K", 3, 2, len(text) + 1))

    def test_sidecar_bytes(self) -> None:
        self.assertEqual(sidecar_bytes(SIDECAR).unwrap(), 1_234_567)
        self.assertIn("not valid JSON", sidecar_bytes("{").unwrap_err())
        self.assertIn("no integer field bytes", sidecar_bytes('{"bytes": true}').unwrap_err())
        self.assertIn("no integer field bytes", sidecar_bytes("[1]").unwrap_err())

    def test_export_bytes(self) -> None:
        self.assertEqual(export_bytes(FILES).unwrap(), (56_062, False))
        with_sidecar = EntryFiles(FILES.sources, FILES.present, True, True, None, SIDECAR)
        self.assertEqual(export_bytes(with_sidecar).unwrap(), (1_234_567, True))
        neither = EntryFiles(FILES.sources, FILES.present, True, True, None, None)
        self.assertIn("neither", export_bytes(neither).unwrap_err())

    def test_entry_size(self) -> None:
        size = entry_size(A, FILES).unwrap()
        self.assertEqual(size, EntrySize("a", 56_062, False, (AgdaSize("A.agda", "CC", 2, 2, A_BYTES),)))
        two = entry("t", ("axioms",), files=(AgdaFile("A.agda", CC, "CC"), AgdaFile("B.agda", CU, "CU")))
        self.assertEqual(entry_size(two, FILES).unwrap_err(), "t: agda/B.agda is listed but missing")

    def test_entry_size_refuses_what_the_checker_refuses(self) -> None:
        small = json.dumps({"bytes": 500, "sha256": "0" * 64, "command": "c"})
        cases = (
            (56_062, SIDECAR, "holds both term.ndjson and term.sidecar.json"),
            (None, small, "bytes must be an integer above 1000000"),
            (None, "{", "is not valid JSON"),
            (2_000_000, None, "over the 1,000,000-byte limit"),
        )
        for term_bytes, sidecar, problem in cases:
            files = EntryFiles(FILES.sources, FILES.present, True, True, term_bytes, sidecar)
            self.assertIn(problem, entry_size(A, files).unwrap_err())

    def test_format_sizes(self) -> None:
        sizes = (
            EntrySize("a", 56_062, False, (AgdaSize("A.agda", "CC", 50, 18, 2_062),)),
            EntrySize("b", 1_234_567, True, (AgdaSize("B.agda", "CC", 69, 29, 2_508),
                                             AgdaSize("BC.agda", "CU", 92, 45, 3_796))),
        )
        self.assertEqual(format_sizes(sizes).splitlines(), [
            "| Entry | Export bytes | Agda file | Profile | Lines | Code lines | Agda bytes |",
            "| --- | --- | --- | --- | --- | --- | --- |",
            "| `a` | 56,062 | `A.agda` | CC | 50 | 18 | 2,062 |",
            "| `b` | 1,234,567 (sidecar) | `B.agda` | CC | 69 | 29 | 2,508 |",
            "| | | `BC.agda` | CU | 92 | 45 | 3,796 |",
        ])

    def test_marker(self) -> None:
        self.assertEqual(marker("sizes"),
                         "<!-- Generated by python3 scripts/python/corpus_tables.py --table sizes -->")

    def test_carries(self) -> None:
        block = marker("coverage") + "\n\n| a | b |\n| --- | --- |\n| 1 | 2 |"
        stale = block.replace("| 1 | 2 |", "| 1 | 3 |")
        self.assertTrue(carries(f"# T\n\n{block}\n\nProse.\n", block))
        self.assertTrue(carries(f"# T\n\n{block}\n", block))
        # a stale block, with or without a current copy elsewhere
        self.assertFalse(carries(f"{stale}\n\nProse.\n", block))
        self.assertFalse(carries(f"{stale}\n\n{block}\n", block))
        # an extra row after the generated ones
        self.assertFalse(carries(f"{block}\n| 3 | 4 |\n", block))
        self.assertFalse(carries("no marker here", block))


def write_corpus(root: Path) -> None:
    """A corpus of two entries: one translated, with a committed export,
    and one planned."""
    planned = {"id": "p", "theme": "t", "lean_name": "N.p", "lean_module": "M", "axioms": [],
               "tier": "T0", "features": ["universe-levels"],
               "agda_files": [{"path": "P.agda", "flags": list(CC), "profile": "CC"}],
               "status": "planned", "issue": 9}
    translated = dict(planned, id="a", features=["axioms", "k-and-uip"], axioms=["propext"],
                      tier="T1", status="translated",
                      agda_files=[{"path": "A.agda", "flags": list(CC), "profile": "CC"}])
    (root / "manifest.json").write_text(json.dumps([translated, planned]), "utf-8")
    (root / "a" / "agda").mkdir(parents=True)
    (root / "a" / "lean").mkdir()
    (root / "a" / "agda" / "A.agda").write_text(FILES.sources[0][1], "utf-8")
    (root / "a" / "lean" / "term.ndjson").write_text("x" * 100, "utf-8")


class TestEdge(unittest.TestCase):
    def test_read_entries_and_sizes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_corpus(root)
            entries = read_entries(root).unwrap()
            self.assertEqual([e.id for e in entries], ["a", "p"])
            sizes = read_sizes(root, entries).unwrap()
            self.assertEqual(sizes, (EntrySize("a", 100, False, (AgdaSize("A.agda", "CC", 2, 2, A_BYTES),)),))
            self.assertTrue(render("coverage", root, entries).unwrap().startswith(marker("coverage")))

    def test_read_entries_fails_without_a_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            self.assertTrue(read_entries(Path(tmp)).is_err)

    def test_main(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write_corpus(root)
            out = io.StringIO()
            with redirect_stdout(out):
                self.assertEqual(main(["--corpus", tmp]), 0)
            self.assertEqual(out.getvalue().count("<!-- Generated by"), 3)
            (root / "a" / "lean" / "term.ndjson").unlink()
            err = io.StringIO()
            with redirect_stderr(err), redirect_stdout(io.StringIO()):
                self.assertEqual(main(["--corpus", tmp, "--table", "sizes"]), 1)
            self.assertIn("neither term.ndjson nor term.sidecar.json", err.getvalue())


class TestRepository(unittest.TestCase):
    def test_the_readme_coverage_table_is_generated(self) -> None:
        readme = (REPO / "corpus" / "README.md").read_text("utf-8")
        generated = render("coverage", REPO / "corpus", read_entries(REPO / "corpus").unwrap()).unwrap()
        section = readme.split("\n## Coverage\n", 1)[1].split("\n## ", 1)[0]
        self.assertTrue(carries(readme, generated))
        self.assertIn(marker("coverage"), section)
        self.assertEqual(readme.count("| Feature | Entries | Count |"), 1)


if __name__ == "__main__":
    unittest.main()
