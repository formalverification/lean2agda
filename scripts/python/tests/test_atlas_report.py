"""
File: scripts/python/tests/test_atlas_report.py

Description:
  Tests of atlas_report.py: parsing, names, counts, formatting and the
  report on small atlases built by hand; main end to end on temporary
  files; and two consistency checks against the repository: the record
  fields the Lean program writes (translator/Atlas/Record.lean) are the
  ones the parser reads, and atlas/README.md documents each of them.
"""
from __future__ import annotations

import io
import json
import re
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import replace
from unittest import mock
from pathlib import Path
from typing import Any

from atlas_report import (
    RECORD_FIELDS, ROOT, Count, End, Record, Run, TierCounts,
    agreements, atlas_counts, blocks, bullet, code, comparison_rows, count_records, count_row,
    counted, depends_on_choice, directory_of, field_errors, first_error, group_table,
    grouped, is_mathlib, largest, lean_axioms, main, modules_tsv, name_components,
    namespace_of, num, para, parse_atlas, parse_end, parse_header, parse_object,
    parse_record, parse_run, pct, pinned_stem, render_report, rest, root_of, series,
    StringList, beside, decode_atlas, report_path,
    t3_safety,
    table, tier_cells, tier_counts, tier_table, user_name, without_auto, wrap,
)
from corpus_manifest import AgdaFile, Entry

REPO = Path(__file__).resolve().parents[3]

HEADER: dict[str, Any] = {"atlas": {
    "version": 0, "lean": "4.33.1", "lean_commit": "819816b2e0a3", "mathlib": "v4.33.1",
    "mathlib_commit": "0df444a360ea", "imports": ["Mathlib"], "constants": 3}}
END: dict[str, Any] = {"end": {"records": 3, "value_graph": {"population": 2, "classical": 1}}}


def raw(name: str, module: str, axioms: list[str], **changes: Any) -> dict[str, Any]:
    """A record as the Lean program writes it, its tier from its axioms."""
    from corpus_manifest import tier_of
    base: dict[str, Any] = {
        "name": name, "module": module, "kind": "theorem", "axioms": axioms,
        "tier": tier_of(axioms), "lean_omits": [], "noncomputable": False,
        "unsafe": False, "partial": False, "private": False, "internal": False,
        "auto": False}
    base.update(changes)
    return base


def rec(name: str, module: str, axioms: list[str], **changes: Any) -> Record:
    """A parsed record."""
    return parse_record(json.dumps(raw(name, module, axioms, **changes))).unwrap()


CHOICE = ["Classical.choice", "Quot.sound", "propext"]
RAWS = [
    raw("Classical.choice", "Init.Prelude", ["Classical.choice"], kind="axiom"),
    raw("Finset.card_image", "Mathlib.Data.Finset.Card", CHOICE),
    raw("Foo.mk", "Mathlib.Data.Foo", ["propext"], kind="constructor", lean_omits=["propext"]),
]


def text_of(lines: list[dict[str, Any]]) -> str:
    return "\n".join(json.dumps(x) for x in lines) + "\n"


ATLAS_TEXT = text_of([HEADER, *RAWS, END])
ATLAS = parse_atlas(ATLAS_TEXT).unwrap()
RUN = Run(19.5, 42.1, 137.7, 199.3, 7_869_216)


class TestParsing(unittest.TestCase):
    def test_field_errors(self) -> None:
        self.assertEqual(field_errors({"a": 1, "b": True}, (("a", int), ("b", bool))), ())
        self.assertEqual(field_errors({"a": True}, (("a", int),)), ("field a is not a int",))
        self.assertEqual(field_errors({}, (("a", str),)), ("field a is missing",))
        self.assertEqual(field_errors({"a": ["x", "y"]}, (("a", StringList),)), ())
        self.assertEqual(field_errors({"a": ["x", []]}, (("a", StringList),)),
                         ("field a is not a list of strings",))
        self.assertEqual(field_errors({"a": "x"}, (("a", StringList),)),
                         ("field a is not a list of strings",))

    def test_parse_object(self) -> None:
        self.assertEqual(parse_object('{"a": 1}').unwrap(), {"a": 1})
        self.assertTrue(parse_object("[1]").is_err)
        self.assertTrue(parse_object("{").is_err)
        # Whether this much nesting overflows the parser's stack depends on
        # the machine's stack size (it did here, not on the CI runner), so
        # only an error is required; the overflow branch is driven below.
        self.assertTrue(parse_object("[" * 100_000).is_err)
        with mock.patch("atlas_report.json.loads", side_effect=RecursionError):
            self.assertEqual(parse_object("[]").unwrap_err(), "not JSON (nested too deeply to parse)")

    def test_decode_atlas(self) -> None:
        self.assertEqual(decode_atlas("«x»\n".encode("utf-8")).unwrap(), "«x»\n")
        self.assertIn("not UTF-8 text (byte 0", decode_atlas(b"\xff\xfe").unwrap_err())

    def test_parse_header(self) -> None:
        h = parse_header(json.dumps(HEADER)).unwrap()
        self.assertEqual((h.mathlib, h.imports, h.constants), ("v4.33.1", ("Mathlib",), 3))
        self.assertTrue(parse_header(json.dumps(RAWS[0])).is_err)
        broken = {"atlas": {**HEADER["atlas"], "constants": "3"}}
        self.assertIn("constants", parse_header(json.dumps(broken)).unwrap_err())
        imports = {"atlas": {**HEADER["atlas"], "imports": [1]}}
        self.assertIn("field imports is not a list of strings", parse_header(json.dumps(imports)).unwrap_err())

    def test_parse_end(self) -> None:
        self.assertEqual(parse_end(json.dumps(END)).unwrap(), End(3, 2, 1))
        self.assertIn("cut short", parse_end(json.dumps(RAWS[1])).unwrap_err())

    def test_parse_record(self) -> None:
        r = parse_record(json.dumps(RAWS[2])).unwrap()
        self.assertEqual((r.kind, r.axioms, r.lean_omits, r.tier), ("constructor", ("propext",), ("propext",), "T1"))
        self.assertIn("tier", parse_record(json.dumps({**RAWS[1], "tier": "T1"})).unwrap_err())
        self.assertIn("lean_omits", parse_record(json.dumps({**RAWS[1], "lean_omits": ["sorryAx"]})).unwrap_err())
        self.assertIn("field axioms is not a list of strings",
                      parse_record(json.dumps({**RAWS[1], "axioms": [[]]})).unwrap_err())
        self.assertIn("field lean_omits is not a list of strings",
                      parse_record(json.dumps({**RAWS[1], "lean_omits": [["x"]]})).unwrap_err())
        self.assertIn("field auto is missing",
                      parse_record(json.dumps({k: v for k, v in RAWS[1].items() if k != "auto"})).unwrap_err())

    def test_first_error(self) -> None:
        ok, bad = parse_record(json.dumps(RAWS[1])), parse_record("{")
        self.assertIsNone(first_error([(2, ok)]))
        self.assertTrue(first_error([(2, ok), (3, bad)]).startswith("line 3: "))

    def test_parse_atlas(self) -> None:
        self.assertEqual(len(ATLAS.records), 3)
        self.assertEqual(ATLAS.end, End(3, 2, 1))
        self.assertIn("cut short", parse_atlas(text_of([HEADER, *RAWS])).unwrap_err())
        self.assertIn("2 records", parse_atlas(text_of([HEADER, *RAWS[:2], END])).unwrap_err())
        self.assertIn("line 3", parse_atlas(text_of([HEADER, RAWS[0], {"x": 1}, RAWS[2], END])).unwrap_err())
        self.assertIn("fewer than two", parse_atlas("{}").unwrap_err())

    def test_parse_run(self) -> None:
        good = {"import_seconds": 1, "graph_seconds": 2.5, "records_seconds": 3,
                "total_seconds": 6.5, "peak_rss_kib": 1024}
        self.assertEqual(parse_run(good).unwrap(), Run(1.0, 2.5, 3.0, 6.5, 1024))
        self.assertEqual(parse_run({**good, "peak_rss_kib": None}).unwrap().peak_rss_kib, None)
        self.assertTrue(parse_run({**good, "graph_seconds": True}).is_err)
        self.assertTrue(parse_run([]).is_err)


class TestNames(unittest.TestCase):
    def test_name_components(self) -> None:
        self.assertEqual(name_components("A.«b.c».d"), ("A", "«b.c»", "d"))
        self.assertEqual(name_components("«term∎»"), ("«term∎»",))
        self.assertEqual(name_components("_private.M.N.0.foo"), ("_private", "M", "N", "0", "foo"))

    def test_user_name_and_namespace(self) -> None:
        private = rec("_private.Mathlib.X.0.Foo.bar", "Mathlib.X", [], private=True)
        self.assertEqual(user_name(private), "Foo.bar")
        self.assertEqual(namespace_of(private), "Foo")
        self.assertEqual(namespace_of(rec("mul_comm", "Mathlib.Algebra.Group.Defs", [])), ROOT)
        self.assertEqual(namespace_of(rec("_private.Mathlib.X.0.go", "Mathlib.X", [], private=True)), ROOT)

    def test_modules(self) -> None:
        self.assertEqual(root_of("Mathlib.Data.Finset.Card"), "Mathlib")
        self.assertEqual(directory_of("Mathlib.Data.Finset.Card"), "Mathlib.Data")
        self.assertEqual(directory_of("Mathlib"), "Mathlib")
        self.assertTrue(is_mathlib(ATLAS.records[1]))
        self.assertFalse(is_mathlib(ATLAS.records[0]))
        self.assertFalse(is_mathlib(rec("x", "MathlibExtra.Y", [])))

    def test_lean_axioms(self) -> None:
        self.assertEqual(lean_axioms(ATLAS.records[2]), ())
        self.assertEqual(lean_axioms(ATLAS.records[1]), tuple(CHOICE))


class TestCounting(unittest.TestCase):
    def test_tier_counts(self) -> None:
        c = tier_counts(["T0", "T2", "T2", "T3"])
        self.assertEqual((c.t0, c.t1, c.t2, c.t3, c.total, c.of("T2")), (1, 0, 2, 1, 4, 2))
        self.assertEqual(count_records(ATLAS.records), TierCounts(0, 1, 2, 0))

    def test_grouped_largest_rest(self) -> None:
        g = grouped(ATLAS.records, lambda r: root_of(r.module))
        self.assertEqual(list(g), ["Init", "Mathlib"])
        self.assertEqual(g["Mathlib"], TierCounts(0, 1, 1, 0))
        self.assertEqual(largest(g, 1), (("Mathlib", g["Mathlib"]),))
        self.assertEqual(rest(g, ["Mathlib"]), g["Init"])

    def test_depends_on_choice_and_without_auto(self) -> None:
        self.assertEqual([depends_on_choice(r) for r in ATLAS.records], [True, True, False])
        self.assertEqual(without_auto([rec("a", "M", [], auto=True), rec("b", "M", [])]),
                         (rec("b", "M", []),))

    def test_agreements(self) -> None:
        entry = Entry("finset-card-image", "theme", "Finset.card_image", "Mathlib.Data.Finset.Card",
                      ("propext", "Classical.choice", "Quot.sound"), "T2", ("axioms",),
                      (AgdaFile("A.agda", ("--safe",), "K"),), "planned", 9)
        by_name = {r.name: r for r in ATLAS.records}
        [a] = agreements([entry], by_name)
        self.assertTrue(a.agrees)
        moved = replace(entry, lean_module="Mathlib.Elsewhere")
        self.assertFalse(agreements([moved], by_name)[0].agrees)
        [missing] = agreements([entry], {})
        self.assertFalse(missing.agrees)
        self.assertIsNone(missing.atlas_axioms)


class TestFormatting(unittest.TestCase):
    def test_numbers(self) -> None:
        self.assertEqual(num(1234567), "1,234,567")
        self.assertEqual((pct(1, 3), pct(0, 0), pct(0, 5), pct(41, 569189)), ("33.3", "-", "0.0", "<0.1"))

    def test_tables(self) -> None:
        self.assertEqual(table(["a", "n"], [["x", "1"]], [False, True]),
                         "| a | n |\n| --- | ---: |\n| x | 1 |")
        self.assertEqual(tier_cells(TierCounts(1, 1, 2, 0))[:2], ["4", "1 (25.0)"])
        self.assertIn("| Mathlib | 2 | 0 (0.0) |", tier_table([("Mathlib", TierCounts(0, 1, 1, 0))], "scope"))
        self.assertIn("| Mathlib | 2 | 0 | 1 | 1 | 0 | 50.0 |", group_table([("Mathlib", TierCounts(0, 1, 1, 0))], "root"))
        self.assertEqual(code("x"), "`x`")

    def test_wrap(self) -> None:
        text = " ".join(["word + not a bullet 1. nor a list # nor a heading [x]: nor a link"] * 9)
        for width in range(30, 80):
            lines = wrap(text, width=width).splitlines()
            self.assertEqual(" ".join(lines), text)
            for line in lines[1:]:
                self.assertNotRegex(line, r"^([+*-] |\d+[.)] |#|\[x\]:)")
        self.assertTrue(all(len(line) <= 72 for line in para("a " * 100).splitlines()))
        lines = bullet("b " * 60).splitlines()
        self.assertTrue(lines[0].startswith("+  ") and all(l.startswith("   ") for l in lines[1:]))
        self.assertEqual(para("one.  Two."), "one.  Two.")

    def test_t3_safety(self) -> None:
        recs = [rec("sorryAx", "Init.Prelude", ["sorryAx"], kind="axiom"),
                rec("Part.unwrap", "Mathlib.Data.Part", ["lcProof"], kind="definition", unsafe=True),
                rec("lcProof", "Init.Prelude", ["lcProof"], kind="axiom", unsafe=True),
                rec("Foo", "M", [])]
        self.assertEqual(t3_safety(recs), "Of the 3, 2 are `unsafe`; the other is `sorryAx`.  "
                         "No theorem is T3.  (`docs/lean-findings.md`, LF-2, has what this rules out.)")
        self.assertIn("1 theorem is T3.", t3_safety([rec("t", "M", ["sorryAx"])]))

    def test_words(self) -> None:
        self.assertEqual((counted(1, "theorem"), counted(1, "opaque"), counted(3, "inductive")),
                         ("1 theorem", "1 opaque constant", "3 inductive types"))
        self.assertEqual((series([]), series(["a"]), series(["a", "b"]), series(["a", "b", "c"])),
                         ("none", "a", "a and b", "a, b and c"))
        self.assertEqual(blocks("a", "", "b"), "a\n\nb")
        self.assertEqual(beside(Path("/a/foo.ndjson"), "run.json"), Path("/a/foo.run.json"))
        self.assertEqual(beside(Path("/a/mathlib-v4.33.1-0df444a.ndjson"), "modules.tsv"),
                         Path("/a/mathlib-v4.33.1-0df444a.modules.tsv"))
        self.assertEqual(report_path(Path("/r"), Path("/a/foo.ndjson")), Path("/r/docs/reports/atlas-foo.md"))

    def test_pinned_stem(self) -> None:
        manifest = json.dumps({"packages": [
            {"name": "batteries", "rev": "4488d40d", "inputRev": "main"},
            {"name": "mathlib", "rev": "0df444a360ea", "inputRev": "v4.33.1"}]})
        self.assertEqual(pinned_stem(manifest).unwrap(), "mathlib-v4.33.1-0df444a")
        self.assertTrue(pinned_stem('{"packages": []}').is_err)
        self.assertTrue(pinned_stem("[]").is_err)
        self.assertTrue(pinned_stem("{").is_err)

    def test_modules_tsv(self) -> None:
        tsv = modules_tsv(ATLAS.records[1:]).splitlines()
        self.assertEqual(tsv[0].split("\t")[:3], ["module", "constants", "T0"])
        self.assertEqual(tsv[1].split("\t")[:6], ["Mathlib.Data.Finset.Card", "1", "0", "0", "1", "0"])
        self.assertEqual(len(tsv), 3)

    def test_counts(self) -> None:
        exact, lean, method, named = atlas_counts(ATLAS)
        self.assertEqual((exact.population, exact.classical, exact.revision), (3, 2, "v4.33.1 (0df444a)"))
        self.assertEqual((lean.population, lean.classical), (3, 2))
        self.assertEqual((method.population, method.classical), (2, 1))
        self.assertEqual((named.population, named.classical), (3, 2))
        self.assertEqual(count_row(Count("x", "r", None, 5, "published", "57.5")),
                         ["x", "published", "r", "not stated", "5", "57.5"])
        self.assertEqual(count_row(method), ["Mendoza-Smith's method", "this atlas",
                                             "v4.33.1 (0df444a)", "2", "1", "50.0"])
        rows = comparison_rows(ATLAS)
        self.assertEqual(len(rows), 10)
        self.assertEqual([r[1] for r in rows].count("this atlas"), 4)

    def test_render_report(self) -> None:
        report = render_report(ATLAS, RUN, (), 1234, "ab" * 32, "atlas/x.ndjson",
                               "atlas/x.modules.tsv", "docs/reports/x.md")
        self.assertTrue(report.startswith("<!-- File: docs/reports/x.md -->\n\n# Axiom atlas of Mathlib v4.33.1\n"))
        self.assertIn("the 2 constants declared in Mathlib's own 2 modules", report.replace("\n   ", " "))
        self.assertIn("1 constants of the environment, 1 of them in Mathlib", report.replace("\n   ", " "))
        self.assertIn("is one of the standard three, though the same mechanism can hide `sorryAx`",
                      report.replace("\n   ", " "))
        self.assertIn("| T0 | T1 | 1 |", report)
        self.assertIn("[15226]: https://github.com/leanprover/lean4/issues/15226", report)
        self.assertNotIn("—", report)
        self.assertTrue(all(len(line) <= 72 for line in report.splitlines()
                            if not line.startswith(("|", "<!--", "[", "#")) and "SHA-256" not in line
                            and "`atlas/" not in line))


class TestDegenerateAtlases(unittest.TestCase):
    """Atlases with nothing to say in some section: no omission by Lean (a
    small import, or every atlas once Lean's cache is fixed), no T3, no
    Mathlib constant at all."""

    def render(self, lines: list[dict[str, Any]]) -> str:
        header = {"atlas": {**HEADER["atlas"], "constants": len(lines)}}
        end = {"end": {**END["end"], "records": len(lines)}}
        atlas = parse_atlas(text_of([header, *lines, end])).unwrap()
        return render_report(atlas, RUN, (), 1, "ab" * 32, "a.ndjson", "a.tsv", "r.md")

    def test_no_omission(self) -> None:
        report = self.render([RAWS[0], RAWS[1]])
        self.assertIn("gives every constant of this environment its full axiom set",
                      " ".join(report.split()))
        self.assertNotIn("| tier by Lean |", report)

    def test_omission_without_tier_change(self) -> None:
        report = self.render([RAWS[1], {**RAWS[1], "name": "y", "lean_omits": ["propext"]}])
        self.assertIn("No Mathlib constant changes tier.", report.replace("\n   ", " "))

    def test_no_mathlib_and_no_t3(self) -> None:
        report = self.render([RAWS[0], {**RAWS[0], "name": "z", "lean_omits": ["Classical.choice"]}])
        self.assertIn("Of the 0, 0 are `unsafe`.", report.replace("\n", " "))
        self.assertNotIn("Mathlib's 1 are", report)


class TestMain(unittest.TestCase):
    def test_end_to_end(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            atlas = d / "mathlib-v4.33.1-0df444a.ndjson"
            atlas.write_text(ATLAS_TEXT, "utf-8")
            (d / "mathlib-v4.33.1-0df444a.run.json").write_text(json.dumps(
                {"import_seconds": 1, "graph_seconds": 2, "records_seconds": 3,
                 "total_seconds": 6, "peak_rss_kib": 2048}), "utf-8")
            entry = {"id": "finset-card-image", "theme": "t", "lean_name": "Finset.card_image",
                     "lean_module": "Mathlib.Data.Finset.Card", "axioms": CHOICE, "tier": "T2",
                     "features": ["axioms"], "agda_files": [], "status": "planned", "issue": 9}
            manifest = d / "manifest.json"
            manifest.write_text(json.dumps([entry]), "utf-8")
            out, modules = d / "report.md", d / "modules.tsv"
            argv = [str(atlas), "--out", str(out), "--modules", str(modules), "--manifest", str(manifest)]
            with redirect_stdout(io.StringIO()):
                self.assertEqual(main(argv), 0)
            self.assertIn("The atlas agrees with all 1 entries", out.read_text("utf-8"))
            self.assertTrue(modules.read_text("utf-8").startswith("module\t"))
            manifest.write_text(json.dumps([{**entry, "axioms": ["propext"], "tier": "T1"}]), "utf-8")
            err = io.StringIO()
            with redirect_stdout(io.StringIO()), redirect_stderr(err):
                self.assertEqual(main(argv), 1)
            self.assertIn("disagrees with the corpus about finset-card-image", err.getvalue())

    def test_custom_name_reads_its_own_run_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            d = Path(tmp)
            (d / "foo.ndjson").write_text(ATLAS_TEXT, "utf-8")
            (d / "foo.run.json").write_text(json.dumps(
                {"import_seconds": 1, "graph_seconds": 2, "records_seconds": 3,
                 "total_seconds": 6, "peak_rss_kib": None}), "utf-8")
            (d / "manifest.json").write_text("[]", "utf-8")
            out = d / "report.md"
            with redirect_stdout(io.StringIO()):
                self.assertEqual(main([str(d / "foo.ndjson"), "--out", str(out),
                                       "--manifest", str(d / "manifest.json")]), 0)
            self.assertTrue((d / "foo.modules.tsv").is_file())
            self.assertIn("a peak resident memory of not reported", out.read_text("utf-8"))

    def test_malformed_input_is_an_error_not_a_traceback(self) -> None:
        cases = {"utf8": b"\xff\xfe not UTF-8\n",
                 "axioms": text_of([HEADER, {**RAWS[1], "axioms": [[]]}, RAWS[0], RAWS[2], END]).encode(),
                 "deep": (json.dumps(HEADER) + "\n" + "[" * 100_000 + "\n" + json.dumps(END)).encode()}
        with tempfile.TemporaryDirectory() as tmp:
            for name, content in cases.items():
                atlas = Path(tmp) / f"{name}.ndjson"
                atlas.write_bytes(content)
                err = io.StringIO()
                with redirect_stderr(err):
                    self.assertEqual(main([str(atlas), "--out", str(Path(tmp) / "r.md")]), 1, name)
                self.assertIn(f"{atlas}:", err.getvalue(), name)

    def test_missing_atlas(self) -> None:
        err = io.StringIO()
        with redirect_stderr(err):
            self.assertEqual(main(["/nonexistent/atlas.ndjson"]), 1)
        self.assertIn("File not found", err.getvalue())


class TestRepository(unittest.TestCase):
    def test_lean_writes_the_fields_the_parser_reads(self) -> None:
        source = (REPO / "translator" / "Atlas" / "Record.lean").read_text("utf-8")
        body = source[source.index("def Record.render"):source.index("structure Header")]
        self.assertEqual(re.findall(r'\("([a-z_]+)",', body), [name for name, _ in RECORD_FIELDS])

    def test_both_sides_name_the_atlas_alike(self) -> None:
        main_lean = (REPO / "translator" / "Atlas" / "Main.lean").read_text("utf-8")
        self.assertIn('s!"mathlib-{tag}-{rev.take 7}.ndjson"', main_lean)
        manifest = (REPO / "translator" / "lake-manifest.json").read_text("utf-8")
        self.assertTrue(pinned_stem(manifest).unwrap().startswith("mathlib-v"))

    def test_readme_documents_every_field(self) -> None:
        readme = (REPO / "atlas" / "README.md").read_text("utf-8")
        for name, _ in RECORD_FIELDS:
            self.assertIn(f"`{name}`", readme)


if __name__ == "__main__":
    unittest.main()
