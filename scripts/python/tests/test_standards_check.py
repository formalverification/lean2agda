"""
File: scripts/python/tests/test_standards_check.py

Description:
  Tests of standards_check.py: each pure function on small texts built
  here, and then the checks themselves on the repository, so that the
  suite fails when the module map, docs/translator/architecture.md, falls
  behind the tree, when a file's `File:` header is missing or names
  another path, or when translator/VERSION and CHANGELOG.md disagree.
"""
from __future__ import annotations

import unittest
from pathlib import Path

from standards_check import (
    MAP_PATH,
    DefinitionRow,
    MapRow,
    Table,
    check_tree,
    code_spans,
    coverage_problems,
    definition_problems,
    definition_rows,
    defines,
    effect_problems,
    header_problem,
    header_problems,
    is_rule,
    lean_code,
    link_problems,
    map_problems,
    map_rows,
    named_paths,
    newest_entry,
    parse_tables,
    python_definitions,
    relative_links,
    required_paths,
    split_row,
    uses_effects,
    version_problems,
)

ROOT: Path = Path(__file__).resolve().parents[3]

DOCUMENT: str = """# Map

| File | Stage | Effects |
| --- | --- | --- |
| `translator/A.lean` | load | pure |
| `translator/B.lean` | write | IO: the edge |

```
| File | Effects |
| --- | --- |
| `translator/Fenced.lean` | pure |
```

| Definition | File | Produces |
| --- | --- | --- |
| `run` | `translator/B.lean` | output |
| `Closure.size`, `sortNames` | `translator/A.lean` | a number |

See [the note](notes/a.md#section) and [b].

[b]: ../b.md
[web]: https://example.org/x.md
"""


def files(*paths: str) -> object:
    """An existence test that knows exactly the given paths."""
    return lambda p: p in paths


class TestMarkdown(unittest.TestCase):
    def test_split_row(self) -> None:
        self.assertEqual(split_row("| `a` | b c |  |"), ("`a`", "b c", ""))

    def test_split_row_keeps_an_escaped_pipe(self) -> None:
        self.assertEqual(split_row(r"| a \| b | c |"), (r"a \| b", "c"))

    def test_is_rule(self) -> None:
        self.assertTrue(is_rule(("---", ":---:", "---:")))
        self.assertFalse(is_rule(("---", "text")))

    def test_parse_tables_skips_fenced_code(self) -> None:
        tables = parse_tables(DOCUMENT)
        self.assertEqual([t.header for t in tables],
                         [("File", "Stage", "Effects"), ("Definition", "File", "Produces")])
        self.assertEqual(len(tables[0].rows), 2)

    def test_a_table_without_a_rule_is_not_a_table(self) -> None:
        self.assertEqual(parse_tables("| a | b |\n| c | d |\n"), ())

    def test_code_spans(self) -> None:
        self.assertEqual(code_spans("`a`, `b.c` and d"), ("a", "b.c"))

    def test_map_rows(self) -> None:
        rows = map_rows(parse_tables(DOCUMENT))
        self.assertEqual([r.path for r in rows], ["translator/A.lean", "translator/B.lean"])
        self.assertEqual(rows[1].cells["Effects"], "IO: the edge")

    def test_map_rows_ignore_a_row_without_a_path(self) -> None:
        table = Table(("File", "Role"), (("none", "x"), ("`p`", "y")))
        self.assertEqual(map_rows((table,)), (MapRow("p", {"File": "`p`", "Role": "y"}),))

    def test_definition_rows(self) -> None:
        self.assertEqual(definition_rows(parse_tables(DOCUMENT)), (
            DefinitionRow(("run",), "translator/B.lean"),
            DefinitionRow(("Closure.size", "sortNames"), "translator/A.lean")))

    def test_named_paths(self) -> None:
        self.assertEqual(named_paths(DOCUMENT), (
            "translator/A.lean", "translator/B.lean", "translator/B.lean", "translator/A.lean"))

    def test_relative_links(self) -> None:
        self.assertEqual(relative_links(DOCUMENT), ("../b.md", "notes/a.md"))


class TestLeanSource(unittest.TestCase):
    def test_lean_code_blanks_comments_and_literals(self) -> None:
        code = lean_code('a -- IO\nb /- IO /- nested -/ IO -/ c "IO" d \'"\' e')
        self.assertNotIn("IO", code)
        self.assertEqual(code.split(), ["a", "b", "c", '""', "d", "'", "'", "e"])

    def test_lean_code_keeps_a_prime(self) -> None:
        self.assertIn("x' := IO", lean_code("x' := IO"))

    def test_uses_effects(self) -> None:
        self.assertTrue(uses_effects("def f : IO Unit := pure ()"))
        self.assertTrue(uses_effects("def g : CoreM Nat := pure 0"))
        self.assertTrue(uses_effects("let r ← IO.FS.readFile p"))

    def test_uses_effects_ignores_comments_strings_and_longer_names(self) -> None:
        self.assertFalse(uses_effects('/-- runs in IO -/\ndef f := "IO" -- IO\n'))
        self.assertFalse(uses_effects("def x := Lean.IOError.toString\ndef IOish := 1"))

    def test_defines(self) -> None:
        source = "partial def printExpr (s : Scope)\nstructure Closure where\ndef Closure.size (c) :="
        self.assertTrue(defines("a.lean", source, "printExpr"))
        self.assertTrue(defines("a.lean", source, "Closure"))
        self.assertTrue(defines("a.lean", source, "Closure.size"))
        self.assertFalse(defines("a.lean", source, "print"))
        self.assertFalse(defines("a.lean", source, "Scope"))
        self.assertTrue(defines("a.lean", "def quotRule? (n : Name)", "quotRule?"))

    def test_defines_ignores_lean_comments_and_strings(self) -> None:
        source = '/- def oldPass -/\n/-- def oldDoc -/\n-- def oldLine\ndef s := "def oldString"\n'
        for name in ("oldPass", "oldDoc", "oldLine", "oldString"):
            self.assertFalse(defines("a.lean", source, name), name)
        self.assertTrue(defines("a.lean", source, "s"))

    def test_defines_reads_python_by_its_syntax(self) -> None:
        source = ('"""def old_doc"""\n# def old_comment\nX = "def old_string"\n'
                  "class Module:\n    def parse(self):\n        pass\nasync def run():\n    pass\n")
        for name in ("old_doc", "old_comment", "old_string"):
            self.assertFalse(defines("a.py", source, name), name)
        for name in ("Module", "parse", "run"):
            self.assertTrue(defines("a.py", source, name), name)

    def test_python_definitions_of_unparsable_source(self) -> None:
        self.assertEqual(python_definitions("def f(:\n"), frozenset())
        self.assertEqual(python_definitions("def f(): pass\nclass C: pass\n"), frozenset({"f", "C"}))


class TestMapChecks(unittest.TestCase):
    def test_required_paths(self) -> None:
        tracked = ("translator/A.lean", "translator/t.sh", "translator/README.md",
                   "atlas/probes/P.lean", "scripts/python/corpus_check.py")
        self.assertEqual(required_paths(tracked), (
            "scripts/python/agda_run.py", "scripts/python/scaffold_check.py",
            "translator/A.lean", "translator/t.sh"))

    def test_coverage_missing_absent_and_twice(self) -> None:
        rows = (MapRow("b", {}), MapRow("c", {}), MapRow("c", {}))
        self.assertEqual(coverage_problems(("a", "b"), rows, files("a", "c")), (
            f"a: no row in {MAP_PATH}",
            f"b: {MAP_PATH} has a row for it, but it does not exist",
            f"c: {MAP_PATH} has 2 rows for it"))

    def test_coverage_clean(self) -> None:
        self.assertEqual(coverage_problems(("a",), (MapRow("a", {}),), files("a")), ())

    def test_effects(self) -> None:
        rows = (MapRow("p.lean", {"Effects": "pure"}), MapRow("q.lean", {"Effects": "IO: edge"}),
                MapRow("r.lean", {"Effects": "maybe"}), MapRow("s.py", {"Effects": "pure"}),
                MapRow("t.lean", {}))
        sources = {"p.lean": "def f : IO Unit := pure ()", "q.lean": "def g := 1",
                   "r.lean": "", "s.py": "IO", "t.lean": "IO"}
        self.assertEqual(effect_problems(rows, sources), (
            "p.lean: the map says pure, and the code uses an effect monad",
            "q.lean: the map says IO, and the code uses no effect monad",
            "r.lean: the Effects cell must begin with pure or IO"))

    def test_effects_clean(self) -> None:
        rows = (MapRow("p.lean", {"Effects": "pure"}), MapRow("q.lean", {"Effects": "IO"}))
        self.assertEqual(effect_problems(rows, {"p.lean": "def f := 1", "q.lean": "def g : IO Unit"}), ())

    def test_definitions(self) -> None:
        rows = (DefinitionRow(("f", "g"), "a.lean"), DefinitionRow(("h",), "gone.lean"))
        self.assertEqual(definition_problems(rows, {"a.lean": "def f := 1"}), (
            "a.lean: the map names g, which the file does not define",
            "gone.lean: the map names it for h, and it does not exist"))

    def test_links(self) -> None:
        self.assertEqual(link_problems(("../b.md", "a.md", "../../x.md"), "docs/t/m.md",
                                       files("docs/b.md", "docs/t/a.md")),
                         ("docs/t/m.md: the link ../../x.md names no file",))

    def test_map_problems_on_a_small_tree(self) -> None:
        sources = {"translator/A.lean": "def Closure.size := 0\ndef sortNames := 1",
                   "translator/B.lean": "def run : IO Unit := pure ()"}
        present = files("translator/A.lean", "translator/B.lean", "scripts/python/agda_run.py",
                        "scripts/python/scaffold_check.py", "docs/translator/notes/a.md", "docs/b.md")
        tracked = ("translator/A.lean", "translator/B.lean", "translator/C.lean")
        self.assertEqual(map_problems(DOCUMENT, tracked, sources, present), (
            f"scripts/python/agda_run.py: no row in {MAP_PATH}",
            f"scripts/python/scaffold_check.py: no row in {MAP_PATH}",
            f"translator/C.lean: no row in {MAP_PATH}"))


class TestHeaders(unittest.TestCase):
    def test_a_correct_header(self) -> None:
        self.assertIsNone(header_problem("a/b.lean", "/-\nFile: a/b.lean\n-/\n"))
        self.assertIsNone(header_problem("t.sh", "#!/usr/bin/env bash\n# File: t.sh\n"))

    def test_no_header(self) -> None:
        self.assertEqual(header_problem("a.py", '"""\nNothing here.\n"""\n'),
                         "a.py: no File: header in its first 5 lines")

    def test_a_header_too_late(self) -> None:
        self.assertEqual(header_problem("a.py", "\n" * 5 + "File: a.py\n"),
                         "a.py: no File: header in its first 5 lines")

    def test_a_header_naming_another_path(self) -> None:
        self.assertEqual(header_problem("a/new.py", '"""\nFile: a/old.py\n"""\n'),
                         "a/new.py: its File: header names a/old.py")

    def test_header_problems_checks_lean_python_and_shell_only(self) -> None:
        sources = {"a.lean": "", "b.md": "", "c.sh": "# File: c.sh\n", "d.py": "File: e.py"}
        self.assertEqual(header_problems(sources), (
            "a.lean: no File: header in its first 5 lines",
            "d.py: its File: header names e.py"))


class TestVersion(unittest.TestCase):
    CHANGELOG: str = "# Changelog\n\n## 0.2.0\n\n+  b\n\n## 0.1.0\n\n+  a\n"

    def test_newest_entry(self) -> None:
        self.assertEqual(newest_entry(self.CHANGELOG), "0.2.0")
        self.assertIsNone(newest_entry("# Changelog\n"))

    def test_agreement(self) -> None:
        self.assertEqual(version_problems("0.2.0\n", self.CHANGELOG), ())

    def test_disagreement(self) -> None:
        self.assertEqual(version_problems("0.1.0\n", self.CHANGELOG),
                         ("CHANGELOG.md: its newest entry is 0.2.0, and translator/VERSION says 0.1.0",))

    def test_malformed_version(self) -> None:
        for text in ("0.1\n", "v0.1.0\n", "0.1.0\n0.2.0\n", "01.0.0\n", ""):
            self.assertEqual(version_problems(text, self.CHANGELOG),
                             ("translator/VERSION: must hold one line, MAJOR.MINOR.PATCH",), text)


class TestTheRepository(unittest.TestCase):
    """The checks on the tree this file sits in.  A failure names each
    problem: a module without its row in the map, a stale row, a header,
    or a version the changelog does not name."""

    def test_the_tree_meets_the_standards(self) -> None:
        result = check_tree(ROOT)
        self.assertTrue(result.is_ok, str(result.unwrap_err()) if result.is_err else "")
        problems = result.unwrap()
        self.assertEqual(problems, (), "\n" + "\n".join(problems))


if __name__ == "__main__":
    unittest.main()
