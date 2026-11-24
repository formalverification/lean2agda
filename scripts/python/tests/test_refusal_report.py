"""
File: scripts/python/tests/test_refusal_report.py

Description:
  Tests of refusal_report.py: the classes file, the listing's event
  lines, the loop's and the final check's reports, a module's values,
  the classes of its refusals and of the values behind a refused type,
  across modules too, the tables, and the command line on a directory in
  the shape goldens.sh writes.
"""
from __future__ import annotations

import io
import json
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from dataclasses import replace
from pathlib import Path

from agda_check import build_tree, parse_source
from refusal_report import (
    Event, FinalRow, LoopRow, Rule, TreeRun, by_class, classify, declarations, declared, main, module_report,
    parse_event, parse_final, parse_listing, parse_loop, parse_rules, render, roots_behind,
    sidecar_identifiers, tree_report,
)

# Module A: a type, a definition, a theorem, a recursor, an operation
# table helper, and a mutual block of two definitions.
MODULE_A = """{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U
module U.A where

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat

-- recursor
Nat:rec : {m₀ : Nat → Set} → m₀ Nat:zero → ((n₁ : Nat) → m₀ n₁ → m₀ (Nat:succ n₁)) → (t₁ : Nat) → m₀ t₁
Nat:rec {m₀} z₁ s₂ Nat:zero = z₁
Nat:rec {m₀} z₁ s₂ (Nat:succ n₃) = s₂ n₃ (Nat:rec {m₀} z₁ s₂ n₃)

-- operation table
Nat:add-builtin : Nat → Nat → Nat
Nat:add-builtin x₀ y₁ = x₀

Bad : Set
Bad = Nat

two : Nat
two = Nat:succ (Nat:succ Nat:zero)

-- theorem
opaque
  two~uok : Bad
  two~uok = two

mutual
  f : Nat → Nat
  g : Nat → Nat
  f n₀ = g n₀
  g n₀ = f n₀
"""

# Module B imports A: a value whose type names A's refused type, and one
# that does not.
MODULE_B = """{-# OPTIONS --type-in-type --rewriting #-}
module U.B where
import U.A

usesBad : U.A.Bad
usesBad = U.A.two

clean : U.A.Nat
clean = U.A.two
"""

SIDECAR_A = "\n".join(json.dumps(r) for r in (
    {"naming": {"version": 1}},
    {"agda": "Nat", "lean": []}, {"agda": "Bad", "lean": []}, {"agda": "two", "lean": []},
    {"agda": "two~uok", "lean": []}, {"agda": "f", "lean": []}, {"agda": "g", "lean": []},
    {"agda": "Nat:rec", "lean": []})) + "\n"
SIDECAR_B = "\n".join(json.dumps({"agda": a, "lean": []}) for a in ("usesBad", "clean")) + "\n"

LISTING_A = """checked 5 of 7 declarations, 1 of 1 data types and records
unfolded 1 of 1 theorems, 1 in vain
defined 1 of 1 recursors by pattern matching, 0 refused by the termination checker
unfolded UnequalTerms two~uok for f, in vain | a message
refused value UnequalTerms f | h₁ != h₂ of type p
refused type UnequalTerms Bad | Nat != Bool
dropped two~uok
"""

LISTING_B = """checked 1 of 2 declarations, 0 of 0 data types and records
unfolded 0 of 0 theorems, 0 in vain
defined 0 of 0 recursors by pattern matching, 0 refused by the termination checker
dropped usesBad
"""

LOOP = """checked 6 of 9 declarations, 1 of 1 data types and records
unfolded 1 of 1 theorems, 1 in vain
defined 1 of 1 recursors by pattern matching, 0 refused by the termination checker
2 modules, 7 Agda runs, 3.5 s in all, 2.0 s wall with -j 4

module  runs   seconds  peak MiB  listing
U.A        5       2.5       120  checked 5 of 7 declarations, 1 of 1 data types and records
U.B        2       1.0        80  checked 1 of 2 declarations, 0 of 0 data types and records
"""

FINAL = {"modules": [{"name": "U.A", "path": "U/A.agda", "bytes": 10, "result": "pass", "seconds": 0.5,
                      "peak_kib": 102400, "message": "", "output": ""},
                     {"name": "U.B", "path": "U/B.agda", "bytes": 10, "result": "pass", "seconds": 0.25,
                      "peak_kib": 51200, "message": "", "output": ""}],
         "jobs": 4, "wall_seconds": 0.8}

RULES = (Rule("#27", "UnequalTerms", "f"), Rule("#26", "UnequalTerms", "Ba?"))


def run_of(final: dict = FINAL, listing_a: str = LISTING_A) -> TreeRun:
    sources = [parse_source("U/A.agda", MODULE_A).unwrap(), parse_source("U/B.agda", MODULE_B).unwrap()]
    tree = build_tree(sources).unwrap()
    loop, summary = parse_loop(LOOP)
    rows, wall = parse_final(json.dumps(final)).unwrap()
    lean = frozenset(sidecar_identifiers(SIDECAR_A) + sidecar_identifiers(SIDECAR_B))
    return TreeRun("t", tree, {"U.A": MODULE_A, "U.B": MODULE_B}, {"U.A": listing_a, "U.B": LISTING_B},
                   loop, summary, rows, wall, 1.5, 9, 0, lean)


class RulesTest(unittest.TestCase):

    def test_rules_and_comments(self) -> None:
        rules = parse_rules("# File: x\n\n# a comment\n#27 UnequalTerms dif~upos   h != hc\n#26 X a*\n").unwrap()
        self.assertEqual(rules, (Rule("#27", "UnequalTerms", "dif~upos", "h != hc"), Rule("#26", "X", "a*")))

    def test_a_malformed_line_is_an_error(self) -> None:
        self.assertTrue(parse_rules("#27 UnequalTerms\n").is_err)
        self.assertTrue(parse_rules("27 UnequalTerms x\n").is_err)

    def test_no_rule_may_name_the_report_s_own_issue(self) -> None:
        result = parse_rules("#23 UnequalTerms x\n")
        self.assertTrue(result.is_err)
        self.assertIn("#23", result.unwrap_err())

    def test_classify_matches_the_error_and_a_glob_in_order(self) -> None:
        rules = (Rule("#27", "UnequalTerms", "Sub*"), Rule("#26", "UnequalTerms", "*"))
        self.assertEqual(classify(Event("refused value", "UnequalTerms", "Subtype:eq"), rules), "#27")
        self.assertEqual(classify(Event("refused value", "UnequalTerms", "x"), rules), "#26")
        self.assertIsNone(classify(Event("refused value", "UnequalHiding", "x"), rules))


class ParsingTest(unittest.TestCase):

    def test_event_lines(self) -> None:
        self.assertEqual(parse_event("refused value UnequalTerms f | h != k"),
                         Event("refused value", "UnequalTerms", "f"))
        self.assertEqual(parse_event("refused type HeapExhausted T"), Event("refused type", "HeapExhausted", "T"))
        self.assertEqual(parse_event("dropped x"), Event("dropped", "", "x"))
        self.assertEqual(parse_event("unfolded UnequalTerms t for d, in vain | m"),
                         Event("unfolded", "UnequalTerms", "t", "d", True))
        self.assertEqual(parse_event("unfolded UnequalTerms t for d"), Event("unfolded", "UnequalTerms", "t", "d"))
        self.assertIsNone(parse_event("checked 1 of 2 declarations, 0 of 0 data types and records"))

    def test_a_message_holding_a_bar_is_cut_at_the_first(self) -> None:
        self.assertEqual(parse_listing("refused value E f | a | b\n"), (Event("refused value", "E", "f"),))

    def test_loop_rows_and_summary(self) -> None:
        rows, summary = parse_loop(LOOP)
        self.assertEqual(rows, {"U.A": LoopRow(5, 2.5, 120), "U.B": LoopRow(2, 1.0, 80)})
        self.assertTrue(summary.startswith("2 modules, 7 Agda runs"))

    def test_final_rows(self) -> None:
        rows, wall = parse_final(json.dumps(FINAL)).unwrap()
        self.assertEqual(rows["U.A"], FinalRow("pass", 0.5, 102400))
        self.assertEqual(wall, 0.8)
        self.assertTrue(parse_final("not json").is_err)
        self.assertTrue(parse_final("{}").is_err)

    def test_sidecar_identifiers_skip_the_header_and_bad_lines(self) -> None:
        self.assertEqual(sidecar_identifiers('{"naming":{}}\n{"agda":"x","lean":[]}\nnot json\n'), ("x",))


class CountsTest(unittest.TestCase):

    def test_values_leave_out_recursors_types_and_the_table_s_helpers(self) -> None:
        lean = frozenset(sidecar_identifiers(SIDECAR_A))
        d = declared(MODULE_A, frozenset({"U.A"}), lean)
        self.assertEqual(d.values, {"Bad": 1, "two": 1, "two~uok": 1, "f": 2})
        self.assertIn("Bad", d.refs["two~uok"])

    def test_references_reach_a_refused_type_across_modules(self) -> None:
        refs = {"usesBad": frozenset({"Bad", "two"}), "two": frozenset({"Nat"}), "clean": frozenset({"two"})}
        self.assertEqual(roots_behind("usesBad", refs, frozenset({"Bad"})), frozenset({"Bad"}))
        self.assertEqual(roots_behind("clean", refs, frozenset({"Bad"})), frozenset())
        self.assertEqual(roots_behind("Bad", refs, frozenset({"Bad"})), frozenset({"Bad"}))

    def test_a_module_s_refusals_by_class(self) -> None:
        events = parse_listing(LISTING_A)
        m = module_report("U.A", 100, 7, {"Bad": 1, "two": 1, "two~uok": 1, "f": 2}, events, RULES,
                          {"Bad": "#26"}, {"Bad": "#26", "two~uok": "#26"}, None, None)
        self.assertEqual(m.refused, {"#27": 2})
        self.assertEqual(m.behind, {"#26": 2})
        self.assertEqual(m.types_refused, 1)
        self.assertEqual(m.checked, 1)
        self.assertEqual(m.unclassified, ())

    def test_an_unclassified_refusal_is_still_refused(self) -> None:
        m = module_report("U.A", 100, 7, {"f": 2}, (Event("refused value", "UnequalHiding", "f"),), RULES,
                          {}, {}, None, None)
        self.assertEqual(m.refused, {"unclassified": 2})
        self.assertEqual(m.checked, 0)
        self.assertEqual(m.unclassified, ("U.A: refused value UnequalHiding f",))

    def test_an_unclassified_refused_type_is_reported(self) -> None:
        m = module_report("U.A", 100, 7, {}, (Event("refused type", "HeapExhausted", "T"),), RULES, {}, {}, None, None)
        self.assertEqual(m.unclassified, ("U.A: refused type HeapExhausted T",))


class TreeTest(unittest.TestCase):

    def test_a_drop_in_an_importing_module_is_charged_to_the_type_s_class(self) -> None:
        report = tree_report(run_of(), RULES)
        b = next(m for m in report.modules if m.name == "U.B")
        self.assertEqual((b.declarations, b.values, b.checked, b.behind), (2, 2, 1, {"#26": 1}))
        self.assertEqual([m.name for m in report.modules], ["U.A", "U.B"])
        self.assertTrue(report.passes)

    def test_a_module_the_final_check_refused_fails_the_tree(self) -> None:
        final = {**FINAL, "modules": [{**FINAL["modules"][0], "result": "fail"}, FINAL["modules"][1]]}
        report = tree_report(run_of(final), RULES)
        self.assertFalse(report.final_passes)
        self.assertFalse(report.passes)

    def test_a_module_without_a_listing_checked_nothing_and_fails_the_tree(self) -> None:
        run = run_of()
        report = tree_report(replace(run, listings={"U.A": LISTING_A}), RULES)
        b = next(m for m in report.modules if m.name == "U.B")
        self.assertEqual((b.listed, b.values, b.checked), (False, 2, 0))
        self.assertEqual(report.unlisted, ("U.B",))
        self.assertTrue(report.final_passes)
        self.assertFalse(report.passes)
        self.assertIn("modules the loop did not reach", render([report]))

    def test_an_unclassified_refusal_fails_the_tree(self) -> None:
        report = tree_report(run_of(), (Rule("#27", "UnequalTerms", "f"),))
        self.assertTrue(report.final_passes)
        self.assertFalse(report.passes)
        self.assertIn("U.A: refused type UnequalTerms Bad", report.unclassified)

    def test_declarations_from_the_listing(self) -> None:
        self.assertEqual(declarations(LISTING_A), 7)
        self.assertEqual(declarations(""), 0)

    def test_by_class(self) -> None:
        self.assertEqual(by_class({}), "0")
        self.assertEqual(by_class({"#27": 2, "#26": 1}), "3 (#26 1, #27 2)")

    def test_render(self) -> None:
        text = render([tree_report(run_of(), RULES)])
        self.assertIn("| `t` | 9 | 2 |", text)
        self.assertIn("passes", text)
        self.assertIn("| #26 | 0 + 3 behind |", text)
        self.assertIn("| `U.B` |", text)


class CommandLineTest(unittest.TestCase):

    def write(self, root: Path, listing_a: str = LISTING_A) -> Path:
        d = root / "t"
        for path, text in (("tree/U/A.agda", MODULE_A), ("tree/U/B.agda", MODULE_B),
                           ("tree/U/A.names.ndjson", SIDECAR_A), ("tree/U/B.names.ndjson", SIDECAR_B),
                           ("tree/closure.txt", "# closure\na\nb\n"), ("listings/U/A.checked.txt", listing_a),
                           ("listings/U/B.checked.txt", LISTING_B), ("loop.txt", LOOP),
                           ("final.json", json.dumps(FINAL)), ("translate-seconds", "1.5\n")):
            (d / path).parent.mkdir(parents=True, exist_ok=True)
            (d / path).write_text(text)
        return d

    def run_main(self, argv: list[str]) -> tuple[int, str, str]:
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            status = main(argv)
        return status, out.getvalue(), err.getvalue()

    def test_a_passing_tree(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "classes.txt").write_text("#27 UnequalTerms f\n#26 UnequalTerms Bad\n")
            status, out, err = self.run_main(["--classes", str(root / "classes.txt"), str(self.write(root))])
            self.assertEqual((status, err), (0, ""))
            self.assertIn("| `t` | 2 | 2 |", out)

    def test_an_unclassified_tree_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "classes.txt").write_text("#27 UnequalTerms f\n")
            status, out, err = self.run_main(["--classes", str(root / "classes.txt"), str(self.write(root))])
            self.assertEqual(status, 1)
            self.assertIn("t: 1 unclassified", err)
            self.assertIn("Unclassified:", out)

    def test_a_bad_classes_file_fails(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "classes.txt").write_text("#23 UnequalTerms f\n")
            status, _, err = self.run_main(["--classes", str(root / "classes.txt"), str(self.write(root))])
            self.assertEqual(status, 1)
            self.assertIn("#23", err)


if __name__ == "__main__":
    unittest.main()
