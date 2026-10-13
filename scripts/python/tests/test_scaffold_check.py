"""
File: scripts/python/tests/test_scaffold_check.py

Description:
  Tests of scaffold_check.py.  The pure functions are tested on a small
  scaffold written by hand in the shape Scaffold.render produces, and
  check_module with a fake runner that plays Agda's answers in turn
  (errors shaped as Agda 2.8.0 prints them) and a fake clock.
"""
from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import Sequence

from _utils.pipeline_types import ErrorType, PipelineError, Result
from scaffold_check import (
    Event, Item, Refusal, State, check_module, dependents, listing, locate, parse_item,
    parse_module, parse_refusal, references, render, step,
)

SCAFFOLD = """{-# OPTIONS --type-in-type #-}
-- a comment
module U.A.B where

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

postulate Eq : {α₀ : Set} → α₀ → α₀ → Set

postulate Eq:refl : {α₀ : Set} → (a₁ : α₀) → Eq {α₀} a₁ a₁

two : Nat
two = Nat:succ (Nat:succ Nat:zero)

postulate two~uok : Eq {Nat} two 2

root : Eq {Nat} two 2
root = Eq:refl {Nat} 2
"""


def agda_error(line: int, name: str, message: str) -> str:
    return (f"Checking U.A.B (/tmp/s/U/A/B.agda).\n/tmp/s/U/A/B.agda:{line}.1-9: error: [{name}]\n"
            f"{message}\nwhen checking something\n")


def module_and_state() -> tuple:
    module = parse_module(SCAFFOLD).unwrap()
    return module, State(module.items, tuple(True for _ in module.items), ())


class TestParse(unittest.TestCase):
    def test_kinds_and_names(self) -> None:
        self.assertEqual(parse_item("postulate Eq : Set").names, ("Eq",))
        self.assertEqual(parse_item("two : Nat\ntwo = 2").kind, "definition")
        data = parse_item("data Nat : Set where\n  Nat:zero : Nat\n  Nat:succ : Nat → Nat\n{-# BUILTIN NATURAL Nat #-}")
        self.assertEqual((data.kind, data.names), ("data", ("Nat", "Nat:zero", "Nat:succ")))

    def test_module(self) -> None:
        module, _ = module_and_state()
        self.assertEqual(module.name, "U.A.B")
        self.assertEqual([i.names[0] for i in module.items], ["Nat", "Eq", "Eq:refl", "two", "two~uok", "root"])

    def test_not_a_scaffold(self) -> None:
        self.assertTrue(parse_module("module X where").is_err)
        self.assertTrue(parse_module("postulate A : Set\n\npostulate B : Set").is_err)


class TestReferences(unittest.TestCase):
    def test_mentions_other_items_only(self) -> None:
        module, _ = module_and_state()
        refs = references(module.items)
        self.assertEqual(refs[0], frozenset())  # Nat mentions only its own names
        self.assertEqual(refs[3], frozenset({0}))  # two: Nat and its constructors
        self.assertEqual(refs[5], frozenset({0, 1, 2, 3}))
        # Delimiters separate names: "{α₀}" is not a name and "(Nat:succ" is Nat:succ.
        self.assertEqual(references((Item("postulate", ("A",), "postulate A : Set"),
                                     Item("postulate", ("b",), "postulate b : (x₀ : {A}) → ⦃ A ⦄"))),
                         (frozenset(), frozenset({0})))


class TestRenderAndLocate(unittest.TestCase):
    def test_render_reproduces_the_module(self) -> None:
        module, state = module_and_state()
        text, layout = render(module, state)
        self.assertEqual(text, SCAFFOLD)
        self.assertEqual(layout, ((0, 5), (1, 10), (2, 12), (3, 14), (4, 17), (5, 19)))

    def test_locate(self) -> None:
        layout = ((0, 5), (3, 14), (5, 19))
        self.assertEqual(locate(layout, 15), (3, 1))
        self.assertEqual(locate(layout, 19), (5, 0))
        self.assertIsNone(locate(layout, 2))

    def test_layout_skips_dropped_items(self) -> None:
        module, state = module_and_state()
        _, layout = render(module, State(state.items, (True, False, False, True, True, True), ()))
        self.assertEqual(layout, ((0, 5), (3, 10), (4, 13), (5, 15)))


class TestParseRefusal(unittest.TestCase):
    def test_first_error_and_message(self) -> None:
        self.assertEqual(parse_refusal(agda_error(20, "UnequalTerms", "1 != 2 of type Nat")),
                         Refusal(20, "UnequalTerms", "1 != 2 of type Nat"))

    def test_multiline_range(self) -> None:
        output = "/x/U/A/B.agda:7.3-9.12: error: [ShouldBePi]\nExpression used as function\n"
        self.assertEqual(parse_refusal(output), Refusal(7, "ShouldBePi", "Expression used as function"))

    def test_none_without_a_located_error(self) -> None:
        self.assertIsNone(parse_refusal("error: [LibraryError] no such library\n"))


class TestStep(unittest.TestCase):
    def test_refused_clause_keeps_the_signature(self) -> None:
        _, state = module_and_state()
        after = step(state, 5, 1, Refusal(20, "UnequalTerms", "two != 2"))
        self.assertEqual(after.items[5], Item("postulate", ("root",), "postulate root : Eq {Nat} two 2"))
        self.assertEqual(after.alive, state.alive)
        self.assertEqual(after.events, (Event("refused value", "root", "UnequalTerms", "two != 2"),))

    def test_refused_type_drops_dependents(self) -> None:
        _, state = module_and_state()
        self.assertEqual(dependents(3, references(state.items), state.alive), (3, 4, 5))
        after = step(state, 3, 0, Refusal(14, "UnequalTerms", "m"))
        self.assertEqual(after.alive, (True, True, True, False, False, False))
        self.assertEqual([(e.action, e.name) for e in after.events],
                         [("refused type", "two"), ("dropped", "two~uok"), ("dropped", "root")])

    def test_listing(self) -> None:
        _, state = module_and_state()
        after = step(step(state, 5, 1, Refusal(20, "UnequalTerms", "two != 2")), 4, 0,
                     Refusal(17, "UnequalTerms", "m"))
        self.assertEqual(listing(after, False),
                         "checked 5 of 6 declarations\nrefused value UnequalTerms root\n"
                         "refused type UnequalTerms two~uok\n")
        self.assertIn("refused value UnequalTerms root | two != 2\n", listing(after, True))


class TestCheckModule(unittest.TestCase):
    def test_runs_until_the_rest_checks(self) -> None:
        module, _ = module_and_state()
        answers = iter([agda_error(20, "UnequalTerms", "two != 2"), agda_error(17, "UnequalTerms", "m"), ""])
        seen: list[str] = []

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
            seen.append((cwd / command[1]).read_text())
            output = next(answers)
            if not output:
                return Result.ok(subprocess.CompletedProcess(list(command), 0, "", ""))
            return Result.err(PipelineError(ErrorType.COMMAND_FAILED, "exit 42", context={"stdout": output}))

        ticks = iter(range(100))
        with tempfile.TemporaryDirectory() as scratch:
            checked = check_module(runner, lambda: float(next(ticks)), "agda", module, 60.0, Path(scratch)).unwrap()
            self.assertTrue((Path(scratch) / "U" / "A" / "B.agda").exists())
        self.assertEqual((checked.runs, checked.seconds, checked.last), (3, 3.0, 1.0))
        self.assertEqual(seen[0], SCAFFOLD)
        self.assertIn("postulate root : Eq {Nat} two 2", seen[1])
        self.assertNotIn("two~uok", seen[2])
        self.assertEqual(sum(checked.state.alive), 5)

    def test_an_unplaceable_failure_is_an_error(self) -> None:
        module, _ = module_and_state()

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
            return Result.err(PipelineError(ErrorType.COMMAND_FAILED, "exit 42",
                                            context={"stdout": "error: [LibraryError]\n"}))

        with tempfile.TemporaryDirectory() as scratch:
            self.assertTrue(check_module(runner, lambda: 0.0, "agda", module, 60.0, Path(scratch)).is_err)


if __name__ == "__main__":
    unittest.main()
