"""
File: scripts/python/tests/test_scaffold_check.py

Description:
  Tests of scaffold_check.py.  The pure functions are tested on a small
  scaffold written by hand in the shape Scaffold.render produces, with a
  theorem in an opaque block and a postulated cyclic definition, on the
  record, mutual and pragma blocks of the emitter of issue M2-4, and
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
    Event, Item, Module, Refusal, State, check_module, code, dependents, in_vain, listing, locate,
    parse_item, parse_module, parse_refusal, postulated, references, render, step, theorems,
    transparent, types_only, unfoldable,
)

SCAFFOLD = """{-# OPTIONS --type-in-type #-}
-- a comment
-- refused 1 declarations; refusals.txt names each with its reason
module U.A.B where

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

postulate Eq : {α₀ : Set} → α₀ → α₀ → Set

postulate Eq:refl : {α₀ : Set} → (a₁ : α₀) → Eq {α₀} a₁ a₁

two : Nat
two = Nat:succ (Nat:succ Nat:zero)

-- theorem
opaque
  two~uok : Eq {Nat} two 2
  two~uok = Eq:refl {Nat} two

-- cyclic definition, postulated
postulate loop : Nat → Nat

root : Eq {Nat} two 2
root = two~uok
"""


def agda_error(line: int, name: str, message: str) -> str:
    return (f"Checking U.A.B (/tmp/s/U/A/B.agda).\n/tmp/s/U/A/B.agda:{line}.1-9: error: [{name}]\n"
            f"{message}\nwhen checking something\n")


def module_and_state() -> tuple:
    module = parse_module(SCAFFOLD).unwrap()
    return module, State(module.items, tuple(True for _ in module.items), ())


def postulate(name: str, text: str) -> Item:
    return Item("postulate", "", (name,), 0, text)


class TestParse(unittest.TestCase):
    def test_kinds_and_names(self) -> None:
        self.assertEqual(parse_item("postulate Eq : Set"), postulate("Eq", "postulate Eq : Set"))
        self.assertEqual(parse_item("two : Nat\ntwo = 2").kind, "definition")
        data = parse_item("data Nat : Set where\n  Nat:zero : Nat\n  Nat:succ : Nat → Nat\n{-# BUILTIN NATURAL Nat #-}")
        self.assertEqual((data.kind, data.names, data.types), ("data", ("Nat", "Nat:zero", "Nat:succ"), ("Nat",)))
        theorem = parse_item("-- theorem\nopaque\n  t : A\n  t = a")
        self.assertEqual((theorem.kind, theorem.label, theorem.names, theorem.signature),
                         ("opaque", "theorem", ("t",), 2))
        constant = parse_item("-- opaque constant\nopaque\n  c : A\n  c = a")
        self.assertEqual((constant.kind, constant.label), ("opaque", "opaque constant"))
        cyclic = parse_item("-- cyclic definition, postulated\npostulate loop : Nat → Nat")
        self.assertEqual((cyclic.kind, cyclic.label, cyclic.names, cyclic.signature),
                         ("postulate", "cyclic definition, postulated", ("loop",), 1))

    def test_records(self) -> None:
        record = parse_item("record Prod (α₀ : Set) (β₁ : Set) : Set where\n  constructor Prod:mk\n  field\n"
                            "    fst₂ : α₀\n    {snd₃} : β₁")
        self.assertEqual((record.kind, record.names, record.types), ("record", ("Prod", "Prod:mk"), ("Prod",)))
        unit = parse_item("record PUnit : Set where\n  constructor PUnit:unit")
        self.assertEqual(unit.names, ("PUnit", "PUnit:unit"))
        rose = parse_item("record Rose : Set where\n  inductive\n  no-eta-equality\n  pattern\n"
                          "  constructor Rose:mk\n  field\n    children₀ : List Rose")
        self.assertEqual(rose.names, ("Rose", "Rose:mk"))

    def test_mutual_and_pragma_blocks(self) -> None:
        block = parse_item("mutual\n  data Term : Set where\n    Term:lit : Nat → Term\n    Term:pair : Pair → Term\n"
                           "  record Pair : Set where\n    inductive\n    no-eta-equality\n    pattern\n"
                           "    constructor Pair:mk\n    field\n      left₀ : Term")
        self.assertEqual((block.kind, block.names, block.types),
                         ("mutual", ("Term", "Term:lit", "Term:pair", "Pair", "Pair:mk"), ("Term", "Pair")))
        unchecked = parse_item("{-# NO_POSITIVITY_CHECK #-}\ndata Bad : Set where\n  Bad:mk : (Bad → Nat) → Bad")
        self.assertEqual((unchecked.kind, unchecked.names, unchecked.signature), ("data", ("Bad", "Bad:mk"), 1))
        self.assertEqual(parse_item("{-# BUILTIN NATURAL Nat #-}"), Item("pragma", "", (), 0, "{-# BUILTIN NATURAL Nat #-}"))

    def test_module(self) -> None:
        module, _ = module_and_state()
        self.assertEqual(module.name, "U.A.B")
        self.assertEqual([i.names[0] for i in module.items],
                         ["Nat", "Eq", "Eq:refl", "two", "two~uok", "loop", "root"])
        self.assertEqual(theorems(module.items), 1)

    def test_not_a_scaffold(self) -> None:
        self.assertTrue(parse_module("module X where").is_err)
        self.assertTrue(parse_module("postulate A : Set\n\npostulate B : Set").is_err)


class TestReferences(unittest.TestCase):
    def test_mentions_other_items_only(self) -> None:
        module, _ = module_and_state()
        refs = references(module.items)
        self.assertEqual(refs[0], frozenset())  # Nat mentions only its own names
        self.assertEqual(refs[3], frozenset({0}))  # two: Nat and its constructors
        self.assertEqual(refs[4], frozenset({0, 1, 2, 3}))  # the theorem, through its block
        self.assertEqual(refs[6], frozenset({0, 1, 3, 4}))
        # Delimiters separate names: "{α₀}" is not a name and "(Nat:succ" is Nat:succ.
        self.assertEqual(references((postulate("A", "postulate A : Set"),
                                     postulate("b", "postulate b : (x₀ : {A}) → ⦃ A ⦄"))),
                         (frozenset(), frozenset({0})))

    def test_a_projection_mentions_its_record(self) -> None:
        record = parse_item("record R : Set where\n  constructor R:mk\n  field\n    f₀ : Nat")
        user = parse_item("g : R → Nat\ng r₀ = R.f₀ r₀")
        self.assertEqual(references((record, Item("definition", "", ("h",), 0, "h : Nat\nh = R.f₀"))),
                         (frozenset(), frozenset({0})))
        self.assertEqual(references((record, user))[1], frozenset({0}))

    def test_comments_are_not_references(self) -> None:
        item = Item("definition", "theorem, unfolded for root", ("t",), 1, "-- theorem, unfolded for root\nt : A\nt = a")
        self.assertEqual(code(item), "t : A\nt = a")
        self.assertEqual(references((item, Item("definition", "", ("root",), 0, "root : A\nroot = t"))),
                         (frozenset(), frozenset({0})))


class TestTypesOnly(unittest.TestCase):
    def test_keeps_the_types_and_what_they_mention(self) -> None:
        module = parse_module(SCAFFOLD.replace(
            "postulate Eq : {α₀ : Set} → α₀ → α₀ → Set",
            "record Box : Set where\n  constructor Box:mk\n  field\n    unbox₀ : Hidden\n\n"
            "postulate Hidden : Set\n\npostulate Eq : {α₀ : Set} → α₀ → α₀ → Set")).unwrap()
        kept = types_only(module)
        self.assertEqual([i.names[0] for i in kept.items], ["Nat", "Box", "Hidden"])
        self.assertEqual((kept.name, kept.header), (module.name, module.header))


def chain(n: int) -> tuple[Item, ...]:
    """A data type that mentions a0, each a{i} the next, a{n-1} nothing:
    one reference chain n declarations long."""
    return (Item("data", "", ("T", "T:c"), 0, "data T : Set where\n  T:c : a0 → T", ("T",)),) + tuple(
        postulate(f"a{i}", f"postulate a{i} : a{i + 1}" if i < n - 1 else f"postulate a{i} : Set")
        for i in range(n))


class TestLongChains(unittest.TestCase):
    # Thousands of declarations in one chain of references: the fixed
    # points are loops, not recursions that would exhaust Python's stack.
    def test_types_only_follows_a_long_chain(self) -> None:
        items = chain(3000)
        self.assertEqual(len(types_only(Module("U.A", "module U.A where", items)).items), 3001)

    def test_dependents_follow_a_long_chain(self) -> None:
        items = chain(3000)
        found = dependents(3000, references(items), tuple(True for _ in items))
        self.assertEqual(found, (3000,) + tuple(range(3000)))


class TestRenderAndLocate(unittest.TestCase):
    def test_render_reproduces_the_module(self) -> None:
        module, state = module_and_state()
        text, layout = render(module, state)
        self.assertEqual(text, SCAFFOLD)
        self.assertEqual(layout, ((0, 6), (1, 11), (2, 13), (3, 15), (4, 18), (5, 23), (6, 26)))

    def test_locate(self) -> None:
        layout = ((0, 5), (3, 14), (5, 19))
        self.assertEqual(locate(layout, 15), (3, 1))
        self.assertEqual(locate(layout, 19), (5, 0))
        self.assertIsNone(locate(layout, 2))

    def test_a_long_module(self) -> None:
        # Thousands of declarations: the layout is a running sum, not a
        # recursion that would exhaust Python's stack.
        items = tuple(postulate(f"a{i}", f"postulate a{i} : Set") for i in range(5000))
        module = parse_module("module U.A where\n\n" + "\n\n".join(i.text for i in items)).unwrap()
        _, layout = render(module, State(module.items, tuple(True for _ in items), ()))
        self.assertEqual(layout[-1], (4999, 3 + 2 * 4999))

    def test_layout_skips_dropped_items(self) -> None:
        module, state = module_and_state()
        _, layout = render(module, State(state.items, (True, False, False, True, True, True, True), ()))
        self.assertEqual(layout, ((0, 6), (3, 11), (4, 14), (5, 19), (6, 22)))


class TestParseRefusal(unittest.TestCase):
    def test_first_error_and_message(self) -> None:
        self.assertEqual(parse_refusal(agda_error(20, "UnequalTerms", "1 != 2 of type Nat")),
                         Refusal(20, "UnequalTerms", "1 != 2 of type Nat", "1 != 2 of type Nat"))

    def test_detail_stops_where_the_context_starts(self) -> None:
        output = ("/x/U/A/B.agda:7.3-9.12: error: [UnequalTerms]\nf a !=\ng b of type T\n"
                  "when checking that the expression q has type Q base\nwhen checking more\n")
        self.assertEqual(parse_refusal(output), Refusal(7, "UnequalTerms", "f a !=", "f a != g b of type T"))

    def test_multiline_range(self) -> None:
        output = "/x/U/A/B.agda:7.3-9.12: error: [ShouldBePi]\nExpression used as function\n"
        self.assertEqual(parse_refusal(output), Refusal(7, "ShouldBePi", "Expression used as function",
                                                        "Expression used as function"))

    def test_none_without_a_located_error(self) -> None:
        self.assertIsNone(parse_refusal("error: [LibraryError] no such library\n"))


class TestFallback(unittest.TestCase):
    def test_unfoldable_names_an_opaque_theorem_other_than_the_refused(self) -> None:
        _, state = module_and_state()
        stuck = Refusal(27, "UnequalTerms", "two~uok != x", "two~uok != x of type Eq {Nat} two 2")
        self.assertEqual(unfoldable(state.items, state.alive, 6, stuck), 4)
        self.assertIsNone(unfoldable(state.items, state.alive, 4, stuck))  # its own clause
        self.assertIsNone(unfoldable(state.items, (True,) * 4 + (False,) * 3, 6, stuck))
        plain = Refusal(27, "UnequalTerms", "two != 2", "two != 2 of type Nat")
        self.assertIsNone(unfoldable(state.items, state.alive, 6, plain))  # a definition, not a theorem
        # Only the message proper counts, not what Agda was checking.
        self.assertIsNone(unfoldable(state.items, state.alive, 6, Refusal(27, "UnequalTerms", "a != b", "a != b")))

    def test_transparent_and_postulated(self) -> None:
        _, state = module_and_state()
        unfolded = transparent(state.items[4], "root")
        self.assertEqual(unfolded, Item("definition", "theorem, unfolded for root", ("two~uok",), 1,
                                        "-- theorem, unfolded for root\ntwo~uok : Eq {Nat} two 2\ntwo~uok = Eq:refl {Nat} two"))
        self.assertEqual(postulated(state.items[4]),
                         Item("postulate", "theorem", ("two~uok",), 1, "-- theorem\npostulate two~uok : Eq {Nat} two 2"))
        self.assertEqual(postulated(state.items[3]), postulate("two", "postulate two : Nat"))
        self.assertEqual(postulated(unfolded),
                         Item("postulate", "theorem, unfolded for root", ("two~uok",), 1,
                              "-- theorem, unfolded for root\npostulate two~uok : Eq {Nat} two 2"))

    def test_step_unfolds_the_named_theorem(self) -> None:
        _, state = module_and_state()
        after = step(state, 6, 1, Refusal(27, "UnequalTerms", "two~uok != x", "two~uok != x of type T"))
        self.assertEqual(after.items[4].kind, "definition")
        self.assertEqual(after.alive, state.alive)
        self.assertEqual(after.events, (Event("unfolded", "two~uok", "UnequalTerms", "two~uok != x", "root"),))
        # Once transparent, the same refusal postulates the dependent's value.
        again = step(after, 6, 1, Refusal(27, "UnequalTerms", "two~uok != x", "two~uok != x of type T"))
        self.assertEqual(again.items[6].kind, "postulate")
        self.assertEqual(again.events[-1], Event("refused value", "root", "UnequalTerms", "two~uok != x"))

    def test_in_vain(self) -> None:
        unfold = Event("unfolded", "t", "UnequalTerms", "m", "d")
        refused = Event("refused value", "d", "UnequalTerms", "m")
        other = Event("refused value", "e", "UnequalTerms", "m")
        self.assertTrue(in_vain((unfold, refused), 0))
        self.assertTrue(in_vain((unfold, Event("unfolded", "u", "UnequalTerms", "m", "d"), refused), 0))
        self.assertFalse(in_vain((unfold, other, refused), 0))
        self.assertFalse(in_vain((unfold,), 0))
        self.assertFalse(in_vain((unfold, Event("dropped", "d", "", "")), 0))


class TestStep(unittest.TestCase):
    def test_refused_clause_keeps_the_signature(self) -> None:
        _, state = module_and_state()
        after = step(state, 6, 1, Refusal(27, "UnequalTerms", "two != 2", "two != 2"))
        self.assertEqual(after.items[6], postulate("root", "postulate root : Eq {Nat} two 2"))
        self.assertEqual(after.alive, state.alive)
        self.assertEqual(after.events, (Event("refused value", "root", "UnequalTerms", "two != 2"),))

    def test_refused_opaque_clause_keeps_the_signature(self) -> None:
        _, state = module_and_state()
        after = step(state, 4, 3, Refusal(21, "UnequalTerms", "m", "m"))
        self.assertEqual(after.items[4].text, "-- theorem\npostulate two~uok : Eq {Nat} two 2")
        self.assertEqual(theorems(after.items), 1)

    def test_refused_type_drops_dependents(self) -> None:
        _, state = module_and_state()
        self.assertEqual(dependents(3, references(state.items), state.alive), (3, 4, 6))
        after = step(state, 3, 0, Refusal(15, "UnequalTerms", "m", "m"))
        self.assertEqual(after.alive, (True, True, True, False, False, True, False))
        self.assertEqual([(e.action, e.name) for e in after.events],
                         [("refused type", "two"), ("dropped", "two~uok"), ("dropped", "root")])

    def test_a_refusal_on_the_signature_line_of_a_block_is_a_type(self) -> None:
        _, state = module_and_state()
        after = step(state, 4, 2, Refusal(20, "UnequalTerms", "m", "m"))
        self.assertEqual(after.events[0].action, "refused type")

    def test_listing(self) -> None:
        _, state = module_and_state()
        after = step(step(state, 6, 1, Refusal(27, "UnequalTerms", "two != 2", "two != 2")), 3, 0,
                     Refusal(15, "UnequalTerms", "m", "m"))
        self.assertEqual(listing(after, False),
                         "checked 4 of 7 declarations, 1 of 1 data types and records\n"
                         "unfolded 0 of 1 theorems, 0 in vain\n"
                         "refused value UnequalTerms root\nrefused type UnequalTerms two\n"
                         "dropped two~uok\ndropped root\n")
        self.assertIn("refused value UnequalTerms root | two != 2\n", listing(after, True))

    def test_listing_counts_unfoldings(self) -> None:
        _, state = module_and_state()
        stuck = Refusal(27, "UnequalTerms", "two~uok != x", "two~uok != x of type T")
        helped = step(state, 6, 1, stuck)
        self.assertEqual(listing(helped, True).split("\n")[1:3],
                         ["unfolded 1 of 1 theorems, 0 in vain",
                          "unfolded UnequalTerms two~uok for root | two~uok != x"])
        vain = step(helped, 6, 1, stuck)
        self.assertEqual(listing(vain, False).split("\n")[1:4],
                         ["unfolded 1 of 1 theorems, 1 in vain", "unfolded UnequalTerms two~uok for root, in vain",
                          "refused value UnequalTerms root"])


class TestCheckModule(unittest.TestCase):
    def run_module(self, answers: list[str]) -> tuple:
        module, _ = module_and_state()
        played = iter(answers)
        seen: list[str] = []

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
            seen.append((cwd / command[1]).read_text())
            output = next(played)
            if not output:
                return Result.ok(subprocess.CompletedProcess(list(command), 0, "", ""))
            return Result.err(PipelineError(ErrorType.COMMAND_FAILED, "exit 42", context={"stdout": output}))

        ticks = iter(range(100))
        with tempfile.TemporaryDirectory() as scratch:
            checked = check_module(runner, lambda: float(next(ticks)), "agda", module, 60.0, Path(scratch)).unwrap()
            self.assertTrue((Path(scratch) / "U" / "A" / "B.agda").exists())
        return checked, seen

    def test_runs_until_the_rest_checks(self) -> None:
        checked, seen = self.run_module([agda_error(27, "UnequalTerms", "two != 2"), agda_error(15, "UnequalTerms", "m"), ""])
        self.assertEqual((checked.runs, checked.seconds, checked.last), (3, 3.0, 1.0))
        self.assertEqual(seen[0], SCAFFOLD)
        self.assertIn("postulate root : Eq {Nat} two 2", seen[1])
        self.assertNotIn("two~uok", seen[2])
        self.assertEqual(sum(checked.state.alive), 4)

    def test_unfolds_a_theorem_the_message_names(self) -> None:
        checked, seen = self.run_module([agda_error(27, "UnequalTerms", "two~uok != Eq:refl {Nat} two of type T"), ""])
        self.assertEqual(checked.runs, 2)
        self.assertIn("-- theorem, unfolded for root\ntwo~uok : Eq {Nat} two 2\ntwo~uok = Eq:refl {Nat} two\n", seen[1])
        self.assertNotIn("opaque", seen[1])
        self.assertEqual(listing(checked.state, False).split("\n")[1], "unfolded 1 of 1 theorems, 0 in vain")

    def test_an_unplaceable_failure_is_an_error(self) -> None:
        module, _ = module_and_state()

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
            return Result.err(PipelineError(ErrorType.COMMAND_FAILED, "exit 42",
                                            context={"stdout": "error: [LibraryError]\n"}))

        with tempfile.TemporaryDirectory() as scratch:
            self.assertTrue(check_module(runner, lambda: 0.0, "agda", module, 60.0, Path(scratch)).is_err)


if __name__ == "__main__":
    unittest.main()
