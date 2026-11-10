"""
File: scripts/python/tests/test_scaffold_check.py

Description:
  Tests of scaffold_check.py.  The pure functions are tested on a small
  scaffold written by hand in the shape Scaffold.render produces, with a
  theorem in an opaque block and a postulated cyclic definition, on the
  record, mutual and pragma blocks of the emitter of issue M2-4, on the
  recursor definitions and mutual recursor blocks of issue M2-5, on the
  rewrite rules of issue M2-7, and
  check_module with a fake runner that plays Agda's answers in turn
  (errors shaped as Agda 2.8.0 prints them) and a fake clock.
"""
from __future__ import annotations

import contextlib
import io
import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import Sequence

from _utils.pipeline_types import ErrorType, PipelineError, Result
from agda_run import FileRun, Outcome
from scaffold_check import (
    Event, Item, Module, Refusal, State, capped, charged, check_module, code, dependents, in_vain, listing,
    locate, main, marker, parse_exhaustion, parse_item, parse_module, parse_refusal, postulated, recursors,
    references, render, step, theorems, transparent, types_only, unfoldable, without_rewrites,
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


# A recursor, and a block of two, as Scaffold.render writes them.
RECURSORS = """{-# OPTIONS --type-in-type #-}
module U.R where

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat

-- recursor
Nat:rec : {m₀ : Nat → Set} → m₀ Nat:zero → ((n₁ : Nat) → m₀ n₁ → m₀ (Nat:succ n₁)) → (t₁ : Nat) → m₀ t₁
Nat:rec {m₀} z₁ s₂ Nat:zero = z₁
Nat:rec {m₀} z₁ s₂ (Nat:succ n₃) = s₂ n₃ (Nat:rec {m₀} z₁ s₂ n₃)

mutual
  data Even : Set where
    Even:zero : Even
    Even:succ : Odd → Even
  data Odd : Set where
    Odd:succ : Even → Odd

-- recursor
mutual
  Even:rec : (t₀ : Even) → Nat
  Odd:rec : (t₀ : Odd) → Nat
  Even:rec Even:zero = Nat:zero
  Even:rec (Even:succ o₁) = Nat:succ (Odd:rec o₁)
  Odd:rec (Odd:succ e₁) = Nat:succ (Even:rec e₁)

two : Nat
two = Even:rec (Even:succ (Odd:succ Even:zero))
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
        self.assertTrue(parse_module("postulate A : Set\n\npostulate B : Set").is_err)

    def test_a_header_only_module_has_no_declarations(self) -> None:
        module = parse_module("{-# OPTIONS --type-in-type #-}\n-- refused 1 declarations\nmodule U.X where\n").unwrap()
        self.assertEqual((module.name, module.items), ("U.X", ()))
        state = State((), (), ())
        self.assertEqual(render(module, state), (module.header + "\n", ()))
        self.assertEqual(listing(state, False),
                         "checked 0 of 0 declarations, 0 of 0 data types and records\nunfolded 0 of 0 theorems, 0 in vain\n"
                         "defined 0 of 0 recursors by pattern matching, 0 refused by the termination checker\n")

    def test_recursors(self) -> None:
        module = parse_module(RECURSORS).unwrap()
        nat, block = module.items[1], module.items[3]
        self.assertEqual((nat.kind, nat.label, nat.names, nat.signature),
                         ("definition", "recursor", ("Nat:rec",), 1))
        self.assertEqual((block.kind, block.label, block.names, block.signature, block.types),
                         ("mutual", "recursor", ("Even:rec", "Odd:rec"), 3, ()))
        self.assertEqual(references(module.items)[3], frozenset({0, 2}))
        self.assertEqual(recursors(module.items, tuple(True for _ in module.items)), (3, 3, 0))

    def test_a_block_of_postulates(self) -> None:
        block = parse_item("-- recursor, postulated\npostulate A:rec : A → Set\npostulate B:rec : B → Set")
        self.assertEqual((block.kind, block.label, block.names, block.signature),
                         ("postulate", "recursor, postulated", ("A:rec", "B:rec"), 1))


RULES = """{-# OPTIONS --type-in-type --rewriting #-}
-- a comment
module U.Q where

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq #-}

postulate f : Set → Set

-- computation rule
postulate f-β : (a₀ : Set) → Eq {Set} (f a₀) a₀
{-# REWRITE f-β #-}

{-# REWRITE f-β #-}

root : Eq {Set} (f Set) Set
root = Eq:refl Set
"""


class TestRewriteRules(unittest.TestCase):
    def test_a_rule_is_a_postulate_with_its_label(self) -> None:
        rule = parse_module(RULES).unwrap().items[2]
        self.assertEqual((rule.kind, rule.label, rule.names, rule.signature),
                         ("postulate", "computation rule", ("f-β",), 1))

    def test_without_rewrites_drops_the_pragmas_only(self) -> None:
        module = parse_module(RULES).unwrap()
        stripped = without_rewrites(module)
        self.assertEqual((stripped.name, stripped.header), (module.name, module.header))
        # The rule stays a postulate under its label, the builtin stays in
        # Eq's block, and a block of nothing but the pragma goes.
        self.assertEqual([i.names for i in stripped.items], [("Eq", "Eq:refl"), ("f",), ("f-β",), ("root",)])
        self.assertEqual(stripped.items[2], Item("postulate", "computation rule", ("f-β",), 1,
                                                 "-- computation rule\npostulate f-β : (a₀ : Set) → Eq {Set} (f a₀) a₀"))
        self.assertIs(stripped.items[0], module.items[0])
        self.assertNotIn("REWRITE f-β", render(stripped, State(stripped.items, (True,) * 4, ()))[0])

    def test_without_rewrites_keeps_a_module_without_rules(self) -> None:
        module, _ = module_and_state()
        self.assertEqual(without_rewrites(module), module)


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

    def test_keeps_the_recursors(self) -> None:
        module = parse_module(RECURSORS).unwrap()
        self.assertEqual([i.names[0] for i in types_only(module).items], ["Nat", "Nat:rec", "Even", "Even:rec"])

    def test_postulates_the_theorems_the_types_mention(self) -> None:
        module = parse_module(SCAFFOLD.replace(
            "postulate Eq : {α₀ : Set} → α₀ → α₀ → Set",
            "record Box : Set where\n  constructor Box:mk\n  field\n    unbox₀ : Eq {Nat} two~uok two~uok\n\n"
            "postulate Eq : {α₀ : Set} → α₀ → α₀ → Set")).unwrap()
        kept = types_only(module)
        self.assertEqual([(i.names[0], i.kind) for i in kept.items],
                         [("Nat", "data"), ("Box", "record"), ("Eq", "postulate"), ("two", "definition"),
                          ("two~uok", "postulate")])
        self.assertEqual(kept.items[4].text, "-- theorem\npostulate two~uok : Eq {Nat} two 2")


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
        position = {"t": 0, "u": 0, "c": 1, "d": 2, "e": 3}
        unfold = Event("unfolded", "t", "UnequalTerms", "m", "d")
        refused = Event("refused value", "d", "UnequalTerms", "m")
        earlier = Event("refused value", "c", "UnequalTerms", "m")
        later = Event("refused value", "e", "UnequalTerms", "m")
        self.assertTrue(in_vain((unfold, refused), 0, position))
        self.assertTrue(in_vain((unfold, Event("unfolded", "u", "UnequalTerms", "m", "d"), refused), 0, position))
        self.assertTrue(in_vain((unfold, Event("dropped", "d", "", "")), 0, position))
        # An event at an earlier declaration says nothing about the dependent.
        self.assertTrue(in_vain((unfold, earlier, refused), 0, position))
        # One at a later declaration means the dependent checked.
        self.assertFalse(in_vain((unfold, later, refused), 0, position))
        self.assertFalse(in_vain((unfold,), 0, position))
        self.assertFalse(in_vain((unfold, earlier), 0, position))


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
                         "defined 0 of 0 recursors by pattern matching, 0 refused by the termination checker\n"
                         "refused value UnequalTerms root\nrefused type UnequalTerms two\n"
                         "dropped two~uok\ndropped root\n")
        self.assertIn("refused value UnequalTerms root | two != 2\n", listing(after, True))

    def test_listing_counts_unfoldings(self) -> None:
        _, state = module_and_state()
        stuck = Refusal(27, "UnequalTerms", "two~uok != x", "two~uok != x of type T")
        helped = step(state, 6, 1, stuck)
        self.assertEqual(listing(helped, True).split("\n")[1:4],
                         ["unfolded 1 of 1 theorems, 0 in vain",
                          "defined 0 of 0 recursors by pattern matching, 0 refused by the termination checker",
                          "unfolded UnequalTerms two~uok for root | two~uok != x"])
        vain = step(helped, 6, 1, stuck)
        self.assertEqual(listing(vain, False).split("\n")[1:5],
                         ["unfolded 1 of 1 theorems, 1 in vain",
                          "defined 0 of 0 recursors by pattern matching, 0 refused by the termination checker",
                          "unfolded UnequalTerms two~uok for root, in vain", "refused value UnequalTerms root"])


class TestRecursorSteps(unittest.TestCase):
    def state(self) -> State:
        module = parse_module(RECURSORS).unwrap()
        return State(module.items, tuple(True for _ in module.items), ())

    def test_a_refused_clause_postulates_the_recursor(self) -> None:
        after = step(self.state(), 1, 3, Refusal(12, "UnequalTerms", "m", "m"))
        self.assertEqual(after.items[1].text, "-- recursor\npostulate Nat:rec : " + RECURSORS.split("Nat:rec : ")[1].split("\n")[0])
        self.assertEqual(after.events[0].action, "refused value")

    def test_a_refused_clause_postulates_every_member_of_a_block(self) -> None:
        after = step(self.state(), 3, 5, Refusal(26, "UnequalTerms", "m", "m"))
        self.assertEqual(after.items[3].text, "-- recursor\npostulate Even:rec : (t₀ : Even) → Nat\n"
                         "postulate Odd:rec : (t₀ : Odd) → Nat")
        self.assertEqual((after.items[3].kind, after.items[3].names), ("postulate", ("Even:rec", "Odd:rec")))
        self.assertTrue(all(after.alive))

    def test_a_refused_signature_in_a_block_drops_it(self) -> None:
        after = step(self.state(), 3, 3, Refusal(24, "UnequalTerms", "m", "m"))
        self.assertEqual([(e.action, e.name) for e in after.events],
                         [("refused type", "Even:rec"), ("dropped", "two")])

    def test_the_termination_checker_points_at_the_first_line(self) -> None:
        state = self.state()
        after = step(state, 3, 1, Refusal(22, "TerminationIssue", "Termination checking failed",
                                          "Termination checking failed for the following functions: Even:rec, Odd:rec"))
        self.assertEqual(after.items[3].label, "recursor, refused by the termination checker")
        self.assertTrue(after.items[3].text.startswith("-- recursor, refused by the termination checker\npostulate Even:rec"))
        self.assertEqual(after.events, (Event("refused value", "Even:rec", "TerminationIssue", "Termination checking failed"),))
        self.assertEqual(recursors(after.items, after.alive), (3, 1, 2))
        self.assertEqual(listing(after, False).split("\n")[2],
                         "defined 1 of 3 recursors by pattern matching, 2 refused by the termination checker")


class TestExhaustion(unittest.TestCase):
    def test_capped_bounds_the_heap_and_names_declarations(self) -> None:
        seen: list = []

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
            seen.append(tuple(command))
            return Result.ok(subprocess.CompletedProcess(list(command), 0, "", ""))

        capped(runner, "6G")(("agda", "U/A.agda"), Path("."), 1.0)
        self.assertEqual(seen, [("agda", "+RTS", "-M6G", "-RTS", "-v", "tc.decl:5", "U/A.agda")])

    def test_an_exhausted_heap_is_charged_to_the_last_name(self) -> None:
        output = "Checking U.R (/s/U/R.agda).\nChecking Nat.\nChecked Nat.\nChecking Rec.\nChecked Rec.\n"
        heap = FileRun("U/R.agda", Outcome.FAIL, 9.0, "Command failed with exit code 251", output)
        self.assertEqual(parse_exhaustion(heap), ("Rec", Refusal(0, "HeapExhausted", heap.message, "")))
        # The time bound is the whole run's, so a timed-out run is not an exhaustion.
        self.assertIsNone(parse_exhaustion(FileRun("U/R.agda", Outcome.TIMEOUT, 9.0, "Command timed out after 60 seconds", output)))
        self.assertIsNone(parse_exhaustion(FileRun("U/R.agda", Outcome.FAIL, 9.0, "Command failed with exit code 42", output)))
        self.assertIsNone(parse_exhaustion(FileRun("U/R.agda", Outcome.FAIL, 9.0, heap.message, "")))

    def test_a_marker_charges_the_type_after_it_and_a_name_its_item(self) -> None:
        module = parse_module(RECURSORS).unwrap()
        state = State(module.items, tuple(True for _ in module.items), ())
        self.assertEqual(charged("scaffold-check-mark-3", state), (3, 0))
        self.assertEqual(charged("Odd:rec", state), (3, state.items[3].signature + 1))
        self.assertEqual(charged("Even", state), (2, 1))
        self.assertIsNone(charged("Nowhere", state))
        self.assertIsNone(charged("scaffold-check-mark-9", state))
        self.assertIsNone(charged("scaffold-check-mark-2", State(state.items, (True, True, False, True, True), ())))

    def test_an_exhausted_type_is_dropped_and_a_value_postulated(self) -> None:
        module = parse_module(RECURSORS).unwrap()
        state = State(module.items, tuple(True for _ in module.items), ())
        data = step(state, 2, 0, Refusal(0, "HeapExhausted", "m", ""))
        self.assertEqual([(e.action, e.error, e.name) for e in data.events],
                         [("refused type", "HeapExhausted", "Even"), ("dropped", "", "Even:rec"), ("dropped", "", "two")])
        value = step(state, 4, state.items[4].signature + 1, Refusal(0, "HeapExhausted", "m", ""))
        self.assertEqual((value.items[4].kind, value.events[0].action), ("postulate", "refused value"))
        signature = step(state, 4, 0, Refusal(0, "HeapExhausted", "m", ""))
        self.assertEqual([(e.action, e.name) for e in signature.events], [("refused type", "two")])

    def test_check_module_charges_an_exhaustion(self) -> None:
        module = parse_module(RECURSORS).unwrap()
        answers = iter([("Checking Nat.\nChecked Nat.\nChecking Even.\nChecked Even.\n", 251), ("", 0)])

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
            output, code = next(answers)
            if code == 0:
                return Result.ok(subprocess.CompletedProcess(list(command), 0, "", ""))
            return Result.err(PipelineError(ErrorType.COMMAND_FAILED, f"Command failed with exit code {code}",
                                            context={"stdout": output}))

        ticks = iter(range(100))
        with tempfile.TemporaryDirectory() as scratch:
            checked = check_module(runner, lambda: float(next(ticks)), "agda", module, 60.0, Path(scratch)).unwrap()
        self.assertEqual(listing(checked.state, False).split("\n")[3:6],
                         ["refused type HeapExhausted Even", "dropped Even:rec", "dropped two"])

    def check_scaffold(self, answer) -> Result:
        """Check SCAFFOLD with Agda answering every run by `answer`, which
        takes the text the checker wrote and gives Agda's output and exit
        status (-1 for a run past the time bound)."""
        module, _ = module_and_state()

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
            output, status = answer((cwd / command[1]).read_text())
            if status == 0:
                return Result.ok(subprocess.CompletedProcess(list(command), 0, "", ""))
            if status < 0:
                return Result.err(PipelineError(ErrorType.TIMEOUT, "Command timed out after 60 seconds",
                                                context={"stdout": output}))
            return Result.err(PipelineError(ErrorType.COMMAND_FAILED, f"Command failed with exit code {status}",
                                            context={"stdout": output}))

        ticks = iter(range(100))
        with tempfile.TemporaryDirectory() as scratch:
            return check_module(runner, lambda: float(next(ticks)), "agda", module, 60.0, Path(scratch))

    def test_a_blowup_in_a_postulate_is_charged_to_it(self) -> None:
        # Agda names no postulate, so the last name before the blowup is
        # the marker of the postulate, not the definition before it.
        checked = self.check_scaffold(lambda text: fake_agda(text, "postulate loop")).unwrap()
        self.assertEqual((checked.runs, listing(checked.state, False).split("\n")[3:]),
                         (2, ["refused type HeapExhausted loop", ""]))

    def test_a_blowup_in_a_signature_refuses_the_type(self) -> None:
        # Agda checks a definition's signature before it names the
        # definition, so a blowup there refuses the type at once, and what
        # mentions it goes with it.
        checked = self.check_scaffold(lambda text: fake_agda(text, "two : Nat")).unwrap()
        self.assertEqual((checked.runs, listing(checked.state, False).split("\n")[3:]),
                         (2, ["refused type HeapExhausted two", "dropped two~uok", "dropped root", ""]))

    def test_a_blowup_after_a_type_is_named_is_charged_to_the_type(self) -> None:
        # A data type's positivity check runs after its `Checked` line.
        checked = self.check_scaffold(lambda text: fake_agda(text, "data Nat", named="Nat")).unwrap()
        self.assertEqual(listing(checked.state, False).split("\n")[3], "refused type HeapExhausted Nat")

    def test_a_blowup_in_a_named_definition_postulates_its_value(self) -> None:
        checked = self.check_scaffold(lambda text: fake_agda(text, "two = Nat:succ", named="two")).unwrap()
        self.assertEqual(listing(checked.state, False).split("\n")[3:], ["refused value HeapExhausted two", ""])
        self.assertIn("postulate two : Nat", render(*module_and_state()[:1], checked.state)[0])

    def test_a_timeout_is_an_error_naming_the_declaration_in_progress(self) -> None:
        outcome = self.check_scaffold(lambda text: (
            "Checking scaffold-check-mark-3.\nChecked scaffold-check-mark-3.\nChecking two.\n", -1))
        self.assertTrue(outcome.is_err)
        self.assertIn("while checking two;", outcome.unwrap_err().message)
        self.assertIn("nothing is refused", outcome.unwrap_err().message)

    def test_an_exhaustion_that_names_nothing_is_an_error(self) -> None:
        self.assertTrue(self.check_scaffold(lambda text: ("", 251)).is_err)


class TestMarkers(unittest.TestCase):
    def test_render_marks_each_live_item(self) -> None:
        module, state = module_and_state()
        alive = (True, False, True, True, True, True, True)
        text, layout = render(module, State(state.items, alive, ()), marks=True)
        self.assertEqual(unmarked(text), render(module, State(state.items, alive, ()))[0])
        self.assertEqual([i for i, _ in layout], [-1, 0, -1, 2, -1, 3, -1, 4, -1, 5, -1, 6])
        lines = text.split("\n")
        for (_, mark), (i, start) in zip(layout[::2], layout[1::2]):
            self.assertEqual(lines[mark - 1], f"{marker(i).split(chr(10))[0]}")
            self.assertEqual(lines[start - 1], state.items[i].text.split("\n")[0])
        self.assertEqual(locate(layout, layout[2][1] + 1), (-1, 1))

    def test_heap_takes_a_size(self) -> None:
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                main(["--heap", "8GB", "no-such-module.agda"])
            self.assertEqual(main(["--heap", "512M", "no-such-module.agda"]), 1)


def line_of(text: str, needle: str) -> int:
    """The number of the line of `text` that is `needle`."""
    return text.split("\n").index(needle) + 1


def unmarked(text: str) -> str:
    """A module the checker wrote, without its marker definitions."""
    return "\n\n".join(b for b in text.split("\n\n") if not b.startswith("scaffold-check-mark-"))


def fake_agda(text: str, culprit: str, named: str = "") -> tuple[str, int]:
    """What Agda 2.8.0 prints under `-v tc.decl:5` for a module, and its
    exit status, when the block holding `culprit` exhausts its heap: the
    name of each data type, record and function definition before that
    block, as it starts and ends it, and no postulate's; then, when
    `named` is given, that name of the culprit's block, which Agda names
    before it dies (in a definition's clauses, or in a data type's
    positivity check, after its `Checked` line).  251 for the exhausted
    heap, 0 when no block holds `culprit`."""
    lines: list[str] = []
    for block in text.rstrip("\n").split("\n\n")[1:]:
        if culprit in block:
            return "".join(lines) + (f"Checking {named}.\nChecked {named}.\n" if named else ""), 251
        item = parse_item(block)
        names = item.types if item.types else () if item.kind == "postulate" else item.names
        lines.extend(f"Checking {n}.\nChecked {n}.\n" for n in names)
    return "".join(lines), 0


class TestCheckModule(unittest.TestCase):
    def run_module(self, answers: list) -> tuple:
        """Check SCAFFOLD with Agda's answers played in turn: each answer
        takes the text the checker wrote and gives Agda's output, empty
        for a pass."""
        module, _ = module_and_state()
        played = iter(answers)
        seen: list[str] = []

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
            seen.append((cwd / command[1]).read_text())
            output = next(played)(seen[-1])
            if not output:
                return Result.ok(subprocess.CompletedProcess(list(command), 0, "", ""))
            return Result.err(PipelineError(ErrorType.COMMAND_FAILED, "exit 42", context={"stdout": output}))

        ticks = iter(range(100))
        with tempfile.TemporaryDirectory() as scratch:
            checked = check_module(runner, lambda: float(next(ticks)), "agda", module, 60.0, Path(scratch)).unwrap()
            self.assertTrue((Path(scratch) / "U" / "A" / "B.agda").exists())
        return checked, seen

    def test_runs_until_the_rest_checks(self) -> None:
        checked, seen = self.run_module([
            lambda text: agda_error(line_of(text, "root = two~uok"), "UnequalTerms", "two != 2"),
            lambda text: agda_error(line_of(text, "two : Nat"), "UnequalTerms", "m"),
            lambda text: ""])
        self.assertEqual((checked.runs, checked.seconds, checked.last), (3, 3.0, 1.0))
        self.assertEqual(unmarked(seen[0]), SCAFFOLD)
        self.assertEqual(seen[0].count("scaffold-check-mark-") // 2, len(checked.state.items))
        self.assertIn("postulate root : Eq {Nat} two 2", seen[1])
        self.assertNotIn("two~uok", seen[2])
        self.assertEqual(sum(checked.state.alive), 4)

    def test_an_error_in_a_marker_is_not_placed(self) -> None:
        module, _ = module_and_state()

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
            text = (cwd / command[1]).read_text()
            output = agda_error(line_of(text, "scaffold-check-mark-3 = Set"), "UnequalTerms", "m")
            return Result.err(PipelineError(ErrorType.COMMAND_FAILED, "exit 42", context={"stdout": output}))

        with tempfile.TemporaryDirectory() as scratch:
            outcome = check_module(runner, lambda: 0.0, "agda", module, 60.0, Path(scratch))
        self.assertTrue(outcome.is_err)
        self.assertIn("cannot place", outcome.unwrap_err().message)

    def test_unfolds_a_theorem_the_message_names(self) -> None:
        checked, seen = self.run_module([
            lambda text: agda_error(line_of(text, "root = two~uok"), "UnequalTerms", "two~uok != Eq:refl {Nat} two of type T"),
            lambda text: ""])
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
