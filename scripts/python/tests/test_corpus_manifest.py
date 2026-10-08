"""
File: scripts/python/tests/test_corpus_manifest.py

Description:
  Tests of corpus_manifest.py: every pure rule, the one edge
  (gather_entry_files) on a temporary directory, and two consistency
  checks against the repository: corpus/manifest.json parses with no
  malformed entry, and the feature vocabulary in corpus/SCHEMA.md is
  the FEATURES constant.
"""
from __future__ import annotations

import copy
import json
import re
import tempfile
import unittest
from pathlib import Path
from typing import Any

from corpus_manifest import (
    FEATURES, SIDECAR_THRESHOLD, AgdaFile, Entry, EntryFiles, Malformed, Pragmas,
    agda_file_problems, agda_files_problems, axiom_problems, block_comment_end,
    decode_manifest, entry_file_problems, entry_label, entry_problems,
    entry_status, feature_problems, field_problems, gather_entry_files,
    id_problems, is_agda_source, issue_problems, mark_duplicates, options_of,
    orphan_problems, parse_agda_file, parse_entry, parse_manifest,
    pragma_problems, profile_problems, repeats, scan_pragmas, sidecar_problems,
    status_problems, string_problems, term_problems, tier_of, tier_problems,
    tokens,
)

REPO = Path(__file__).resolve().parents[3]

GOOD: dict[str, Any] = {
    "id": "list-reverse-reverse",
    "theme": "constructive arithmetic and lists",
    "lean_name": "List.reverse_reverse",
    "lean_module": "Init.Data.List.Lemmas",
    "axioms": ["propext"],
    "tier": "T1",
    "features": ["axioms", "universe-levels"],
    "agda_files": [{"path": "ListReverseReverse.agda",
                    "flags": ["--safe", "--cubical-compatible"], "profile": "CC"}],
    "status": "translated",
    "issue": 7,
}
CC_FILE = AgdaFile("ListReverseReverse.agda", ("--safe", "--cubical-compatible"), "CC")
SOURCE = "{-# OPTIONS --safe --cubical-compatible #-}\nmodule ListReverseReverse where\n"


def with_(**changes: Any) -> dict[str, Any]:
    """GOOD with some fields replaced."""
    raw = copy.deepcopy(GOOD)
    raw.update(changes)
    return raw


def problems_of(raw: object) -> tuple[str, ...]:
    item = parse_entry(raw, 0)
    return item.problems if isinstance(item, Malformed) else ()


def entry() -> Entry:
    item = parse_entry(GOOD, 0)
    assert isinstance(item, Entry)
    return item


def files(**changes: Any) -> EntryFiles:
    base: dict[str, Any] = dict(sources=(("ListReverseReverse.agda", SOURCE),),
                                present=("ListReverseReverse.agda",), has_statement=True,
                                has_notes=True, term_bytes=3, sidecar=None)
    base.update(changes)
    return EntryFiles(**base)


class TestTierOf(unittest.TestCase):
    def test_tiers(self) -> None:
        self.assertEqual(tier_of([]), "T0")
        self.assertEqual(tier_of(["propext"]), "T1")
        self.assertEqual(tier_of(["Quot.sound"]), "T1")
        self.assertEqual(tier_of(["propext", "Classical.choice", "Quot.sound"]), "T2")
        self.assertEqual(tier_of(["sorryAx"]), "T3")
        # native_decide at Lean v4.33.1 adds an axiom of its own.
        self.assertEqual(tier_of(["propext", "foo._native.native_decide.ax_1_1"]), "T3")


class TestProfileProblems(unittest.TestCase):
    def test_agreeing_flags(self) -> None:
        self.assertEqual(profile_problems(["--safe"], "K"), ())
        self.assertEqual(profile_problems(["--safe", "--cubical-compatible"], "CC"), ())
        self.assertEqual(profile_problems(["--safe", "--cubical", "--guardedness"], "CU"), ())

    def test_missing_and_forbidden_flags(self) -> None:
        self.assertEqual(profile_problems(["--cubical-compatible"], "CC"),
                         ("profile CC needs --safe, which the flags lack",))
        self.assertEqual(profile_problems(["--safe", "--without-K"], "K"),
                         ("profile K forbids --without-K",))
        self.assertEqual(profile_problems(["--safe", "--cubical-compatible"], "CU"),
                         ("profile CU needs --cubical, which the flags lack",))


class TestSmallHelpers(unittest.TestCase):
    def test_repeats(self) -> None:
        self.assertEqual(repeats(["a", "b", "a", "c", "b", "a"]), ("a", "b"))
        self.assertEqual(repeats(["a", "b"]), ())

    def test_field_problems(self) -> None:
        self.assertEqual(field_problems({"a": 1, "z": 2}, ("a", "b"), "x"),
                         ("x lacks the field 'b'", "x has the unknown field 'z'"))

    def test_entry_label_and_status(self) -> None:
        self.assertEqual(entry_label(GOOD, 3), "list-reverse-reverse")
        self.assertEqual(entry_label({"id": 5}, 3), "entry 3")
        self.assertEqual(entry_label([], 3), "entry 3")
        self.assertEqual(entry_status(GOOD), "translated")
        self.assertEqual(entry_status({"status": None}), "?")


class TestAgdaFiles(unittest.TestCase):
    def test_good_file(self) -> None:
        self.assertEqual(parse_agda_file(GOOD["agda_files"][0], 0).unwrap(), CC_FILE)

    def test_bad_files(self) -> None:
        self.assertEqual(agda_file_problems("x", 0), ("agda_files[0] is not an object",))
        self.assertEqual(agda_file_problems({"path": "A.agda"}, 1),
                         ("agda_files[1] lacks the field 'flags'", "agda_files[1] lacks the field 'profile'"))
        bad = agda_file_problems({"path": "sub/A.lagda", "flags": ["safe"], "profile": "U"}, 0)
        self.assertEqual(len(bad), 3)
        self.assertTrue(parse_agda_file({"path": "A.agda", "flags": ["--safe"], "profile": "CC"}, 0).is_err)


class TestFieldRules(unittest.TestCase):
    def test_id(self) -> None:
        self.assertEqual(id_problems("set-ext"), ())
        self.assertEqual(id_problems("set--ext"), ("id 'set--ext' is not lowercase kebab-case",))
        self.assertEqual(id_problems(3), ("id 3 is not lowercase kebab-case",))

    def test_strings(self) -> None:
        self.assertEqual(string_problems({"theme": "x"}, "theme"), ())
        self.assertEqual(string_problems({"theme": 1}, "theme"), ("theme must be a non-empty string",))

    def test_axioms_and_tier(self) -> None:
        self.assertEqual(axiom_problems([]), ())
        self.assertEqual(axiom_problems([1]), ("axioms must be a list of strings",))
        self.assertEqual(tier_problems("T0", []), ())
        self.assertEqual(tier_problems("T0", ["propext"]), ("tier is T0 but the axioms imply T1",))
        # A tier is not judged against axioms that are not a list.
        self.assertEqual(tier_problems("T0", "propext"), ())

    def test_features(self) -> None:
        self.assertEqual(feature_problems(["quotients"]), ())
        self.assertEqual(feature_problems("quotients"), ("features must be a non-empty list of strings",))

    def test_agda_files_and_status(self) -> None:
        self.assertEqual(agda_files_problems(GOOD["agda_files"]), ())
        self.assertEqual(agda_files_problems({}), ("agda_files must be a list",))
        self.assertEqual(status_problems("planned", []), ())
        self.assertEqual(status_problems("translated", GOOD["agda_files"]), ())
        self.assertEqual(status_problems("translated", []),
                         ("a translated entry must list at least one Agda file",))

    def test_issue(self) -> None:
        self.assertEqual(issue_problems(7), ())
        self.assertEqual(issue_problems("7"), ("issue '7' is not a positive integer",))

    def test_entry_problems_collects_every_rule(self) -> None:
        self.assertEqual(entry_problems(GOOD), ())
        self.assertEqual(len(entry_problems(with_(id="X", theme="", tier="T2", issue=0))), 4)


class TestParseEntry(unittest.TestCase):
    def test_good_entry(self) -> None:
        self.assertEqual(entry(), Entry(
            "list-reverse-reverse", "constructive arithmetic and lists", "List.reverse_reverse",
            "Init.Data.List.Lemmas", ("propext",), "T1", ("axioms", "universe-levels"),
            (CC_FILE,), "translated", 7))

    def test_not_an_object(self) -> None:
        self.assertEqual(parse_entry([1], 2), Malformed("entry 2", "?", ("the entry is not a JSON object",)))

    def test_missing_field(self) -> None:
        raw = with_()
        del raw["theme"]
        self.assertEqual(problems_of(raw), ("the entry lacks the field 'theme'",))

    def test_every_value_rule(self) -> None:
        cases: list[tuple[dict[str, Any], str]] = [
            (with_(id="Bad_Id"), "id 'Bad_Id' is not lowercase kebab-case"),
            (with_(theme=" "), "theme must be a non-empty string"),
            (with_(axioms=["propext", "propext"]), "axiom 'propext' is listed twice"),
            (with_(axioms="propext"), "axioms must be a list of strings"),
            (with_(tier="T2"), "tier is T2 but the axioms imply T1"),
            (with_(tier="T9"), "tier 'T9' is not one of T0, T1, T2, T3"),
            (with_(features=[]), "features must be a non-empty list of strings"),
            (with_(features=["quotient"]), "feature 'quotient' is not in the vocabulary of corpus/SCHEMA.md"),
            (with_(features=["axioms", "axioms"]), "feature 'axioms' is listed twice"),
            (with_(agda_files=[]), "a translated entry must list at least one Agda file"),
            (with_(agda_files=GOOD["agda_files"] * 2), "agda file 'ListReverseReverse.agda' is listed twice"),
            (with_(status="done"), "status 'done' is not one of planned, translated"),
            (with_(issue=True), "issue True is not a positive integer"),
            (with_(issue=0), "issue 0 is not a positive integer"),
        ]
        for raw, problem in cases:
            with self.subTest(problem=problem):
                self.assertIn(problem, problems_of(raw))

    def test_a_planned_entry_may_list_no_files(self) -> None:
        self.assertEqual(problems_of(with_(status="planned", agda_files=[])), ())

    def test_all_problems_are_reported(self) -> None:
        self.assertEqual(len(problems_of(with_(id="X", tier="T2", issue=-1))), 3)


class TestManifest(unittest.TestCase):
    def test_duplicates_are_malformed(self) -> None:
        items = mark_duplicates([entry(), entry(), Malformed("entry 2", "?", ("x",))])
        self.assertEqual([type(i).__name__ for i in items], ["Malformed", "Malformed", "Malformed"])
        self.assertIn("used by more than one entry", items[0].problems[0])  # type: ignore[union-attr]

    def test_parse_manifest(self) -> None:
        self.assertEqual(parse_manifest({"entries": []}).unwrap_err(), "the manifest is not a JSON array")
        self.assertEqual(parse_manifest([GOOD]).unwrap(), (entry(),))

    def test_decode_manifest(self) -> None:
        self.assertIn("not valid JSON", decode_manifest("[").unwrap_err())
        self.assertEqual(decode_manifest(json.dumps([GOOD])).unwrap(), (entry(),))

    def test_the_repository_manifest_is_well_formed(self) -> None:
        items = decode_manifest((REPO / "corpus" / "manifest.json").read_text("utf-8")).unwrap()
        self.assertEqual([i for i in items if isinstance(i, Malformed)], [])
        self.assertEqual(len(items), 12)

    def test_schema_md_lists_the_vocabulary(self) -> None:
        schema = (REPO / "corpus" / "SCHEMA.md").read_text("utf-8")
        section = schema.split("### Features", 1)[1].split("\n## ", 1)[0]
        slugs = re.findall(r"^\| `([a-z-]+)` \|", section, re.MULTILINE)
        self.assertEqual(tuple(slugs), FEATURES)


# The shapes measured with Agda 2.8.0: a pragma inside a block comment,
# nested or not, is ignored silently; one after the module header is
# ignored with the warning UselessPragma; both let a postulate through
# where --safe would have rejected it.
IN_COMMENT = "{-\n{-# OPTIONS --safe --cubical-compatible #-}\n-}\nmodule M where\n"
IN_NESTED = "{- a {- b -}\n{-# OPTIONS --safe --cubical-compatible #-}\n-}\nmodule M where\n"
AFTER_HEADER = "module M where\n{-# OPTIONS --safe --cubical-compatible #-}\n"
NO_HEADER = "{-# OPTIONS --safe --cubical-compatible #-}\nopen import Data.Nat\n"


class TestPragmas(unittest.TestCase):
    def test_block_comment_end(self) -> None:
        self.assertEqual(block_comment_end("{- a -} b", 0), 7)
        self.assertEqual(block_comment_end("{- {- -} -} b", 0), 11)
        self.assertEqual(block_comment_end("x {- {-# P #-} -} y", 2), 17)
        self.assertEqual(block_comment_end("{- never closed", 0), 15)

    def test_tokens(self) -> None:
        kinds = [k for k, _ in tokens('-- c\n{- b -}\n{-# OPTIONS --safe #-}\nmodule "s" x--y')]
        self.assertEqual(kinds, ["line", "space", "comment", "space", "pragma", "space",
                                 "other", "space", "string", "space", "other", "line"])

    def test_options_of(self) -> None:
        span = [("pragma", "{-# OPTIONS --safe\n  --cubical-compatible #-}"),
                ("pragma", "{-# BUILTIN NATURAL N #-}"), ("comment", "{- {-# OPTIONS --x #-} -}")]
        self.assertEqual(options_of(span), (("--safe", "--cubical-compatible"),))

    def test_scan_pragmas(self) -> None:
        cc = ("--safe", "--cubical-compatible")
        self.assertEqual(scan_pragmas(SOURCE), Pragmas((cc,), ()))
        self.assertEqual(scan_pragmas("-- {-# OPTIONS --type-in-type #-}\n" + SOURCE), Pragmas((cc,), ()))
        self.assertEqual(scan_pragmas(IN_COMMENT), Pragmas((), ()))
        self.assertEqual(scan_pragmas(IN_NESTED), Pragmas((), ()))
        self.assertEqual(scan_pragmas(AFTER_HEADER), Pragmas((), (cc,)))
        self.assertEqual(scan_pragmas(NO_HEADER), Pragmas((cc,), ()))
        self.assertEqual(scan_pragmas("module M where\n"), Pragmas((), ()))

    def test_pragma_problems(self) -> None:
        missing = ("agda/ListReverseReverse.agda has no OPTIONS pragma before its module "
                   "declaration, the only place Agda honors one (not inside a comment)")
        late = ("agda/ListReverseReverse.agda has an OPTIONS pragma after its module header, "
                "which Agda ignores; move it to the top of the file")
        self.assertEqual(pragma_problems(CC_FILE, SOURCE), ())
        self.assertEqual(pragma_problems(CC_FILE, NO_HEADER), ())
        self.assertEqual(pragma_problems(CC_FILE, "module M where\n"), (missing,))
        self.assertEqual(pragma_problems(CC_FILE, IN_COMMENT), (missing,))
        self.assertEqual(pragma_problems(CC_FILE, AFTER_HEADER), (missing, late))
        self.assertEqual(pragma_problems(CC_FILE, SOURCE + "{-# OPTIONS --safe #-}\n"), (late,))
        self.assertIn("2 OPTIONS pragmas",
                      pragma_problems(CC_FILE, "{-# OPTIONS --safe #-}\n" + SOURCE)[0])
        self.assertEqual(
            pragma_problems(CC_FILE, "{-# OPTIONS --cubical-compatible --safe #-}\n"),
            ("agda/ListReverseReverse.agda declares --cubical-compatible --safe "
             "but the manifest lists --safe --cubical-compatible",))

    def test_is_agda_source(self) -> None:
        for path in ("A.agda", "Sub/A.agda", "A.lagda", "A.lagda.md", "A.lagda.tex"):
            self.assertTrue(is_agda_source(path), path)
        for path in ("A.agdai", "A.md", "notes.agda.txt", "Makefile"):
            self.assertFalse(is_agda_source(path), path)


class TestSidecar(unittest.TestCase):
    def test_good_sidecar(self) -> None:
        good = {"bytes": 2_000_000, "sha256": "a" * 64, "command": "lake exe lean4export M -- N"}
        self.assertEqual(sidecar_problems(json.dumps(good)), ())

    def test_bad_sidecars(self) -> None:
        self.assertIn("not valid JSON", sidecar_problems("{")[0])
        self.assertEqual(sidecar_problems("[]"), ("lean/term.sidecar.json is not a JSON object",))
        self.assertEqual(len(sidecar_problems(json.dumps({"bytes": 1}))), 2)
        small = {"bytes": 10, "sha256": "A" * 64, "command": ""}
        self.assertEqual(len(sidecar_problems(json.dumps(small))), 3)


class TestEntryFiles(unittest.TestCase):
    def test_complete_directory(self) -> None:
        self.assertEqual(entry_file_problems(entry(), files()), ())
        sidecar = json.dumps({"bytes": 2_000_000, "sha256": "0" * 64, "command": "c"})
        self.assertEqual(entry_file_problems(entry(), files(term_bytes=None, sidecar=sidecar)), ())

    def test_every_missing_piece(self) -> None:
        problems = entry_file_problems(entry(), files(
            sources=(), present=("Extra.agda", "Sub/More.agda", "Notes.lagda.md"),
            has_statement=False, has_notes=False, term_bytes=None))
        unlisted = ("is not one of the files the manifest lists (plain .agda files directly "
                    "in agda/), so it would never be checked")
        self.assertEqual(problems, (
            "agda/ListReverseReverse.agda is listed but missing",
            f"agda/Extra.agda {unlisted}",
            f"agda/Sub/More.agda {unlisted}",
            f"agda/Notes.lagda.md {unlisted}",
            "lean/Statement.lean is missing",
            "notes.md is missing",
            "lean/ holds neither term.ndjson nor term.sidecar.json",
        ))

    def test_gather_entry_files(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "agda").mkdir()
            (root / "lean").mkdir()
            (root / "agda" / "ListReverseReverse.agda").write_text(SOURCE, "utf-8")
            (root / "agda" / "ListReverseReverse.agdai").write_text("", "utf-8")
            (root / "lean" / "Statement.lean").write_text("", "utf-8")
            gathered = gather_entry_files(root, entry()).unwrap()
            self.assertEqual(gathered, files(has_notes=False, term_bytes=None))

    def test_gather_finds_every_agda_source_and_the_term_size(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "agda" / "Sub").mkdir(parents=True)
            (root / "lean").mkdir()
            (root / "agda" / "ListReverseReverse.agda").write_text(SOURCE, "utf-8")
            (root / "agda" / "Sub" / "Extra.agda").write_text("module Sub.Extra where\n", "utf-8")
            (root / "agda" / "Sub" / "Extra.agdai").write_text("", "utf-8")
            (root / "agda" / "Notes.lagda.md").write_text("# n\n", "utf-8")
            (root / "lean" / "term.ndjson").write_text("{}\n", "utf-8")
            gathered = gather_entry_files(root, entry()).unwrap()
            self.assertEqual(gathered.present,
                             ("ListReverseReverse.agda", "Notes.lagda.md", "Sub/Extra.agda"))
            self.assertEqual(gathered.term_bytes, 3)

    def test_gather_without_an_agda_directory(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            gathered = gather_entry_files(Path(tmp), entry()).unwrap()
            self.assertEqual(gathered.present, ())
            self.assertEqual(gathered.sources, ())


class TestTermFiles(unittest.TestCase):
    SIDECAR = json.dumps({"bytes": 2_000_000, "sha256": "0" * 64, "command": "c"})

    def test_one_of_the_two(self) -> None:
        self.assertEqual(term_problems(56_062, None), ())
        self.assertEqual(term_problems(SIDECAR_THRESHOLD, None), ())
        self.assertEqual(term_problems(None, self.SIDECAR), ())

    def test_neither_both_or_too_large(self) -> None:
        self.assertEqual(term_problems(None, None),
                         ("lean/ holds neither term.ndjson nor term.sidecar.json",))
        self.assertEqual(term_problems(3, self.SIDECAR),
                         ("lean/ holds both term.ndjson and term.sidecar.json; the sidecar stands "
                          "in place of an export over 1 MB, so keep one",))
        self.assertEqual(term_problems(SIDECAR_THRESHOLD + 1, None),
                         ("lean/term.ndjson is 1,000,001 bytes, over the 1,000,000-byte limit; "
                          "commit lean/term.sidecar.json in its place",))


class TestOrphans(unittest.TestCase):
    def test_orphan_directories(self) -> None:
        items = (entry(), Malformed("set-ext", "planned", ("x",)))
        self.assertEqual(
            orphan_problems(["stray", "set-ext", "list-reverse-reverse", ".cache", "__pycache__"], items),
            ("corpus/stray/ is not the id of any manifest entry",))


if __name__ == "__main__":
    unittest.main()
