"""
File: scripts/python/tests/test_agda_check.py

Description:
  Tests of agda_check.py.  The tree's parsing, the import graph, the
  scheduling rule and its replay, the report and the refusal loop over a
  tree are tested on small modules written by hand in the shape
  `lake exe lean2agda --out` writes, with a fake measuring runner that
  plays Agda's answers and a fake clock.  The real measuring runner is
  tested on short Python processes: a peak it must see, a failure, and a
  timeout.
"""
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from dataclasses import replace
from pathlib import Path
from typing import Callable, Mapping, Sequence

from _utils.pipeline_types import ErrorType, PipelineError, Result
from agda_check import (
    Progress, Pruned, Source, Span, assemble, blocked, build_tree, capped, check_tree, dependents,
    execute, exit_status, find_cycle, foreign_names, named, format_summary, format_table, launchable,
    Tree, Unfold, in_vain_unfolds, injections, keep_target, measured_run, merged, module_run,
    next_requests, parse_args,
    parse_source, positive, predropped, prune_tree, read_tree, requests, simulate, skipped, strays, summed,
    sum_counts, topological, types_only_tree, unfold_modules, without,
)
from agda_run import FileRun, Outcome
from scaffold_check import Event, Module, State, listing, parse_item, parse_module, transparent

HEADER = "{-# OPTIONS --type-in-type #-}\n-- a comment\n"

# A diamond: D imports B and C, which import A; E imports nothing.
DIAMOND: dict[str, frozenset[str]] = {
    "A": frozenset(), "B": frozenset({"A"}), "C": frozenset({"A"}),
    "D": frozenset({"B", "C"}), "E": frozenset(),
}


def line_of(text: str, start: str) -> int:
    """The 1-based number of the first line of `text` that begins with
    `start`: where a fake Agda points its error."""
    return next(i for i, line in enumerate(text.split("\n"), 1) if line.startswith(start))


def module_text(name: str, imports: Sequence[str] = (), body: str = "postulate X : Set\n",
                opens: Sequence[str] = ()) -> str:
    lines = [f"import {m}" for m in imports] + [f"open import {m}" for m in opens]
    return HEADER + f"module {name} where\n" + "".join(line + "\n" for line in lines) + "\n" + body


def passed(command: Sequence[str]) -> Result[subprocess.CompletedProcess, PipelineError]:
    return Result.ok(subprocess.CompletedProcess(list(command), 0, "", ""))


def failed(stdout: str, code: int = 42) -> Result[subprocess.CompletedProcess, PipelineError]:
    return Result.err(PipelineError(ErrorType.COMMAND_FAILED, f"Command failed with exit code {code}",
                                    context={"return_code": code, "stdout": stdout}))


class TestParseSource(unittest.TestCase):
    def test_name_and_imports(self) -> None:
        text = module_text("U.A.B", ["U.C", "U.D"], opens=["U.A.B.~p1"]) + "\nimport U.Late\n"
        source = parse_source("U/A/B.agda", text + "open import U.A.B.~p2 public\n").unwrap()
        self.assertEqual((source.name, source.path, source.imports), ("U.A.B", "U/A/B.agda",
                                                                      ("U.C", "U.D", "U.A.B.~p1")))
        self.assertEqual(source.size, len((text + "open import U.A.B.~p2 public\n").encode("utf-8")))

    def test_public_reexports_are_imports(self) -> None:
        text = HEADER + "module U.A where\nopen import U.A.~p1 public\nopen import U.A.~p2 public\n"
        self.assertEqual(parse_source("U/A.agda", text).unwrap().imports, ("U.A.~p1", "U.A.~p2"))

    def test_a_file_at_the_wrong_path(self) -> None:
        self.assertEqual(parse_source("U/B.agda", module_text("U.A")).unwrap_err(),
                         "U/B.agda: module U.A belongs at U/A.agda")

    def test_no_module_line(self) -> None:
        self.assertTrue(parse_source("U/A.agda", "postulate X : Set\n").is_err)


class TestGraph(unittest.TestCase):
    def test_imports_outside_the_tree_are_not_edges(self) -> None:
        tree = build_tree((Source("A", "A.agda", ("Data.Nat",), 1), Source("B", "B.agda", ("A",), 1))).unwrap()
        self.assertEqual(dict(tree.graph), {"A": frozenset(), "B": frozenset({"A"})})

    def test_a_cycle_is_refused(self) -> None:
        sources = (Source("A", "A.agda", ("B",), 1), Source("B", "B.agda", ("A",), 1), Source("C", "C.agda", ("A",), 1))
        self.assertEqual(build_tree(sources).unwrap_err(), "an import cycle: A -> B -> A")
        self.assertIsNone(find_cycle(DIAMOND))

    def test_two_files_for_one_module(self) -> None:
        self.assertTrue(build_tree((Source("A", "A.agda", (), 1), Source("A", "x/A.agda", (), 1))).is_err)

    def test_topological_order(self) -> None:
        self.assertEqual(topological(DIAMOND), ("A", "B", "C", "D", "E"))
        self.assertEqual(topological({"Z": frozenset(), "Y": frozenset({"Z"})}), ("Z", "Y"))

    def test_dependents_and_blocked(self) -> None:
        self.assertEqual(dependents(DIAMOND), {"A": 3, "B": 1, "C": 1, "D": 0, "E": 0})
        self.assertEqual(blocked(DIAMOND, frozenset({"B"})), frozenset({"D"}))
        self.assertEqual(blocked(DIAMOND, frozenset({"A"})), frozenset({"B", "C", "D"}))

    def test_read_tree(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "U" / "A").mkdir(parents=True)
            (root / "_build" / "U").mkdir(parents=True)
            (root / "U" / "A.agda").write_text(module_text("U.A"))
            (root / "U" / "A" / "B.agda").write_text(module_text("U.A.B", ["U.A"]))
            (root / "_build" / "U" / "Junk.agda").write_text("not a module")
            tree = read_tree(root).unwrap()
            self.assertEqual(dict(tree.graph), {"U.A": frozenset(), "U.A.B": frozenset({"U.A"})})
            self.assertTrue(read_tree(root / "U" / "A" / "missing").is_err)

    def test_a_keep_target(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root, target = Path(d) / "tree", Path(d) / "kept"
            (root / "U").mkdir(parents=True)
            (root / "U" / "A.agda").write_text(module_text("U.A"))
            tree = read_tree(root).unwrap()
            self.assertTrue(keep_target(tree, target).is_ok)
            (target / "U").mkdir(parents=True)
            (target / "U" / "A.agda").write_text("an earlier copy, replaced")
            (target / "_build" / "U").mkdir(parents=True)
            (target / "_build" / "U" / "Old.agda").write_text("ignored, as read_tree ignores it")
            self.assertEqual(strays(tree, target), [])
            self.assertTrue(keep_target(tree, target).is_ok)
            (target / "U" / "Stray.agda").write_text(module_text("U.Stray"))
            self.assertEqual(strays(tree, target), [str(Path("U") / "Stray.agda")])
            self.assertIn("U/Stray.agda", keep_target(tree, target).unwrap_err())
            self.assertTrue((target / "U" / "Stray.agda").exists())


class TestScheduling(unittest.TestCase):
    def test_launchable_waits_for_every_import(self) -> None:
        priority = dependents(DIAMOND)
        self.assertEqual(launchable(DIAMOND, Progress(), 4, priority), ("A", "E"))
        started = Progress(started=frozenset({"A", "E"}), finished=frozenset({"E"}))
        self.assertEqual(launchable(DIAMOND, started, 4, priority), ())
        progress = Progress(started=frozenset({"A", "E", "B"}), finished=frozenset({"A", "E", "B"}))
        self.assertEqual(launchable(DIAMOND, progress, 4, priority), ("C",))

    def test_launchable_respects_the_slots_and_prefers_what_others_wait_for(self) -> None:
        priority = dependents(DIAMOND)
        self.assertEqual(launchable(DIAMOND, Progress(), 1, priority), ("A",))
        self.assertEqual(launchable(DIAMOND, Progress(), 0, priority), ())

    def test_a_failed_import_blocks_its_users(self) -> None:
        progress = Progress(started=frozenset({"A", "E"}), finished=frozenset({"A", "E"}), failed=frozenset({"A"}))
        self.assertEqual(launchable(DIAMOND, progress, 4, dependents(DIAMOND)), ())
        self.assertEqual(skipped(DIAMOND, progress), frozenset({"B", "C", "D"}))

    def assert_respects_imports(self, spans: tuple[Span, ...], graph: Mapping[str, frozenset[str]], jobs: int) -> None:
        end = {s.module: s.end for s in spans}
        for s in spans:
            for i in graph[s.module]:
                self.assertLessEqual(end[i], s.start, f"{s.module} started before its import {i} ended")
        for s in spans:
            overlapping = sum(1 for t in spans if t.start <= s.start < t.end)
            self.assertLessEqual(overlapping, jobs)

    def test_simulate_runs_in_parallel_only_what_is_independent(self) -> None:
        duration = {"A": 2.0, "B": 3.0, "C": 1.0, "D": 1.0, "E": 5.0}
        spans = simulate(DIAMOND, 2, duration)
        self.assertEqual([(s.module, s.start, s.end) for s in spans],
                         [("A", 0.0, 2.0), ("E", 0.0, 5.0), ("B", 2.0, 5.0), ("C", 5.0, 6.0), ("D", 6.0, 7.0)])
        self.assert_respects_imports(spans, DIAMOND, 2)
        wide = simulate(DIAMOND, 4, duration)
        self.assert_respects_imports(wide, DIAMOND, 4)
        self.assertEqual(max(s.end for s in wide), 6.0)
        self.assertEqual(max(s.end for s in simulate(DIAMOND, 1, duration)), 12.0)

    def test_simulate_never_starts_what_a_failure_blocks(self) -> None:
        spans = simulate(DIAMOND, 4, {m: 1.0 for m in DIAMOND}, fails=frozenset({"B"}))
        self.assertEqual(sorted(s.module for s in spans), ["A", "B", "C", "E"])

    def test_execute_with_threads(self) -> None:
        lock = threading.Lock()
        log: list[tuple[str, str]] = []
        seen: dict[str, frozenset[str]] = {}

        def work(module: str, done: Mapping[str, str]) -> str:
            with lock:
                log.append(("start", module))
            seen[module] = frozenset(done)
            with lock:
                log.append(("end", module))
            return "fail" if module == "C" else "ok"

        results = execute(DIAMOND, 3, work, lambda r: r == "ok")
        self.assertEqual(results, {"A": "ok", "B": "ok", "C": "fail", "E": "ok"})
        for module, imports in DIAMOND.items():
            if module in results:
                self.assertLessEqual(imports, seen[module])
                for i in imports:
                    self.assertLess(log.index(("end", i)), log.index(("start", module)))


class TestMeasuredRuns(unittest.TestCase):
    def test_capped(self) -> None:
        self.assertEqual(capped(("agda", "U/A.agda"), "8G"),
                         ("agda", "+RTS", "-M8G", "-RTS", "-v", "tc.decl:5", "U/A.agda"))

    def test_a_peak_it_must_see(self) -> None:
        result, peak = measured_run((sys.executable, "-c", "x = bytearray(200_000_000); x[-1] = 1"), Path("."), 60.0)
        self.assertTrue(result.is_ok)
        self.assertGreater(peak, 190_000)

    def test_a_failure_keeps_the_output(self) -> None:
        result, _ = measured_run((sys.executable, "-c", "print('out'); raise SystemExit(42)"), Path("."), 60.0)
        error = result.unwrap_err()
        self.assertEqual((error.error_type, error.message, error.context["stdout"]),
                         (ErrorType.COMMAND_FAILED, "Command failed with exit code 42", "out\n"))

    def test_a_timeout(self) -> None:
        result, _ = measured_run((sys.executable, "-c", "import time; time.sleep(30)"), Path("."), 0.5)
        self.assertEqual(result.unwrap_err().error_type, ErrorType.TIMEOUT)

    def test_the_timer_firing_after_the_child_exits(self) -> None:
        # The race: the child exits on its own, and the timer fires before
        # its exit is noted.  Each wait call is made to pause past the
        # timeout after it returns, the window widened to certainty.
        # The timer must signal nothing it no longer owns: a kill of a
        # reaped PID raises ProcessLookupError in the timer's thread (or,
        # with the PID reused, kills another process).
        real = {name: getattr(os, name) for name in ("waitid", "wait4")}
        raised: list[BaseException | None] = []
        hook = threading.excepthook
        def slow(name: str) -> Callable[..., object]:
            def call(*args: object) -> object:
                answer = real[name](*args)
                time.sleep(1.0)
                return answer
            return call
        try:
            threading.excepthook = lambda e: raised.append(e.exc_value)
            for name in real:
                setattr(os, name, slow(name))
            result, _ = measured_run((sys.executable, "-c", "pass"), Path("."), 0.5)
        finally:
            for name, call in real.items():
                setattr(os, name, call)
            threading.excepthook = hook
        self.assertTrue(result.is_ok, result)
        self.assertEqual(raised, [])

    def test_a_child_killed_otherwise_is_no_timeout(self) -> None:
        result, _ = measured_run(("sh", "-c", "kill -9 $$"), Path("."), 60.0)
        self.assertEqual(result.unwrap_err().message, "Command failed with exit code -9")

    def test_positive_jobs(self) -> None:
        self.assertEqual(positive("3"), 3)
        for text in ("0", "-2", "x", ""):
            with self.assertRaises(argparse.ArgumentTypeError):
                positive(text)
        self.assertEqual(parse_args(["-j", "2", "t"]).jobs, 2)

    def test_a_missing_command(self) -> None:
        result, peak = measured_run(("no-such-agda-here", "x"), Path("."), 5.0)
        self.assertEqual((result.unwrap_err().message, peak), ("Command not found: no-such-agda-here", 0))


class TestReport(unittest.TestCase):
    source = Source("U.A", "U/A.agda", (), 2500)

    def test_module_run(self) -> None:
        self.assertEqual(module_run(self.source, FileRun("U/A.agda", Outcome.PASS, 1.5, "", ""), 2048).result, "pass")
        heap = module_run(self.source, FileRun("U/A.agda", Outcome.FAIL, 9.0, "Command failed with exit code 251",
                                               "Checking a.\nChecked a.\nChecking b.\n"), 8_000_000)
        self.assertEqual((heap.result, heap.message), ("heap", "heap exhausted at b"))
        late = module_run(self.source, FileRun("U/A.agda", Outcome.TIMEOUT, 60.0, "Command timed out", "Checking c.\n"), 1)
        self.assertEqual((late.result, late.message), ("timeout", "Command timed out at c"))
        bad = module_run(self.source, FileRun("U/A.agda", Outcome.FAIL, 1.0, "A.agda:3.1-2: error: [X]", "..."), 1)
        self.assertEqual((bad.result, bad.message), ("fail", "A.agda:3.1-2: error: [X]"))

    def test_check_tree_with_a_fake_agda(self) -> None:
        sources = {name: Source(name, name.replace(".", "/") + ".agda", tuple(sorted(DIAMOND[name])), 1000)
                   for name in DIAMOND}
        tree = build_tree(tuple(sources.values())).unwrap()
        lock = threading.Lock()
        commands: list[tuple[str, ...]] = []

        def runner(command: Sequence[str], cwd: Path, timeout: float) -> tuple:
            with lock:
                commands.append(tuple(command))
            path = command[-1]
            return (failed("A.agda:1.1-2: error: [Bad]\n") if path == "B.agda" else passed(command)), 4096

        ticks = iter(range(1000))
        report = check_tree(tree, Path("/tree"), runner, lambda: float(next(ticks)), "agda", 2, 60.0, "4G")
        self.assertEqual([(r.name, r.result) for r in report.rows],
                         [("A", "pass"), ("B", "fail"), ("C", "pass"), ("D", "skipped"), ("E", "pass")])
        self.assertTrue(all(c[:6] == ("agda", "+RTS", "-M4G", "-RTS", "-v", "tc.decl:5") for c in commands))
        self.assertEqual(sorted(c[-1] for c in commands), ["A.agda", "B.agda", "C.agda", "E.agda"])
        self.assertEqual(report.rows[0].peak_kib, 4096)
        self.assertEqual(exit_status(report), 1)
        self.assertIn("5 modules, 3 checked, 1 fail, 1 skipped", format_summary(report))
        self.assertEqual(format_table(report).split("\n")[1].split(), ["A", "pass", "1.0", "4", "1"])

    def test_every_module_checked(self) -> None:
        tree = build_tree((self.source,)).unwrap()
        row = module_run(self.source, FileRun("U/A.agda", Outcome.PASS, 1.0, "", ""), 1024)
        self.assertEqual(exit_status(assemble(tree, {"U.A": row}, 1, 1.0)), 0)


# Module U.A drops `bad` (its type refused) and postulates `soft`;
# U.B uses both, and its `user` is used by `chain`.
MODULE_B = module_text("U.B", ["U.A"], body=(
    "keep : U.A.Nat\nkeep = U.A.Nat:zero\n\n"
    "user : U.A.Nat\nuser = U.A.bad\n\n"
    "chain : U.A.Nat\nchain = user\n\n"
    "soft~uuse : U.A.Nat\nsoft~uuse = U.A.soft\n\n"
    "field~uuse : U.A.R → U.A.Nat\nfield~uuse r₀ = U.A.R.f₀ r₀\n"))


class TestUnfoldingAcrossModules(unittest.TestCase):
    """The fallback across modules: a refusal naming another module's
    opaque theorem asks for it, the next pass makes it transparent there,
    and the dependent's listing records the unfolding."""

    theorem = parse_item("-- theorem\nopaque\n  thm : T\n  thm = t")
    graph = {"U.A": frozenset(), "U.B": frozenset({"U.A"}), "U.C": frozenset()}
    tree = Tree({}, graph)

    def pruned(self, alive: bool = True, detail: str = "U.A.thm != x of type T") -> dict[str, Pruned]:
        a = State((self.theorem,), (alive,), ())
        user = parse_item("user : T\nuser = x")
        b = State((user,), (True,), (Event("refused value", "user", "UnequalTerms", "thm != x", detail=detail),))
        c = State((parse_item("-- theorem\nopaque\n  other : T\n  other = t"),), (True,), ())
        return {m: Pruned(m, "", frozenset(), 1, 0.0, 0, "", s) for m, s in (("U.A", a), ("U.B", b), ("U.C", c))}

    def test_requests(self) -> None:
        self.assertEqual(requests(self.tree, self.pruned()),
                         (Unfold("U.A", "thm", "U.B", "user", "UnequalTerms", "thm != x"),))
        self.assertEqual(requests(self.tree, self.pruned(alive=False)), ())
        # A theorem of a module U.B does not import is not its to unfold.
        self.assertEqual(requests(self.tree, self.pruned(detail="other != x")), ())
        self.assertEqual(requests(self.tree, self.pruned(detail="nothing named")), ())

    def test_an_unfolding_in_vain_is_undone(self) -> None:
        one = Unfold("U.A", "thm", "U.B", "user", "UnequalTerms", "thm != x")
        # The dependent is refused again, naming no other theorem: in vain.
        refused = self.pruned(detail="nothing named")
        self.assertEqual(in_vain_unfolds((one,), (), refused), frozenset({("U.A", "thm", "user")}))
        self.assertEqual(next_requests(self.tree, refused, (one,), frozenset()), ((), frozenset({("U.A", "thm", "user")})))
        # Still asking for a theorem: the chain goes on, nothing is undone.
        self.assertEqual(in_vain_unfolds((one,), (replace(one, theorem="t2"),), refused), frozenset())
        # A dependent that checked made no unfolding in vain.
        checked = dict(refused, **{"U.B": replace(refused["U.B"], state=State(refused["U.B"].state.items, (True,), ()))})
        self.assertEqual(in_vain_unfolds((one,), (), checked), frozenset())

    def test_an_undone_theorem_can_be_asked_for_again(self) -> None:
        one = Unfold("U.A", "thm", "U.B", "user", "UnequalTerms", "thm != x")
        # The same dependent does not ask twice; another one may.
        self.assertEqual(next_requests(self.tree, self.pruned(), (one,), frozenset({("U.A", "thm", "user")})),
                         ((), frozenset()))
        other = replace(one, dependent="other")
        self.assertEqual(next_requests(self.tree, self.pruned(), (other,), frozenset({("U.A", "thm", "other")})),
                         ((one,), frozenset()))

    def test_a_dependent_after_one_already_asked_still_asks(self) -> None:
        # Two refusals name the theorem in one pass, the first by a
        # dependent that asked for it before, in vain: the second still asks.
        pruned = self.pruned()
        b = pruned["U.B"].state
        first = Event("refused value", "other", "UnequalTerms", "thm != y", detail="U.A.thm != y of type T")
        pruned = dict(pruned, **{"U.B": replace(pruned["U.B"], state=State(b.items, b.alive, (first,) + b.events))})
        asked = Unfold("U.A", "thm", "U.B", "other", "UnequalTerms", "thm != y")
        fresh, _ = next_requests(self.tree, pruned, (asked,), frozenset({("U.A", "thm", "other")}))
        self.assertEqual([u.dependent for u in fresh], ["user"])

    def test_every_dependent_that_asks_claims_the_theorem(self) -> None:
        # Two refusals name the theorem t2 in one pass: both claim it, so
        # that their chains run side by side and each records its own; the
        # second, whose unfolding of thm is active, is still asking.
        t2 = parse_item("-- theorem\nopaque\n  t2 : T\n  t2 = t")
        a = State((t2,), (True,), ())
        b = State((parse_item("first : T\nfirst = x"), parse_item("user : T\nuser = x")), (True, True),
                  (Event("refused value", "first", "UnequalTerms", "t2 != x", detail="U.A.t2 != x of type T"),
                   Event("refused value", "user", "UnequalTerms", "t2 != y", detail="U.A.t2 != y of type T")))
        pruned = {m: Pruned(m, "", frozenset(), 1, 0.0, 0, "", s) for m, s in (("U.A", a), ("U.B", b))}
        tree = Tree({}, {"U.A": frozenset(), "U.B": frozenset({"U.A"})})
        active = Unfold("U.A", "thm", "U.B", "user", "UnequalTerms", "thm != x")
        fresh, vain = next_requests(tree, pruned, (active,), frozenset())
        self.assertEqual([(u.theorem, u.dependent) for u in fresh], [("t2", "first"), ("t2", "user")])
        self.assertEqual(vain, frozenset())

    def test_unfold_modules(self) -> None:
        module = Module("U.A", "header", (self.theorem, parse_item("thm2 : T\nthm2 = t")))
        out = unfold_modules({"U.A": module}, (Unfold("U.A", "thm", "U.B", "user", "E", "m"),))["U.A"]
        self.assertEqual(out.items[0], transparent(self.theorem, "user"))
        self.assertEqual(out.items[1], module.items[1])

    def test_the_listing_records_it(self) -> None:
        unfold = Unfold("U.A", "thm", "U.B", "user", "UnequalTerms", "thm != x")
        injected = injections((unfold,))["U.B"]
        items = (parse_item("user : T\nuser = x"), parse_item("next : T\nnext = x"))
        checked = listing(State(items, (True, True), injected), False)
        self.assertIn("unfolded 1 of 0 theorems, 0 in vain\n", checked)
        self.assertTrue(checked.endswith("\nunfolded UnequalTerms thm for user\n"), checked)
        refused = State(items, (True, True), injected + (Event("refused value", "user", "UnequalTerms", "again"),))
        self.assertIn("unfolded UnequalTerms thm for user, in vain\n", listing(refused, False))
        # Two such unfoldings in one module: neither is looked up there.
        two = injected + injections((replace(unfold, theorem="thm2", dependent="next"),))["U.B"]
        self.assertIn("unfolded 2 of 0 theorems, 0 in vain", listing(State(items, (True, True), two), False))

    def test_summed(self) -> None:
        first = {"U.A": Pruned("U.A", "one", frozenset(), 3, 1.5, 100)}
        second = {"U.A": Pruned("U.A", "two", frozenset(), 2, 1.0, 80)}
        self.assertEqual(summed((first, second)), {"U.A": Pruned("U.A", "two", frozenset(), 5, 2.5, 100)})


class TestRefusalsOverATree(unittest.TestCase):
    modules = frozenset({"U.A", "U.B", "U.A.~p1"})

    def test_foreign_names(self) -> None:
        self.assertEqual(foreign_names("U.A.R.f₀ r₀ (U.A.Nat:succ x) U.A.~p1.y local", self.modules, "U.B"),
                         frozenset({"R", "Nat:succ", "y"}))
        self.assertEqual(foreign_names("U.B.z", self.modules, "U.B"), frozenset())
        self.assertEqual(foreign_names("R.f₀ r₀", self.modules, "U.B"), frozenset())

    def test_named_takes_bare_and_qualified_names(self) -> None:
        self.assertEqual(named("U.A.R.f₀ x₀ (local y) R.f₀ U.A.~p1.z", self.modules, "U.B"),
                         frozenset({"R", "z", "x₀", "local", "y"}))

    def test_predropped_sees_what_an_opened_part_dropped(self) -> None:
        part = parse_module(module_text("U.A.~p2", opens=["U.A.~p1"], body=(
            "keep : Nat\nkeep = Nat:zero\n\nuser : Nat\nuser = bad\n\nchain : Nat\nchain = user\n"))).unwrap()
        gone = predropped(part, frozenset({"bad"}), self.modules)
        self.assertEqual([part.items[i].names[0] for i in gone], ["user", "chain"])

    def test_predropped_reads_no_string(self) -> None:
        module = parse_module(module_text("U.B", ["U.A"], body=(
            'greeting : U.A.Str\ngreeting = "prefix U.A.bad bad suffix"\n\n'
            "uses : U.A.Str\nuses = greeting\n\nuser : Nat\nuser = U.A.bad\n"))).unwrap()
        gone = predropped(module, frozenset({"bad"}), self.modules)
        self.assertEqual([module.items[i].names[0] for i in gone], ["user"])

    def test_predropped_takes_local_dependents(self) -> None:
        module = parse_module(MODULE_B).unwrap()
        gone = predropped(module, frozenset({"bad", "R"}), self.modules)
        self.assertEqual([module.items[i].names[0] for i in gone], ["user", "chain", "field~uuse"])
        self.assertEqual(predropped(module, frozenset(), self.modules), ())

    def test_merged_keeps_places(self) -> None:
        module = parse_module(MODULE_B).unwrap()
        rest = without(module, (1, 2))
        checked = State(rest.items, (True, False, True), ())
        state = merged(module, (1, 2), checked)
        self.assertEqual(state.alive, (True, False, False, False, True))
        self.assertEqual([(e.action, e.name) for e in state.events], [("dropped", "user"), ("dropped", "chain")])

    def test_sum_counts(self) -> None:
        a = "checked 3 of 4 declarations, 1 of 1 data types and records\nunfolded 0 of 2 theorems, 0 in vain\ndropped x\n"
        b = "checked 5 of 5 declarations, 0 of 2 data types and records\nunfolded 1 of 1 theorems, 1 in vain\n"
        self.assertEqual(sum_counts([a, b]),
                         "checked 8 of 9 declarations, 1 of 3 data types and records\n"
                         "unfolded 1 of 3 theorems, 1 in vain\n")
        self.assertEqual(sum_counts([]), "")

    def test_types_only_tree_keeps_what_other_modules_need(self) -> None:
        module_a = parse_module(module_text("U.A", body=(
            "postulate Nat : Set\n\npostulate Unused : Set\n\npostulate Size : Set\n\n"
            "postulate size : Size\n\npostulate Far : Set"))).unwrap()
        module_b = parse_module(module_text("U.B", ["U.A"], body=(
            "data T : Set where\n  T:mk : U.A.Nat → T\n\n"
            "f : U.A.Size\nf = U.A.size\n\n"
            "g : U.A.Far\ng = g"))).unwrap()
        restricted = types_only_tree({"U.A": module_a, "U.B": module_b})
        self.assertEqual([i.names[0] for i in restricted["U.B"].items], ["T"])
        self.assertEqual([i.names[0] for i in restricted["U.A"].items], ["Nat"])

    def test_prune_tree_drops_before_agda_runs(self) -> None:
        module_a = module_text("U.A", body=(
            "data Nat : Set where\n  Nat:zero : Nat\n\n"
            "postulate bad : Nat\n\n"
            "soft : Nat\nsoft = Nat:zero\n\n"
            "record R : Set where\n  constructor R:mk\n  field\n    f₀ : Nat\n"))
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "U").mkdir()
            (root / "U" / "A.agda").write_text(module_a)
            (root / "U" / "B.agda").write_text(MODULE_B)
            tree = read_tree(root).unwrap()
            seen: dict[str, list[str]] = {"U/A.agda": [], "U/B.agda": []}
            # A: `bad`'s type is refused, then `soft`'s value, once `bad`
            # is gone; each error points at the line where the checker's
            # copy has that declaration (after a marker definition).
            answers = {"U/A.agda": iter([("postulate bad", "X"), ("soft = ", "Y"), None]),
                       "U/B.agda": iter([None])}

            def runner(command: Sequence[str], cwd: Path, timeout: float) -> tuple:
                path = command[-1]
                text = (cwd / path).read_text()
                seen[path].append(text)
                answer = next(answers[path])
                if answer is None:
                    return passed(command), 100
                return failed(f"/s/{path}:{line_of(text, answer[0])}.1-9: error: [{answer[1]}]\nno\nwhen x\n"), 100

            ticks = iter(range(1000))
            pruned, _ = prune_tree(tree, root, root, runner, lambda: float(next(ticks)), "agda", 2, 60.0, "8G", False)
            final = (root / "U" / "A.agda").read_text()
            self.assertIn("postulate soft : Nat", final)
            # What B imports, and --keep copies, has no marker definitions.
            self.assertNotIn("scaffold-check-mark", final)
        self.assertEqual(pruned["U.A"].dead, frozenset({"bad"}))
        self.assertEqual(len(seen["U/B.agda"]), 1)
        self.assertNotIn("user", seen["U/B.agda"][0])
        self.assertNotIn("chain", seen["U/B.agda"][0])
        self.assertIn("soft~uuse = U.A.soft", seen["U/B.agda"][0])
        self.assertEqual(pruned["U.B"].listing,
                         "checked 3 of 5 declarations, 0 of 0 data types and records\n"
                         "unfolded 0 of 0 theorems, 0 in vain\n"
                     "defined 0 of 0 recursors by pattern matching, 0 refused by the termination checker\n"
                     "dropped user\ndropped chain\n")
        self.assertEqual((pruned["U.A"].runs, pruned["U.B"].runs, pruned["U.B"].peak_kib), (3, 1, 100))
        self.assertIsInstance(pruned["U.B"], Pruned)

    def test_a_name_out_of_scope_is_an_error_not_a_refusal(self) -> None:
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "U").mkdir()
            (root / "U" / "B.agda").write_text(module_text("U.B", body="keep : Nat\nkeep = lost\n"))
            tree = read_tree(root).unwrap()
            answers = iter([True, False])

            def runner(command: Sequence[str], cwd: Path, timeout: float) -> tuple:
                if not next(answers):
                    return passed(command), 1
                line = line_of((cwd / command[-1]).read_text(), "keep = lost")
                return failed(f"/s/U/B.agda:{line}.1-9: error: [NotInScope]\nNot in scope:\n  lost\nwhen x\n"), 1

            ticks = iter(range(100))
            pruned, _ = prune_tree(tree, root, root, runner, lambda: float(next(ticks)), "agda", 1, 60.0, "8G", False)
        self.assertEqual(pruned["U.B"].error, "Agda found names out of scope, which the drop missed: keep")


if __name__ == "__main__":
    unittest.main()
