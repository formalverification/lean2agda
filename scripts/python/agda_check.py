"""
File: scripts/python/agda_check.py

Description:
  Check the Agda tree that `lake exe lean2agda --out DIR` emits, one
  Agda process per module, each started once every module it imports
  has checked and at most N at a time, and record each module's time
  and peak memory.

  The tree is read from its files: every `.agda` file under DIR outside
  `_build/` is a module, named by its `module` line, and it depends on
  the modules of the tree that its `import` lines name (`import M`,
  `open import M`, with or without `public`).  The import graph must be
  acyclic, which Lean's module graph guarantees for an emitted tree, and
  each file must sit at the path its module's name asks for, as Agda
  requires.  The tree's `.agda-lib`, at DIR, is what lets Agda run from
  DIR resolve the imports.

  Two modes, as follows:

  + The default checks each module as it is, `agda <module>` run once
    from DIR, so that each module's interface is written under
    DIR/_build and every later module reads it instead of checking the
    module again.  A module whose import did not check is skipped, not
    run: Agda would check the import again, as part of the module.  The
    report has a row per module (result, seconds, peak memory, size) and
    a summary with the wall time; the exit status is 1 unless every
    module checks.  Agda reuses an interface that is newer than its
    module, so a second run over an unchanged tree checks nothing;
    `--fresh` removes DIR/_build first, which a measurement needs.
    `make check-output OUT=DIR` runs this mode.
  + `--refusals` runs the refusal loop of scaffold_check.py on each
    module of a scratch copy of the tree, in the same order, so that a
    module is checked against the final text of the modules it imports:
    a declaration that the loop reduced to a postulate in one module is
    a postulate for every module that imports it, and one that the loop
    dropped is dropped from every importing module before Agda runs,
    with what refers to it there, and counted as `dropped`, as Agda
    would otherwise meet it as a name out of scope.  The listing of each
    module is scaffold_check.py's, and a line per count sums them over
    the tree.  `--listings OUT` writes each module's listing beside its
    path under OUT (`U/Init/Core.checked.txt`) and the sums to
    OUT/checked.txt; `--keep OUT` copies the final tree there, which the
    default mode can then time without the loop (an OUT holding modules
    outside the tree is refused, since the next read of it would take
    them in).  `--types-only` keeps
    in each module what scaffold_check.py's `--types-only` keeps, and
    what any kept declaration of the tree names, in its own module or
    another, directly or not.  `--without-rewrite` removes every module's
    `REWRITE` pragmas first, as scaffold_check.py's `--without-rewrite`
    does: what checks with them and is refused without them is what a
    rewrite rule fired for.

    python3 scripts/python/agda_check.py [-j N] [--fresh] [--agda AGDA]
        [--timeout SECONDS] [--heap SIZE] [--json] DIR
    python3 scripts/python/agda_check.py --refusals [-j N] [--messages]
        [--listings OUT] [--keep OUT] [--types-only] [--without-rewrite]
        [--agda AGDA] [--timeout SECONDS] [--heap SIZE] DIR

  Agda runs with GHC's heap bounded (`--heap`, 8G by default, GHC's
  `-M`) and names each declaration as it starts it (`-v tc.decl:5`), so
  that a module that exhausts the heap fails alone, charged to the
  declaration Agda named last, instead of taking the machine with it.

Design Principles:
  - The peak memory of a module is the maximum resident set size of its
    own Agda process, which os.wait4 returns for that one child
    (ru_maxrss, in KiB on Linux).  resource.getrusage(RUSAGE_CHILDREN)
    cannot give it under -j: its ru_maxrss is the largest of every child
    waited for so far, so a module's figure would be any earlier
    module's that was larger.
  - Scheduling is pure: `launchable` says which modules may start, given
    what has finished, failed and started, and `simulate` replays a
    schedule with given durations, which is how the tests show that no
    module starts before the modules it imports have finished.
    `execute` runs the same rule with threads, one Agda each.
  - Each Agda run goes through agda_run.check_file and an injected
    runner and clock; the measuring runner is the only function that
    starts a process, and the report is built by pure functions.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Callable, Mapping, Optional, Sequence, TypeVar

from _utils.file_ops import read_text, write_text, ensure_dir_exists
from _utils.pipeline_types import ErrorType, PipelineError, Result
from agda_run import Clock, FileRun, Outcome, Runner, check_file, real_clock
from scaffold_check import (
    Checked, Event, Module, State, check_module, code, listing, parse_module, reach,
    references, types_only, without_rewrites,
)

DEFAULT_TIMEOUT: float = 3600.0
DEFAULT_HEAP: str = "8G"
DEFAULT_JOBS: int = max(1, (os.cpu_count() or 2) // 2)

T = TypeVar("T")

# The command, the directory it runs in, and the timeout in seconds; the
# result as command_runner shapes it, and the peak resident set size of
# the process in KiB (0 when no process ran).
MeasuredRunner = Callable[
    [Sequence[str], Path, float],
    tuple[Result[subprocess.CompletedProcess, PipelineError], int],
]

_MODULE = re.compile(r"^module (\S+) where$", re.MULTILINE)
_IMPORT = re.compile(r"^(?:open )?import (\S+)(?: public)?$", re.MULTILINE)
# "Checking X." which `-v tc.decl:5` prints as Agda starts a declaration.
_CHECKING = re.compile(r"^Checking (\S+)\.$", re.MULTILINE)
# GHC's runtime exits with 251 when the heap is exhausted.
_HEAP_EXIT = "exit code 251"
# A dotted word of printed Agda: an identifier, a projection `R.f`, or a
# reference qualified by a module's name.
_DOTTED = re.compile(r"[^\s(){}⦃⦄;]+")
# A count line of scaffold_check's listing: "checked 5 of 7 declarations,
# ...", as opposed to an event line, whose second word is not a number.
_COUNT_LINE = re.compile(r"^\w+ \d+ of \d+\b")
_NUMBER = re.compile(r"\d+")
# The error of a name out of scope, which in a tree means that a module's
# drop missed a declaration an imported module dropped: a defect, not a
# refusal.
_NOT_IN_SCOPE = "NotInScope"


# ---------------------------------------------------------------------------
# The tree
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Source:
    """One module of the tree: its name, its file relative to the tree's
    root, the modules its import lines name, and its size in bytes."""

    name: str
    path: str
    imports: tuple[str, ...]
    size: int


@dataclass(frozen=True)
class Tree:
    """The modules of a tree, by name, and for each the modules of the
    tree it imports."""

    modules: Mapping[str, Source]
    graph: Mapping[str, frozenset[str]]


def parse_source(path: str, text: str) -> Result[Source, str]:
    """The module a file declares and the modules it imports; an error
    for a file without a module line, or one at a path its name does not
    ask for."""
    match = _MODULE.search(text)
    if match is None:
        return Result.err(f"{path}: no module line")
    name = match.group(1)
    expected = "/".join(name.split(".")) + ".agda"
    if path != expected:
        return Result.err(f"{path}: module {name} belongs at {expected}")
    imports = tuple(dict.fromkeys(_IMPORT.findall(text.split("\n\n")[0])))
    return Result.ok(Source(name, path, imports, len(text.encode("utf-8"))))


def build_tree(sources: Sequence[Source]) -> Result[Tree, str]:
    """The tree of the sources: an error for two files declaring one
    module or for an import cycle."""
    modules = {s.name: s for s in sources}
    if len(modules) != len(sources):
        return Result.err("two files declare the same module")
    graph = {s.name: frozenset(i for i in s.imports if i in modules) for s in sources}
    found = find_cycle(graph)
    return Result.err(f"an import cycle: {' -> '.join(found)}") if found else Result.ok(Tree(modules, graph))


def find_cycle(graph: Mapping[str, frozenset[str]]) -> Optional[tuple[str, ...]]:
    """A cycle of the graph, as the modules along it with the first
    repeated at the end, or None.  Kahn's algorithm removes every module
    that is on no cycle; a walk among the rest closes one."""
    remaining = dict(graph)
    while True:
        free = tuple(m for m, deps in remaining.items() if not (deps & remaining.keys()))
        if not free:
            break
        remaining = {m: deps for m, deps in remaining.items() if m not in free}
    if not remaining:
        return None
    def walk(path: tuple[str, ...]) -> tuple[str, ...]:
        while path[-1] not in path[:-1]:
            path = path + (min(remaining[path[-1]] & remaining.keys()),)
        return path[path.index(path[-1]):]
    return walk((min(remaining),))


def topological(graph: Mapping[str, frozenset[str]]) -> tuple[str, ...]:
    """The modules, each after every module it imports, the smallest name
    first among those free to go: Kahn's algorithm, as a loop, since a
    chain of imports can be long."""
    order: tuple[str, ...] = ()
    done: frozenset[str] = frozenset()
    while len(order) < len(graph):
        free = min(m for m, deps in graph.items() if m not in done and deps <= done)
        order, done = order + (free,), done | {free}
    return order


def module_files(root: Path) -> list[Path]:
    """Every `.agda` file under `root`, outside `_build/`, relative to it."""
    return sorted(p.relative_to(root) for p in root.rglob("*.agda") if "_build" not in p.relative_to(root).parts)


def read_tree(root: Path) -> Result[Tree, str]:
    """Read every module of the tree under `root`, outside `_build/`."""
    paths = [root / p for p in module_files(root)]
    sources = []
    for p in paths:
        text = read_text(p)
        if text.is_err:
            return Result.err(str(text.unwrap_err()))
        source = parse_source(p.relative_to(root).as_posix(), text.unwrap())
        if source.is_err:
            return Result.err(source.unwrap_err())
        sources.append(source.unwrap())
    if not sources:
        return Result.err(f"{root}: no Agda modules")
    return build_tree(sources)


# ---------------------------------------------------------------------------
# Scheduling
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Progress:
    """What has started, what has finished, and which of those failed."""

    started: frozenset[str] = frozenset()
    finished: frozenset[str] = frozenset()
    failed: frozenset[str] = frozenset()


def dependents(graph: Mapping[str, frozenset[str]]) -> dict[str, int]:
    """For each module, how many modules import it, directly or not: the
    order in which `launchable` prefers modules, since a module many
    others wait for is best started early."""
    users: dict[str, frozenset[str]] = {m: frozenset(u for u, deps in graph.items() if m in deps) for m in graph}
    return {m: len(reach(frozenset(users[m]), lambda u: users[u])) for m in graph}


def blocked(graph: Mapping[str, frozenset[str]], failed: frozenset[str]) -> frozenset[str]:
    """The modules that import a failed module, directly or not."""
    users: dict[str, frozenset[str]] = {m: frozenset(u for u, deps in graph.items() if m in deps) for m in graph}
    return reach(failed, lambda m: users[m]) - failed


def launchable(graph: Mapping[str, frozenset[str]], progress: Progress, slots: int,
               priority: Mapping[str, int]) -> tuple[str, ...]:
    """The modules to start now, at most `slots` of them: those not yet
    started whose imports have all finished and checked, the ones most
    others wait for first, then by name."""
    good = progress.finished - progress.failed
    ready = sorted((m for m in graph if m not in progress.started and graph[m] <= good),
                   key=lambda m: (-priority[m], m))
    return tuple(ready[:max(0, slots)])


def skipped(graph: Mapping[str, frozenset[str]], progress: Progress) -> frozenset[str]:
    """The modules that will never start, because an import failed."""
    return blocked(graph, progress.failed) - progress.started


@dataclass(frozen=True)
class Span:
    """When a module ran in a simulated schedule."""

    module: str
    start: float
    end: float


def simulate(graph: Mapping[str, frozenset[str]], jobs: int, duration: Mapping[str, float],
             fails: frozenset[str] = frozenset()) -> tuple[Span, ...]:
    """Replay `launchable` with the given durations: the spans of the
    modules that ran, in the order they started.  A loop of events, each
    the earliest end among the running modules."""
    priority = dependents(graph)
    progress, spans, running, now = Progress(), (), {}, 0.0
    while True:
        for m in launchable(graph, progress, jobs - len(running), priority):
            running[m] = now + duration[m]
            spans = spans + (Span(m, now, now + duration[m]),)
            progress = replace(progress, started=progress.started | {m})
        if not running:
            return spans
        module = min(running, key=lambda m: (running[m], m))
        now = running.pop(module)
        failed = progress.failed | ({module} if module in fails else frozenset())
        progress = replace(progress, finished=progress.finished | {module}, failed=failed)


def execute(graph: Mapping[str, frozenset[str]], jobs: int, work: Callable[[str, Mapping[str, T]], T],
            passed: Callable[[T], bool]) -> dict[str, T]:
    """Run `work` on every module the schedule reaches, at most `jobs` at
    once, each after its imports have passed, giving it the results so
    far, which hold those of everything it imports: the result of each
    module that ran.  The one impure loop of the scheduler: threads, since
    each unit of work waits on its own Agda process."""
    priority = dependents(graph)
    progress, results = Progress(), {}
    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        running: dict[Future, str] = {}
        while True:
            for m in launchable(graph, progress, jobs - len(running), priority):
                running[pool.submit(work, m, dict(results))] = m
                progress = replace(progress, started=progress.started | {m})
            if not running:
                return results
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                module = running.pop(future)
                results[module] = future.result()
                failed = progress.failed | (frozenset() if passed(results[module]) else {module})
                progress = replace(progress, finished=progress.finished | {module}, failed=failed)


# ---------------------------------------------------------------------------
# Measured runs
# ---------------------------------------------------------------------------

def capped(command: Sequence[str], heap: str) -> tuple[str, ...]:
    """Agda's command with its heap bounded and each declaration named as
    Agda starts it."""
    return (command[0], "+RTS", f"-M{heap}", "-RTS", "-v", "tc.decl:5", *command[1:])


def measured_run(command: Sequence[str], cwd: Path,
                 timeout: float) -> tuple[Result[subprocess.CompletedProcess, PipelineError], int]:
    """The real measuring runner: start the command with its output in
    temporary files, kill it at the timeout, and reap it with os.wait4,
    which returns the child's own resource usage.  The result has the
    shapes command_runner gives (errors with "stdout" and "stderr" in
    their context), so agda_run.classify reads it unchanged.

    The timer and the reaping race: the child can exit on its own just as
    the timer fires.  The child is first waited for with WNOWAIT, which
    leaves it unreaped, so that its PID stays its own; then, under a lock
    the timer also takes, it is marked exited, and only then reaped.  So
    the timer signals only a child not yet reaped, never a reused PID, and
    a run is a timeout only when that signal is what ended it, as the exit
    status shows: a child that exited by itself first passes or fails on
    its own exit code."""
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        try:
            process = subprocess.Popen(list(command), cwd=cwd, stdout=out, stderr=err)
        except OSError as e:
            return Result.err(PipelineError(ErrorType.COMMAND_FAILED, f"Command not found: {command[0]}",
                                            cause=e)), 0
        lock = threading.Lock()
        exited = threading.Event()
        signalled = threading.Event()
        def kill() -> None:
            with lock:
                if not exited.is_set():
                    os.kill(process.pid, signal.SIGKILL)
                    signalled.set()
        timer = threading.Timer(timeout, kill)
        timer.start()
        try:
            os.waitid(os.P_PID, process.pid, os.WEXITED | os.WNOWAIT)
            with lock:
                exited.set()
            _, status, usage = os.wait4(process.pid, 0)
        finally:
            timer.cancel()
        process.returncode = os.waitstatus_to_exitcode(status)
        expired = signalled.is_set() and process.returncode == -signal.SIGKILL
        out.seek(0)
        err.seek(0)
        stdout = out.read().decode("utf-8", errors="replace")
        stderr = err.read().decode("utf-8", errors="replace")
    peak = int(usage.ru_maxrss)
    context = {"command": " ".join(command), "stdout": stdout, "stderr": stderr.strip()}
    if expired:
        return Result.err(PipelineError(ErrorType.TIMEOUT, f"Command timed out after {timeout:g} seconds",
                                        context={**context, "timeout": timeout})), peak
    if process.returncode != 0:
        return Result.err(PipelineError(ErrorType.COMMAND_FAILED,
                                        f"Command failed with exit code {process.returncode}",
                                        context={**context, "return_code": process.returncode})), peak
    return Result.ok(subprocess.CompletedProcess(list(command), 0, stdout, stderr)), peak


def metered(runner: MeasuredRunner, heap: str, peaks: list[int]) -> Runner:
    """An agda_run Runner over the measuring runner: it bounds Agda's
    heap and appends each run's peak to `peaks`, which belongs to one
    unit of work, the edge where a measurement is kept."""
    def run(command: Sequence[str], cwd: Path, timeout: float) -> Result[subprocess.CompletedProcess, PipelineError]:
        result, peak = runner(capped(command, heap), cwd, timeout)
        peaks.append(peak)
        return result
    return run


# ---------------------------------------------------------------------------
# The default mode: each module once
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ModuleRun:
    """One module of the report: its result ("pass", "fail", "timeout",
    "heap" or "skipped"), the seconds and peak KiB of its Agda run (None
    when skipped), a one-line message, and Agda's output on a failure."""

    name: str
    path: str
    size: int
    result: str
    seconds: Optional[float]
    peak_kib: Optional[int]
    message: str
    output: str


@dataclass(frozen=True)
class Report:
    """The rows in dependency order, the parallelism, and the wall time."""

    rows: tuple[ModuleRun, ...]
    jobs: int
    wall: float


def last_declaration(output: str) -> Optional[str]:
    """The declaration Agda named last in `-v tc.decl:5` output."""
    names = _CHECKING.findall(output)
    return names[-1] if names else None


def module_run(source: Source, run: FileRun, peak: int) -> ModuleRun:
    """The row of a module that ran.  A heap exhaustion or a timeout is
    charged to the declaration Agda named last."""
    heap = run.outcome == Outcome.FAIL and run.message.endswith(_HEAP_EXIT)
    result = "heap" if heap else run.outcome.value
    last = last_declaration(run.output) if result in ("heap", "timeout") else None
    message = ("heap exhausted" if heap else run.message) + (f" at {last}" if last else "")
    return ModuleRun(source.name, source.path, source.size, result, run.seconds, peak, message, run.output)


def skipped_run(source: Source) -> ModuleRun:
    """The row of a module whose import did not check."""
    return ModuleRun(source.name, source.path, source.size, "skipped", None, None,
                     "an import did not check", "")


def assemble(tree: Tree, runs: Mapping[str, ModuleRun], jobs: int, wall: float) -> Report:
    """The report: a row per module in dependency order."""
    return Report(tuple(runs.get(m, skipped_run(tree.modules[m])) for m in topological(tree.graph)), jobs, wall)


def exit_status(report: Report) -> int:
    """0 when every module checked, 1 otherwise."""
    return 0 if all(r.result == "pass" for r in report.rows) else 1


def _mib(kib: Optional[int]) -> str:
    return "-" if kib is None else f"{kib / 1024:.0f}"


def _secs(seconds: Optional[float]) -> str:
    return "-" if seconds is None else f"{seconds:.1f}"


def format_table(report: Report) -> str:
    """One row per module: name, result, seconds, peak MiB, size KB."""
    width = max([len("module")] + [len(r.name) for r in report.rows])
    head = f"{'module':<{width}}  {'result':<7}  {'seconds':>8}  {'peak MiB':>8}  {'KB':>6}"
    rows = tuple(f"{r.name:<{width}}  {r.result:<7}  {_secs(r.seconds):>8}  {_mib(r.peak_kib):>8}  "
                 f"{r.size / 1000:>6.0f}" for r in report.rows)
    return "\n".join((head,) + rows)


def format_summary(report: Report) -> str:
    """The counts, the wall time, the sum of the modules' times, and the
    largest peak."""
    counts = {k: sum(1 for r in report.rows if r.result == k) for k in ("pass", "fail", "timeout", "heap", "skipped")}
    total = sum(r.seconds or 0.0 for r in report.rows)
    peak = max((r.peak_kib or 0 for r in report.rows), default=0)
    failed = ", ".join(f"{n} {k}" for k, n in counts.items() if k != "pass" and n)
    return (f"{len(report.rows)} modules, {counts['pass']} checked" + (f", {failed}" if failed else "")
            + f"; {report.wall:.1f} s wall with -j {report.jobs}, {total:.1f} s in all, "
            f"largest peak {_mib(peak)} MiB")


def format_details(report: Report) -> str:
    """The message and output of every module that did not check."""
    return "\n\n".join(f"{r.name}: {r.message}" + (f"\n{r.output.rstrip()}" if r.output else "")
                       for r in report.rows if r.result not in ("pass", "skipped"))


def format_text(report: Report) -> str:
    """The table, the failures, and the summary."""
    return "\n\n".join(p for p in (format_table(report), format_details(report), format_summary(report)) if p)


def format_json(report: Report) -> str:
    """The report as one JSON object."""
    return json.dumps({
        "modules": [{"name": r.name, "path": r.path, "bytes": r.size, "result": r.result,
                     "seconds": r.seconds, "peak_kib": r.peak_kib, "message": r.message, "output": r.output}
                    for r in report.rows],
        "jobs": report.jobs,
        "wall_seconds": report.wall,
    }, indent=2, ensure_ascii=False)


def check_tree(tree: Tree, root: Path, runner: MeasuredRunner, clock: Clock, agda: str,
               jobs: int, timeout: float, heap: str) -> Report:
    """Check every module once, in dependency order, `jobs` at a time."""
    def work(name: str, _: Mapping[str, ModuleRun]) -> ModuleRun:
        peaks: list[int] = []
        run = check_file(metered(runner, heap, peaks), clock, agda, root, tree.modules[name].path, timeout)
        return module_run(tree.modules[name], run, max(peaks, default=0))
    start = clock()
    runs = execute(tree.graph, jobs, work, lambda r: r.result == "pass")
    return assemble(tree, runs, jobs, clock() - start)


# ---------------------------------------------------------------------------
# --refusals: scaffold_check's loop over the tree
# ---------------------------------------------------------------------------

def foreign_names(text: str, modules: frozenset[str], own: str) -> frozenset[str]:
    """The identifiers that `text` takes from other modules of the tree:
    for each word qualified by a module's name other than `own`, the
    first component after the longest such name (`U.A.R.f` takes `R`
    from `U.A`)."""
    def split(word: str) -> Optional[str]:
        parts = word.split(".")
        prefixes = (".".join(parts[:k]) for k in range(len(parts) - 1, 0, -1))
        found = next((p for p in prefixes if p in modules and p != own), None)
        return None if found is None else parts[len(found.split("."))]
    return frozenset(n for n in map(split, _DOTTED.findall(text)) if n is not None)


def named(text: str, modules: frozenset[str], own: str) -> frozenset[str]:
    """Every identifier `text` names: those it takes from other modules
    by qualified names (`foreign_names`), and the first component of
    every other word, which names an identifier of its own module or of
    a module it opens, as a part of a split module opens the earlier
    parts."""
    def first(word: str) -> Optional[str]:
        parts = word.split(".")
        qualified = any(".".join(parts[:k]) in modules for k in range(1, len(parts)))
        return None if qualified else parts[0]
    bare = frozenset(n for n in map(first, _DOTTED.findall(text)) if n is not None)
    return bare | foreign_names(text, modules, own)


def predropped(module: Module, dead: frozenset[str], modules: frozenset[str]) -> tuple[int, ...]:
    """The items of `module` to drop before Agda runs: those whose code
    names a dead identifier of a module it imports or opens, and the
    items that refer to those, directly or through each other, in module
    order.  Identifiers are unique across a tree, so a dead one named
    bare is one an opened module dropped."""
    seeds = frozenset(i for i, item in enumerate(module.items)
                      if named(code(item), modules, module.name) & dead)
    refs = references(module.items)
    users = {i: frozenset(j for j, r in enumerate(refs) if i in r) for i in range(len(module.items))}
    return tuple(sorted(reach(seeds, lambda i: users[i])))


def without(module: Module, gone: tuple[int, ...]) -> Module:
    """The module with the items at `gone` removed."""
    return Module(module.name, module.header, tuple(item for i, item in enumerate(module.items) if i not in gone))


def merged(module: Module, gone: tuple[int, ...], checked: State) -> State:
    """The state of the whole module: the items dropped before Agda ran,
    dead and listed first as `dropped`, and the loop's state for the
    rest, at their places."""
    kept = tuple(i for i in range(len(module.items)) if i not in gone)
    place = {i: k for k, i in enumerate(kept)}
    items = tuple(checked.items[place[i]] if i in place else item for i, item in enumerate(module.items))
    alive = tuple(checked.alive[place[i]] if i in place else False for i in range(len(module.items)))
    events = tuple(Event("dropped", module.items[i].names[0], "", "") for i in gone)
    return State(items, alive, events + checked.events)


def types_only_tree(modules: Mapping[str, Module]) -> dict[str, Module]:
    """Each module restricted as scaffold_check.types_only restricts it,
    together with every item that a kept item of the tree names, in its
    module or another, directly or not, so that no kept item names one
    that is gone.  A kept item is the restricted module's version of it
    when there is one (a theorem postulated, say), else the original."""
    names = frozenset(modules)
    local = {m: {item.names[0]: item for item in types_only(mod).items} for m, mod in modules.items()}
    version = {(m, i): local[m].get(item.names[0], item)
               for m, mod in modules.items() for i, item in enumerate(mod.items)}
    owner = {n: (m, i) for m, mod in modules.items() for i, item in enumerate(mod.items) for n in item.names}
    within = {m: references(tuple(version[(m, i)] for i in range(len(mod.items)))) for m, mod in modules.items()}

    def successors(node: tuple[str, int]) -> frozenset[tuple[str, int]]:
        m, i = node
        taken = named(code(version[node]), names, m)
        return (frozenset((m, j) for j in within[m][i])
                | frozenset(owner[n] for n in taken if n in owner and owner[n][0] != m))

    starts = frozenset((m, i) for m, mod in modules.items()
                       for i, item in enumerate(mod.items) if item.names[0] in local[m])
    keep = reach(starts, successors)
    return {m: Module(mod.name, mod.header, tuple(version[(m, i)] for i in range(len(mod.items)) if (m, i) in keep))
            for m, mod in modules.items()}


def dead_names(state: State) -> frozenset[str]:
    """The identifiers of a checked module that its importers cannot use."""
    return frozenset(n for item, a in zip(state.items, state.alive) if not a for n in item.names)


def sum_counts(listings: Sequence[str]) -> str:
    """The count lines of scaffold_check's listings summed: each line
    that begins "word N of M", with every number replaced by its sum over
    the listings that have a line of the same words."""
    def counts(text: str) -> tuple[str, ...]:
        return tuple(line for line in text.splitlines() if _COUNT_LINE.match(line))
    lines = [counts(t) for t in listings]
    shapes = list(dict.fromkeys(_NUMBER.sub("#", line) for ls in lines for line in ls))
    def total(shape: str) -> str:
        rows = [tuple(map(int, _NUMBER.findall(line))) for ls in lines for line in ls
                if _NUMBER.sub("#", line) == shape]
        sums = iter(tuple(sum(col) for col in zip(*rows)))
        return re.sub("#", lambda _: str(next(sums)), shape)
    return "\n".join(map(total, shapes)) + ("\n" if shapes else "")


@dataclass(frozen=True)
class Pruned:
    """One module after the loop: its listing, its dead identifiers, the
    number of Agda runs and their seconds, the largest peak, or the error
    that stopped the loop."""

    name: str
    listing: str
    dead: frozenset[str]
    runs: int
    seconds: float
    peak_kib: int
    error: str = ""


def rewrites_removed(modules: Mapping[str, Module]) -> dict[str, Module]:
    """Each module without its `REWRITE` pragmas, as
    scaffold_check.without_rewrites leaves it."""
    return {name: without_rewrites(module) for name, module in modules.items()}


def restrict_tree(tree: Tree, scratch: Path,
                  restrict: Callable[[Mapping[str, Module]], Mapping[str, Module]] = types_only_tree
                  ) -> Result[None, str]:
    """Rewrite the scratch tree's modules as `restrict` gives them,
    types_only_tree by default."""
    parsed: dict[str, Module] = {}
    for name, source in tree.modules.items():
        module = read_text(scratch / source.path).map_err(str).and_then(lambda t: parse_module(t).map_err(str))
        if module.is_err:
            return Result.err(module.unwrap_err())
        parsed[name] = module.unwrap()
    for name, module in restrict(parsed).items():
        text = "\n\n".join((module.header,) + tuple(item.text for item in module.items)) + "\n"
        written = write_text(scratch / tree.modules[name].path, text)
        if written.is_err:
            return Result.err(str(written.unwrap_err()))
    return Result.ok(None)


def prune_module(tree: Tree, scratch: Path, runner: MeasuredRunner, clock: Clock, agda: str,
                 timeout: float, heap: str, messages: bool, done: Mapping[str, Pruned], name: str) -> Pruned:
    """Run scaffold_check's loop on one module of the scratch tree, after
    dropping what takes a dead identifier from a module it imports."""
    source = tree.modules[name]
    imported = reach(tree.graph[name], lambda m: tree.graph[m])
    dead = frozenset().union(*(done[m].dead for m in imported if m in done))
    parsed = read_text(scratch / source.path).map_err(str).and_then(
        lambda t: parse_module(t).map_err(str))
    if parsed.is_err:
        return Pruned(name, "", frozenset(), 0, 0.0, 0, parsed.unwrap_err())
    module = parsed.unwrap()
    gone = predropped(module, dead, frozenset(tree.modules))
    peaks: list[int] = []
    outcome = check_module(metered(runner, heap, peaks), clock, agda, without(module, gone), timeout, scratch)
    if outcome.is_err:
        return Pruned(name, "", frozenset(), 0, 0.0, max(peaks, default=0), str(outcome.unwrap_err()))
    result: Checked = outcome.unwrap()
    state = merged(module, gone, result.state)
    lost = tuple(e.name for e in state.events if e.error == _NOT_IN_SCOPE)
    error = f"Agda found names out of scope, which the drop missed: {', '.join(lost)}" if lost else ""
    return Pruned(name, listing(state, messages), dead_names(state), result.runs, result.seconds,
                  max(peaks, default=0), error)


def format_pruned(tree: Tree, pruned: Mapping[str, Pruned], jobs: int, wall: float) -> str:
    """The listings summed over the tree, then a row per module: its Agda
    runs, their seconds, its largest peak, and the first count line of
    its listing."""
    order = topological(tree.graph)
    width = max([len("module")] + [len(m) for m in order])
    rows = tuple(
        f"{m:<{width}}  {pruned[m].runs:>4}  {pruned[m].seconds:>8.1f}  {_mib(pruned[m].peak_kib):>8}  "
        + (pruned[m].listing.split("\n")[0] if not pruned[m].error else f"error: {pruned[m].error}")
        if m in pruned else f"{m:<{width}}  skipped: an import did not finish"
        for m in order)
    total = sum(p.seconds for p in pruned.values())
    runs = sum(p.runs for p in pruned.values())
    head = f"{'module':<{width}}  {'runs':>4}  {'seconds':>8}  {'peak MiB':>8}  listing"
    return (sum_counts([p.listing for p in pruned.values()])
            + f"{len(order)} modules, {runs} Agda runs, {total:.1f} s in all, {wall:.1f} s wall with -j {jobs}\n\n"
            + "\n".join((head,) + rows) + "\n")


def strays(tree: Tree, target: Path) -> list[str]:
    """The modules under `target` that are not the tree's: copied over,
    they would join the tree the next read of `target` finds."""
    own = {Path(s.path) for s in tree.modules.values()}
    return [str(p) for p in module_files(target) if p not in own] if target.is_dir() else []


def keep_target(tree: Tree, target: Path) -> Result[None, str]:
    """`target` can take the tree: nothing there, or only the tree's own
    modules, which the copy replaces.  Any other module refuses it, since
    deleting what a user's directory holds is no checker's business."""
    found = strays(tree, target)
    if not found:
        return Result.ok(None)
    more = f" and {len(found) - 1} more" if len(found) > 1 else ""
    return Result.err(f"--keep {target} holds modules outside the tree ({found[0]}{more}); "
                      "remove them or keep the tree elsewhere")


def copy_tree(tree: Tree, source: Path, target: Path) -> Result[None, str]:
    """Copy the tree's modules and its `.agda-lib` file to `target`."""
    try:
        target.mkdir(parents=True, exist_ok=True)
        for lib in source.glob("*.agda-lib"):
            shutil.copyfile(lib, target / lib.name)
        for s in tree.modules.values():
            (target / s.path).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source / s.path, target / s.path)
        return Result.ok(None)
    except OSError as e:
        return Result.err(str(e))


def write_listings(tree: Tree, pruned: Mapping[str, Pruned], out: Path) -> Result[None, str]:
    """Each module's listing at its path under `out`, as NAME.checked.txt,
    and the summed counts in out/checked.txt."""
    for name, p in pruned.items():
        target = out / Path(tree.modules[name].path).with_suffix(".checked.txt")
        made = ensure_dir_exists(target.parent).and_then(lambda _: write_text(target, p.listing))
        if made.is_err:
            return Result.err(str(made.unwrap_err()))
    written = ensure_dir_exists(out).and_then(
        lambda _: write_text(out / "checked.txt", sum_counts([p.listing for p in pruned.values()])))
    return written.map(lambda _: None).map_err(str)


def prune_tree(tree: Tree, root: Path, scratch: Path, runner: MeasuredRunner, clock: Clock,
               agda: str, jobs: int, timeout: float, heap: str, messages: bool) -> tuple[dict[str, Pruned], float]:
    """The loop over every module of a scratch copy of the tree, in
    dependency order, `jobs` at a time, and the wall time it took."""
    def work(name: str, done: Mapping[str, Pruned]) -> Pruned:
        return prune_module(tree, scratch, runner, clock, agda, timeout, heap, messages, done, name)
    start = clock()
    results = execute(tree.graph, jobs, work, lambda p: not p.error)
    return results, clock() - start


# ---------------------------------------------------------------------------
# The command line
# ---------------------------------------------------------------------------

def positive(text: str) -> int:
    """An argparse type: a whole number of at least 1."""
    try:
        n = int(text)
    except ValueError:
        n = 0
    if n < 1:
        raise argparse.ArgumentTypeError(f"needs a whole number of at least 1, not {text!r}")
    return n


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    """The command line."""
    parser = argparse.ArgumentParser(description="Check an emitted Agda tree in dependency order.")
    parser.add_argument("tree", type=Path, help="the directory lean2agda --out wrote")
    parser.add_argument("-j", "--jobs", type=positive, default=DEFAULT_JOBS,
                        help=f"Agda processes at once (default: {DEFAULT_JOBS})")
    parser.add_argument("--agda", default="agda")
    parser.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT,
                        help=f"seconds allowed per Agda run (default: {DEFAULT_TIMEOUT:g})")
    parser.add_argument("--heap", default=DEFAULT_HEAP, help=f"Agda's heap bound (default: {DEFAULT_HEAP})")
    parser.add_argument("--json", action="store_true", help="print the report as JSON")
    parser.add_argument("--fresh", action="store_true",
                        help="remove the tree's _build directory first, so that every module is checked")
    parser.add_argument("--refusals", action="store_true",
                        help="run scaffold_check's refusal loop on each module of a scratch copy")
    parser.add_argument("--messages", action="store_true", help="with --refusals, list each error's message")
    parser.add_argument("--listings", type=Path, help="with --refusals, write each module's listing here")
    parser.add_argument("--keep", type=Path, help="with --refusals, copy the final tree here")
    parser.add_argument("--types-only", action="store_true",
                        help="with --refusals, keep the data types and records and what they need")
    parser.add_argument("--without-rewrite", action="store_true",
                        help="with --refusals, remove the REWRITE pragmas first")
    return parser.parse_args(argv)


def main(argv: Sequence[str]) -> int:
    """Read the tree, check it, print the report."""
    args = parse_args(argv)
    root = args.tree.resolve()
    read = read_tree(root)
    if read.is_err:
        print(f"agda_check: {read.unwrap_err()}", file=sys.stderr)
        return 1
    tree = read.unwrap()
    if not args.refusals:
        if args.fresh:
            shutil.rmtree(root / "_build", ignore_errors=True)
        report = check_tree(tree, root, measured_run, real_clock, args.agda, args.jobs, args.timeout, args.heap)
        print(format_json(report) if args.json else format_text(report))
        return exit_status(report)
    target = keep_target(tree, args.keep) if args.keep else Result.ok(None)
    if target.is_err:
        print(f"agda_check: {target.unwrap_err()}", file=sys.stderr)
        return 1
    with tempfile.TemporaryDirectory(prefix="agda-check-") as scratch:
        copied = copy_tree(tree, root, Path(scratch)).and_then(
            lambda _: restrict_tree(tree, Path(scratch), rewrites_removed) if args.without_rewrite
            else Result.ok(None)).and_then(
            lambda _: restrict_tree(tree, Path(scratch)) if args.types_only else Result.ok(None))
        if copied.is_err:
            print(f"agda_check: {copied.unwrap_err()}", file=sys.stderr)
            return 1
        pruned, wall = prune_tree(tree, root, Path(scratch), measured_run, real_clock, args.agda,
                                  args.jobs, args.timeout, args.heap, args.messages)
        kept = copy_tree(tree, Path(scratch), args.keep) if args.keep else Result.ok(None)
    listed = write_listings(tree, pruned, args.listings) if args.listings else Result.ok(None)
    print(format_pruned(tree, pruned, args.jobs, wall), end="")
    problems = [r.unwrap_err() for r in (kept, listed) if r.is_err]
    problems += [f"{p.name}: {p.error}" for p in pruned.values() if p.error]
    for problem in problems:
        print(f"agda_check: {problem}", file=sys.stderr)
    return 1 if problems or len(pruned) < len(tree.modules) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
