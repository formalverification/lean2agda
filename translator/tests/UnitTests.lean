/-
File: translator/tests/UnitTests.lean
-/
import Check
import Inductives
import Modules
import Naming
import Printing
import Recursors
import Scaffold

/-!
# The unit tests

The root of the executable `unittests`, the package's test driver:
`lake test` builds it and runs it, and `lake test -- NAME...` runs the
named checks only.  Each check imports the environments it needs when it
runs, reads its fixtures then, and throws on a failure; the driver runs
every check selected, reports each, and exits 1 if any failed, 2 on a
usage error.  The checks read their fixtures by paths relative to
`translator/`, which is where `lake test` runs from.

`Printing` and `Naming` also write the Agda files that `tests/run.sh`
checks with Agda afterwards, when `PRINTING_AGDA_TEST_DIR` and
`NAMING_AGDA_TEST_DIR` name a directory.  The checks that need Agda, a
previous run's output, or a golden file stay in `run.sh`.
-/

/-- The checks, by the names `lake test -- NAME` selects them by. -/
def checks : List (String × IO Unit) :=
  [("check", CheckTests.runChecks), ("inductives", InductiveTests.run),
   ("modules", ModulesTests.run), ("naming", NamingTests.run), ("printing", PrintingTests.run),
   ("recursors", RecursorTests.run), ("scaffold", ScaffoldTests.run)]

/-- Run one check, timed; its failure is reported, not thrown. -/
def runCheck (name : String) (check : IO Unit) : IO Bool := do
  let start ← IO.monoMsNow
  try
    check
    IO.println s!"unittests: {name} passed in {(← IO.monoMsNow) - start} ms"
    return true
  catch e =>
    IO.eprintln s!"unittests: {name} failed: {e}"
    return false

def main (args : List String) : IO UInt32 := do
  let names := checks.map (·.1)
  let unknown := args.filter (!names.contains ·)
  unless unknown.isEmpty do
    IO.eprintln s!"unittests: no check named {", ".intercalate unknown}; the checks are {", ".intercalate names}"
    return 2
  unless ← System.FilePath.pathExists "tests/UnitTests.lean" do
    IO.eprintln "unittests: run from translator/, where the checks find their fixtures (cd translator && lake test)"
    return 2
  let selected := if args.isEmpty then checks else checks.filter (args.contains ·.1)
  let results ← selected.mapM fun (name, check) => runCheck name check
  let failed := (selected.zip results).filterMap fun ((name, _), ok) => if ok then none else some name
  if failed.isEmpty then
    IO.println s!"unittests: {selected.length} of {selected.length} checks passed"
    return 0
  IO.eprintln s!"unittests: {failed.length} of {selected.length} checks failed: {", ".intercalate failed}"
  return 1
