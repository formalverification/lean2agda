/-
File: translator/Lean2Agda/Main.lean
-/
import Lean2Agda
import Lean

namespace Lean2Agda

open Lean

/-- Lake supplies LEAN_PATH.  Imported environment extensions require
initializers and interpreter support, as in the existing atlas program. -/
def importEnvironment (modules : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  importModules (modules.map ({ module := · })) {} (loadExts := true)

def run (args : Args) : IO Unit := do
  let env ← importEnvironment args.modules
  let roots ← IO.ofExcept (selectRoots env args.modules args.declarations)
  let closure ← IO.ofExcept (dependencyClosure env roots)
  let listing := renderClosure args.profile closure
  if let some dir := args.out then
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir / "closure.txt") listing
  (← IO.getStdout).putStr listing

end Lean2Agda

def main (argv : List String) : IO UInt32 := do
  match Lean2Agda.parseArgs argv with
  | .error e =>
    IO.eprintln s!"lean2agda: {e}\n{Lean2Agda.usage}"
    return 2
  | .ok args =>
    if args.help then
      IO.println Lean2Agda.usage
      return 0
    try
      Lean2Agda.run args
      return 0
    catch e =>
      IO.eprintln s!"lean2agda: {e}"
      return 1
