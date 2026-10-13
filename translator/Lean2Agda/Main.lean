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

/-- The scaffold's comment names the roots, up to five. -/
def scaffoldComment (closure : Closure) : String :=
  let shown := closure.roots.toList.take 5 |>.map agdaIdent
  let more := if closure.roots.size > 5 then s!" and {closure.roots.size - 5} more" else ""
  s!"lean2agda, profile U: the scaffold of the closure of {" ".intercalate shown}{more}"

/-- With `--out DIR`, write the listing, the names sidecars of the shared
closure (so that they cover its auxiliary definitions), the scaffold at
the path of its root's sidecar, and `refusals.txt`, one line per
declaration the scaffold refuses, with its reason. -/
def writeOutputs (env : Environment) (args : Args) (dir : System.FilePath) (closure : Closure)
    (listing : String) : IO Unit := do
  let shared ← IO.ofExcept (shareClosure env args.share closure)
  let maps ← IO.ofExcept <| moduleNameMaps args.root shared
  let s ← IO.ofExcept (scaffold env args.root shared)
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "closure.txt") listing
  for map in maps do
    let filename := map.sidecarPath dir
    IO.FS.createDirAll filename.parent.get!
    IO.FS.writeFile filename map.render
  let file := s.filePath dir
  IO.FS.createDirAll file.parent.get!
  IO.FS.writeFile file (s.render (scaffoldComment closure))
  IO.FS.writeFile (dir / "refusals.txt") s.renderRefusals

def run (args : Args) : IO Unit := do
  let env ← importEnvironment args.modules
  let roots ← IO.ofExcept (selectRoots env args.modules args.declarations)
  let closure ← IO.ofExcept (dependencyClosure env roots)
  let listing := renderClosure args.profile closure
  if let some dir := args.out then writeOutputs env args dir closure listing
  (← IO.getStdout).putStr listing
  if args.stats then (← IO.getStdout).putStr closure.stats.render

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
