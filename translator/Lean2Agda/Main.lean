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

/-- Write `text` to `file`, making its directory first. -/
def writeMaking (file : System.FilePath) (text : String) : IO Unit := do
  if let some parent := file.parent then IO.FS.createDirAll parent
  IO.FS.writeFile file text

/-- With `--out DIR`, write the listing, the names sidecars of the shared
closure (so that they cover its auxiliary definitions), the scaffold's
tree of modules, each at the path of its source module's sidecar (a part
beside it, in a directory of the module's name), the library file and a
`libraries` file naming it by its absolute path, the module importing
every module, and `refusals.txt`, one line per declaration the scaffold
refuses, with its reason. -/
def writeOutputs (env : Environment) (args : Args) (dir : System.FilePath) (closure : Closure)
    (listing : String) : IO Unit := do
  let shared ← IO.ofExcept (shareClosure env args.share closure)
  let maps ← IO.ofExcept <| moduleNameMaps args.root shared
  let tree ← IO.ofExcept (scaffoldTree env args.root shared args.split)
  let comment := scaffoldComment closure
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "closure.txt") listing
  for map in maps do
    writeMaking (map.sidecarPath dir) map.render
  for m in tree.modules do
    writeMaking (m.filePath dir) (m.render comment)
  writeMaking (tree.everythingPath.foldl (· / ·) dir |>.addExtension "agda") (tree.renderEverything comment)
  IO.FS.writeFile (dir / tree.libraryFile) (tree.renderLibrary comment)
  IO.FS.writeFile (dir / "libraries") s!"{← IO.FS.realPath (dir / tree.libraryFile)}\n"
  IO.FS.writeFile (dir / "refusals.txt") tree.renderRefusals

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
