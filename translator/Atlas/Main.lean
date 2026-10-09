/-
File: translator/Atlas/Main.lean
-/
import Atlas.Collect

/-!
# Atlas.Main

The command line of the axiom atlas, `lake exe atlas`, run from
`translator/`:

    lake exe atlas [--import MODULE]... [--out FILE]

It imports the modules (by default `Mathlib`) from the `.olean` files
Lake's dependencies provide, computes the exact axiom set of every
constant of the resulting environment (`Atlas.Graph`), writes one NDJSON
record per constant (`Atlas.Record`), and beside the records a small
JSON file with the run's time and peak memory.  The default output is
`../atlas/mathlib-<tag>-<commit>.ndjson`, named after the Mathlib pin
that `lake-manifest.json` records.

The program imports `Lean` only and loads Mathlib when it runs, as
lean4export and Batteries' `runLinter` do, so `lake build` never needs
Mathlib's modules.
-/

open Lean Atlas

/-- The command line, parsed. -/
structure Args where
  imports : Array Name := #[]
  out     : Option System.FilePath := none

/-- Parse the arguments; an error names the argument it cannot use. -/
def parseArgs : List String → Except String Args
  | [] => pure {}
  | "--import" :: m :: rest => do
    let args ← parseArgs rest
    pure { args with imports := #[m.toName] ++ args.imports }
  | "--out" :: path :: rest => do
    let args ← parseArgs rest
    pure { args with out := some path }
  | arg :: _ => throw s!"unexpected argument {arg}; usage: atlas [--import MODULE]... [--out FILE]"

/-- Mathlib's tag and commit, from the text of `lake-manifest.json`. -/
def mathlibPin (manifest : String) : Except String (String × String) := do
  let json ← Json.parse manifest
  let packages ← json.getObjValAs? (Array Json) "packages"
  let isMathlib (p : Json) := (p.getObjValAs? String "name").toOption == some "mathlib"
  let some mathlib := packages.find? isMathlib
    | throw "lake-manifest.json names no package mathlib"
  return (← mathlib.getObjValAs? String "inputRev", ← mathlib.getObjValAs? String "rev")

/-- The default output file, named after the Mathlib pin. -/
def defaultOut (tag rev : String) : System.FilePath :=
  "../atlas" / s!"mathlib-{tag}-{rev.take 7}.ndjson"

/-- The file beside the records that holds the run's time and memory. -/
def runFile (out : System.FilePath) : System.FilePath :=
  out.withExtension "run.json"

/-- The peak resident memory in KiB, from the text of `/proc/self/status`
(Linux's `VmHWM` line), or `none` where there is no such line. -/
def peakKiB (status : String) : Option Nat := do
  let line ← (status.splitOn "\n").find? (·.startsWith "VmHWM:")
  (String.ofList (line.toList.filter Char.isDigit)).toNat?

/-- How long each phase of a run took, in milliseconds, and the peak
memory in KiB if the system reports it. -/
structure Run where
  importMs  : Nat
  graphMs   : Nat
  recordsMs : Nat
  peakKiB   : Option Nat

/-- The run file's text. -/
def Run.render (r : Run) : String :=
  let seconds (ms : Nat) : String := (Json.num ⟨ms, 3⟩).compress
  renderObject [
    ("import_seconds", seconds r.importMs),
    ("graph_seconds", seconds r.graphMs),
    ("records_seconds", seconds r.recordsMs),
    ("total_seconds", seconds (r.importMs + r.graphMs + r.recordsMs)),
    ("peak_rss_kib", match r.peakKiB with | some k => renderNat k | none => "null")
  ] ++ "\n"

/-- Write one record per constant to `handle`, in the order of
`constants`, whose exact axiom sets `axioms` is aligned with; return how
many there were. -/
def writeRecords (handle : IO.FS.Handle) (constants : Array (Name × ConstantInfo))
    (axioms : Array (Array Name)) : CoreM Nat := do
  for (n, ci) in constants, axs in axioms do
    handle.putStrLn (← recordOf n ci axs).render
  return constants.size

/-- Read a file, or fail with a message that names it. -/
def readOrFail (path : System.FilePath) : IO String := do
  try IO.FS.readFile path
  catch e => throw <| IO.userError s!"atlas: cannot read {path}: {e}"

/-- The environment of the modules, loaded from Lake's `.olean` files. -/
def importEnv (imports : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  -- Mathlib's modules register environment extensions with `initialize`;
  -- importing with `loadExts` runs those initializers, which needs this.
  unsafe enableInitializersExecution
  importModules (imports.map ({ module := · })) {} (loadExts := true) (leakEnv := true)

/-- Milliseconds since an arbitrary start, after running `x`; `x` is
forced first, so that a pure computation is timed where it is wanted. -/
def timed {α : Type} (x : Unit → α) : IO (α × Nat) := do
  let a ← IO.lazyPure x
  return (a, ← IO.monoMsNow)

/-- Write the atlas of `env` to `out`: the header, one record per
constant, and the last line; return the number of records and the
milliseconds the graph and the records took. -/
def writeAtlas (env : Environment) (header : Array (Name × ConstantInfo) → Header)
    (out : System.FilePath) : IO (Nat × Nat × Nat) := do
  let start ← IO.monoMsNow
  let constants := constantsInOrder env
  let ((axioms, count), graphed) ← timed fun _ => (axiomSets constants, valueGraphCount constants)
  if let some dir := out.parent then IO.FS.createDirAll dir
  let handle ← IO.FS.Handle.mk out .write
  handle.putStrLn (header constants).render
  let ctx : Core.Context := {
    fileName := "<atlas>", fileMap := default, options := maxHeartbeats.set {} 0 }
  let written ← (writeRecords handle constants axioms).toIO' ctx { env }
  handle.putStrLn (endLine written count)
  handle.flush
  return (written, graphed - start, (← IO.monoMsNow) - graphed)

def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv with
    | .ok args => pure args
    | .error msg => IO.eprintln s!"atlas: {msg}"; return 2
  let (tag, rev) ← match mathlibPin (← readOrFail "lake-manifest.json") with
    | .ok pin => pure pin
    | .error msg => IO.eprintln s!"atlas: lake-manifest.json: {msg}"; return 2
  let imports := if args.imports.isEmpty then #[`Mathlib] else args.imports
  let out := args.out.getD (defaultOut tag rev)
  let start ← IO.monoMsNow
  let env ← importEnv imports
  let imported ← IO.monoMsNow
  let header (constants : Array (Name × ConstantInfo)) : Header := {
    leanVersion := Lean.versionString, leanCommit := Lean.githash,
    mathlibTag := tag, mathlibRev := rev, imports, constants := constants.size }
  let (written, graphMs, recordsMs) ← writeAtlas env header out
  let peak := peakKiB (← IO.FS.readFile "/proc/self/status" <|> pure "")
  let run : Run := { importMs := imported - start, graphMs, recordsMs, peakKiB := peak }
  IO.FS.writeFile (runFile out) run.render
  IO.println s!"atlas: {written} records of {imports} at Mathlib {tag} ({rev.take 7}) in {out}"
  IO.println s!"atlas: {run.render.trimAscii}"
  return 0
