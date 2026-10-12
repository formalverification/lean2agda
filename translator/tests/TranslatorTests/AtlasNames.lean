/-
File: translator/tests/TranslatorTests/AtlasNames.lean
-/
import Lean2Agda
import Lean

open Lean Lean2Agda

namespace NamingAtlas

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

structure Population where
  names : Array Name
  mathlib : Nat

private def appendComponent (baseName : Name) (component : String) : Name :=
  match component.toNat? with
  | some n => .num baseName n
  | none => .str baseName component

/-- Lean prints macro scopes without quoting `_@`, which its name-literal
decoder rejects.  Recover this atlas form structurally and require both
the real macro-scope predicate and an exact printed round trip.  The
optional environment probe checks for ambiguity at the pinned population. -/
def parseAtlasName (text : String) : Except String Name := do
  let name ← match parseName text with
    | .ok name => pure name
    | .error e =>
      let name := (text.splitOn ".").foldl appendComponent Name.anonymous
      if name.hasMacroScopes then pure name else .error e
  unless toString name == text do throw s!"noncanonical atlas name: {text}"
  return name

/-- Read format 0 without importing Mathlib, and refuse a different pin,
an incomplete file, or a name that the atlas printer cannot round-trip. -/
def readPopulation (filename : System.FilePath) : IO Population := do
  let manifest ← IO.ofExcept <| Json.parse (← IO.FS.readFile "lake-manifest.json")
  let packages ← IO.ofExcept <| manifest.getObjValAs? (Array Json) "packages"
  let some mathlib := packages.find? (fun p =>
    (p.getObjValAs? String "name").toOption == some "mathlib")
    | throw (IO.userError "manifest has no Mathlib pin")
  let revision ← IO.ofExcept <| mathlib.getObjValAs? String "rev"
  let file ← IO.FS.Handle.mk filename .read
  let first ← IO.ofExcept <| Json.parse (← file.getLine)
  let header ← IO.ofExcept <| first.getObjVal? "atlas"
  require ((← IO.ofExcept <| header.getObjValAs? Nat "version") == 0) "atlas version"
  require ((← IO.ofExcept <| header.getObjValAs? String "lean") == versionString)
    "atlas Lean version differs from toolchain"
  require ((← IO.ofExcept <| header.getObjValAs? String "lean_commit") == githash)
    "atlas Lean commit differs from toolchain"
  require ((← IO.ofExcept <| header.getObjValAs? String "mathlib_commit") == revision)
    "atlas Mathlib revision differs from manifest"
  require ((← IO.ofExcept <| header.getObjValAs? String "mathlib") == "v" ++ versionString)
    "atlas Mathlib tag differs from toolchain"
  require ((← IO.ofExcept <| header.getObjValAs? (Array String) "imports") == #["Mathlib"])
    "atlas must cover import Mathlib"
  let expected ← IO.ofExcept <| header.getObjValAs? Nat "constants"
  require (expected > 0) "empty atlas population"
  let mut names : Array Name := #[]
  let mut mathlibCount : Nat := 0
  repeat
    let line ← file.getLine
    require (!line.isEmpty) "atlas has no footer"
    let record ← IO.ofExcept <| Json.parse line
    if let .ok footer := record.getObjVal? "end" then
      let count ← IO.ofExcept <| footer.getObjValAs? Nat "records"
      require (count == expected && names.size == expected) "atlas record count differs"
      require ((← file.getLine).isEmpty) "trailing data after atlas footer"
      break
    let text ← IO.ofExcept <| record.getObjValAs? String "name"
    let name ← IO.ofExcept <| parseAtlasName text
    names := names.push name
    let source ← IO.ofExcept <| record.getObjValAs? String "module"
    let moduleName ← IO.ofExcept <| parseName source
    if (`Mathlib).isPrefixOf moduleName then mathlibCount := mathlibCount + 1
  return { names, mathlib := mathlibCount }

end NamingAtlas
