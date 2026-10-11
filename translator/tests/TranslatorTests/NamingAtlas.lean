/-
File: translator/tests/TranslatorTests/NamingAtlas.lean
-/
import TranslatorTests.AtlasNames

open Lean Lean2Agda

namespace NamingAtlas

def check (population : Population) : IO Unit := do
  let start ← IO.monoMsNow
  let identifiers ← IO.lazyPure fun _ => population.names.map agdaIdent
  let mappingMs := (← IO.monoMsNow) - start
  let mut seen : Std.HashMap String Name := {}
  let mut escaped : Nat := 0
  let mut bytes : Nat := 0
  for i in [:population.names.size] do
    let name := population.names[i]!
    let ident := identifiers[i]!
    if let some previous := seen[ident]? then
      if previous == name then throw (IO.userError s!"duplicate atlas name: {name}")
      else throw (IO.userError s!"collision: {reprStr previous}, {reprStr name} -> {ident}")
    seen := seen.insert ident name
    if needsNameEscape name then escaped := escaped + 1
    bytes := bytes + ident.utf8ByteSize
  let reversed ← IO.lazyPure fun _ => population.names.reverse.map agdaIdent
  require (identifiers == reversed.reverse) "mapping depends on input order"
  IO.println <| (Json.mkObj [
    ("constants", toJson seen.size), ("mathlib_constants", toJson population.mathlib),
    ("mapping_ms", toJson mappingMs), ("escaped", toJson escaped),
    ("collision_indices", toJson (0 : Nat)), ("identifier_bytes", toJson bytes)]).compress

end NamingAtlas

def main (args : List String) : IO UInt32 := do
  let [filename] := args
    | IO.eprintln "usage: lake exe naming-check-atlas FILE.ndjson"; return 2
  try
    NamingAtlas.check (← NamingAtlas.readPopulation filename)
    return 0
  catch e =>
    IO.eprintln s!"naming-check-atlas: {e}"
    return 1
