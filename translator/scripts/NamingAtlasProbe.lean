/-
File: translator/scripts/NamingAtlasProbe.lean
-/
import TranslatorTests.AtlasNames

open Lean Lean2Agda

/-- The atlas text representation is adequate for this pin, although it is
not lossless on arbitrary Name values.  This optional probe checks against
the original structured names and needs Mathlib's prebuilt cache. -/
def main : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules #[{ module := `Mathlib }] {} (loadExts := true)
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then continue
    unless (NamingAtlas.parseAtlasName (toString name)).toOption == some name do
      throw (IO.userError s!"atlas name loses structure: {reprStr name}")
    count := count + 1
  IO.println s!"atlas printed-name round trips: {count} imported Mathlib-environment constants"
