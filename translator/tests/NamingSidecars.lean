/-
File: translator/tests/NamingSidecars.lean
-/
import Lean2Agda.Main

open Lean Lean2Agda

/- Read the actual files emitted by the command-line executable, then
resolve every identifier back to its original name and source module. -/
#eval show IO Unit from do
  let some dir ← IO.getEnv "NAMING_OUTPUT_DIR"
    | throw (IO.userError "NAMING_OUTPUT_DIR is required")
  let root ← IO.ofExcept <| parseName ((← IO.getEnv "NAMING_ROOT").getD "U")
  let env ← importEnvironment #[`TranslatorTests.Input.Consumer]
  let closure ← IO.ofExcept <| dependencyClosure env #[`Fixtures.selected]
  let maps ← IO.ofExcept <| moduleNameMaps root closure
  for expected in maps do
    let text ← IO.FS.readFile (expected.sidecarPath dir)
    let actual ← IO.ofExcept <| ModuleNames.parse text
    unless actual.source == expected.source && actual.root == root && text == expected.render do
      throw (IO.userError "emitted sidecar differs from source module map")
    for entry in expected.reverse.entries do
      let recovered := actual.reverse.lookup entry.agdaName == some entry.leanName
      unless recovered do throw (IO.userError "emitted reverse lookup differs")
  unless maps.size > 1 && closure.declarations.any (isPrivateName ∘ (·.name)) do
    throw (IO.userError "sidecar test needs private and cross-module names")
  IO.println s!"emitted sidecars: {maps.size} modules, {closure.size} original names recovered"
