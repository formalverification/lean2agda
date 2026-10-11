/-
File: translator/tests/NamingAtlasFixture.lean
-/
import TranslatorTests.NamingAtlas

open Lean

#eval show IO Unit from do
  let some dir ← IO.getEnv "NAMING_AGDA_TEST_DIR"
    | throw (IO.userError "NAMING_AGDA_TEST_DIR is required")
  let manifest ← IO.ofExcept <| Json.parse (← IO.FS.readFile "lake-manifest.json")
  let packages ← IO.ofExcept <| manifest.getObjValAs? (Array Json) "packages"
  let some mathlib := packages.find? (fun p =>
    (p.getObjValAs? String "name").toOption == some "mathlib")
    | throw (IO.userError "missing Mathlib pin")
  let rev ← IO.ofExcept <| mathlib.getObjValAs? String "rev"
  let header := Json.mkObj [("atlas", Json.mkObj [
    ("version", toJson (0 : Nat)), ("lean", toJson versionString),
    ("lean_commit", toJson githash), ("mathlib", toJson ("v" ++ versionString)),
    ("mathlib_commit", toJson rev), ("imports", toJson #["Mathlib"]),
    ("constants", toJson (5 : Nat))])]
  let names : Array Name := #[`A.b, .str `A "b.c", .str `A "2", .num `A 2,
    addMacroScope `Init `f 3]
  let rows := names.map fun name =>
    (Json.mkObj [("name", toJson (toString name)), ("module", toJson "Mathlib.Fixture")]).compress
  let footer := (Json.mkObj [("end", Json.mkObj [("records", toJson names.size)])]).compress
  let body := "\n".intercalate rows.toList ++ "\n"
  let text := header.compress ++ "\n" ++ body ++ footer ++ "\n"
  let filename (stem : String) := System.FilePath.mk dir / s!"atlas-{stem}.ndjson"
  IO.FS.writeFile (filename "valid") text
  IO.FS.writeFile (filename "truncated") (header.compress ++ "\n" ++ body)
  IO.FS.writeFile (filename "count") (header.compress ++ "\n" ++ rows[0]! ++ "\n" ++ footer ++ "\n")
  IO.FS.writeFile (filename "duplicate")
    (header.compress ++ "\n" ++ rows[0]! ++ "\n" ++ rows[0]! ++ "\n" ++
      "\n".intercalate (rows.toList.drop 2) ++ "\n" ++ footer ++ "\n")
  IO.FS.writeFile (filename "trailing") (text ++ rows[0]! ++ "\n")
  IO.FS.writeFile (filename "pin") (text.replace githash "wrong-commit")
  IO.FS.writeFile (filename "malformed") "not json\n"
  unless (NamingAtlas.parseAtlasName "f._@.Init._hyg.3").toOption ==
      some (addMacroScope `Init `f 3) do throw (IO.userError "hygienic atlas parser")
  unless (NamingAtlas.parseAtlasName "A..B").toOption.isNone do
    throw (IO.userError "malformed atlas name accepted")
