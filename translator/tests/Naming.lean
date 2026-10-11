/-
File: translator/tests/Naming.lean
-/
import Lean2Agda.Main

open Lean Lean2Agda

namespace NamingTests

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def samples : Array Name := Id.run do
  let strings := #["", "a", "A", "0", "01", "1e3", "_", "__", "a_b", "a-b",
    ":", ".", "a.b", "a:b", "~", "~u", "~e", "~a", "~n0", "~srecord", "~x0~",
    "record", "Set", "Prop", "λ", "✝", "x✝", "_inaccessible", "_private", "_uniq",
    "_hyg", "_@", "a»b", "a b", "'x", "x'", "--", "{-", "-}", "\n", "\x00",
    "\t", "\r", "\\", "\"", "/", "𝒜", "é", "é"] ++ agdaReserved.toArray
  let mut names := #[Name.anonymous]
  for s in strings do
    names := names.push (.str .anonymous s)
    for t in strings do
      names := names.push (.str (.str .anonymous s) t)
    for i in [:4] do
      names := names.push (.num (.str .anonymous s) i)
      names := names.push (.str (.num .anonymous i) s)
  for i in [:256] do
    names := names.push (.str .anonymous (String.singleton (Char.ofNat i)))
  names := names.push (.num .anonymous (2^128))
  names := names.push (addMacroScope `Init `f 2)
  names := names.push (addMacroScope `Init `f 3)
  return names

def checkInjectivity (names : Array Name) : IO Nat := do
  let mut mapped : Std.HashMap String Name := {}
  for n in names do
    let ident := agdaIdent n
    if let some previous := mapped[ident]? then
      require (previous == n) s!"collision: {reprStr previous}, {reprStr n} -> {ident}"
    mapped := mapped.insert ident n
  return mapped.size

def checkExamples : IO Unit := do
  let cases : Array (Name × String) := #[
    (`Nat.gcd_self, "Nat:gcd~uself"),
    (.str `A "b:c", "A:b~x3a~c"), (.str `A "b.c", "A:b~x2e~c"),
    (`A.b.c, "A:b:c"), (.num `A 2, "A:~n2"), (.str `A "2", "A:~s2"),
    (mkPrivateNameCore `Init.Data.Nat.Gcd `Nat.helper,
      "~uprivate:Init:Data:Nat:Gcd:~n0:Nat:helper"),
    (`f._proof_1, "f:~uproof~u1"), (.num `_uniq 231, "~uuniq:~n231"),
    (.str .anonymous "x✝", "x~x271d~"), (`_inaccessible, "~uinaccessible"),
    (`record, "~srecord"), (.str .anonymous "~srecord", "~x7e~srecord"),
    (.str .anonymous "a b", "a~x20~b"), (.str .anonymous "λ", "~x3bb~"),
    (.str .anonymous "f'", "f~x27~"), (.str .anonymous "", "~e"),
    (.str .anonymous "~e", "~x7e~e"), (.anonymous, "~a"),
    (addMacroScope `Init `f 2, "f:~u~x40~:Init:~uhyg:~n2")]
  for (name, expected) in cases do
    require (agdaIdent name == expected) s!"encoding {reprStr name}: {agdaIdent name}"
  require (agdaModule `CC.Constructive `Mathlib.Data.Nat.Basic ==
    ["CC", "Constructive", "Mathlib", "Data", "Nat", "Basic"]) "module root"
  require (agdaModule .anonymous `A.B.C == ["A", "B", "C"]) "empty root"
  require (agdaModule `U .anonymous == ["U", "~a"]) "anonymous module"
  require (agdaModule `record (.num (.str .anonymous "a/b") 2) ==
    ["~srecord", "a~x2f~b", "~n2"]) "escaped module"
  require (!needsNameEscape `A.b && needsNameEscape `A.b_c &&
    needsNameEscape (.num `A 2) && needsNameEscape .anonymous) "escape statistics"

def checkReverseMap (names : Array Name) : IO Unit := do
  let reverse ← IO.ofExcept <| ReverseMap.build names
  for name in names do
    require (reverse.lookup (agdaIdent name) == some name) "reverse lookup"
    require ((nameFromJson (nameToJson name)).toOption == some name) "tagged-name round trip"
  require ((reverse.lookup "missing:~a").isNone) "unknown reverse lookup"
  let map : ModuleNames := { root := `CC.Constructive, source := `Init, reverse }
  let text := map.render
  let parsed ← IO.ofExcept <| ModuleNames.parse text
  require (parsed.render == text && parsed.root == map.root && parsed.source == map.source)
    "serialized reverse-map round trip"
  require (parsed.reverse.entries == reverse.entries) "parsed structured names changed"
  let reordered ← IO.ofExcept <| ReverseMap.build (names.reverse ++ names)
  require (({ map with reverse := reordered }).render == text) "order-dependent reverse map"

def checkMalformedReverseMaps : IO Unit := do
  for json in [Json.null, toJson "name", toJson #[Json.mkObj [("str", toJson "x"),
      ("num", toJson "0")]], toJson #[Json.mkObj [("num", toJson "01")]],
      toJson #[Json.mkObj [("num", toJson "-1")]],
      toJson #[Json.mkObj [("num", toJson (3 : Nat))]],
      toJson #[Json.mkObj [("other", toJson "x")]]] do
    require ((nameFromJson json).toOption.isNone) "invalid tagged name accepted"
  let reverse ← IO.ofExcept <| ReverseMap.build #[`Nat, `Bool]
  let map : ModuleNames := { root := `U, source := `Init.Prelude, reverse }
  let text := map.render
  for bad in ["", "{}\n", text.replace "\"version\":1" "\"version\":2",
    text.replace "\"records\":2" "\"records\":1",
    text.replace "\"agda\":\"Nat\"" "\"agda\":\"Wrong\"",
    text.replace "\"target\":[\"U\",\"Init\",\"Prelude\"]" "\"target\":[\"Elsewhere\"]",
    text ++ "{}\n", text ++ "\n", "\n".intercalate ((text.splitOn "\n").take 3) ++ "\n"] do
    require ((ModuleNames.parse bad).toOption.isNone) "invalid reverse map accepted"
  let rows := text.splitOn "\n" |>.toArray
  require ((ModuleNames.parse ("\n".intercalate
    [rows[0]!, rows[2]!, rows[1]!, rows[3]!] ++ "\n")).toOption.isNone)
    "unsorted reverse map accepted"
  require ((ModuleNames.parse ("\n".intercalate
    [rows[0]!, rows[1]!, rows[1]!, rows[3]!] ++ "\n")).toOption.isNone)
    "duplicate reverse-map record accepted"
  let empty : ModuleNames := { map with reverse := ← IO.ofExcept (ReverseMap.build #[]) }
  require ((ModuleNames.parse empty.render).toOption.isSome) "empty reverse map rejected"

def checkModuleGrouping : IO Unit := do
  let env ← importEnvironment #[`Init.Data.Nat.Gcd]
  let closure ← IO.ofExcept <| dependencyClosure env #[``Nat.gcd_self]
  let maps ← IO.ofExcept <| moduleNameMaps `U closure
  let mut count : Nat := 0
  for map in maps do
    for entry in map.reverse.entries do
      let some declaration := closure.declarations.find? (·.name == entry.leanName)
      | throw (IO.userError "sidecar contains a name outside closure")
      require (declaration.sourceModule == some map.source) "wrong sidecar ownership"
      count := count + 1
  require (count == closure.size) "sidecars omit closure declarations"
  let reversed : Closure := { closure with groups := closure.groups.reverse.map Array.reverse }
  let again ← IO.ofExcept <| moduleNameMaps `U reversed
  require (maps.map ModuleNames.render == again.map ModuleNames.render) "group-order-dependent sidecars"
  let localDecl : Lean2Agda.Declaration := {
    name := `localDecl
    info := default
    sourceModule := none
    dependencies := #[] }
  require ((moduleNameMaps `U { roots := #[`localDecl], groups := #[#[localDecl]] }).toOption.isNone)
    "unowned declaration accepted for emission"

/-- Agda declares and uses every sample identifier, including every byte value.
The test harness supplies a temporary directory and checks the generated file. -/
def writeLexicalFixture (dir : System.FilePath) : IO Unit := do
  let mut seen : Std.HashSet String := {}
  let mut lines := #["-- File: NamingLexical.agda",
    "{-# OPTIONS --safe --cubical-compatible #-}", "module NamingLexical where"]
  for n in samples do
    let ident := agdaIdent n
    if seen.contains ident then continue
    seen := seen.insert ident
    lines := lines.push s!"{ident} : Set₁"
    lines := lines.push s!"{ident} = Set"
    lines := lines.push s!"use:{ident} : Set₁"
    lines := lines.push s!"use:{ident} = {ident}"
  IO.FS.writeFile (dir / "NamingLexical.agda") ("\n".intercalate lines.toList ++ "\n")
  let parts := agdaModule `U (.num (.str `record "a/b") 2)
  let moduleFile := parts.foldl (fun p s => p / s) dir |>.addExtension "agda"
  IO.FS.createDirAll moduleFile.parent.get!
  let qualified := ".".intercalate parts
  let options := "{-# OPTIONS --safe --cubical-compatible #-}\n"
  IO.FS.writeFile moduleFile
    ("-- File: generated module lexical fixture\n" ++ options ++
      s!"module {qualified} where\nvalue : Set₁\nvalue = Set\n")
  IO.FS.writeFile (dir / "NamingImport.agda")
    ("-- File: NamingImport.agda\n" ++ options ++
      s!"module NamingImport where\nimport {qualified}\nvalue : Set₁\nvalue = {qualified}.value\n")

def run : IO Unit := do
  checkExamples
  checkReverseMap samples
  checkMalformedReverseMaps
  checkModuleGrouping
  let count ← checkInjectivity samples
  let env ← importEnvironment #[`Init]
  let names := env.constants.toList.toArray.filterMap fun (n, _) =>
    if (env.getModuleIdxFor? n).isSome then some n else none
  let initCount ← checkInjectivity names
  checkReverseMap names
  let moduleNames := env.header.moduleNames
  let mut paths : Std.HashMap (List String) Name := {}
  for n in moduleNames do
    let p := agdaModule `U n
    require (!paths.contains p) s!"module collision: {n}"
    paths := paths.insert p n
  if let some dir ← IO.getEnv "NAMING_AGDA_TEST_DIR" then writeLexicalFixture dir
  IO.println s!"naming checks: {count} distinct samples, {initCount} Init constants, {paths.size} modules"

end NamingTests

#eval NamingTests.run
