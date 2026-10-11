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
  let count ← checkInjectivity samples
  let env ← importEnvironment #[`Init]
  let names := env.constants.toList.toArray.filterMap fun (n, _) =>
    if (env.getModuleIdxFor? n).isSome then some n else none
  let initCount ← checkInjectivity names
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
