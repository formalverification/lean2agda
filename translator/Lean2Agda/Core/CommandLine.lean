/-
File: translator/Lean2Agda/Core/CommandLine.lean
-/
import Lean2Agda.Core.Types
import Lean2Agda.Core.Naming
import Lean2Agda.Core.Share
import Lean2Agda.Core.Modules
import Lean2Agda.Core.Arithmetic
import Lean.Syntax

namespace Lean2Agda

open Lean

def usage : String :=
  "usage: lean2agda [--profile U] [--root NAME] [--out DIR] [--share N] [--split BYTES]\n" ++
  "                 [--arithmetic agda|lean] [--stats] MODULE... [-- DECL...]\n" ++
  "       lean2agda --help | --version"

structure Args where
  profile : String := "U"
  root : Root := `U
  out : Option System.FilePath := none
  /-- The sharing pass's threshold; zero turns the pass off. -/
  share : Nat := defaultShareThreshold
  /-- The bytes of printed Agda past which a module is split into parts;
  zero never splits. -/
  split : Nat := defaultSplitThreshold
  /-- Which definitions of Lean's accelerated operations on `Nat` the
  scaffold emits: the operation table's, or Lean's compiled ones. -/
  arithmetic : Arithmetic := .agda
  stats : Bool := false
  help : Bool := false
  version : Bool := false
  modules : Array Name := #[]
  declarations : Array Name := #[]
  deriving Inhabited

/-- Use Lean's name-literal decoder, preserving quoted, numeric, and
private name components instead of splitting the string on dots. -/
def parseName (text : String) : Except String Name :=
  match Syntax.decodeNameLit ("`" ++ text) with
  | some n => if n == .anonymous then .error "empty name" else .ok n
  | none => .error s!"invalid Lean name: {text}"

private def parseArgsAux (args : Args) : List String → Except String Args
  | [] => pure args
  | "--" :: rest => do
    let declarations ← rest.toArray.mapM parseName
    return { args with declarations }
  | "--profile" :: profile :: rest => do
    unless profile == "U" do throw s!"unsupported profile {profile}; only U is available"
    parseArgsAux { args with profile } rest
  | "--root" :: root :: rest => do
    if root.isEmpty || root.startsWith "--" then throw "--root needs a Lean name"
    let root ← parseName root
    parseArgsAux { args with root } rest
  | "--out" :: dir :: rest => do
    if dir.isEmpty || dir.startsWith "--" then throw "--out needs a directory"
    parseArgsAux { args with out := some dir } rest
  | "--share" :: n :: rest => do
    let some share := n.toNat? | throw "--share needs a natural number"
    parseArgsAux { args with share } rest
  | "--split" :: n :: rest => do
    let some split := n.toNat? | throw "--split needs a natural number"
    parseArgsAux { args with split } rest
  | "--arithmetic" :: value :: rest => do
    let some arithmetic := Arithmetic.parse? value | throw "--arithmetic needs agda or lean"
    parseArgsAux { args with arithmetic } rest
  | "--stats" :: rest => parseArgsAux { args with stats := true } rest
  | "--help" :: rest => parseArgsAux { args with help := true } rest
  | "--version" :: rest => parseArgsAux { args with version := true } rest
  | "--profile" :: [] => throw "--profile needs a value"
  | "--root" :: [] => throw "--root needs a Lean name"
  | "--out" :: [] => throw "--out needs a directory"
  | "--share" :: [] => throw "--share needs a natural number"
  | "--split" :: [] => throw "--split needs a natural number"
  | "--arithmetic" :: [] => throw "--arithmetic needs agda or lean"
  | arg :: rest => do
    if arg.startsWith "-" then throw s!"unknown option {arg}"
    let name ← parseName arg
    parseArgsAux { args with modules := args.modules.push name } rest

def parseArgs (argv : List String) : Except String Args := do
  let args ← parseArgsAux {} argv
  if args.modules.isEmpty && !args.help && !args.version then throw "at least one module is required"
  return args

end Lean2Agda
