/-
File: translator/Lean2Agda/Core/CommandLine.lean
-/
import Lean2Agda.Core.Types
import Lean.Syntax

namespace Lean2Agda

open Lean

def usage : String :=
  "usage: lean2agda [--profile U] [--out DIR] [--stats] MODULE... [-- DECL...]"

structure Args where
  profile : String := "U"
  out : Option System.FilePath := none
  stats : Bool := false
  help : Bool := false
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
  | "--out" :: dir :: rest => do
    if dir.isEmpty || dir.startsWith "--" then throw "--out needs a directory"
    parseArgsAux { args with out := some dir } rest
  | "--stats" :: rest => parseArgsAux { args with stats := true } rest
  | "--help" :: rest => parseArgsAux { args with help := true } rest
  | "--profile" :: [] => throw "--profile needs a value"
  | "--out" :: [] => throw "--out needs a directory"
  | arg :: rest => do
    if arg.startsWith "-" then throw s!"unknown option {arg}"
    let name ← parseName arg
    parseArgsAux { args with modules := args.modules.push name } rest

def parseArgs (argv : List String) : Except String Args := do
  let args ← parseArgsAux {} argv
  if args.modules.isEmpty && !args.help then throw "at least one module is required"
  return args

end Lean2Agda
