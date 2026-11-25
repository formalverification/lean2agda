/-
File: translator/Lean2Agda/Core/ReverseMap.lean
-/
import Lean2Agda.Core.Naming
import Lean2Agda.Core.Types
import Lean.Data.Json

namespace Lean2Agda

open Lean

/-- Root-to-leaf tagged components.  Decimal strings preserve arbitrary
natural numbers in consumers whose JSON numbers have limited precision.
With `instances`, the name is a key of a closure of instances
(`Specialize.lean`), and the component that holds an instance's pattern
is tagged `levels` and carries the letters alone: the components before
it are the Lean constant's, and the letters say which of its split level
parameters are zero. -/
def nameToJson (name : Name) (instances : Bool := false) : Json := .arr (components name)
where
  components : Name → Array Json
    | .anonymous => #[]
    | .str p s =>
      if instances && isPatternComponent s then
        components p |>.push (Json.mkObj [("levels", .str (String.ofList (s.toList.drop 1)))])
      else components p |>.push (Json.mkObj [("str", .str s)])
    | .num p n => components p |>.push (Json.mkObj [("num", .str (toString n))])

def nameFromJson (json : Json) (instances : Bool := false) : Except String Name := do
  let components ← json.getArr?
  components.foldlM (fun baseName component => do
    let object ← component.getObj?
    unless object.size == 1 do throw "name component must have exactly one tag"
    match component.getObjVal? "str" with
    | .ok value =>
      let s ← value.getStr?
      if instances && isPatternComponent s then throw "a string component of the form a pattern has"
      return .str baseName s
    | .error _ =>
      if instances then
        if let .ok letters := component.getObjValAs? String "levels" then
          unless isPatternComponent ("#" ++ letters) do throw "invalid pattern letters"
          return .str baseName ("#" ++ letters)
      let text ← component.getObjValAs? String "num"
      let some n := text.toNat? | throw "invalid numeric name component"
      unless toString n == text do throw "noncanonical numeric name component"
      return .num baseName n) .anonymous

structure ReverseEntry where
  agdaName : String
  leanName : Name
  deriving BEq, Inhabited

structure ReverseMap where
  entries : Array ReverseEntry
  byIdent : Std.HashMap String Name

/-- Deduplicate identical inputs, refuse collisions, and sort independently
of the environment's hash order or the closure's traversal order.  `ident`
is `agdaIdent`, or `instanceIdent` for the keys of a closure of
instances. -/
def ReverseMap.build (names : Array Name) (ident : Name → String := agdaIdent) : Except String ReverseMap := do
  let mut entries : Array ReverseEntry := #[]
  let mut byIdent : Std.HashMap String Name := {}
  for name in names do
    let ident := ident name
    if let some previous := byIdent[ident]? then
      unless previous == name do throw s!"identifier collision at {ident}"
    else
      entries := entries.push { agdaName := ident, leanName := name }
      byIdent := byIdent.insert ident name
  return { entries := entries.qsort (·.agdaName < ·.agdaName), byIdent }

def ReverseMap.lookup (map : ReverseMap) (identifier : String) : Option Name :=
  map.byIdent[identifier]?

/-- One module's reverse map.  With `instances` its names are the keys of
a closure of instances, and its sidecar is naming version 2: a key's
pattern is a `levels` component, and an identifier is `instanceIdent`'s.
Without, it is version 1, as before the specialization. -/
structure ModuleNames where
  root : Root
  source : ModuleName
  reverse : ReverseMap
  instances : Bool := false

def ModuleNames.version (map : ModuleNames) : Nat := if map.instances then 2 else 1

def ModuleNames.path (map : ModuleNames) : List String := agdaModule map.root map.source

def ModuleNames.sidecarPath (map : ModuleNames) (dir : System.FilePath) : System.FilePath :=
  map.path.foldl (fun p s => p / s) dir |>.addExtension "names.ndjson"

def ModuleNames.render (map : ModuleNames) : String :=
  let header := Json.mkObj [("naming", Json.mkObj [
    ("version", toJson map.version), ("root", nameToJson map.root),
    ("source", nameToJson map.source), ("target", toJson map.path)])]
  let records := map.reverse.entries.map fun entry =>
    (Json.mkObj [("agda", .str entry.agdaName), ("lean", nameToJson entry.leanName map.instances)]).compress
  let footer := Json.mkObj [("end", Json.mkObj [("records", toJson records.size)])]
  "\n".intercalate (header.compress :: records.toList ++ [footer.compress]) ++ "\n"

/-- Check all redundant fields; parsed data must describe the same naming
function and canonical record order as data constructed in the core. -/
def ModuleNames.parse (text : String) : Except String ModuleNames := do
  let lines := text.splitOn "\n"
  let lines := (if lines.getLast? == some "" then lines.dropLast else lines).toArray
  unless lines.size ≥ 2 do throw "reverse map needs a header and footer"
  let header ← Json.parse lines[0]!
  let naming ← header.getObjVal? "naming"
  let version ← naming.getObjValAs? Nat "version"
  unless version == 1 || version == 2 do throw "unsupported naming version"
  let instances := version == 2
  let identOf : Name → String := if instances then instanceIdent else agdaIdent
  let root ← nameFromJson (← naming.getObjVal? "root")
  let source ← nameFromJson (← naming.getObjVal? "source")
  let target ← naming.getObjValAs? (List String) "target"
  unless target == agdaModule root source do throw "reverse map target differs from module path"
  let mut names : Array Name := #[]
  let mut previous : Option String := none
  for line in lines.extract 1 (lines.size - 1) do
    let record ← Json.parse line
    let ident ← record.getObjValAs? String "agda"
    let name ← nameFromJson (← record.getObjVal? "lean") instances
    unless ident == identOf name do throw "reverse map identifier differs from Lean name"
    if let some before := previous then
      unless before < ident do throw "reverse map records are unsorted or duplicated"
    previous := some ident
    names := names.push name
  let footer ← Json.parse lines[lines.size - 1]!
  let ending ← footer.getObjVal? "end"
  unless (← ending.getObjValAs? Nat "records") == names.size do
    throw "reverse map footer count differs"
  return { root, source, reverse := ← ReverseMap.build names identOf, instances }

/-- One sidecar per source module in a closure.  A future pass that creates
local declarations must assign their source modules before calling this.
With `instances` the closure is one of instances, whose declarations'
names are keys. -/
def moduleNameMaps (root : Root) (closure : Closure) (instances : Bool := false) :
    Except String (Array ModuleNames) := do
  let identOf : Name → String := if instances then instanceIdent else agdaIdent
  let mut modules : Std.HashMap Name (Array Name) := {}
  for declaration in closure.declarations do
    let some source := declaration.sourceModule
      | throw s!"no source module assigned to {declaration.name}"
    modules := modules.insert source ((modules[source]?.getD #[]).push declaration.name)
  let maps ← modules.toArray.mapM fun (source, names) => do
    return { root, source, reverse := ← ReverseMap.build names identOf, instances : ModuleNames }
  return maps.qsort (fun a b => ".".intercalate a.path < ".".intercalate b.path)

end Lean2Agda
