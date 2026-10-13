/-
File: translator/Lean2Agda/Core/Scaffold.lean
-/
import Lean2Agda.Core.Inductive
import Lean2Agda.Core.Share

/-!
# The profile U scaffold

One Agda module per closure, the test of the printer and the emitters
until issues M2-5 to M2-7 emit recursors, definitions and quotients.  It
declares every constant of the closure with its printed type.  Each
constant is a postulate, except the following:

+  the inductive types, each block of them one declaration
   (`Inductive.lean`): a record for each structure-like type and a data
   type for each other, `Nat` among them, bound to `BUILTIN NATURAL` so
   that literals print as decimals;
+  `String`, a postulate bound to `BUILTIN STRING`, which needs one, and
   so its constructor and recursor are postulates too;
+  the type abbreviations, definitions with their printed values, since a
   type can be well formed only through one (`outParam`, `DecidableEq`);
+  the roots that have values, and the sharing pass's auxiliary
   definitions, definitions with their printed values.

Agda parses and scope-checks the whole module.  It type-checks each
declaration that needs no definitional unfolding beyond these
definitions; `docs/translator/printing.md`
says which do not, and why.
-/

namespace Lean2Agda

open Lean

def profileUOptions : String := "{-# OPTIONS --type-in-type #-}"

/-- One declaration of a module: the identifiers it declares, those its
text refers to, and its text.  A definition also carries its fallback, the
references and text of a postulate of its type. -/
structure ScaffoldItem where
  provides : Array String
  references : Array String
  text : String
  fallback : Option (Array String × String) := none
  deriving Inhabited

structure Scaffold where
  path : List String
  items : Array ScaffoldItem
  counts : PrintCounts
  deriving Inhabited

def Scaffold.moduleName (s : Scaffold) : String := ".".intercalate s.path

def Scaffold.filePath (s : Scaffold) (dir : System.FilePath) : System.FilePath :=
  s.path.foldl (· / ·) dir |>.addExtension "agda"

/-- The module's text: the profile's options, a comment, the header, and
the declarations, separated by blank lines. -/
def Scaffold.render (s : Scaffold) (comment : String) : String :=
  s.items.foldl (fun out item => out ++ "\n" ++ item.text)
    s!"{profileUOptions}\n-- {comment}\nmodule {s.moduleName} where\n"

/-- A type abbreviation: a definition whose type ends in a sort and whose
value, under its leading lambdas, is a Pi type, a sort, or one of those
lambdas' variables. -/
def isTypeAbbreviation : ConstantInfo → Bool
  | .defnInfo v => endsInSort v.type && former v.value
  | _ => false
where
  endsInSort : Expr → Bool
    | .forallE _ _ b _ | .mdata _ b => endsInSort b
    | .sort _ => true
    | _ => false
  former : Expr → Bool
    | .lam _ _ b _ | .mdata _ b => former b
    | .forallE .. | .sort _ | .bvar _ => true
    | _ => false

/-- The auxiliary definitions reachable from `starts` through the types
and values of auxiliary definitions. -/
def reachableAuxiliaries (auxiliaries : Std.HashMap Name Declaration) (starts : Array Expr) :
    Std.HashSet Name := Id.run do
  let mut queue := starts.foldl (fun q e =>
    q ++ (expressionDependencies e).filter auxiliaries.contains) #[]
  let mut seen : Std.HashSet Name := {}
  while h : 0 < queue.size do
    let n := queue.back
    queue := queue.pop
    unless seen.contains n do
      seen := seen.insert n
      for e in constantExprs auxiliaries[n]!.info do
        queue := queue ++ (expressionDependencies e).filter auxiliaries.contains
  return seen

/-- Order items so that each follows every item providing an identifier it
refers to, keeping the closure's order otherwise.  The closure orders its
groups, but inside a group (an inductive type with its constructors and
recursor) only the printed references decide. -/
partial def orderItems (items : Array ScaffoldItem) : Except String (Array ScaffoldItem) := do
  let provider : Std.HashMap String Nat := (List.range items.size).foldl (fun m i =>
    items[i]!.provides.foldl (fun m n => m.insert n i) m) {}
  for item in items do
    for r in item.references do
      unless provider.contains r do
        throw s!"the scaffold refers to {r}, which nothing declares"
  let rec visit (i : Nat) (state : Std.HashSet Nat × Array Nat × Std.HashSet Nat) :
      Except String (Std.HashSet Nat × Array Nat × Std.HashSet Nat) := do
    let (done, order, active) := state
    if done.contains i then return state
    if active.contains i then
      throw s!"a cycle among the scaffold's declarations through {items[i]!.provides}"
    let mut state := (done, order, active.insert i)
    for r in items[i]!.references do
      if let some j := provider[r]? then
        unless j == i do state ← visit j state
    let (done, order, active) := state
    return (done.insert i, order.push i, active.erase i)
  let mut state := ({}, #[], {})
  for i in [:items.size] do state ← visit i state
  return state.2.1.map (items[·]!)

/-- Postulate every definition whose printed value refers to itself or to
a definition that refers back to it.  Lean's kernel accepts such a cycle
only among unsafe definitions, such as the `_unsafe_rec` companions of
mutual `partial` definitions, and Agda could check none of them. -/
def breakCycles (items : Array ScaffoldItem) : Array ScaffoldItem := Id.run do
  let provider : Std.HashMap String Nat := (List.range items.size).foldl (fun m i =>
    items[i]!.provides.foldl (fun m n => m.insert n i) m) {}
  let successors (i : Nat) : List Nat := items[i]!.references.toList.filterMap (provider[·]?)
  let mut result := items
  for group in SCC.scc (List.range items.size) successors do
    let cyclic := match group with
      | [i] => (successors i).contains i
      | _ => true
    if cyclic then
      for i in group do
        if let some (references, text) := items[i]!.fallback then
          result := result.set! i { items[i]! with references, text, fallback := none }
  return result

def postulateItem (p : Printer) (decl : Declaration) : Except String (ScaffoldItem × PrintCounts) := do
  let (t, counts) ← p.type decl.info.type
  let name := agdaIdent decl.name
  return ({ provides := #[name], references := t.constants,
            text := s!"postulate {name} : {t.render}\n" }, counts)

def definitionItem (p : Printer) (decl : Declaration) : Except String (ScaffoldItem × PrintCounts) := do
  let some value := decl.info.value? (allowOpaque := true) | postulateItem p decl
  let (t, c₁) ← p.type decl.info.type
  let (clause, c₂) ← p.clause decl.info.type value
  let name := agdaIdent decl.name
  let references := clause.body.constants.foldl (fun acc n => if acc.contains n then acc else acc.push n)
    t.constants
  return ({ provides := #[name], references,
            text := s!"{name} : {t.render}\n{clause.render name}\n",
            fallback := some (t.constants, s!"postulate {name} : {t.render}\n") }, c₁.add c₂)

/-- `String`, a postulate, since `BUILTIN STRING` binds Agda's string
literals to a postulated type, whether or not it is a root. -/
def stringItem (p : Printer) (decl : Declaration) : Except String (ScaffoldItem × PrintCounts) := do
  let (item, counts) ← postulateItem p decl
  return ({ item with text := item.text ++ s!"\{-# BUILTIN STRING {agdaIdent ``String} #-}\n" }, counts)

/-- A block of inductive types as one item, declaring its types and
constructors. -/
def inductiveItem (p : Printer) (byName : Std.HashMap Name Declaration) (v : InductiveVal) :
    Except String (ScaffoldItem × PrintCounts) := do
  let d ← inductiveDecl p (← blockMembers (fun n => byName[n]?.map (·.info)) v)
  return ({ provides := d.provides, references := d.references,
            text := "\n".intercalate d.lines.toList ++ "\n" }, d.counts)

/-- Whether the scaffold gives a declaration its value: an auxiliary
definition, a type abbreviation, or a root. -/
def emitsValue (_env : Environment) (closure : Closure) (decl : Declaration) : Bool :=
  decl.auxiliary || isTypeAbbreviation decl.info || closure.roots.contains decl.name

/-- The scaffold's item for one declaration, or none for one that its
inductive block's item declares: a constructor, or a type of a mutual
block other than its first, which the emitter refuses for now. -/
def scaffoldItem (p : Printer) (closure : Closure) (byName : Std.HashMap Name Declaration)
    (decl : Declaration) : Except String (Option (ScaffoldItem × PrintCounts)) := do
  match decl.info with
  | .inductInfo v =>
    if v.name == ``String then return some (← stringItem p decl)
    if v.all.head? != some v.name then return none
    return some (← inductiveItem p byName v)
  | .ctorInfo c =>
    if c.induct == ``String then return some (← postulateItem p decl)
    return none
  | _ =>
    if emitsValue p.env closure decl then return some (← definitionItem p decl)
    return some (← postulateItem p decl)

/-- The scaffold of a closure that the sharing pass has already rewritten.
Its path is the one its names sidecar has, from the source module of the
closure's first root.  An auxiliary definition appears when something the
scaffold prints uses it. -/
def scaffold (env : Environment) (root : Root) (closure : Closure) : Except String Scaffold := do
  let env ← addAuxiliaries env closure
  let some first := closure.roots[0]? | throw "the closure has no roots"
  let decls := closure.declarations
  let some owner := decls.find? (·.name == first) | throw s!"root {first} missing"
  let some module := owner.sourceModule | throw s!"no source module assigned to {first}"
  let byName : Std.HashMap Name Declaration := decls.foldl (fun m d => m.insert d.name d) {}
  let auxiliaries : Std.HashMap Name Declaration :=
    decls.foldl (fun m d => if d.auxiliary then m.insert d.name d else m) {}
  let needed := reachableAuxiliaries auxiliaries <| decls.foldl (fun acc d =>
    if d.auxiliary then acc
    else if emitsValue env closure d then acc ++ constantExprs d.info
    else acc.push d.info.type) #[]
  let p : Printer := { env }
  let mut counts : PrintCounts := {}
  let mut items := #[]
  for decl in decls do
    unless decl.auxiliary && !needed.contains decl.name do
      if let some (item, c) ← scaffoldItem p closure byName decl then
        items := items.push item
        counts := counts.add c
  return { path := agdaModule root module, items := ← orderItems (breakCycles items), counts }

end Lean2Agda
