/-
File: translator/Lean2Agda/Core/Scaffold.lean
-/
import Lean2Agda.Core.Inductive
import Lean2Agda.Core.Share

/-!
# The profile U scaffold

One Agda module per closure, the test of the printer and the emitters
until issues M2-5 and M2-7 emit recursors and quotients.  It declares
every constant of the closure that it does not refuse, by kind, as
follows:

+  the inductive types, each block of them one declaration
   (`Inductive.lean`): a record for each structure-like type and a data
   type for each other, `Nat` among them, bound to `BUILTIN NATURAL` so
   that literals print as decimals;
+  `String`, a postulate bound to `BUILTIN STRING`, which needs one, and
   so its constructor and recursor are postulates too;
+  a definition (`defnInfo`, `partial` companions and the projection
   functions of records included) as a transparent definition with its
   printed clause, since Lean's terms rely on unfolding it; the sharing
   pass's auxiliary definitions are such definitions too;
+  a theorem (`thmInfo`) inside an `opaque` block of its own, so that
   Agda's conversion checking never unfolds a proof; when a dependent
   needs one to unfold, `scripts/python/scaffold_check.py` re-emits that
   theorem transparently and counts it (the fallback);
+  one of Lean's opaque constants (`opaqueInfo`, a `partial` definition
   among them) inside an `opaque` block with its value, which is what
   Lean's kernel has: a value it never unfolds;
+  an axiom, a recursor and a quotient primitive as a postulate.

It refuses `sorryAx`, every `unsafe` declaration, and whatever depends on
one of those, and names each with its reason (`Scaffold.refused`,
written to `refusals.txt`).  A definition whose printed value refers to
itself, or to a definition that refers back to it, is postulated instead
(`breakCycles`).

Agda parses and scope-checks the whole module, and `scaffold_check.py`
type-checks it declaration by declaration; `docs/translator/printing.md`
says what it refuses, and why.
-/

namespace Lean2Agda

open Lean

def profileUOptions : String := "{-# OPTIONS --type-in-type #-}"

/-- One declaration of a module: the identifiers it declares, those its
text refers to, and its text.  A declaration with a value also carries
its fallback, the references and text of a postulate of its type. -/
structure ScaffoldItem where
  provides : Array String
  references : Array String
  text : String
  fallback : Option (Array String × String) := none
  deriving Inhabited

/-! ## Refusals -/

/-- What a refusal bottoms out at: the axiom `sorryAx`, a proof left to
`sorry`, or an `unsafe` declaration, exempt from Lean's kernel. -/
inductive RefusalRoot where
  | sorryAx
  | unsafeDecl
  deriving BEq, Repr, Inhabited

/-- A declaration the scaffold leaves out: its name and kind, the
declaration at the root of the refusal (itself, or one it depends on),
why that one is refused, and the direct dependency through which the
refusal arrived, when it is not the declaration's own. -/
structure Refusal where
  name : Name
  kind : Kind
  root : Name
  cause : RefusalRoot
  via : Option Name := none
  deriving Inhabited

/-- The reason, as `refusals.txt` prints it. -/
def Refusal.reason (r : Refusal) : String :=
  match r.via with
  | none => match r.cause with
    | .sorryAx => "sorryAx: a proof left to sorry"
    | .unsafeDecl => "unsafe: exempt from Lean's kernel"
  | some d => if d == r.root then s!"depends on {r.root}" else s!"depends on {d}, and through it on {r.root}"

/-- The declarations to refuse: `sorryAx`, every `unsafe` declaration,
and whatever depends on a refused one, which the pass reaches by
revisiting the closure until nothing changes. -/
def refuseDeclarations (decls : Array Declaration) : Std.HashMap Name Refusal := Id.run do
  let mut refused : Std.HashMap Name Refusal := {}
  let mut changed := true
  while changed do
    changed := false
    for d in decls do
      unless refused.contains d.name do
        let own : Option RefusalRoot :=
          if d.name == ``sorryAx then some .sorryAx
          else if d.info.isUnsafe then some .unsafeDecl
          else none
        let refusal : Option Refusal := match own with
          | some cause => some { name := d.name, kind := d.kind, root := d.name, cause }
          | none => (d.dependencies.find? refused.contains).map fun via =>
              let r := refused[via]!
              { name := d.name, kind := d.kind, root := r.root, cause := r.cause, via := some via }
        if let some r := refusal then
          refused := refused.insert d.name r
          changed := true
  return refused

/-! ## The module -/

structure Scaffold where
  path : List String
  items : Array ScaffoldItem
  counts : PrintCounts
  /-- The refused declarations, in the closure's order, auxiliary
  definitions left out: an auxiliary is refused only with its owner. -/
  refused : Array Refusal := #[]
  deriving Inhabited

def Scaffold.moduleName (s : Scaffold) : String := ".".intercalate s.path

def Scaffold.filePath (s : Scaffold) (dir : System.FilePath) : System.FilePath :=
  s.path.foldl (· / ·) dir |>.addExtension "agda"

/-- The module's text: the profile's options, a comment, a count of the
refused declarations when there are any, the header, and the
declarations, separated by blank lines. -/
def Scaffold.render (s : Scaffold) (comment : String) : String :=
  let refused := if s.refused.isEmpty then "" else
    s!"-- refused {s.refused.size} declarations; refusals.txt names each with its reason\n"
  s.items.foldl (fun out item => out ++ "\n" ++ item.text)
    s!"{profileUOptions}\n-- {comment}\n{refused}module {s.moduleName} where\n"

/-- One tab-separated line per refused declaration: kind, name, reason. -/
def Scaffold.renderRefusals (s : Scaffold) : String :=
  s.refused.foldl (fun out r => out ++ s!"{r.kind.label}\t{r.name}\t{r.reason}\n") ""

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
a definition that refers back to it, under a comment saying so.  Lean's
kernel accepts such a cycle only among the `_unsafe_rec` companions of
`partial` definitions, whose safety is `partial`, and Agda could check
none of them. -/
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
          let text := "-- cyclic definition, postulated\n" ++ text
          result := result.set! i { items[i]! with references, text, fallback := none }
  return result

/-! ## Items by kind -/

def postulateItem (p : Printer) (decl : Declaration) : Except String (ScaffoldItem × PrintCounts) := do
  let (t, counts) ← p.type decl.info.type
  let name := agdaIdent decl.name
  return ({ provides := #[name], references := t.constants,
            text := s!"postulate {name} : {t.render}\n" }, counts)

/-- A declaration with its printed signature and clause, laid out by
`layout`, with a postulate of its type as its fallback. -/
def valueItem (p : Printer) (decl : Declaration) (layout : String → String → String) :
    Except String (ScaffoldItem × PrintCounts) := do
  let some value := decl.info.value? (allowOpaque := true)
    | throw s!"{decl.name} has no value to print"
  let (t, c₁) ← p.type decl.info.type
  let (clause, c₂) ← p.clause decl.info.type value
  let name := agdaIdent decl.name
  let signature := s!"{name} : {t.render}"
  let references := clause.body.constants.foldl (fun acc n => if acc.contains n then acc else acc.push n)
    t.constants
  return ({ provides := #[name], references, text := layout signature (clause.render name),
            fallback := some (t.constants, s!"postulate {signature}\n") }, c₁.add c₂)

/-- A transparent definition: its signature and its clause. -/
def definitionItem (p : Printer) (decl : Declaration) : Except String (ScaffoldItem × PrintCounts) :=
  valueItem p decl fun signature clause => s!"{signature}\n{clause}\n"

/-- A theorem or one of Lean's opaque constants: its signature and clause
inside an `opaque` block of its own, under a comment naming which of the
two it is, which `scaffold_check.py` reads to know where the fallback
applies. -/
def opaqueItem (p : Printer) (decl : Declaration) (label : String) :
    Except String (ScaffoldItem × PrintCounts) :=
  valueItem p decl fun signature clause => s!"-- {label}\nopaque\n  {signature}\n  {clause}\n"

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

/-- The scaffold's item for one declaration, by its kind, or none for one
that its inductive block's item declares: a constructor, or a type of a
mutual block other than its first. -/
def scaffoldItem (p : Printer) (byName : Std.HashMap Name Declaration) (decl : Declaration) :
    Except String (Option (ScaffoldItem × PrintCounts)) := do
  match decl.info with
  | .inductInfo v =>
    if v.name == ``String then return some (← stringItem p decl)
    if v.all.head? != some v.name then return none
    return some (← inductiveItem p byName v)
  | .ctorInfo c =>
    if c.induct == ``String then return some (← postulateItem p decl)
    return none
  | .defnInfo _ => return some (← definitionItem p decl)
  | .thmInfo _ => return some (← opaqueItem p decl "theorem")
  | .opaqueInfo _ => return some (← opaqueItem p decl "opaque constant")
  | _ => return some (← postulateItem p decl)

/-- The scaffold of a closure that the sharing pass has already rewritten.
Its path is the one its names sidecar has, from the source module of the
closure's first root.  An auxiliary definition appears when something the
scaffold prints uses it; a refused declaration does not appear, nor do
its auxiliaries. -/
def scaffold (env : Environment) (root : Root) (closure : Closure) : Except String Scaffold := do
  let env ← addAuxiliaries env closure
  let some first := closure.roots[0]? | throw "the closure has no roots"
  let decls := closure.declarations
  let some owner := decls.find? (·.name == first) | throw s!"root {first} missing"
  let some module := owner.sourceModule | throw s!"no source module assigned to {first}"
  let byName : Std.HashMap Name Declaration := decls.foldl (fun m d => m.insert d.name d) {}
  let refused := refuseDeclarations decls
  let kept := decls.filter fun d => !refused.contains d.name
  let auxiliaries : Std.HashMap Name Declaration :=
    kept.foldl (fun m d => if d.auxiliary then m.insert d.name d else m) {}
  let needed := reachableAuxiliaries auxiliaries <| kept.foldl (fun acc d =>
    if d.auxiliary then acc else acc ++ constantExprs d.info) #[]
  let p : Printer := { env }
  let mut counts : PrintCounts := {}
  let mut items := #[]
  for decl in kept do
    unless decl.auxiliary && !needed.contains decl.name do
      if let some (item, c) ← scaffoldItem p byName decl then
        items := items.push item
        counts := counts.add c
  return { path := agdaModule root module, items := ← orderItems (breakCycles items), counts,
           refused := decls.filterMap fun d => if d.auxiliary then none else refused[d.name]? }

end Lean2Agda
