/-
File: translator/Lean2Agda/Core/Share.lean
-/
import Lean2Agda.Core.Closure
import Lean2Agda.Core.Literals
import Lean.Util.CollectLevelParams
import Lean.Util.ReplaceExpr

/-!
# The sharing pass

A kernel expression is a graph: a subterm reached twice is one object, and
lean4export writes it once.  Printed text is a tree, so a subterm is
printed once per path that reaches it, which can be exponentially many.
The pass finds, in each declaration's type and value, the closed subterms
that the printed tree would repeat and that are at least a threshold in
size, and makes each one an auxiliary definition, referenced by name
wherever it occurred.  `docs/translator/printing.md` gives the rules and
the measurements.

Subterms are identified by structural equality that keeps binder names
and binder information (`ExprStructEq`), because the printer prints both.

Before it shares anything, the pass gives each distinct string literal of
the closure one definition, the literal's kernel expansion
(`Literals.lean`), and refers to it wherever the literal occurs, in every
declaration: the table of literals, the one sharing across declarations.
-/

namespace Lean2Agda

open Lean

/-- Drop every `mdata` node.  Annotations carry nothing the printer
prints, and two subterms that differ only by one must share. -/
partial def stripMData (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (stripMData b)
    | _ => none

/-- A distinct subterm: its children, its size as a tree (the number of
nodes the printer visits, counting a repeated child each time), and
whether it is closed. -/
structure ShareNode where
  expr : Expr
  children : Array Nat
  treeSize : Nat
  closed : Bool
  deriving Inhabited

/-- Distinct subterms in post-order, so that every child precedes each of
its parents. -/
structure ShareGraph where
  nodes : Array ShareNode := #[]
  index : Std.HashMap ExprStructEq Nat := {}
  deriving Inhabited

partial def ShareGraph.visit (e : Expr) : StateM ShareGraph Nat := do
  if let some i := (← get).index[(e : ExprStructEq)]? then return i
  let children : Array Nat ← match e with
    | .app f a => pure #[← ShareGraph.visit f, ← ShareGraph.visit a]
    | .lam _ t b _ | .forallE _ t b _ => pure #[← ShareGraph.visit t, ← ShareGraph.visit b]
    | .letE _ t v b _ =>
      pure #[← ShareGraph.visit t, ← ShareGraph.visit v, ← ShareGraph.visit b]
    | .proj _ _ s | .mdata _ s => pure #[← ShareGraph.visit s]
    | _ => pure #[]
  let g ← get
  let treeSize := children.foldl (fun n k => n + g.nodes[k]!.treeSize) 1
  let i := g.nodes.size
  set { nodes := g.nodes.push { expr := e, children, treeSize, closed := !e.hasLooseBVars },
        index := g.index.insert e i : ShareGraph }
  return i

def ShareGraph.build (roots : Array Expr) : Array Nat × ShareGraph :=
  (roots.mapM ShareGraph.visit).run {}

/-- A closed subterm worth sharing.  Lambdas are left in place: the
printer gives a lambda the visibility its context expects, which a
reference to a shared definition would no longer carry. -/
def ShareNode.candidate (node : ShareNode) (threshold : Nat) : Bool :=
  node.closed && node.treeSize ≥ threshold && !node.expr.isLambda

/-- Count each subterm's occurrences in the printed tree, parents before
children, and choose the subterms to share as the count is settled: a
subterm occurring twice or more, closed, at least `threshold` in size,
and `allowed`.  A chosen subterm is printed once, in its auxiliary
definition, so its children are counted once for it. -/
def ShareGraph.choose (g : ShareGraph) (roots : Array Nat) (threshold : Nat)
    (allowed : Expr → Bool := fun _ => true) : Array Bool := Id.run do
  let mut occurrences : Array Nat := .replicate g.nodes.size 0
  for r in roots do occurrences := occurrences.modify r (· + 1)
  let mut chosen : Array Bool := .replicate g.nodes.size false
  for j in [:g.nodes.size] do
    let i := g.nodes.size - 1 - j
    let node := g.nodes[i]!
    let o := occurrences[i]!
    let share := o ≥ 2 && node.candidate threshold && allowed node.expr
    if share then chosen := chosen.set! i true
    let each := if share then 1 else o
    for k in node.children do occurrences := occurrences.modify k (· + each)
  return chosen

/-- The total size of the printed trees of `roots`, with the chosen
subterms printed once each and replaced by a name elsewhere. -/
def ShareGraph.printedSize (g : ShareGraph) (roots : Array Nat) (chosen : Array Bool) : Nat := Id.run do
  let mut size : Array Nat := .replicate g.nodes.size 0
  for i in [:g.nodes.size] do
    let node := g.nodes[i]!
    size := size.set! i (node.children.foldl (fun n k =>
      n + if chosen[k]! then 1 else size[k]!) 1)
  let shared := (List.range g.nodes.size).foldl (fun n i => if chosen[i]! then n + size[i]! else n) 0
  return roots.foldl (fun n r => n + if chosen[r]! then 1 else size[r]!) shared

/-- The smallest subterm the pass shares, as a number of expression
nodes; `docs/translator/printing.md` gives the measurements behind it. -/
def defaultShareThreshold : Nat := 32

/-- The name of a declaration's `k`th auxiliary definition. -/
def auxiliaryName (owner : Name) (k : Nat) : Name := .num (.str owner "_share") k

/-- The level parameters of `owner` that occur in `e`, in `owner`'s order. -/
def usedLevelParams (owner : List Name) (e : Expr) : List Name :=
  let used := (collectLevelParams {} e).params
  owner.filter used.contains

/-- A declaration's type and, when it has one, its value. -/
def constantExprs (info : ConstantInfo) : Array Expr :=
  match info.value? (allowOpaque := true) with
  | some v => #[info.type, v]
  | none => #[info.type]

/-- Replace a declaration's type and, when it has one, its value. -/
def replaceExprs (info : ConstantInfo) (type : Expr) (value : Option Expr) : ConstantInfo :=
  match info, value with
  | .defnInfo v, some e => .defnInfo { v with type, value := e }
  | .thmInfo v, some e => .thmInfo { v with type, value := e }
  | .opaqueInfo v, some e => .opaqueInfo { v with type, value := e }
  | .axiomInfo v, _ => .axiomInfo { v with type }
  | .defnInfo v, none => .defnInfo { v with type }
  | .thmInfo v, none => .thmInfo { v with type }
  | .opaqueInfo v, none => .opaqueInfo { v with type }
  | .quotInfo v, _ => .quotInfo { v with type }
  | .inductInfo v, _ => .inductInfo { v with type }
  | .ctorInfo v, _ => .ctorInfo { v with type }
  | .recInfo v, _ => .recInfo { v with type }

/-- The inductive types of the block a type or a constructor belongs to,
and none for any other declaration. -/
def ownBlock (env : Environment) : ConstantInfo → List Name
  | .inductInfo v => v.all
  | .ctorInfo c => match env.find? c.induct with
    | some (.inductInfo v) => v.all
    | _ => [c.induct]
  | _ => []

/-- Whether a subterm of a type's or a constructor's type may become an
auxiliary definition: only if it mentions no type of their block.  The
scaffold declares a block as one item, its types with their constructors,
so an auxiliary that mentioned the block would have to sit inside it;
excluded, every auxiliary a block uses precedes the block.  Such a
subterm is rare, since it must be closed: it occurs only in the
constructors of a type without parameters.  A subterm mentions a type as
`expressionDependencies` counts it, by a constant or by a projection,
though Lean's kernel refuses a projection of a block's type in the
block's own constructors, whose constructor it does not yet know. -/
def outsideBlock (block : List Name) (e : Expr) : Bool :=
  block.isEmpty || (e.find? fun sub => match sub with
    | .const n _ | .proj n _ _ => block.contains n
    | _ => false).isNone

/-- One declaration after sharing: the declaration with its type and value
rewritten, and its auxiliary definitions, each before any that uses it. -/
structure Shared where
  declaration : Declaration
  auxiliaries : Array Declaration
  deriving Inhabited

/-- Share the closed subterms of one declaration's type and value.  An
auxiliary's type is the kernel's, inferred from the subterm as it
occurred, and its source module is its owner's. -/
def shareDeclaration (env : Environment) (threshold : Nat) (decl : Declaration) :
    Except String Shared := do
  let exprs := (constantExprs decl.info).map stripMData
  let (roots, g) := ShareGraph.build exprs
  let chosen := g.choose roots threshold (outsideBlock (ownBlock env decl.info))
  let picked := (List.range g.nodes.size).filter (chosen[·]!) |>.toArray
  let mut names : Std.HashMap ExprStructEq Name := {}
  for h : k in [:picked.size] do
    let name := auxiliaryName decl.name (k + 1)
    if env.contains name then throw s!"auxiliary name {name} is already a constant"
    names := names.insert g.nodes[picked[k]]!.expr name
  let levelParams := decl.info.levelParams
  let reference (e : Expr) (name : Name) : Expr :=
    .const name (usedLevelParams levelParams e |>.map Level.param)
  let rewrite (e : Expr) : Expr := e.replace fun sub =>
    (names[(sub : ExprStructEq)]?).map (reference sub)
  -- An auxiliary's own value keeps its root and rewrites below it.
  let rewriteBelow (e : Expr) : Expr := match e with
    | .app f a => .app (rewrite f) (rewrite a)
    | .lam n t b bi => .lam n (rewrite t) (rewrite b) bi
    | .forallE n t b bi => .forallE n (rewrite t) (rewrite b) bi
    | .letE n t v b nd => .letE n (rewrite t) (rewrite v) (rewrite b) nd
    | .proj s i b => .proj s i (rewrite b)
    | e => e
  let mut auxiliaries := #[]
  for i in picked do
    let e := g.nodes[i]!.expr
    let name := names[(e : ExprStructEq)]!
    let type ← match Kernel.check env {} e with
      | .ok t => pure t
      | .error _ => throw s!"the kernel could not infer the type of a shared subterm of {decl.name}"
    let info : ConstantInfo := .defnInfo {
      name, levelParams := usedLevelParams levelParams e, type := stripMData type,
      value := rewriteBelow e, hints := .abbrev, safety := .safe, all := [name] }
    auxiliaries := auxiliaries.push {
      name, info, sourceModule := decl.sourceModule, auxiliary := true,
      dependencies := expressionDependencies info.type ++ expressionDependencies info.value! }
  let value := exprs[1]?.map rewrite
  let info := replaceExprs decl.info (rewrite exprs[0]!) value
  let references := auxiliaries.map (·.name)
  return { declaration := { decl with info, dependencies := decl.dependencies ++ references },
           auxiliaries }

/-- A closure's declarations ordered again by strongly connected groups,
each group after those it depends on, as `dependencyClosure` orders them. -/
def regroup (roots : Array Name) (decls : Array Declaration) : Closure :=
  let byName : Std.HashMap Name Declaration := decls.foldl (fun m d => m.insert d.name d) {}
  let names := sortNames (decls.map (·.name))
  let groups := SCC.scc names.toList fun n =>
    (byName[n]!.dependencies.filter byName.contains).toList
  { roots, groups := groups.toArray.map fun group => (sortNames group.toArray).map (byName[·]!) }

/-! ## The table of string literals -/

/-- The name of the definition of the string literal `s`: `String._lit`
followed by the literal's text as one more component.  It is the
literal's alone, whatever else a closure holds, and Agda's identifier
escapes the text injectively (`String:~ulit:ab` for `"ab"`,
`docs/translator/naming.md`), so no two literals share one. -/
def literalName (s : String) : Name := .str (.str ``String "_lit") s

/-- The distinct string literals of `e`. -/
def stringLiterals (e : Expr) : Std.HashSet String := runST fun σ => do
  let found : ST.Ref σ (Std.HashSet String) ← ST.mkRef {}
  e.forEach (ω := σ) (m := ST σ) fun sub => do
    match sub with
    | .lit (.strVal s) => found.modify (·.insert s)
    | _ => pure ()
  found.get

/-- `e` with every string literal replaced by a reference to its
definition. -/
def referToLiterals (e : Expr) : Expr :=
  e.replace fun
    | .lit (.strVal s) => some (.const (literalName s) [])
    | _ => none

/-- The definition of the string literal `s`: its kernel expansion, of
type `String`, an auxiliary definition of the module `home`. -/
def literalDeclaration (home : Name) (s : String) : Declaration :=
  let name := literalName s
  let value := stringLiteralExpansion s
  let type : Expr := .const ``String []
  { name, sourceModule := some home, auxiliary := true,
    info := .defnInfo { name, levelParams := [], type, value, hints := .abbrev, safety := .safe, all := [name] },
    dependencies := uniqueNames (expressionDependencies type ++ expressionDependencies value) }

/-- Give each distinct string literal of a closure one definition
(`literalDeclaration`), and refer to it wherever the literal occurs in a
declaration's type or value, so that a literal prints once however many
declarations hold it.  The definitions belong to the module of
`String.ofList`, `Init.Prelude`, which every module holding a literal
imports, since it declares `String`; their values name only constants of
that module, and the closure of those constants holds no literal, so no
definition refers back to itself.  A recursor's computation rules are
left as they are, as the sharing pass leaves them, and the printer
prints a literal there as its expansion. -/
def tabulateLiterals (env : Environment) (closure : Closure) : Except String Closure := do
  let decls := closure.declarations
  let used := decls.map fun d =>
    (constantExprs d.info).foldl (fun acc e => (stringLiterals e).fold (·.insert ·) acc) ({} : Std.HashSet String)
  let literals := (used.foldl (fun acc ls => ls.fold (·.insert ·) acc) ({} : Std.HashSet String)).toArray.qsort (· < ·)
  if literals.isEmpty then return closure
  let some home := moduleOf env ``String.ofList
    | throw "a string literal, and no String.ofList to expand it to"
  for s in literals do
    if env.contains (literalName s) then throw s!"the literal's name {literalName s} is already a constant"
  let rewritten := (decls.zip used).map fun (d, ls) =>
    if ls.isEmpty then d else
      let exprs := (constantExprs d.info).map referToLiterals
      { d with info := replaceExprs d.info exprs[0]! exprs[1]?,
               dependencies := uniqueNames (d.dependencies ++ ls.toArray.map literalName) }
  return regroup closure.roots (rewritten ++ literals.map (literalDeclaration home))

/-- The environment with a closure's auxiliary definitions added, so that
the printer and the kernel's `whnf` can see them.  The kernel checks each
one, which also checks the type the pass inferred for it.  An auxiliary is
added after those it uses. -/
partial def addAuxiliaries (env : Environment) (closure : Closure) : Except String Environment := do
  let auxiliaries : Std.HashMap Name Declaration := closure.declarations.foldl
    (fun m d => if d.auxiliary then m.insert d.name d else m) {}
  let rec add (n : Name) (start : Environment) : Except String Environment := do
    if start.contains n then return start
    let d := auxiliaries[n]!
    let mut env := start
    for dep in d.dependencies do
      if auxiliaries.contains dep then env ← add dep env
    let .defnInfo v := d.info | throw s!"the auxiliary {n} is not a definition"
    match env.addDeclCore 0 0 (.defnDecl v) none with
    | .ok extended => pure extended
    | .error _ => throw s!"the kernel rejected the auxiliary definition {n}"
  closure.declarations.foldlM (init := env) fun env d =>
    if d.auxiliary then add d.name env else pure env

/-- Tabulate a closure's string literals (`tabulateLiterals`), then share
every declaration but the `unsafe` ones, and order the result again by
strongly connected groups, so that each auxiliary precedes its users and
follows what it uses.  An `unsafe` declaration is left as it is: the
scaffold refuses it, and the kernel would refuse a safe auxiliary
definition made from a subterm of its value.  A threshold of zero shares
no subterm, and the literals are tabulated all the same. -/
def shareClosure (env : Environment) (threshold : Nat) (closure : Closure) : Except String Closure := do
  let closure ← tabulateLiterals env closure
  if threshold == 0 then return closure
  -- A shared subterm can mention a literal's definition, whose type the
  -- kernel needs to infer the subterm's.
  let env ← addAuxiliaries env closure
  let shared ← closure.declarations.mapM fun d =>
    if d.info.isUnsafe then pure { declaration := d, auxiliaries := #[] }
    else shareDeclaration env threshold d
  return regroup closure.roots (shared.foldl (fun acc s => acc.push s.declaration ++ s.auxiliaries) #[])

end Lean2Agda
