/-
File: translator/Lean2Agda/Core/Scaffold.lean
-/
import Lean2Agda.Core.Arithmetic
import Lean2Agda.Core.Recursor
import Lean2Agda.Core.Share

/-!
# The profile U scaffold

The Agda declarations of a closure, the test of the printer and the
emitters; `Modules.lean` lays them out as one Agda module per Lean
module.  It declares every constant of the closure that it does not
refuse, by kind, as follows:

+  the inductive types, each block of them one declaration
   (`Inductive.lean`): a record for each structure-like type and a data
   type for each other, `Nat` among them, bound to `BUILTIN NATURAL` so
   that literals print as decimals;
+  `String`, a postulate bound to `BUILTIN STRING`, which needs one, and
   so its constructor and recursor are postulates too;
+  the recursive cores of Lean's accelerated operations on `Nat`, by the
   operation table (`Arithmetic.lean`): Agda's builtins and Lean's
   equations over them, with the helpers they use, the rewrite rule that
   restores `Nat.sub`'s equation at a successor, and `Bool` bound to
   `BUILTIN BOOL`; or, under `--arithmetic lean`, Lean's compiled
   definitions as any other;
+  the recursors of each block of inductive types as one definition by
   pattern matching (`Recursor.lean`), whose clauses are the kernel's
   computation rules, under the comment `-- recursor`;
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
+  an axiom and a quotient primitive as a postulate, with the kernel's
   computation rules of `Quot.lift` and `Quot.ind` after their
   postulates as rewrite rules (issue M2-7): a postulate of the
   equation, over `Eq`, which `Inductive.lean` declares the rewrite
   relation, followed by its `REWRITE` pragma.

It refuses `sorryAx`, every `unsafe` declaration, and whatever depends on
one of those, and names each with its reason (`Scaffold.refused`,
written to `refusals.txt`).  A definition whose printed value refers to
itself, or to a definition that refers back to it, is postulated instead
(`breakCycles`); a recursor refers to itself through its recursive
calls, which Agda's termination checker decides, and is exempt.

`scripts/python/agda_check.py --refusals` type-checks the modules
declaration by declaration, with `scaffold_check.py`'s loop;
`docs/translator/printing.md` says what it refuses, and why.
-/

namespace Lean2Agda

open Lean

/-- Profile U's options: every sort is `Set`, and the quotient's
computation rules are rewrite rules. -/
def profileUOptions : String := "{-# OPTIONS --type-in-type --rewriting #-}"

/-- One declaration of a module: the identifiers it declares, those its
text refers to, and its text.  A declaration with a value also carries
its fallback, the references and text of a postulate of its type.  A
structural one is a recursor block defined by pattern matching, whose
recursion on its constructors' fields Agda's termination checker judges:
its references leave out the block's own names (`recursorDecl`), and
`breakCycles` would not count a reference to itself as a cycle either. -/
structure ScaffoldItem where
  provides : Array String
  references : Array String
  text : String
  fallback : Option (Array String × String) := none
  structural : Bool := false
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

/-! ## Order -/

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

/-- Order the items of one module so that each follows every item
providing an identifier it refers to, keeping the closure's order
otherwise.  The closure orders its groups, but inside a group (an
inductive type with its constructors and recursor) only the printed
references decide.  A reference no item provides names another module's
constant, which `Modules.lean` checks. -/
partial def orderItems (items : Array ScaffoldItem) : Except String (Array ScaffoldItem) := do
  let provider : Std.HashMap String Nat := (List.range items.size).foldl (fun m i =>
    items[i]!.provides.foldl (fun m n => m.insert n i) m) {}
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
none of them.  A structural item's references to itself are its
recursion, not a cycle. -/
def breakCycles (items : Array ScaffoldItem) : Array ScaffoldItem := Id.run do
  let provider : Std.HashMap String Nat := (List.range items.size).foldl (fun m i =>
    items[i]!.provides.foldl (fun m n => m.insert n i) m) {}
  let successors (i : Nat) : List Nat := items[i]!.references.toList.filterMap fun r =>
    (provider[r]?).filter fun j => !(j == i && items[i]!.structural)
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
  return ({ provides := #[name], references := t.references p.naming,
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
  let references := (clause.body.references p.naming).foldl (fun acc n => if acc.contains n then acc else acc.push n)
    (t.references p.naming)
  return ({ provides := #[name], references, text := layout signature (clause.render name),
            fallback := some (t.references p.naming, s!"postulate {signature}\n") }, c₁.add c₂)

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

/-! ## The operation table -/

/-- A row of the operation table: Lean's signature, printed, and the
table's clauses in place of the value, under the comment
`-- operation table`.  It refers to the helpers its clauses use and is
structural, since several of the clauses recur, as a recursor's do. -/
def tableItem (p : Printer) (helperName : String → String) (decl : Declaration) (entry : TableEntry) :
    Except String (ScaffoldItem × PrintCounts) := do
  let (t, counts) ← p.type decl.info.type
  let name := agdaIdent decl.name
  let q : TableNaming := ⟨p.naming.constant, helperName⟩
  let signature := s!"{name} : {t.render}"
  let references := (t.references p.naming ++ entry.uses.map helperName ++
    entry.mentions.map p.naming.constant).foldl (fun acc n =>
      if acc.contains n || n == name then acc else acc.push n) #[]
  let lines := #["-- operation table", signature] ++ entry.clauses q name
  return ({ provides := #[name], references, text := "\n".intercalate lines.toList ++ "\n",
            fallback := some (t.references p.naming, s!"postulate {signature}\n"), structural := true }, counts)

/-- A helper of the operation table, or its rewrite rule, as an item of
its home module, naming what it mentions as `q` says. -/
def helperItem (q : TableNaming) (h : Helper) : ScaffoldItem :=
  let references := (h.uses.map q.helper ++ h.mentions.map q.constant).foldl (fun acc n =>
    if acc.contains n || n == h.name then acc else acc.push n) #[]
  { provides := #[h.name], references, structural := true,
    text := "\n".intercalate ("-- operation table" :: (h.lines q).toList) ++ "\n" }

/-- `String`, a postulate, since `BUILTIN STRING` binds Agda's string
literals to a postulated type, whether or not it is a root. -/
def stringItem (p : Printer) (decl : Declaration) : Except String (ScaffoldItem × PrintCounts) := do
  let (item, counts) ← postulateItem p decl
  return ({ item with text := item.text ++ s!"\{-# BUILTIN STRING {agdaIdent ``String} #-}\n" }, counts)

/-! ## The quotient's computation rules -/

/-- `∀ (x₁ : T₁) … (xₙ : Tₙ), body`, the binders outermost first, where a
free variable whose identifier is a binder's name stands for that binder
in the types after it and in the body. -/
def forallOver (binders : List (Name × Expr × BinderInfo)) (body : Expr) : Expr :=
  binders.foldr (fun (x, t, bi) b => .forallE x t (b.abstract #[.fvar ⟨x⟩]) bi) body

/-- `Quot.lift f h (Quot.mk r a) = f a`, over `Quot.lift`'s binders
`{α} {r} {β} (f) (h)` and `(a : α)`: the statement of Lean's
`Quot.liftBeta`, built here because a closure can hold `Quot` without it
(`init_quot` is in `Init.Prelude`, the theorem in `Init.Core`). -/
def quotLiftRuleType : Expr :=
  let u := Level.param `u
  let v := Level.param `v
  let x (n : Name) : Expr := .fvar ⟨n⟩
  let rel := forallOver [(`a, x `α, .default), (`b, x `α, .default)] (.sort .zero)
  let respects := forallOver [(`a, x `α, .default), (`b, x `α, .default),
      (`p, mkApp2 (x `r) (x `a) (x `b), .default)]
    (mkApp3 (.const ``Eq [v]) (x `β) (.app (x `f) (x `a)) (.app (x `f) (x `b)))
  forallOver [(`α, .sort u, .implicit), (`r, rel, .implicit), (`β, .sort v, .implicit),
      (`f, forallOver [(`a, x `α, .default)] (x `β), .default), (`h, respects, .default),
      (`a, x `α, .default)]
    (mkApp3 (.const ``Eq [v]) (x `β)
      (mkAppN (.const ``Quot.lift [u, v])
        #[x `α, x `r, x `β, x `f, x `h, mkApp3 (.const ``Quot.mk [u]) (x `α) (x `r) (x `a)])
      (.app (x `f) (x `a)))

/-- `Quot.ind mk (Quot.mk r a) = mk a`, over `Quot.ind`'s binders
`{α} {r} {β} (mk)` and `(a : α)`: the statement of Lean's
`Quot.indBeta`. -/
def quotIndRuleType : Expr :=
  let u := Level.param `u
  let x (n : Name) : Expr := .fvar ⟨n⟩
  let rel := forallOver [(`a, x `α, .default), (`b, x `α, .default)] (.sort .zero)
  let quotMk (a : Expr) : Expr := mkApp3 (.const ``Quot.mk [u]) (x `α) (x `r) a
  let motive := forallOver [(`q, mkApp2 (.const ``Quot [u]) (x `α) (x `r), .default)] (.sort .zero)
  forallOver [(`α, .sort u, .implicit), (`r, rel, .implicit), (`β, motive, .implicit),
      (`mk, forallOver [(`a, x `α, .default)] (.app (x `β) (quotMk (x `a))), .default),
      (`a, x `α, .default)]
    (mkApp3 (.const ``Eq [.zero]) (.app (x `β) (quotMk (x `a)))
      (mkAppN (.const ``Quot.ind [u]) #[x `α, x `r, x `β, x `mk, quotMk (x `a)])
      (.app (x `mk) (x `a)))

/-- The computation rule that follows a quotient primitive's postulate,
for `Quot.lift` and `Quot.ind`: its identifier, the primitive's with
`-β` appended, which no `agdaIdent` can produce (it escapes both
characters), and its type. -/
def quotRule? (n : Name) : Option (String × Expr) :=
  if n == ``Quot.lift then some (agdaIdent n ++ "-β", quotLiftRuleType)
  else if n == ``Quot.ind then some (agdaIdent n ++ "-β", quotIndRuleType)
  else none

/-- A computation rule as a rewrite rule: a postulate of its equation,
under the comment `-- computation rule`, then its `REWRITE` pragma.  The
printer gives `Quot.lift` and `Quot.mk` the visibilities of their types,
so the left-hand side is the term the scaffold prints wherever Lean's
kernel would reduce.  The rule's type refers to `Eq`, which the closure
always declares: `directDependencies` gives every quotient primitive all
four, and `Quot.lift`'s type mentions `Eq`. -/
def ruleItem (p : Printer) (name : String) (type : Expr) : Except String (ScaffoldItem × PrintCounts) := do
  let (t, counts) ← p.type type
  return ({ provides := #[name], references := t.references p.naming,
            text := s!"-- computation rule\npostulate {name} : {t.render}\n\{-# REWRITE {name} #-}\n" }, counts)

/-- A block of inductive types as one item, declaring its types and
constructors. -/
def inductiveItem (p : Printer) (byName : Std.HashMap Name Declaration) (v : InductiveVal)
    (arithmetic : Arithmetic) : Except String (ScaffoldItem × PrintCounts) := do
  let d ← inductiveDecl p (← blockMembers (fun n => byName[n]?.map (·.info)) v)
  -- The operation table binds `Bool` to Agda's builtin booleans, which
  -- `NATEQUALS` and `NATLESS` need.
  let lines := if v.name == ``Bool && arithmetic == .agda then d.lines ++ boolPragmas else d.lines
  return ({ provides := d.provides, references := d.references,
            text := "\n".intercalate lines.toList ++ "\n" }, d.counts)

/-- The recursors of a block of inductive types as one structural item
under the comment `-- recursor`, with the postulates of their types as
its fallback. -/
def recursorItem (p : Printer) (members : Array RecursorVal) : Except String (ScaffoldItem × PrintCounts) := do
  let d ← recursorDecl p members
  let postulates := "\n".intercalate d.postulates.toList ++ "\n"
  return ({ provides := d.provides, references := d.references,
            text := "-- recursor\n" ++ "\n".intercalate d.lines.toList ++ "\n",
            fallback := some (d.typeReferences, "-- recursor, postulated\n" ++ postulates),
            structural := true }, d.counts)

/-- The recursors of each block of inductive types in a closure, keyed by
the block's first type, in `recursorRank`'s order. -/
def recursorBlocks (decls : Array Declaration) : Std.HashMap Name (Array RecursorVal) :=
  let blocks := decls.foldl (init := ({} : Std.HashMap Name (Array RecursorVal))) fun m d =>
    match d.info with
    | .recInfo r => match r.all.head? with
      | some first => m.insert first ((m.getD first #[]).push r)
      | none => m
    | _ => m
  blocks.fold (init := {}) fun m first members => m.insert first <| members.qsort fun a b =>
    let (ra, rb) := (recursorRank a.all a.name, recursorRank b.all b.name)
    ra < rb || (ra == rb && toString a.name < toString b.name)

/-- The scaffold's item for one declaration, by its kind, or none for one
that its block's item declares: a constructor, a type of a mutual block
other than its first, or a recursor other than its block's first.  Under
`--arithmetic agda` a definition with a row in the operation table is
that row's item. -/
def scaffoldItem (p : Printer) (byName : Std.HashMap Name Declaration)
    (recursors : Std.HashMap Name (Array RecursorVal)) (decl : Declaration)
    (arithmetic : Arithmetic := .agda) (helperName : String → String := id) :
    Except String (Option (ScaffoldItem × PrintCounts)) := do
  match decl.info with
  | .inductInfo v =>
    if v.name == ``String then return some (← stringItem p decl)
    if v.all.head? != some v.name then return none
    return some (← inductiveItem p byName v arithmetic)
  | .ctorInfo c =>
    if c.induct == ``String then return some (← postulateItem p decl)
    return none
  | .recInfo r =>
    -- `String` is a postulate, and so is its recursor.
    if r.all.contains ``String then return some (← postulateItem p decl)
    let members := (r.all.head?.bind (recursors[·]?)).getD #[r]
    if members[0]?.map (·.name) != some r.name then return none
    return some (← recursorItem p members)
  | .defnInfo _ =>
    if arithmetic == .agda then
      if let some entry ← tableEntry? decl.name decl.info.type then
        return some (← tableItem p helperName decl entry)
    return some (← definitionItem p decl)
  | .thmInfo _ => return some (← opaqueItem p decl "theorem")
  | .opaqueInfo _ => return some (← opaqueItem p decl "opaque constant")
  | _ => return some (← postulateItem p decl)

end Lean2Agda
