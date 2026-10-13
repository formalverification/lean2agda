/-
File: translator/Lean2Agda/Core/Inductive.lean
-/
import Lean2Agda.Core.Print
import Lean2Agda.Core.InductiveShape

/-!
# Inductive types as Agda declarations

An inductive type becomes one Agda declaration: a `record` when
`isAgdaRecord` says so (structure-like, every parameter an Agda
parameter) and a `data` type otherwise.  Every constructor and field keeps the
binder visibilities of its Lean type, so that the printer's applications,
which pass each argument with the visibility of the head's Lean type,
check against it:

+  Agda's constructors take a type's parameters implicitly, or as instance
   arguments where the type declares them as instances, which is how
   Lean's constructors take theirs.
+  A record's fields are bound as its constructor's fields are, explicitly,
   implicitly (`{n₂} : Nat`) or as instances (`⦃ toFunctor₁ ⦄ : Functor f₀`).
+  A record has eta, as Lean's structure-like types have.

`docs/translator/inductives.md` gives the rules and the probes behind
them.
-/

namespace Lean2Agda

open Lean

/-- One inductive type of a block, as the closure holds it after sharing:
the type and its constructors, whose types may refer to auxiliary
definitions. -/
structure InductiveMember where
  type : InductiveVal
  ctors : Array ConstructorVal
  deriving Inhabited

/-- A block's declaration: its lines, the identifiers it declares (its
types and constructors), the identifiers its text refers to, and what the
printer counted. -/
structure InductiveDecl where
  lines : Array String
  provides : Array String
  references : Array String
  counts : PrintCounts
  deriving Inhabited

/-- The members of an inductive type's block, read through `lookup`: the
environment, or a closure after sharing, whose types may refer to
auxiliary definitions. -/
def blockMembers (lookup : Name → Option ConstantInfo) (v : InductiveVal) :
    Except String (Array InductiveMember) :=
  v.all.toArray.mapM fun n => do
    let some (ConstantInfo.inductInfo type) := lookup n
      | throw s!"no inductive type {n}, of the block of {v.name}"
    let ctors ← type.ctors.toArray.mapM fun c => do
      let some (ConstantInfo.ctorInfo ctor) := lookup c | throw s!"no constructor {c}"
      pure ctor
    pure { type, ctors }

/-- A type's first binders replaced by the free variables of its
inductive type's parameter telescope, each binder exposed by `whnf` when
it is not syntactically a Pi type. -/
def instantiateParams (s : Scope) (type : Expr) (params : Array Expr) : PrintM Expr :=
  params.foldlM (init := type) fun t fv => do
    let some (.forallE _ _ b _) ← asPi s t
      | throw "a constructor with fewer binders than its type has parameters"
    return b.instantiate1 fv

/-- The free variables `enterTelescope` gives the first `k` binders it
enters from the empty scope. -/
def parameterVariables (k : Nat) : Array Expr :=
  (List.range k).toArray.map fun j => .fvar (Scope.fvarId j)

def telescopeText (binders : Array (Visibility × String × AgdaTerm)) : String :=
  if binders.isEmpty then "" else " " ++ renderTelescope binders

/-- A field line: Agda's record fields can be bound as the constructor
binds them, `f : T`, `{f} : T` or `⦃ f ⦄ : T`. -/
def fieldText (v : Visibility) (name type : String) : String :=
  match v with
  | .explicit => s!"{name} : {type}"
  | .implicit => s!"\{{name}} : {type}"
  | .instance => s!"⦃ {name} ⦄ : {type}"

/-- The printed parts of a declaration, kept to collect the constants
they refer to. -/
abbrev Printed := Array String × Array AgdaTerm

def binderTerms (binders : Array (Visibility × String × AgdaTerm)) : Array AgdaTerm :=
  binders.map (·.2.2)

/-- `data T params : indices → Set where`, then each constructor with its
type after the parameters, in the scope of the type's parameters. -/
def dataLines (m : InductiveMember) (indent : String) : PrintM Printed := do
  let k := m.type.numParams
  let (binders, inner, rest) ← enterTelescope {} m.type.type k
  let target ← printExpr inner rest
  let mut lines := #[s!"{indent}data {agdaIdent m.type.name}{telescopeText binders} : {target.render} where"]
  let mut terms := binderTerms binders |>.push target
  for c in m.ctors do
    let t ← printExpr inner (← instantiateParams inner c.type (parameterVariables k))
    lines := lines.push s!"{indent}  {agdaIdent c.name} : {t.render}"
    terms := terms.push t
  return (lines, terms)

/-- `record T params : Set where`, its constructor, and its fields, each
field's type printed in the scope of the parameters and the fields before
it, under the name the printer gives a projection of it. -/
def recordLines (m : InductiveMember) (indent : String) : PrintM Printed := do
  let k := m.type.numParams
  let (binders, inner, rest) ← enterTelescope {} m.type.type k
  let target ← printExpr inner rest
  let #[c] := m.ctors | throw s!"the record {m.type.name} has other than one constructor"
  let mut lines := #[s!"{indent}record {agdaIdent m.type.name}{telescopeText binders} : {target.render} where"]
  lines := lines.push s!"{indent}  constructor {agdaIdent c.name}"
  let mut terms := binderTerms binders |>.push target
  if c.numFields > 0 then lines := lines.push s!"{indent}  field"
  let mut scope := inner
  let mut rest ← instantiateParams inner c.type (parameterVariables k)
  for _ in [:c.numFields] do
    let some (.forallE x t b bi) ← asPi scope rest
      | throw s!"the constructor {c.name} has fewer binders than fields"
    let ft ← printExpr scope t
    let (scope', name, fv) := scope.enter x t bi
    lines := lines.push s!"{indent}    {fieldText (Visibility.ofBinderInfo bi) name ft.render}"
    terms := terms.push ft
    scope := scope'
    rest := b.instantiate1 fv
  return (lines, terms)

def memberLines (m : InductiveMember) (indent : String) : PrintM Printed := do
  if isAgdaRecord (← read).env m.type then recordLines m indent else dataLines m indent

/-- A type's block as one declaration, `Nat` with `BUILTIN NATURAL`, so
that literals print as decimals.  A mutual block is refused until the
emitter declares one. -/
def inductiveDecl (p : Printer) (members : Array InductiveMember) : Except String InductiveDecl := do
  let #[m] := members | throw s!"a mutual block of {members.size} types"
  let ((lines, terms), counts) ← runPrint p (memberLines m "")
  let lines := if members.map (·.type.name) == #[``Nat] then lines.push s!"\{-# BUILTIN NATURAL {agdaIdent ``Nat} #-}"
    else lines
  let provides := members.foldl (fun acc m =>
    (acc.push (agdaIdent m.type.name)) ++ m.ctors.map (agdaIdent ·.name)) #[]
  let references := terms.foldl (fun acc t => t.constants.foldl (fun acc n =>
    if acc.contains n || provides.contains n then acc else acc.push n) acc) #[]
  return { lines, provides, references, counts }

end Lean2Agda
