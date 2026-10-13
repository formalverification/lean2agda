/-
File: translator/Lean2Agda/Core/InductiveShape.lean
-/
import Lean.Environment
import Lean.ProjFns

/-!
# The shape of an inductive type in Agda

How a Lean inductive type maps onto an Agda declaration: whether it
becomes a `record` or a `data` type, how many of its parameters stay Agda
parameters, and which binder of its constructor each record field is.
These are pure functions of the environment, shared by the printer, which
prints a projection from a record as the record's field projection, and
by the emitter in `Inductive.lean`, which declares the types.
`docs/translator/inductives.md` gives the rules and the probes behind
them.
-/

namespace Lean2Agda

open Lean

/-- The binder information of a type's first `n` binders, read
syntactically, as the kernel stores an inductive type's or a
constructor's type. -/
def leadingBinderInfos : Expr → Nat → List BinderInfo
  | .mdata _ b, n => leadingBinderInfos b n
  | .forallE _ _ b bi, n + 1 => bi :: leadingBinderInfos b n
  | _, _ => []

/-- Whether Agda's constructor binds a parameter the way Lean's does.
Agda's constructors take a parameter declared as an instance as an
instance argument, and every other parameter as an implicit one. -/
def bindsLikeAgda (typeInfo ctorInfo : BinderInfo) : Bool :=
  match ctorInfo with
  | .instImplicit => typeInfo == .instImplicit
  | .implicit | .strictImplicit => typeInfo != .instImplicit
  | .default => false

/-- How many of a type's parameters stay Agda parameters: the longest
prefix of them that every constructor binds as Agda's constructors bind
parameters.  The rest become indices.  This undoes Lean's promotion of an
index to a parameter where a constructor binds it explicitly: `Eq.refl`
binds `a`, a parameter of `Eq` in the kernel, as `(a : α)`, and Agda's
constructor of a parameter `a` would bind it implicitly, which every
printed application `Eq.refl {α} a` would contradict. -/
def agdaParamCount (env : Environment) (v : InductiveVal) : Nat :=
  let typeInfos := leadingBinderInfos v.type v.numParams
  let keeps (ctor : Name) (j : Nat) : Bool :=
    match env.find? ctor with
    | some (.ctorInfo c) => match (leadingBinderInfos c.type v.numParams)[j]?, typeInfos[j]? with
      | some ci, some ti => bindsLikeAgda ti ci
      | _, _ => false
    | _ => false
  (List.range v.numParams).takeWhile (fun j => v.ctors.all (keeps · j)) |>.length

/-- Whether a type becomes an Agda record: structure-like (one
constructor, no indices, not recursive), every parameter an Agda
parameter, since a record has no indices, and not `String`, which
`BUILTIN STRING` needs as a postulate.  Records have eta in Agda, as
structure-like types have in Lean; everything else becomes `data`. -/
def isAgdaRecord (env : Environment) (v : InductiveVal) : Bool :=
  v.ctors.length == 1 && v.numIndices == 0 && !v.isRec && v.name != ``String &&
    agdaParamCount env v == v.numParams

def isAgdaRecordName (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.inductInfo v) => isAgdaRecord env v
  | _ => false

/-- The binder name and depth of field `i` of a constructor of type
`ctorType` with `numParams` parameters: a record's declaration enters
every parameter and field in turn, so field `i` sits at depth
`numParams + i`, and the printer names it from both. -/
def recordFieldBinder (ctorType : Expr) (numParams i : Nat) : Option (Name × Nat) :=
  go ctorType (numParams + i)
where
  go : Expr → Nat → Option (Name × Nat)
    | .mdata _ b, k => go b k
    | .forallE x _ _ _, 0 => some (x, numParams + i)
    | .forallE _ _ b _, k + 1 => go b k
    | _, _ => none

/-- Whether a constant is a projection function of a type that becomes
a record.  Its value, `fun params self => self.i`, prints as the record's
field projection, and the scaffold gives it that value, so that a type
mentioning `S.f self` checks against one whose field projection is
Agda's. -/
def isRecordProjection (env : Environment) (n : Name) : Bool :=
  match env.getProjectionFnInfo? n with
  | some info => match env.find? info.ctorName with
    | some (.ctorInfo c) => isAgdaRecordName env c.induct
    | _ => false
  | none => false

end Lean2Agda
