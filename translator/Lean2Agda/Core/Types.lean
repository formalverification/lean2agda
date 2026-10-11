/-
File: translator/Lean2Agda/Core/Types.lean
-/
import Lean.Environment

namespace Lean2Agda

open Lean

/-- The kinds of declarations exposed by Lean's elaborated environment. -/
inductive Kind where
  | axiom | definition | theorem | opaque | inductive | constructor | recursor | quotient
  deriving BEq, Repr, Inhabited

def Kind.ofConstantInfo : ConstantInfo → Kind
  | .axiomInfo _ => .axiom
  | .defnInfo _ => .definition
  | .thmInfo _ => .theorem
  | .opaqueInfo _ => .opaque
  | .inductInfo _ => .inductive
  | .ctorInfo _ => .constructor
  | .recInfo _ => .recursor
  | .quotInfo _ => .quotient

def Kind.label : Kind → String
  | .axiom => "axiom"
  | .definition => "definition"
  | .theorem => "theorem"
  | .opaque => "opaque"
  | .inductive => "inductive"
  | .constructor => "constructor"
  | .recursor => "recursor"
  | .quotient => "quotient"

/-- An original Lean declaration, its source module, and its direct
dependencies.  Keeping `ConstantInfo` leaves expressions and structured
names available to later translation passes. -/
structure Declaration where
  name : Name
  info : ConstantInfo
  sourceModule : Option Name
  dependencies : Array Name
  deriving Inhabited

def Declaration.kind (decl : Declaration) : Kind := Kind.ofConstantInfo decl.info

/-- A dependency closure ordered by strongly connected components.
Dependencies outside a group precede it; declarations in a group may
depend on each other.  Module ownership stays on individual declarations. -/
structure Closure where
  roots : Array Name
  groups : Array (Array Declaration)

def Closure.declarations (closure : Closure) : Array Declaration :=
  closure.groups.foldl (· ++ ·) #[]

def Closure.size (closure : Closure) : Nat :=
  closure.groups.foldl (fun n group => n + group.size) 0

end Lean2Agda
