/-
File: translator/Lean2Agda/Core/Stats.lean
-/
import Lean2Agda.Core.Types

namespace Lean2Agda

/-- Counts include constructors and primitive recursors as separate
constants, even though they belong to an inductive declaration group. -/
structure Stats where
  constants : Nat := 0
  groups : Nat := 0
  axioms : Nat := 0
  definitions : Nat := 0
  theorems : Nat := 0
  opaques : Nat := 0
  inductives : Nat := 0
  constructors : Nat := 0
  recursors : Nat := 0
  quotients : Nat := 0
  deriving BEq, Repr, Inhabited

def Stats.add (s : Stats) (kind : Kind) : Stats :=
  let s := { s with constants := s.constants + 1 }
  match kind with
  | .axiom => { s with axioms := s.axioms + 1 }
  | .definition => { s with definitions := s.definitions + 1 }
  | .theorem => { s with theorems := s.theorems + 1 }
  | .opaque => { s with opaques := s.opaques + 1 }
  | .inductive => { s with inductives := s.inductives + 1 }
  | .constructor => { s with constructors := s.constructors + 1 }
  | .recursor => { s with recursors := s.recursors + 1 }
  | .quotient => { s with quotients := s.quotients + 1 }

def Closure.stats (closure : Closure) : Stats :=
  closure.groups.foldl (fun s group =>
    group.foldl (fun s decl => s.add decl.kind) s) { groups := closure.groups.size }

def Stats.render (s : Stats) : String :=
  "# stats\n" ++ "\n".intercalate [
    s!"constants\t{s.constants}", s!"groups\t{s.groups}",
    s!"axiom\t{s.axioms}", s!"definition\t{s.definitions}",
    s!"theorem\t{s.theorems}", s!"opaque\t{s.opaques}",
    s!"inductive\t{s.inductives}", s!"constructor\t{s.constructors}",
    s!"recursor\t{s.recursors}", s!"quotient\t{s.quotients}"] ++ "\n"

end Lean2Agda
