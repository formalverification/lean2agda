/-
File: translator/tests/TranslatorTests/Input/Kinds.lean
-/

/-!
Declarations of every kind the scaffold emits or refuses, for the tests
of its rules (`tests/Scaffold.lean`) and for the golden scaffold `kinds`
of `tests/run.sh`: a definition, theorems, one of Lean's opaque
constants, an axiom, a class with an instance, a `partial` definition
with its `_unsafe_rec` companion, a theorem left to `sorry` with a
dependent, and `unsafe` definitions with a dependent.  `useAlias` is the
pair the fallback fires on: Lean accepts it by proof irrelevance, and
Agda accepts it only once `alias` unfolds to `base`.  `wide` repeats a
closed subterm that mentions an `unsafe` constant, which the sharing pass
must leave alone.
-/

namespace KindFixtures

axiom Q : True → Type

theorem base : True := trivial

theorem alias : True := base

def useBase (_ : Q base) : Nat := 0

def useAlias (q : Q alias) : Nat := useBase q

opaque hidden : Nat := 5

def plain (n : Nat) : Nat := Nat.add n hidden

class Marker (α : Type) where
  mark : α

instance instMarkerNat : Marker Nat := ⟨0⟩

def useMark : Nat := Marker.mark

partial def loop (n : Nat) : Nat := loop n

theorem usesSorry : True := sorry

def onSorry (_ : Q usesSorry) : Nat := 1

unsafe def danger : Nat := 3

unsafe def onDanger : Nat := Nat.succ danger

unsafe def wide : Nat := Nat.add (Nat.succ danger) (Nat.succ danger)

end KindFixtures
