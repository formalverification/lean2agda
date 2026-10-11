/-
File: translator/tests/TranslatorTests/Input/Base.lean
-/

namespace Fixtures

axiom Marker : Type

inductive Envelope where
  | wrap : Marker → Envelope

structure Box where
  element : Marker

mutual
  inductive Tree where
    | leaf : Tree
    | node : Forest → Tree
  inductive Forest where
    | nil : Forest
    | cons : Tree → Forest → Forest
end

def token : Nat := 17

end Fixtures
