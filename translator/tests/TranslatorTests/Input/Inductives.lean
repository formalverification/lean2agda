/-
File: translator/tests/TranslatorTests/Input/Inductives.lean
-/

/-!
Inductive types for the emitter's tests (issue M2-4), one for each rule
of `docs/translator/inductives.md`: an indexed family in the style of
`Vector`; a type whose constructor binds a promoted parameter explicitly,
as `Eq.refl` does, and one with a field as well, which Lean treats as
structure-like and Agda receives as a data type; a structure with an
instance parameter and implicit, instance and dependent fields; a
unit-like structure; recursive structures, nested through `List` and
recursive through a function type; a mutual block of a data type and a
structure-like type; an unsafe type that is not strictly positive; and a
constructor type that repeats large closed terms, one mentioning its own
type and one not, for the sharing pass.
-/

namespace InductiveFixtures

universe u

/-- A length-indexed family: `α` a parameter, the length an index. -/
inductive Vec (α : Type u) : Nat → Type u where
  | nil : Vec α 0
  | cons {n : Nat} (head : α) (tail : Vec α n) : Vec α (n + 1)

/-- Lean promotes `a` to a parameter, and the constructor binds it
explicitly. -/
inductive Same {α : Type} : α → α → Prop where
  | refl (a : α) : Same a a

/-- Structure-like for Lean once it promotes `n`, which the constructor
binds explicitly; a data type with an index for Agda. -/
inductive Sized : Nat → Type where
  | mk (n : Nat) (value : Fin n) : Sized n

class Measure (α : Type) where
  measure : α → Nat

/-- An instance parameter, an implicit field, an instance field, and a
field whose type mentions three earlier ones. -/
structure Packed (α : Type) [BEq α] where
  {width : Nat}
  [measured : Measure α]
  value : α
  fits : Measure.measure value ≤ width

/-- A unit-like structure: one constructor and no fields. -/
structure Token where

/-- A recursive structure, nested through `List`. -/
structure Rose where
  label : Nat
  children : List Rose

/-- Recursive through a function type, with one constructor. -/
inductive Stream' where
  | mk (head : Nat) (tail : Nat → Stream')

mutual
  /-- A data type of a mutual block. -/
  inductive Term where
    | lit : Nat → Term
    | pair : Pair → Term
  /-- A structure-like type of the same block. -/
  inductive Pair where
    | mk (left right : Term) : Pair
end

/-- Not strictly positive, which Lean's kernel accepts only of an unsafe
type, since it checks no unsafe type for positivity. -/
unsafe inductive Bad where
  | mk : (Bad → Nat) → Bad

/-- A constructor type that repeats a closed term of 33 nodes mentioning
`Wide`, and one of 33 nodes that does not. -/
inductive Wide where
  | leaf : Wide
  | node (f g : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Wide)
      (h k : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat) : Wide

end InductiveFixtures
