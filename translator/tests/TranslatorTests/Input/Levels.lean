/-
File: translator/tests/TranslatorTests/Input/Levels.lean
-/

/-!
Constants for the Prop-instantiation specialization (issue M3-3;
`tests/Levels.lean`, and the golden scaffold `levels` of `tests/run.sh`,
printed with `--specialize`).  One constant per rule of
`docs/translator/levels.md`: which level parameters are split, which
instance a use selects, what an `imax` becomes in each instance, and the
quotient's computation rule at more than one instance.
-/

namespace LevelFixtures

universe u v

/-- Split on `u`: `Sort u` is `Prop` at zero. -/
def twice {α : Sort u} (f : α → α) (a : α) : α := f (f a)

/-- A use of `twice` at a type, which selects its nonzero instance. -/
def atType (n : Nat) : Nat := twice Nat.succ n

/-- A use of `twice` at a proposition, which selects its instance at zero. -/
theorem atProp (h : True) : True := twice (fun x => x) h

/-- Not split: `Type u` and `Type (max u v)` are never `Prop`. -/
def lifted (α : Type u) : Type (max u v) := ULift.{v, u} α

/-- Split on `v` only because it passes `v` to `PUnit`, which is split on
its parameter: no sort of its own mentions `v`. -/
def passes : PUnit.{v} → PUnit.{v} := fun x => x

/-- Not split: it passes `v + 1`, which is never zero. -/
def passesSucc : PUnit.{v + 1} → PUnit.{v + 1} := fun x => x

/-- Split on `u` by the predecessor rule alone: `max 1 u` is never zero,
but it is one above `0` at `u = 0` and one above `u - 1` elsewhere, and
no level in `u` says both. -/
def wide (α : Sort (max 1 u)) : Sort (max 1 u) := α

/-- An `imax`, which is zero in the two instances where `v` is, `v + 1`
where only `u` is zero, and a `max` where neither is. -/
def arrow (α : Sort u) (β : Sort v) : Sort (imax u v) := α → β

/-- A structure over any sort, an Agda record, and its projection. -/
structure Box (α : Sort u) where
  val : α

def unbox {α : Sort u} (b : Box α) : α := b.val

theorem unboxProof (b : Box True) : True := unbox b

def unboxNat (b : Box Nat) : Nat := unbox b

/-- A type with two constructors, whose recursor a match uses at the
motive's level: a proposition's in one instance, a type's in the other. -/
inductive Pick (α : Sort u) where
  | left (a : α)
  | right (a : α)

def Pick.get {α : Sort u} : Pick α → α
  | .left a => a
  | .right a => a

theorem Pick.get_left (n : Nat) : (Pick.left n).get = n := rfl

/-- A type with one constructor that binds its parameter explicitly, as
`Eq.refl` does: Lean's kernel projects from it, and it is no Agda record,
so the printer writes a projection from it through `Tagged.rec`, at the
instance the level of the field's type selects. -/
inductive Tagged : Sort u → Sort (max 1 u) where
  | mk (α : Sort u) (a : α) : Tagged α

def Tagged.get {α : Sort u} (t : Tagged α) : α := t.1

theorem Tagged.get_mk (n : Nat) : (Tagged.mk Nat n).get = n := rfl

/-- A type in `Type u` whose constructor takes a field in `Sort u`: the
type's own sort is never `Prop`, and its constructor's field is a
proposition at zero, so the block is split on `u` for the constructor
alone, and its type with it. -/
inductive Holder : Type u where
  | mk (α : Sort u) (a : α) : Holder

/-- A nested type over any sort: its recursors, `Tree.rec` and the
kernel's `Tree.rec_1` for the list of children, are one `mutual`
definition at each pattern. -/
inductive Tree (α : Sort u) : Type u where
  | node (label : α) (children : List (Tree α)) : Tree α

mutual
  /-- Two types of one mutual declaration over any sort: one `mutual`
  block of Agda at each pattern, whose types come together. -/
  inductive Even (α : Sort u) : Type u where
    | zero : Even α
    | succ (a : α) (n : Odd α) : Even α
  inductive Odd (α : Sort u) : Type u where
    | succ (a : α) (n : Even α) : Odd α
end

/-- A quotient of a proposition, lifted into a type: the instance of
`Quot.lift` at zero and nonzero, whose computation rule is its own. -/
def fromProofs (q : Quot (fun (_ _ : True) => True)) : Nat :=
  Quot.lift (fun _ => 0) (fun _ _ _ => rfl) q

theorem fromProofs_mk (h : True) : fromProofs (Quot.mk _ h) = 0 := rfl

/-- A quotient of a type, lifted into a proposition: the instance at
nonzero and zero, whose rule is an equation between proofs, over the
instance of `Eq` at zero. -/
theorem toProof (q : Quot (@Eq Nat)) : True :=
  Quot.lift (fun _ => True.intro) (fun _ _ _ => rfl) q

end LevelFixtures
