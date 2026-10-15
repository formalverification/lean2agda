/-
File: translator/tests/TranslatorTests/Input/Recursors.lean
-/

/-!
Inductive types for the recursors' tests (issue M2-5), each with values
that compute through its recursor, so that Agda checks them only when the
recursor's clauses are the kernel's rules: a plain recursive type, whose
structural recursion Lean compiles through `brecOn`; an indexed family; a
type nested through `Array` and `List`, whose recursors are a block of
three; a mutual pair; a `K`-like family, a proposition with one
constructor and no fields; a structure-like type that Agda receives as a
data type, projected through its recursor; and a type without
constructors.  Each theorem is proved by `rfl`, which Lean's kernel
checks by computing.
-/

namespace RecursorFixtures

/-- A plain recursive type. -/
inductive Tree where
  | leaf : Tree
  | node (left right : Tree) : Tree

/-- Structural recursion, compiled through `Tree.brecOn`. -/
def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size + 1

theorem Tree.size_example : (Tree.node .leaf (.node .leaf .leaf)).size = 5 := rfl

/-- The recursor applied directly. -/
noncomputable def Tree.leaves (t : Tree) : Nat :=
  Tree.rec 1 (fun _ _ l r => l + r) t

theorem Tree.leaves_example : (Tree.node .leaf (.node .leaf .leaf)).leaves = 3 := rfl

/-- An indexed family: the length an index. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} (head : α) (tail : Vec α n) : Vec α (n + 1)

noncomputable def Vec.sum {n : Nat} (v : Vec Nat n) : Nat :=
  Vec.rec (motive := fun _ _ => Nat) 0 (fun h _ s => h + s) v

theorem Vec.sum_example : Vec.sum (.cons 2 (.cons 3 .nil)) = 5 := rfl

/-- Nested through `Array` and `List`: the kernel's auxiliary types give
`Doc.rec` two siblings, `Doc.rec_1` on `Array Doc` and `Doc.rec_2` on
`List Doc`. -/
inductive Doc where
  | text (n : Nat) : Doc
  | block (kids : Array Doc) : Doc

noncomputable def Doc.total (d : Doc) : Nat :=
  Doc.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) (motive_3 := fun _ => Nat)
    (fun n => n) (fun _ s => s) (fun _ s => s) 0 (fun _ _ a b => a + b) d

theorem Doc.total_example : Doc.total (.block #[.text 2, .block #[.text 3], .text 4]) = 9 := rfl

mutual
  /-- A mutual pair. -/
  inductive Even where
    | zero : Even
    | succ (o : Odd) : Even
  inductive Odd where
    | succ (e : Even) : Odd
end

noncomputable def Even.toNat (e : Even) : Nat :=
  Even.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat) 0 (fun _ n => n + 1) (fun _ n => n + 1) e

theorem Even.toNat_example : Even.toNat (.succ (.succ (.succ (.succ .zero)))) = 4 := rfl

/-- `K`-like: a proposition with one constructor and no fields, its
`a` a parameter that Agda keeps as an index. -/
inductive Same {α : Type} : α → α → Prop where
  | refl (a : α) : Same a a

noncomputable def Same.transport {a b : Nat} (h : Same a b) (n : Nat) : Nat :=
  Same.rec (motive := fun _ _ => Nat) n h

theorem Same.transport_example : Same.transport (Same.refl 3) 7 = 7 := rfl

/-- Structure-like for Lean, which projects from it, and a data type with
an index for Agda, since its constructor binds the promoted `n`: a
projection prints through the recursor, and the dependent one checks
only when the recursor computes. -/
inductive Tagged : Nat → Type where
  | mk (n : Nat) (k : Nat) (v : Fin (k + 1)) : Tagged n

def Tagged.value {n : Nat} (x : Tagged n) : Fin (x.1 + 1) := x.2

theorem Tagged.value_example : (Tagged.value (.mk 4 2 1)).val = 1 := rfl

/-- No constructors. -/
inductive Void where

noncomputable def Void.elim (v : Void) : Nat := Void.rec (fun _ => Nat) v

end RecursorFixtures
