/-
File: translator/tests/TranslatorTests/Input/Printing.lean
-/

/-!
Declarations for the printer's tests.  Each value but one needs no
definitional unfolding to type-check, so that Agda can check it against
the postulates of the scaffold: together they print every expression
constructor, every binder visibility, both kinds of binder repair, and a
term the sharing pass shrinks from exponential to linear size.
`PrintFixtures.Dependent.value` is the exception, a projection whose
field type depends on an earlier field, which Agda refuses until records
compute (`docs/translator/printing.md`).
-/

namespace PrintFixtures

set_option linter.unusedVariables false in
/-- A value whose lambda is explicit where its type's binder is implicit:
the printer aligns it with the type (a top-level repair). -/
def alignedTop : {α : Type} → α → α := @fun α a => a

def applyImplicit (f : {α : Type} → α → α) : Nat := f 3

set_option linter.unusedVariables false in
/-- A lambda argument whose binder disagrees with the parameter's type
(a repair below the top level). -/
def alignedDeep : Nat := applyImplicit (@fun α a => a)

def withLet (n : Nat) : Nat :=
  let m := Nat.add n n
  Nat.add m m

def redex : Nat := (fun (x : Nat) => Nat.succ x) 3

def higher (f : Nat → Nat) (g : (Nat → Nat) → Nat) : Nat := g f

def strict ⦃n : Nat⦄ (_ : n = n) : Nat := n

def pick (α : Type) [Inhabited α] : α := default

def greeting : String := "a\"b\\c\nλ✝"

def large : Nat := 18446744073709551616

def sorts : Type → Prop → Type := fun α _ => α

structure Pair where
  first : Nat
  second : Nat

structure Dependent where
  size : Nat
  value : Fin size

/-- `Nat.add` doubled `n` times: a tree of `2 ^ n` leaves with `n + 1`
distinct subterms. -/
syntax "doubled!" num : term
macro_rules
  | `(doubled! $n) => do
    match n.getNat with
    | 0 => `(Nat.zero)
    | k + 1 =>
      let m := Lean.Syntax.mkNumLit (toString k)
      `(Nat.add (doubled! $m) (doubled! $m))

def doubling : Nat := doubled! 10

end PrintFixtures
