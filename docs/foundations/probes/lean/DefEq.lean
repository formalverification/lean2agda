-- File: docs/foundations/probes/lean/DefEq.lean
-- Lean's definitional equalities at the pin; the one error below (the recursive structure's eta) is the intended rejection.
-- Run from translator/ as: lake env lean ../docs/foundations/probes/lean/DefEq.lean
import Lean
open Lean
-- Lean's definitional equalities at the pin (Lean v4.33.1), each as an `example` the
-- elaborator and kernel accept, with the recursor flags and a few declarations printed.

-- proof irrelevance is definitional
example (p : Prop) (h1 h2 : p) : h1 = h2 := rfl
-- so UIP holds for every type, since a = b is a Prop
example {α : Sort u} {a b : α} (p q : a = b) : p = q := rfl
-- K-like reduction: Eq.rec on a neutral proof of a = a reduces
example {α : Sort u} {a : α} {C : α → Sort v} (x : C a) (h : a = a) : (h ▸ x) = x := rfl
-- structure eta and unit eta
example {α β : Type} (p : α × β) : p = (p.1, p.2) := rfl
example (u : PUnit) : u = PUnit.unit := rfl
-- a recursive structure has no eta: this one is rejected (type mismatch)
structure Tree where
  children : List Tree
example (t : Tree) : t = ⟨t.children⟩ := rfl
-- Nat literals and kernel arithmetic
example : 18446744073709551616 + 1 = 18446744073709551617 := rfl
example : 2 ^ 64 = 18446744073709551616 := by decide
example : Nat.gcd 1000000007 998244353 = 1 := by decide
example : Nat.gcd 12 18 = 6 := rfl
-- String literals (String.mk is deprecated at this version; the kernel expands to String.ofList)
example : "a" = String.mk ['a'] := rfl
example : "ab" ++ "c" = "abc" := by decide
-- Quot computes definitionally
example {α : Sort u} (r : α → α → Prop) (f : α → Nat) (h : ∀ a b, r a b → f a = f b) (a : α) :
    Quot.lift f h (Quot.mk r a) = f a := rfl
#print Quot
#print Quot.lift
#print Quot.ind
#print Quot.sound
#print propext
#print Classical.choice
#print axioms Classical.em
#print Classical.propDecidable
#print axioms Classical.propDecidable
#print Nat.gcd
#check @Nat.gcd._unary
#eval show CoreM Unit from do
  let env ← getEnv
  for n in [``Eq.rec, ``HEq.rec, ``Acc.rec, ``And.rec, ``True.rec, ``False.rec, ``Nonempty.rec, ``Exists.rec, ``Iff.rec, ``Or.rec, ``PUnit.rec, ``Subtype.rec] do
    match env.find? n with
    | some (.recInfo v) => IO.println s!"{n} k={v.k} levels={v.levelParams} nparams={v.numParams} nindices={v.numIndices}"
    | _ => IO.println s!"{n} not a recursor"
  for n in [``Eq, ``HEq, ``Acc, ``And, ``True, ``False, ``Nonempty, ``Exists, ``Or, ``Iff] do
    match env.find? n with
    | some (.inductInfo v) => IO.println s!"{n} levels={v.levelParams} ctors={v.ctors} isRec={v.isRec} numNested={v.numNested}"
    | _ => pure ()
  IO.println s!"Quot kind: {env.find? ``Quot |>.map (fun ci => match ci with | .quotInfo _ => "quotInfo" | _ => "other")}"

/- Output on 2026-10-07 (Lean v4.33.1, Mathlib v4.33.1):
DefEq.lean:18:41: error: Type mismatch
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  t = { children := t.children }
DefEq.lean:25:16: warning: `String.mk` has been deprecated: Use `String.ofList` instead
Quotient primitive Quot.{u} : {α : Sort u} → (α → α → Prop) → Sort u
Quotient primitive Quot.lift.{u, v} : {α : Sort u} →
  {r : α → α → Prop} → {β : Sort v} → (f : α → β) → (∀ (a b : α), r a b → f a = f b) → Quot r → β
Quotient primitive Quot.ind.{u} : ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
  (∀ (a : α), β (Quot.mk r a)) → ∀ (q : Quot r), β q
axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b
axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b
axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α
'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound]
@[instance_reducible] def Classical.propDecidable : (a : Prop) → Decidable a :=
fun a => Classical.choice ⋯
'Classical.propDecidable' depends on axioms: [propext, Classical.choice, Quot.sound]
@[irreducible] def Nat.gcd : Nat → Nat → Nat :=
fun m n => Nat.gcd._unary ⟨m, n⟩
Nat.gcd._unary : (_ : Nat) ×' Nat → Nat
Eq.rec k=true levels=[u, u_1] nparams=2 nindices=1
HEq.rec k=true levels=[u_1, u] nparams=2 nindices=2
Acc.rec k=false levels=[u_1, u] nparams=2 nindices=1
And.rec k=false levels=[u] nparams=2 nindices=0
True.rec k=true levels=[u] nparams=0 nindices=0
False.rec k=false levels=[u] nparams=0 nindices=0
Nonempty.rec k=false levels=[u] nparams=1 nindices=0
Exists.rec k=false levels=[u] nparams=2 nindices=0
Iff.rec k=false levels=[u] nparams=2 nindices=0
Or.rec k=false levels=[] nparams=2 nindices=0
PUnit.rec k=false levels=[u_1, u] nparams=0 nindices=0
Subtype.rec k=false levels=[u_1, u] nparams=2 nindices=0
Eq levels=[u_1] ctors=[Eq.refl] isRec=false numNested=0
HEq levels=[u] ctors=[HEq.refl] isRec=false numNested=0
Acc levels=[u] ctors=[Acc.intro] isRec=true numNested=0
And levels=[] ctors=[And.intro] isRec=false numNested=0
True levels=[] ctors=[True.intro] isRec=false numNested=0
False levels=[] ctors=[] isRec=false numNested=0
Nonempty levels=[u] ctors=[Nonempty.intro] isRec=false numNested=0
Exists levels=[u] ctors=[Exists.intro] isRec=false numNested=0
Or levels=[] ctors=[Or.inl, Or.inr] isRec=false numNested=0
Iff levels=[] ctors=[Iff.intro] isRec=false numNested=0
Quot kind: (some quotInfo)
-/
