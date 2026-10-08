-- File: docs/foundations/probes/lean/Gcd.lean
-- WellFounded.Nat.fix at the pin, the failed rfl tests for the gcd equation on variables, String.mk; the two rfl errors are the intended rejections.
-- Run from translator/ as: lake env lean ../docs/foundations/probes/lean/Gcd.lean
import Lean
open Lean
#print WellFounded.Nat.fix
#print axioms WellFounded.Nat.fix
#check @WellFounded.Nat.fix_eq
#print Nat.gcd.eq_1
#print axioms Nat.gcd.eq_1
-- does the defining equation at a successor hold by conversion alone, with a variable?
set_option maxRecDepth 4000 in
example (x y : Nat) : Nat.gcd (x+1) y = Nat.gcd (y % (x+1)) (x+1) := by with_unfolding_all rfl
-- and the equation lemma itself, by conversion?
set_option maxRecDepth 4000 in
example (m n : Nat) : Nat.gcd m n = if m = 0 then n else Nat.gcd (n % m) m := by with_unfolding_all rfl
#print WellFounded.fix
#print axioms WellFounded.fix_eq
#print String.mk
#check @String.ofList
#eval show CoreM Unit from do
  let env ← getEnv
  for n in [``WellFounded.Nat.fix, ``WellFounded.fix, ``Nat.gcd, ``Nat.gcd._unary, ``String.mk, ``String.ofList] do
    match env.find? n with
    | some (.defnInfo v) => IO.println s!"{n}: def, uses {v.value.getUsedConstants.toList.take 12}"
    | some (.thmInfo _) => IO.println s!"{n}: theorem"
    | some _ => IO.println s!"{n}: other"
    | none => IO.println s!"{n}: missing"

/- Output on 2026-10-08 (Lean v4.33.1, Mathlib v4.33.1), from translator/ as
   lake env lean ../docs/foundations/probes/lean/Gcd.lean  (exit status 1, 1 s):
@[implicit_reducible] def WellFounded.Nat.fix.{u, v} : {α : Sort u} →
  {motive : α → Sort v} →
    (h : α → Nat) →
      ((x : α) → ((y : α) → InvImage (fun x1 x2 => x1 < x2) h y x → motive y) → motive x) → (x : α) → motive x :=
fun {α} {motive} h F x => WellFounded.Nat.fix.go h F (WellFounded.Nat.eager (h x + 1)) x ⋯
'WellFounded.Nat.fix' does not depend on any axioms
@WellFounded.Nat.fix_eq : ∀ {α : Sort u_1} {motive : α → Sort u_2} (h : α → Nat)
  (F : (x : α) → ((y : α) → InvImage (fun x1 x2 => x1 < x2) h y x → motive y) → motive x) (x : α),
  WellFounded.Nat.fix h F x = F x fun y x => WellFounded.Nat.fix h F y
theorem Nat.gcd.eq_1 : ∀ (m n : Nat), m.gcd n = if m = 0 then n else (n % m).gcd m :=
fun m n => Eq.trans (Nat.gcd.eq_def m n) (Eq.refl (if m = 0 then n else (n % m).gcd m))
'Nat.gcd.eq_1' depends on axioms: [Quot.sound]
../docs/foundations/probes/lean/Gcd.lean:13:91: error: Tactic `rfl` failed: The left-hand side
  (x + 1).gcd y
is not definitionally equal to the right-hand side
  (y % (x + 1)).gcd (x + 1)

x y : Nat
⊢ (x + 1).gcd y = (y % (x + 1)).gcd (x + 1)
../docs/foundations/probes/lean/Gcd.lean:16:100: error: Tactic `rfl` failed: The left-hand side
  m.gcd n
is not definitionally equal to the right-hand side
  if m = 0 then n else (n % m).gcd m

m n : Nat
⊢ m.gcd n = if m = 0 then n else (n % m).gcd m
def WellFounded.fix.{u, v} : {α : Sort u} →
  {C : α → Sort v} → {r : α → α → Prop} → WellFounded r → ((x : α) → ((y : α) → r y x → C y) → C x) → (x : α) → C x :=
fun {α} {C} {r} hwf F x => WellFounded.fixF F x ⋯
'WellFounded.fix_eq' does not depend on any axioms
def String.mk : List Char → String :=
fun data => { toByteArray := data.utf8Encode, isValidUTF8 := ⋯ }
String.ofList : List Char → String
WellFounded.Nat.fix: def, uses [Nat, InvImage, LT.lt, instLTNat, WellFounded.Nat.fix.go, WellFounded.Nat.eager, HAdd.hAdd, instHAdd, instAddNat, OfNat.ofNat, instOfNatNat, WellFounded.Nat.fix._proof_2]
WellFounded.fix: def, uses [WellFounded, WellFounded.fixF, WellFounded.apply]
Nat.gcd: def, uses [Nat, Nat.gcd._unary, PSigma.mk]
Nat.gcd._unary: def, uses [WellFounded.Nat.fix, PSigma, Nat, PSigma.casesOn, InvImage, LT.lt, instLTNat, PSigma.mk, dite, Eq, OfNat.ofNat, instOfNatNat]
String.mk: def, uses [List, Char, String.ofByteArray, List.utf8Encode, String.mk._proof_1]
String.ofList: def, uses [List, Char, String.ofByteArray, List.utf8Encode, String.ofList._proof_1]
-/
