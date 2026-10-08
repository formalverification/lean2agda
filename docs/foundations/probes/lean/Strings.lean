-- File: docs/foundations/probes/lean/Strings.lean
-- String and Char at the pin, the deprecation warnings, Lists'.Subset and Lists.Equiv, Nat.gcd_succ.
-- Run from translator/ as: lake env lean ../docs/foundations/probes/lean/Strings.lean
import Mathlib.SetTheory.Lists
open Lean
-- String and Char at the pin, the deprecation warnings of the native-reduction family,
-- the one mutual inductive block in Mathlib's mathematics, and Nat.gcd_succ.
#print String
#check @String.ofList
#print String.mk
#print Char
#print Lean.Syntax
set_option linter.deprecated true in
example : Lean.trustCompiler = Lean.trustCompiler := rfl
set_option linter.deprecated true in
example : @Lean.ofReduceNat = @Lean.ofReduceNat := rfl
#print axioms Classical.decEq
#print Decidable
#check @Decidable.decide
#print Lists'.Subset
#print Lists.Equiv
#print Nat.gcd_succ
#print axioms Nat.gcd_succ
#print axioms Nat.gcd
#print Nat.gcd._unary
#eval show CoreM Unit from do
  let env ← getEnv
  for n in [``Lists'.Subset, ``Lists.Equiv, ``Lean.Syntax, ``String] do
    match env.find? n with
    | some (.inductInfo v) => IO.println s!"{n}: inductive numNested={v.numNested} all={v.all} isRec={v.isRec}"
    | some _ => IO.println s!"{n}: other"
    | none => IO.println s!"{n}: missing"

/- Output on 2026-10-08 (Lean v4.33.1, Mathlib v4.33.1), from translator/ as
   lake env lean ../docs/foundations/probes/lean/Strings.lean  (exit status 0, 1 s):
structure String : Type
number of parameters: 0
fields:
  String.toByteArray : ByteArray
  String.isValidUTF8 : self.toByteArray.IsValidUTF8
constructor:
  String.ofByteArray (toByteArray : ByteArray) (isValidUTF8 : toByteArray.IsValidUTF8) : String
String.ofList : List Char → String
def String.mk : List Char → String :=
fun data => { toByteArray := data.utf8Encode, isValidUTF8 := ⋯ }
structure Char : Type
number of parameters: 0
fields:
  Char.val : UInt32
  Char.valid : self.val.isValidChar
constructor:
  Char.mk (val : UInt32) (valid : val.isValidChar) : Char
inductive Lean.Syntax : Type
number of parameters: 0
constructors:
Lean.Syntax.missing : Syntax
Lean.Syntax.node : SourceInfo → SyntaxNodeKind → Array Syntax → Syntax
Lean.Syntax.atom : SourceInfo → String → Syntax
Lean.Syntax.ident : SourceInfo → Substring.Raw → Name → List Syntax.Preresolved → Syntax
../docs/foundations/probes/lean/Strings.lean:14:10: warning: `Lean.trustCompiler` has been deprecated: in-kernel native reduction is deprecated; assert native evaluations with axioms instead
../docs/foundations/probes/lean/Strings.lean:14:31: warning: `Lean.trustCompiler` has been deprecated: in-kernel native reduction is deprecated; assert native evaluations with axioms instead
../docs/foundations/probes/lean/Strings.lean:16:11: warning: `Lean.ofReduceNat` has been deprecated: in-kernel native reduction is deprecated; assert native evaluations with axioms instead
../docs/foundations/probes/lean/Strings.lean:16:31: warning: `Lean.ofReduceNat` has been deprecated: in-kernel native reduction is deprecated; assert native evaluations with axioms instead
'Classical.decEq' depends on axioms: [propext, Classical.choice, Quot.sound]
inductive Decidable : Prop → Type
number of parameters: 1
constructors:
Decidable.isFalse : {p : Prop} → ¬p → Decidable p
Decidable.isTrue : {p : Prop} → p → Decidable p
decide : (p : Prop) → [h : Decidable p] → Bool
inductive Lists'.Subset.{u_1} : {α : Type u_1} → Lists' α true → Lists' α true → Prop
number of parameters: 1
constructors:
Lists'.Subset.nil : ∀ {α : Type u_1} {l : Lists' α true}, Lists'.nil.Subset l
Lists'.Subset.cons : ∀ {α : Type u_1} {a a' : Lists α} {l l' : Lists' α true},
  a.Equiv a' → a' ∈ l'.toList → l.Subset l' → (Lists'.cons a l).Subset l'
inductive Lists.Equiv.{u_1} : {α : Type u_1} → Lists α → Lists α → Prop
number of parameters: 1
constructors:
Lists.Equiv.refl : ∀ {α : Type u_1} (l : Lists α), l.Equiv l
Lists.Equiv.antisymm : ∀ {α : Type u_1} {l₁ l₂ : Lists' α true},
  l₁.Subset l₂ → l₂.Subset l₁ → Lists.Equiv ⟨true, l₁⟩ ⟨true, l₂⟩
theorem Nat.gcd_succ : ∀ (x y : ℕ), x.succ.gcd y = (y % x.succ).gcd x.succ :=
fun x y =>
  Eq.mpr (id (congrArg (fun _a => _a = (y % x.succ).gcd x.succ) (Nat.gcd.eq_1✝ x.succ y)))
    (Eq.refl (if x.succ = 0 then y else (y % x.succ).gcd x.succ))
'Nat.gcd_succ' depends on axioms: [Quot.sound]
'Nat.gcd' does not depend on any axioms
def Nat.gcd._unary : (_ : ℕ) ×' ℕ → ℕ :=
WellFounded.Nat.fix (fun x => PSigma.casesOn x fun m n => m) fun _x a =>
  PSigma.casesOn (motive := fun _x =>
    ((y : (_ : ℕ) ×' ℕ) → InvImage (fun x1 x2 => x1 < x2) (fun x => PSigma.casesOn x fun m n => m) y _x → ℕ) → ℕ) _x
    (fun m n a => if h : m = 0 then n else a ⟨n % m, m⟩ ⋯) a
Lists'.Subset: inductive numNested=0 all=[Lists.Equiv, Lists'.Subset] isRec=true
Lists.Equiv: inductive numNested=0 all=[Lists.Equiv, Lists'.Subset] isRec=true
Lean.Syntax: inductive numNested=2 all=[Lean.Syntax] isRec=true
String: inductive numNested=0 all=[String] isRec=false
-/
