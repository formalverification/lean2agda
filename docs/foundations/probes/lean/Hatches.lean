-- File: docs/foundations/probes/lean/Hatches.lean
-- The trust escape hatches at the pin: sorryAx, the native-reduction family, lcProof, native_decide, partial, unsafe.
-- Run from translator/ as: lake env lean ../docs/foundations/probes/lean/Hatches.lean
import Lean
open Lean
-- The trust escape hatches at the pin.
#print sorryAx
#print Lean.ofReduceBool
#print Lean.trustCompiler
#check Lean.ofReduceNat
set_option linter.deprecated true in
example : Lean.trustCompiler = Lean.trustCompiler := rfl
#print lcProof
theorem nd : 2 ^ 10 = 1024 := by native_decide
#print axioms nd
partial def loop (n : Nat) : Nat := loop (n+1)
#print loop
#print axioms loop
#print loop._unsafe_rec
unsafe def u1 : Nat := 0
#print u1
#eval show CoreM Unit from do
  let env ← getEnv
  IO.println s!"loop implemented_by: {Compiler.getImplementedBy? env ``loop}"
  IO.println s!"loop._unsafe_rec present: {env.contains (``loop ++ `_unsafe_rec)}"
  IO.println s!"Classical.propDecidable noncomputable: {isNoncomputable env ``Classical.propDecidable}"

/- Output on 2026-10-08 (Lean v4.33.1, Mathlib v4.33.1), from translator/ as
   lake env lean ../docs/foundations/probes/lean/Hatches.lean  (exit status 0, 1 s):
axiom sorryAx.{u} : (α : Sort u) → Bool → α
axiom Lean.ofReduceBool : ∀ (a b : Bool), reduceBool a = b → a = b
axiom Lean.trustCompiler : True
Lean.ofReduceNat (a b : Nat) (h : reduceNat a = b) : a = b
../docs/foundations/probes/lean/Hatches.lean:12:10: warning: `Lean.trustCompiler` has been deprecated: in-kernel native reduction is deprecated; assert native evaluations with axioms instead
../docs/foundations/probes/lean/Hatches.lean:12:31: warning: `Lean.trustCompiler` has been deprecated: in-kernel native reduction is deprecated; assert native evaluations with axioms instead
unsafe axiom lcProof : ∀ {α : Prop}, α
'nd' depends on axioms: [nd._native.native_decide.ax_1_1]
opaque loop : Nat → Nat
'loop' does not depend on any axioms
partial def loop._unsafe_rec : Nat → Nat :=
fun n => loop._unsafe_rec (n + 1)
unsafe def u1 : Nat :=
0
loop implemented_by: none
loop._unsafe_rec present: true
Classical.propDecidable noncomputable: true
-/
