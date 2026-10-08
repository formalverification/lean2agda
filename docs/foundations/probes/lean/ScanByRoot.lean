-- File: docs/foundations/probes/lean/ScanByRoot.lean
-- The same scan's hatch counts per module root, and every Mathlib constant depending on a non-standard axiom.  Needs Mathlib's cache.
-- Run from translator/ as: lake env lean ../docs/foundations/probes/lean/ScanByRoot.lean
import Mathlib
open Lean

def modNameOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => Name.anonymous

def rootOf (m : Name) : String :=
  match m.components with
  | r :: _ => toString r
  | [] => "<none>"

def isStdAxiom (a : Name) : Bool := a == ``propext || a == ``Quot.sound || a == ``Classical.choice

structure Counts where
  constants : Nat := 0
  unsafeC : Nat := 0
  partialC : Nat := 0
  implBy : Nat := 0
  noncomp : Nat := 0
  t3 : Nat := 0
  deriving Inhabited

#eval show CoreM Unit from do
  let env ← getEnv
  let mut byRoot : Std.HashMap String Counts := {}
  let mut mathlibT3 : Array String := #[]
  for (n, ci) in env.constants.toList do
    let m := modNameOf env n
    let r := rootOf m
    let mut c := byRoot.getD r {}
    c := { c with constants := c.constants + 1 }
    if ci.isUnsafe then c := { c with unsafeC := c.unsafeC + 1 }
    if isNoncomputable env n then c := { c with noncomp := c.noncomp + 1 }
    if (Compiler.getImplementedBy? env n).isSome then c := { c with implBy := c.implBy + 1 }
    if let .opaqueInfo _ := ci then
      if env.contains (n ++ `_unsafe_rec) then c := { c with partialC := c.partialC + 1 }
    let axs ← collectAxioms n
    let bad := axs.filter (fun a => !isStdAxiom a)
    if !bad.isEmpty then
      c := { c with t3 := c.t3 + 1 }
      if r == "Mathlib" then mathlibT3 := mathlibT3.push s!"{n} ({m}) {bad}"
    byRoot := byRoot.insert r c
  IO.println "root constants unsafe partial implemented_by noncomputable nonstandard-axiom"
  for (r, c) in byRoot.toList.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"{r} {c.constants} {c.unsafeC} {c.partialC} {c.implBy} {c.noncomp} {c.t3}"
  IO.println s!"--- Mathlib constants depending on a non-standard axiom ({mathlibT3.size}) ---"
  for s in mathlibT3.qsort (· < ·) do IO.println s

/- Output on 2026-10-07 (Lean v4.33.1, Mathlib v4.33.1):
root constants unsafe partial implemented_by noncomputable nonstandard-axiom
<none> 34 0 0 0 0 0
Aesop 6504 120 60 15 0 6
Batteries 10138 50 62 11 3 12
ImportGraph 91 0 3 0 0 0
Init 65994 77 52 41 238 62
Lake 7 0 0 0 0 0
Lean 65486 375 979 222 2 117
LeanSearchClient 202 0 0 0 0 0
Mathlib 569189 68 266 28 15734 41
Plausible 618 2 3 2 0 0
ProofWidgets 1182 6 4 6 0 3
Qq 633 2 22 2 0 0
Std 51085 14 57 14 44 14
--- Mathlib constants depending on a non-standard axiom (41) ---
CauSeq.Completion.instReprCauchy (Mathlib.Algebra.Order.CauSeq.Completion) #[lcProof]
Complex.instRepr (Mathlib.Data.Complex.Basic) #[lcProof]
Cycle.instRepr (Mathlib.Data.List.Cycle) #[lcProof]
DFinsupp.instRepr (Mathlib.Data.DFinsupp.Notation) #[lcProof]
Equiv.Perm.instRepr (Mathlib.GroupTheory.Perm.Cycle.Concrete) #[lcProof]
FP.Float.add (Mathlib.Data.FP.Basic) #[lcProof]
FP.Float.div (Mathlib.Data.FP.Basic) #[lcProof]
FP.Float.instAdd (Mathlib.Data.FP.Basic) #[lcProof]
FP.Float.instSub (Mathlib.Data.FP.Basic) #[lcProof]
FP.Float.mul (Mathlib.Data.FP.Basic) #[lcProof]
FP.Float.sub (Mathlib.Data.FP.Basic) #[lcProof]
FP.nextDn (Mathlib.Data.FP.Basic) #[lcProof]
FP.nextDnPos (Mathlib.Data.FP.Basic) #[lcProof]
FP.nextDnPos._proof_1 (Mathlib.Data.FP.Basic) #[lcProof]
FP.nextDnPos._proof_2 (Mathlib.Data.FP.Basic) #[lcProof]
FP.nextUp (Mathlib.Data.FP.Basic) #[lcProof]
FP.nextUpPos (Mathlib.Data.FP.Basic) #[lcProof]
FP.nextUpPos._proof_2 (Mathlib.Data.FP.Basic) #[lcProof]
FP.ofPosRatDn (Mathlib.Data.FP.Basic) #[lcProof]
FP.ofPosRatDn._proof_1 (Mathlib.Data.FP.Basic) #[lcProof]
FP.ofRat (Mathlib.Data.FP.Basic) #[lcProof]
FP.ofRatDn (Mathlib.Data.FP.Basic) #[lcProof]
FP.ofRatUp (Mathlib.Data.FP.Basic) #[lcProof]
Finset.instRepr (Mathlib.Data.Finset.Sort) #[lcProof]
Finsupp.instRepr (Mathlib.Data.Finsupp.Notation) #[lcProof]
Multiset.instRepr (Mathlib.Data.Multiset.Sort) #[lcProof]
Multiset.instToExprOfToLevel (Mathlib.Data.Multiset.Sort) #[lcProof]
Part.unwrap (Mathlib.Data.Part) #[lcProof]
Part.unwrap._proof_1 (Mathlib.Data.Part) #[lcProof]
PrimeMultiset.instRepr (Mathlib.Data.PNat.Factors) #[lcProof]
Quot.unquot (Mathlib.Data.Quot) #[lcProof]
Quot.unquot._proof_1 (Mathlib.Data.Quot) #[lcProof]
Real.instRepr (Mathlib.Data.Real.Basic) #[lcProof]
Sym2.instRepr (Mathlib.Data.Sym.Sym2) #[lcProof]
TensorProduct.instRepr (Mathlib.LinearAlgebra.TensorProduct.Defs) #[lcProof]
_private.Mathlib.Tactic.Simproc.Divisors.0.Nat.divisors_ofNat.unsafe_1 (Mathlib.Tactic.Simproc.Divisors) #[lcProof]
_private.Mathlib.Tactic.Simproc.Divisors.0.Nat.properDivisors_ofNat.unsafe_1 (Mathlib.Tactic.Simproc.Divisors) #[lcProof]
_private.Mathlib.Util.MemoFix.0.memoFixImpl (Mathlib.Util.MemoFix) #[lcProof]
_private.Mathlib.Util.MemoFix.0.memoFixImpl.fix (Mathlib.Util.MemoFix) #[lcProof]
instReprENNReal (Mathlib.Data.ENNReal.Basic) #[lcProof]
instReprNNReal (Mathlib.Data.NNReal.Defs) #[lcProof]
-/
