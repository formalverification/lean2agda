-- File: docs/foundations/probes/lean/NatOpsUses.lean
-- Which constants of Init the kernel unfolds an accelerated operation's definition for, by its diagnostics' counters.
-- Run from translator/ as: lake env lean ../docs/foundations/probes/lean/NatOpsUses.lean > uses.tsv
import Lean
open Lean

/-- The operations whose definitions the table replaces. -/
def targets : Array Name := #[``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.beq, ``Nat.ble,
  ``Nat.div.go, ``Nat.modCore.go, ``Nat.bitwise, ``Nat.shiftLeft, ``Nat.shiftRight]

/- Re-check every theorem and definition of the modules under `Init` with
the kernel's diagnostics on, and print, per constant, which targets the
kernel unfolded while checking it. -/
#eval show CoreM Unit from do
  let env ← getEnv
  let mut checked := 0
  let mut rejected := 0
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`Init).isPrefixOf m do continue
    let decl? := match ci with
      | .thmInfo v => some (Declaration.thmDecl { v with name := n ++ `_recheck })
      | .defnInfo v => if v.safety == DefinitionSafety.safe then some (Declaration.defnDecl { v with name := n ++ `_recheck }) else none
      | _ => none
    let some decl := decl? | continue
    checked := checked + 1
    match (env.toKernelEnv.enableDiag true).addDecl {} decl with
    | .error _ => rejected := rejected + 1
    | .ok kenv =>
      let hits := kenv.diagnostics.unfoldCounter.toList.filter fun (r, _) => targets.contains r
      unless hits.isEmpty do
        let kind := if ci matches .thmInfo _ then "theorem" else "definition"
        let ops := " ".intercalate (hits.map fun (r, k) => s!"{r}:{k}")
        lines := lines.push s!"{kind}\t{m}\t{n}\t{ops}"
  IO.println s!"# {checked} theorems and definitions of Init re-checked, {rejected} rejected"
  for l in lines.qsort (· < ·) do IO.println l

/- Output on 2026-11-10 (Lean v4.33.1), from translator/ as above (exit status 0, 91 s):
   its first line, then one tab-separated line per constant (kind, module, name, and
   each target the kernel unfolded with its count), 3,447 in all; the constants whose
   check unfolds each target, other than its own equation lemmas, number as follows:
   # 63034 theorems and definitions of Init re-checked, 0 rejected
   Nat.add: 2646 constants, 2205 of them theorems
   Nat.sub: 663 constants, 615 of them theorems
   Nat.mul: 178 constants, 160 of them theorems
   Nat.pow: 250 constants, 240 of them theorems
   Nat.beq: 331 constants, 311 of them theorems
   Nat.ble: 431 constants, 419 of them theorems
   Nat.div.go: 53 constants, 52 of them theorems
   Nat.modCore.go: 4 constants, 3 of them theorems
   Nat.bitwise: 167 constants, 167 of them theorems
   Nat.shiftLeft: 28 constants, 25 of them theorems
   Nat.shiftRight: 97 constants, 93 of them theorems
   In Init.Prelude and Init.Core, the constants that unfold Nat.sub are Nat.sub_le and
   Nat.succ_sub_succ_eq_sub; the four that unfold Nat.modCore.go are Nat.modCoreGo_lt
   and Nat.modCore_lt (Init.Prelude), Fin.castSucc_one and the private fuel_congr._f.
-/
