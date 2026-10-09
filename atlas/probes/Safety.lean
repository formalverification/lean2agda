/-
File: atlas/probes/Safety.lean

Whether the kernel's safety separation holds over the environment of
`import Mathlib`, for the Mathlib of any checkout.  Run it as the other
probes are run (`../README.md`, "Probes"):

    lake env lean /path/to/atlas/probes/Safety.lean

The kernel checks a declaration once, when it is added; a module that
imports an `.olean` does not check its declarations again.  A safe
declaration must use only safe ones, and a `partial` one no `unsafe`
one.  The probe counts the imported constants by safety
(`DefinitionVal.safety` for a definition, `ConstantInfo.isUnsafe` for the
other kinds), then lists every safe or `partial` constant whose type,
value or constructors use a constant of a safety it may not use, and
the safety of the `_unsafe_rec` companions; the count of edges between
each pair of safeties shows that the scan sees the edges a violation
would be.  At Lean v4.33.1 and Mathlib
v4.33.1 (2026-10-08) it found no such use (`docs/lean-findings.md`,
LF-3).
-/
import Mathlib

open Lean Elab Command

/-- The constants the kernel checks a declaration against: those its type
and value use, and an inductive type's constructors. -/
def safetyDeps : ConstantInfo → Array Name
  | .axiomInfo v  => v.type.getUsedConstants
  | .defnInfo v   => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v    => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _   => #[]
  | .ctorInfo v   => v.type.getUsedConstants
  | .recInfo v    => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- `"unsafe"`, `"partial"` or `"safe"`: a definition's own safety, and
`isUnsafe` for every other kind of constant. -/
def safetyOf : ConstantInfo → String
  | .defnInfo v => match v.safety with
    | .unsafe => "unsafe"
    | .partial => "partial"
    | .safe => "safe"
  | ci => if ci.isUnsafe then "unsafe" else "safe"

/-- Whether a constant of safety `user` may use one of safety `used`. -/
def mayUse (user used : String) : Bool :=
  user == "unsafe" || used == "safe" || (user == "partial" && used == "partial")

elab "#safety" : command => do
  let env ← getEnv
  let consts := env.constants.toList.toArray.filter fun (n, _) => (env.getModuleIdxFor? n).isSome
  let mut bySafety : Std.HashMap String Nat := {}
  let mut companions : Std.HashMap String Nat := {}
  let mut violations : Array String := #[]
  -- Every edge by the safety of its two ends: the control that shows the
  -- scan sees edges between different safeties, which a zero needs.
  let mut pairs : Std.HashMap String Nat := {}
  for (n, ci) in consts do
    let s := safetyOf ci
    bySafety := bySafety.insert s (bySafety.getD s 0 + 1)
    if let .str _ "_unsafe_rec" := n then
      companions := companions.insert s (companions.getD s 0 + 1)
    for d in safetyDeps ci do
      if let some dci := env.find? d then
        let pair := s!"{s} uses {safetyOf dci}"
        pairs := pairs.insert pair (pairs.getD pair 0 + 1)
        unless mayUse s (safetyOf dci) do
          violations := violations.push s!"{s} {n} uses {safetyOf dci} {d}"
  logInfo m!"imported constants {consts.size}; by safety {bySafety.toList}"
  logInfo m!"_unsafe_rec companions by safety {companions.toList}"
  logInfo m!"edges by safety: {pairs.toList}"
  logInfo m!"uses the kernel forbids: {violations.size}"
  for v in violations[0:20] do
    logInfo v

#safety
