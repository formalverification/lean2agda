/-
File: translator/Atlas/Collect.lean
-/
import Lean
import Atlas.AutoDecl
import Atlas.Record

/-!
# Atlas.Collect

The atlas's questions to an environment: the record of one constant, and
the order in which the constants are written.  Everything here reads an
environment `Atlas.Main` has imported, in `CoreM`; nothing writes.
-/

namespace Atlas

open Lean

/-- The module that declares `n`.  Every constant of an imported
environment has one; a constant added after the import would not. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames.getD idx.toNat .anonymous
  | none     => .anonymous

/-- Whether `n` is a `partial def`.  Lean compiles one to an `opaque`
constant that depends on no axiom and carries no `implemented_by`
attribute, beside a companion `n._unsafe_rec` whose safety is `partial`
(not `unsafe`); the companion is the reliable sign. -/
def isPartialDef (env : Environment) (n : Name) : ConstantInfo → Bool
  | .opaqueInfo _ => env.contains (n ++ `_unsafe_rec)
  | _             => false

/-- The record of the constant `n`, whose exact axiom set is `axioms`
(sorted); an error if `Lean.collectAxioms` names an axiom that `axioms`
lacks, which would mean the graph has lost an edge Lean follows. -/
def recordOf (n : Name) (ci : ConstantInfo) (axioms : Array Name) : CoreM Record := do
  let env ← getEnv
  let lean ← collectAxioms n
  let extra := lean.filter (!axioms.contains ·)
  unless extra.isEmpty do
    throwError "atlas: Lean's collectAxioms gives {n} the axioms {extra}, which the graph does not reach"
  return {
    name            := n
    module          := moduleOf env n
    kind            := kindOf ci
    axioms
    leanOmits       := axioms.filter (!lean.contains ·)
    isNoncomputable := isNoncomputable env n
    isUnsafe        := ci.isUnsafe
    isPartial       := isPartialDef env n ci
    isPrivate       := isPrivateName n
    isInternal      := n.isInternal
    isAuto          := isAutoDecl env n
  }

/-- Every constant of the environment, in the atlas's order (`sortNames`). -/
def constantsInOrder (env : Environment) : Array (Name × ConstantInfo) :=
  let all := env.constants.fold (fun acc n ci => acc.push (toString n, n, ci)) #[]
  all.qsort (·.1 < ·.1) |>.map (·.2)

end Atlas
