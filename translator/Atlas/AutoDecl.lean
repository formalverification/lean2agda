/-
File: translator/Atlas/AutoDecl.lean

Copyright (c) 2020 Floris van Doorn.  Released under Apache 2.0 license.
Authors: Floris van Doorn, Robert Y. Lewis, Gabriel Ebner.
Adapted from Batteries (https://github.com/leanprover-community/batteries),
`Batteries/Tactic/Lint/Basic.lean` at commit 4488d40, the revision
`translator/lake-manifest.json` pins: `Lean.Environment.isAutoDecl`,
renamed `Atlas.isAutoDecl`, otherwise unchanged.  See NOTICE.
-/
import Lean

/-!
# Atlas.AutoDecl

Which constants are auto-generated: the test of Batteries' linter
framework, which Mathlib's `#lint` runs.  It is Lean's
`isAutoDeclOrPrivate_Internal` (`Lean/AutoDecl.lean`) except that a
private name is judged by the name it was written with, so that a
private lemma written by hand is not counted as generated; Lean's test
is this one or `isPrivateName`.

The atlas imports Lean only, not Batteries, so the function is copied
here.  When the pins move, compare it with Batteries' at the new
revision (`docs/pinning.md` lists the atlas among what moves).
-/

namespace Atlas

open Lean

/-- Whether `decl` is an automatically generated declaration, or an
internal name, or one created during macro expansion, after its private
mangling is removed. -/
partial def isAutoDecl (env : Environment) (decl : Name) : Bool := Id.run do
  let declUserName := privateToUserName decl
  if declUserName.hasMacroScopes || declUserName.isInternal then return true
  if isReservedName env decl then return true
  if let Name.str n s := decl then
    if isAutoDecl env n then return true
    if s.startsWith "proof_"
        || s.startsWith "match_"
        || s.startsWith "unsafe_"
        || s.startsWith "grind_"
    then return true
    if env.isConstructor n && s ∈ ["injEq", "inj", "sizeOf_spec", "elim", "noConfusion"] then
      return true
    if let ConstantInfo.inductInfo _ := env.find? n then
      if s.startsWith "brecOn_" || s.startsWith "below_" then return true
      if s ∈ [casesOnSuffix, recOnSuffix, brecOnSuffix, belowSuffix,
          "ndrec", "ndrecOn", "noConfusionType", "noConfusion", "ofNat", "toCtorIdx", "ctorIdx",
          "ctorElim", "ctorElimType"] then
        return true
      if let some _ := isSubobjectField? env n (.mkSimple s) then
        return true
    -- Coinductive/inductive lattice-theoretic predicates:
    if let ConstantInfo.inductInfo _ := env.find? (Name.str n "_functor") then
      if s == "functor_unfold" || s == casesOnSuffix || s == "mutual" then return true
      if env.isConstructor (Name.str (Name.str n "_functor") s) then return true
  pure false

end Atlas
