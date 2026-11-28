{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.CompleteLattice.Defs
module U.Mathlib.Order.CompleteLattice.Defs where
import U.Init.Core
import U.Init.Prelude
import U.Mathlib.Data.~sSet.Defs
import U.Mathlib.Order.BoundedOrder.Basic
import U.Mathlib.Order.Bounds.Basic
import U.Mathlib.Order.Bounds.Defs
import U.Mathlib.Order.Defs.PartialOrder
import U.Mathlib.Order.Lattice
import U.Mathlib.Order.SetNotation

record CompleteLattice (α₀ : Set) : Set where
  constructor CompleteLattice:mk
  field
    ⦃ toLattice₁ ⦄ : U.Mathlib.Order.Lattice.Lattice α₀
    ⦃ toSupSet₂ ⦄ : U.Mathlib.Order.SetNotation.SupSet α₀
    isLUBsSup₃ : (s₃ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsLUB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ U.Mathlib.Order.Lattice.SemilatticeSup:toPartialOrder {α₀} ⦃ U.Mathlib.Order.Lattice.Lattice:toSemilatticeSup {α₀} ⦃ toLattice₁ ⦄ ⦄ ⦄ ⦄ ⦄ s₃ (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ toSupSet₂ ⦄ s₃)
    ⦃ toInfSet₄ ⦄ : U.Mathlib.Order.SetNotation.InfSet α₀
    isGLBsInf₅ : (s₅ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsGLB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ U.Mathlib.Order.Lattice.SemilatticeSup:toPartialOrder {α₀} ⦃ U.Mathlib.Order.Lattice.Lattice:toSemilatticeSup {α₀} ⦃ toLattice₁ ⦄ ⦄ ⦄ ⦄ ⦄ s₅ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ toInfSet₄ ⦄ s₅)
    ⦃ toBoundedOrder₆ ⦄ : U.Mathlib.Order.BoundedOrder.Basic.BoundedOrder α₀ ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ U.Mathlib.Order.Lattice.SemilatticeSup:toPartialOrder {α₀} ⦃ U.Mathlib.Order.Lattice.Lattice:toSemilatticeSup {α₀} ⦃ toLattice₁ ⦄ ⦄ ⦄ ⦄ ⦄

-- recursor
CompleteLattice:rec : {α₀ : Set} → {motive₁ : CompleteLattice α₀ → Set} → (⦃ toLattice₂ : U.Mathlib.Order.Lattice.Lattice α₀ ⦄ → ⦃ toSupSet₃ : U.Mathlib.Order.SetNotation.SupSet α₀ ⦄ → (isLUBsSup₄ : (s₄ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsLUB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ U.Mathlib.Order.Lattice.SemilatticeSup:toPartialOrder {α₀} ⦃ U.Mathlib.Order.Lattice.Lattice:toSemilatticeSup {α₀} ⦃ toLattice₂ ⦄ ⦄ ⦄ ⦄ ⦄ s₄ (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ toSupSet₃ ⦄ s₄)) → ⦃ toInfSet₅ : U.Mathlib.Order.SetNotation.InfSet α₀ ⦄ → (isGLBsInf₆ : (s₆ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsGLB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ U.Mathlib.Order.Lattice.SemilatticeSup:toPartialOrder {α₀} ⦃ U.Mathlib.Order.Lattice.Lattice:toSemilatticeSup {α₀} ⦃ toLattice₂ ⦄ ⦄ ⦄ ⦄ ⦄ s₆ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ toInfSet₅ ⦄ s₆)) → ⦃ toBoundedOrder₇ : U.Mathlib.Order.BoundedOrder.Basic.BoundedOrder α₀ ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ U.Mathlib.Order.Lattice.SemilatticeSup:toPartialOrder {α₀} ⦃ U.Mathlib.Order.Lattice.Lattice:toSemilatticeSup {α₀} ⦃ toLattice₂ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ → motive₁ (CompleteLattice:mk {α₀} ⦃ toLattice₂ ⦄ ⦃ toSupSet₃ ⦄ isLUBsSup₄ ⦃ toInfSet₅ ⦄ isGLBsInf₆ ⦃ toBoundedOrder₇ ⦄)) → (t₂ : CompleteLattice α₀) → motive₁ t₂
CompleteLattice:rec {α₀} {motive₁} mk₂ (CompleteLattice:mk ⦃ toLattice₃ ⦄ ⦃ toSupSet₄ ⦄ isLUBsSup₅ ⦃ toInfSet₆ ⦄ isGLBsInf₇ ⦃ toBoundedOrder₈ ⦄) = mk₂ ⦃ toLattice₃ ⦄ ⦃ toSupSet₄ ⦄ isLUBsSup₅ ⦃ toInfSet₆ ⦄ isGLBsInf₇ ⦃ toBoundedOrder₈ ⦄

CompleteLattice:toInfSet : {α₀ : Set} → ⦃ _ : CompleteLattice α₀ ⦄ → U.Mathlib.Order.SetNotation.InfSet α₀
CompleteLattice:toInfSet {α₀} ⦃ self₁ ⦄ = CompleteLattice.toInfSet₄ {α₀} self₁

CompleteLattice:toLattice : {α₀ : Set} → ⦃ _ : CompleteLattice α₀ ⦄ → U.Mathlib.Order.Lattice.Lattice α₀
CompleteLattice:toLattice {α₀} ⦃ self₁ ⦄ = CompleteLattice.toLattice₁ {α₀} self₁

-- theorem
opaque
  CompleteLattice:isGLB~usInf : {α₀ : Set} → ⦃ self₁ : CompleteLattice α₀ ⦄ → (s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsGLB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ U.Mathlib.Order.Lattice.SemilatticeSup:toPartialOrder {α₀} ⦃ U.Mathlib.Order.Lattice.Lattice:toSemilatticeSup {α₀} ⦃ CompleteLattice:toLattice {α₀} ⦃ self₁ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ s₂ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteLattice:toInfSet {α₀} ⦃ self₁ ⦄ ⦄ s₂)
  CompleteLattice:isGLB~usInf {α₀} ⦃ self₁ ⦄ = CompleteLattice.isGLBsInf₅ {α₀} self₁

record CompleteSemilatticeInf (α₀ : Set) : Set where
  constructor CompleteSemilatticeInf:mk
  field
    ⦃ toPartialOrder₁ ⦄ : U.Mathlib.Order.Defs.PartialOrder.PartialOrder α₀
    ⦃ toInfSet₂ ⦄ : U.Mathlib.Order.SetNotation.InfSet α₀
    isGLBsInf₃ : (s₃ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsGLB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₁ ⦄ ⦄ ⦄ s₃ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ toInfSet₂ ⦄ s₃)

-- recursor
CompleteSemilatticeInf:rec : {α₀ : Set} → {motive₁ : CompleteSemilatticeInf α₀ → Set} → (⦃ toPartialOrder₂ : U.Mathlib.Order.Defs.PartialOrder.PartialOrder α₀ ⦄ → ⦃ toInfSet₃ : U.Mathlib.Order.SetNotation.InfSet α₀ ⦄ → (isGLBsInf₄ : (s₄ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsGLB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₂ ⦄ ⦄ ⦄ s₄ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ toInfSet₃ ⦄ s₄)) → motive₁ (CompleteSemilatticeInf:mk {α₀} ⦃ toPartialOrder₂ ⦄ ⦃ toInfSet₃ ⦄ isGLBsInf₄)) → (t₂ : CompleteSemilatticeInf α₀) → motive₁ t₂
CompleteSemilatticeInf:rec {α₀} {motive₁} mk₂ (CompleteSemilatticeInf:mk ⦃ toPartialOrder₃ ⦄ ⦃ toInfSet₄ ⦄ isGLBsInf₅) = mk₂ ⦃ toPartialOrder₃ ⦄ ⦃ toInfSet₄ ⦄ isGLBsInf₅

CompleteLattice:toCompleteSemilatticeInf : {α₀ : Set} → ⦃ _ : CompleteLattice α₀ ⦄ → CompleteSemilatticeInf α₀
CompleteLattice:toCompleteSemilatticeInf {α₀} ⦃ self₁ ⦄ = CompleteSemilatticeInf:mk {α₀} ⦃ U.Mathlib.Order.Lattice.SemilatticeSup:toPartialOrder {α₀} ⦃ U.Mathlib.Order.Lattice.Lattice:toSemilatticeSup {α₀} ⦃ CompleteLattice:toLattice {α₀} ⦃ self₁ ⦄ ⦄ ⦄ ⦄ ⦃ CompleteLattice:toInfSet {α₀} ⦃ self₁ ⦄ ⦄ (CompleteLattice:isGLB~usInf {α₀} ⦃ self₁ ⦄)

CompleteLattice:toSupSet : {α₀ : Set} → ⦃ _ : CompleteLattice α₀ ⦄ → U.Mathlib.Order.SetNotation.SupSet α₀
CompleteLattice:toSupSet {α₀} ⦃ self₁ ⦄ = CompleteLattice.toSupSet₂ {α₀} self₁

-- theorem
opaque
  CompleteLattice:isLUB~usSup : {α₀ : Set} → ⦃ self₁ : CompleteLattice α₀ ⦄ → (s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsLUB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ U.Mathlib.Order.Lattice.SemilatticeSup:toPartialOrder {α₀} ⦃ U.Mathlib.Order.Lattice.Lattice:toSemilatticeSup {α₀} ⦃ CompleteLattice:toLattice {α₀} ⦃ self₁ ⦄ ⦄ ⦄ ⦄ ⦄ ⦄ s₂ (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ CompleteLattice:toSupSet {α₀} ⦃ self₁ ⦄ ⦄ s₂)
  CompleteLattice:isLUB~usSup {α₀} ⦃ self₁ ⦄ = CompleteLattice.isLUBsSup₃ {α₀} self₁

record CompleteSemilatticeSup (α₀ : Set) : Set where
  constructor CompleteSemilatticeSup:mk
  field
    ⦃ toPartialOrder₁ ⦄ : U.Mathlib.Order.Defs.PartialOrder.PartialOrder α₀
    ⦃ toSupSet₂ ⦄ : U.Mathlib.Order.SetNotation.SupSet α₀
    isLUBsSup₃ : (s₃ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsLUB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₁ ⦄ ⦄ ⦄ s₃ (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ toSupSet₂ ⦄ s₃)

-- recursor
CompleteSemilatticeSup:rec : {α₀ : Set} → {motive₁ : CompleteSemilatticeSup α₀ → Set} → (⦃ toPartialOrder₂ : U.Mathlib.Order.Defs.PartialOrder.PartialOrder α₀ ⦄ → ⦃ toSupSet₃ : U.Mathlib.Order.SetNotation.SupSet α₀ ⦄ → (isLUBsSup₄ : (s₄ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsLUB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₂ ⦄ ⦄ ⦄ s₄ (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ toSupSet₃ ⦄ s₄)) → motive₁ (CompleteSemilatticeSup:mk {α₀} ⦃ toPartialOrder₂ ⦄ ⦃ toSupSet₃ ⦄ isLUBsSup₄)) → (t₂ : CompleteSemilatticeSup α₀) → motive₁ t₂
CompleteSemilatticeSup:rec {α₀} {motive₁} mk₂ (CompleteSemilatticeSup:mk ⦃ toPartialOrder₃ ⦄ ⦃ toSupSet₄ ⦄ isLUBsSup₅) = mk₂ ⦃ toPartialOrder₃ ⦄ ⦃ toSupSet₄ ⦄ isLUBsSup₅

CompleteLattice:toCompleteSemilatticeSup : {α₀ : Set} → ⦃ _ : CompleteLattice α₀ ⦄ → CompleteSemilatticeSup α₀
CompleteLattice:toCompleteSemilatticeSup {α₀} ⦃ self₁ ⦄ = CompleteSemilatticeSup:mk {α₀} ⦃ U.Mathlib.Order.Lattice.SemilatticeSup:toPartialOrder {α₀} ⦃ U.Mathlib.Order.Lattice.Lattice:toSemilatticeSup {α₀} ⦃ CompleteLattice:toLattice {α₀} ⦃ self₁ ⦄ ⦄ ⦄ ⦄ ⦃ CompleteLattice:toSupSet {α₀} ⦃ self₁ ⦄ ⦄ (CompleteLattice:isLUB~usSup {α₀} ⦃ self₁ ⦄)

CompleteSemilatticeInf:toPartialOrder : {α₀ : Set} → ⦃ _ : CompleteSemilatticeInf α₀ ⦄ → U.Mathlib.Order.Defs.PartialOrder.PartialOrder α₀
CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ self₁ ⦄ = CompleteSemilatticeInf.toPartialOrder₁ {α₀} self₁

CompleteSemilatticeSup:toPartialOrder : {α₀ : Set} → ⦃ _ : CompleteSemilatticeSup α₀ ⦄ → U.Mathlib.Order.Defs.PartialOrder.PartialOrder α₀
CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ self₁ ⦄ = CompleteSemilatticeSup.toPartialOrder₁ {α₀} self₁

CompleteSemilatticeSup:toSupSet : {α₀ : Set} → ⦃ _ : CompleteSemilatticeSup α₀ ⦄ → U.Mathlib.Order.SetNotation.SupSet α₀
CompleteSemilatticeSup:toSupSet {α₀} ⦃ self₁ ⦄ = CompleteSemilatticeSup.toSupSet₂ {α₀} self₁

-- theorem
opaque
  CompleteSemilatticeSup:isLUB~usSup : {α₀ : Set} → ⦃ self₁ : CompleteSemilatticeSup α₀ ⦄ → (s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsLUB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ self₁ ⦄ ⦄ ⦄ ⦄ s₂ (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ CompleteSemilatticeSup:toSupSet {α₀} ⦃ self₁ ⦄ ⦄ s₂)
  CompleteSemilatticeSup:isLUB~usSup {α₀} ⦃ self₁ ⦄ = CompleteSemilatticeSup.isLUBsSup₃ {α₀} self₁

-- theorem
opaque
  isLUB~usSup : {α₀ : Set} → ⦃ inst₁ : CompleteSemilatticeSup α₀ ⦄ → (s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsLUB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ s₂ (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ CompleteSemilatticeSup:toSupSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)
  isLUB~usSup {α₀} ⦃ inst₁ ⦄ s₂ = CompleteSemilatticeSup:isLUB~usSup {α₀} ⦃ inst₁ ⦄ s₂

-- theorem
opaque
  le~usSup : {α₀ : Set} → ⦃ inst₁ : CompleteSemilatticeSup α₀ ⦄ → {s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀} → {a₃ : α₀} → U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₂ a₃ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ a₃ (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ CompleteSemilatticeSup:toSupSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)
  le~usSup {α₀} ⦃ inst₁ ⦄ {s₂} {a₃} h₄ = U.Init.Prelude.And:left {U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ (U.Mathlib.Order.Bounds.Defs.upperBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ s₂) (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ CompleteSemilatticeSup:toSupSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)} {U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ (U.Mathlib.Order.Bounds.Defs.lowerBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ (U.Mathlib.Order.Bounds.Defs.upperBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ s₂)) (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ CompleteSemilatticeSup:toSupSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)} (isLUB~usSup {α₀} ⦃ inst₁ ⦄ s₂) {a₃} h₄

-- theorem
opaque
  sSup~ule : {α₀ : Set} → ⦃ inst₁ : CompleteSemilatticeSup α₀ ⦄ → {s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀} → {a₃ : α₀} → ((b₄ : α₀) → U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₂ b₄ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ b₄ a₃) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ CompleteSemilatticeSup:toSupSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂) a₃
  sSup~ule {α₀} ⦃ inst₁ ⦄ {s₂} {a₃} h₄ = U.Init.Prelude.And:right {U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ (U.Mathlib.Order.Bounds.Defs.upperBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ s₂) (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ CompleteSemilatticeSup:toSupSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)} {U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ (U.Mathlib.Order.Bounds.Defs.lowerBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ (U.Mathlib.Order.Bounds.Defs.upperBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeSup:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ s₂)) (U.Mathlib.Order.SetNotation.SupSet:sSup {α₀} ⦃ CompleteSemilatticeSup:toSupSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)} (isLUB~usSup {α₀} ⦃ inst₁ ⦄ s₂) {a₃} h₄

CompleteSemilatticeInf:toInfSet : {α₀ : Set} → ⦃ _ : CompleteSemilatticeInf α₀ ⦄ → U.Mathlib.Order.SetNotation.InfSet α₀
CompleteSemilatticeInf:toInfSet {α₀} ⦃ self₁ ⦄ = CompleteSemilatticeInf.toInfSet₂ {α₀} self₁

-- theorem
opaque
  CompleteSemilatticeInf:isGLB~usInf : {α₀ : Set} → ⦃ self₁ : CompleteSemilatticeInf α₀ ⦄ → (s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsGLB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ self₁ ⦄ ⦄ ⦄ ⦄ s₂ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ self₁ ⦄ ⦄ s₂)
  CompleteSemilatticeInf:isGLB~usInf {α₀} ⦃ self₁ ⦄ = CompleteSemilatticeInf.isGLBsInf₃ {α₀} self₁

-- theorem
opaque
  isGLB~usInf : {α₀ : Set} → ⦃ inst₁ : CompleteSemilatticeInf α₀ ⦄ → (s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀) → U.Mathlib.Order.Bounds.Defs.IsGLB {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ s₂ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)
  isGLB~usInf {α₀} ⦃ inst₁ ⦄ s₂ = CompleteSemilatticeInf:isGLB~usInf {α₀} ⦃ inst₁ ⦄ s₂

-- theorem
opaque
  sInf~ule~usInf : {α₀ : Set} → ⦃ inst₁ : CompleteSemilatticeInf α₀ ⦄ → {s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀} → {t₃ : U.Mathlib.Data.~sSet.Defs.~sSet α₀} → U.Init.Prelude.LE:le {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instLE {α₀} ⦄ s₂ t₃ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ t₃) (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)
  sInf~ule~usInf {α₀} ⦃ inst₁ ⦄ {s₂} {t₃} h₄ = U.Mathlib.Order.Bounds.Basic.IsGLB:mono {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ {s₂} {t₃} {U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂} {U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ t₃} (isGLB~usInf {α₀} ⦃ inst₁ ⦄ s₂) (isGLB~usInf {α₀} ⦃ inst₁ ⦄ t₃) h₄

-- theorem
opaque
  le~usInf : {α₀ : Set} → ⦃ inst₁ : CompleteSemilatticeInf α₀ ⦄ → {s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀} → {a₃ : α₀} → ((b₄ : α₀) → U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₂ b₄ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ a₃ b₄) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ a₃ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)
  le~usInf {α₀} ⦃ inst₁ ⦄ {s₂} {a₃} h₄ = U.Init.Prelude.And:right {U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ (U.Mathlib.Order.Bounds.Defs.lowerBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ s₂) (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)} {U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ (U.Mathlib.Order.Bounds.Defs.upperBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ (U.Mathlib.Order.Bounds.Defs.lowerBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ s₂)) (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)} (isGLB~usInf {α₀} ⦃ inst₁ ⦄ s₂) {a₃} h₄

-- theorem
opaque
  sInf~ule : {α₀ : Set} → ⦃ inst₁ : CompleteSemilatticeInf α₀ ⦄ → {s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀} → {a₃ : α₀} → U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₂ a₃ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂) a₃
  sInf~ule {α₀} ⦃ inst₁ ⦄ {s₂} {a₃} h₄ = U.Init.Prelude.And:left {U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ (U.Mathlib.Order.Bounds.Defs.lowerBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ s₂) (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)} {U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ (U.Mathlib.Order.Bounds.Defs.upperBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ (U.Mathlib.Order.Bounds.Defs.lowerBounds {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ s₂)) (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)} (isGLB~usInf {α₀} ⦃ inst₁ ⦄ s₂) {a₃} h₄

-- theorem
opaque
  le~usInf~uiff : {α₀ : Set} → ⦃ inst₁ : CompleteSemilatticeInf α₀ ⦄ → {s₂ : U.Mathlib.Data.~sSet.Defs.~sSet α₀} → {a₃ : α₀} → U.Init.Core.Iff (U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ a₃ (U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂)) ((b₄ : α₀) → U.Init.Prelude.Membership:mem {α₀} {U.Mathlib.Data.~sSet.Defs.~sSet α₀} ⦃ U.Mathlib.Data.~sSet.Defs.~sSet:instMembership {α₀} ⦄ s₂ b₄ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ ⦄ a₃ b₄)
  le~usInf~uiff {α₀} ⦃ inst₁ ⦄ {s₂} {a₃} = U.Mathlib.Order.Bounds.Basic.le~uisGLB~uiff {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ CompleteSemilatticeInf:toPartialOrder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ {s₂} {U.Mathlib.Order.SetNotation.InfSet:sInf {α₀} ⦃ CompleteSemilatticeInf:toInfSet {α₀} ⦃ inst₁ ⦄ ⦄ s₂} {a₃} (isGLB~usInf {α₀} ⦃ inst₁ ⦄ s₂)
