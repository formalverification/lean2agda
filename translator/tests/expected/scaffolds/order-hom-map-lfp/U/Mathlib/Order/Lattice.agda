{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.Lattice
module U.Mathlib.Order.Lattice where
import U.Init.Prelude
import U.Mathlib.Order.Defs.PartialOrder

record SemilatticeSup (α₀ : Set) : Set where
  constructor SemilatticeSup:mk
  field
    ⦃ toPartialOrder₁ ⦄ : U.Mathlib.Order.Defs.PartialOrder.PartialOrder α₀
    sup₂ : α₀ → α₀ → α₀
    lesupleft₃ : (a₃ : α₀) → (b₄ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₁ ⦄ ⦄ ⦄ a₃ (sup₂ a₃ b₄)
    lesupright₄ : (a₄ : α₀) → (b₅ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₁ ⦄ ⦄ ⦄ b₅ (sup₂ a₄ b₅)
    suple₅ : (a₅ : α₀) → (b₆ : α₀) → (c₇ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₁ ⦄ ⦄ ⦄ a₅ c₇ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₁ ⦄ ⦄ ⦄ b₆ c₇ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₁ ⦄ ⦄ ⦄ (sup₂ a₅ b₆) c₇

-- recursor
SemilatticeSup:rec : {α₀ : Set} → {motive₁ : SemilatticeSup α₀ → Set} → (⦃ toPartialOrder₂ : U.Mathlib.Order.Defs.PartialOrder.PartialOrder α₀ ⦄ → (sup₃ : α₀ → α₀ → α₀) → (lesupleft₄ : (a₄ : α₀) → (b₅ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₂ ⦄ ⦄ ⦄ a₄ (sup₃ a₄ b₅)) → (lesupright₅ : (a₅ : α₀) → (b₆ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₂ ⦄ ⦄ ⦄ b₆ (sup₃ a₅ b₆)) → (suple₆ : (a₆ : α₀) → (b₇ : α₀) → (c₈ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₂ ⦄ ⦄ ⦄ a₆ c₈ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₂ ⦄ ⦄ ⦄ b₇ c₈ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ toPartialOrder₂ ⦄ ⦄ ⦄ (sup₃ a₆ b₇) c₈) → motive₁ (SemilatticeSup:mk {α₀} ⦃ toPartialOrder₂ ⦄ sup₃ lesupleft₄ lesupright₅ suple₆)) → (t₂ : SemilatticeSup α₀) → motive₁ t₂
SemilatticeSup:rec {α₀} {motive₁} mk₂ (SemilatticeSup:mk ⦃ toPartialOrder₃ ⦄ sup₄ lesupleft₅ lesupright₆ suple₇) = mk₂ ⦃ toPartialOrder₃ ⦄ sup₄ lesupleft₅ lesupright₆ suple₇

SemilatticeSup:toPartialOrder : {α₀ : Set} → ⦃ _ : SemilatticeSup α₀ ⦄ → U.Mathlib.Order.Defs.PartialOrder.PartialOrder α₀
SemilatticeSup:toPartialOrder {α₀} ⦃ self₁ ⦄ = SemilatticeSup.toPartialOrder₁ {α₀} self₁

record Lattice (α₀ : Set) : Set where
  constructor Lattice:mk
  field
    ⦃ toSemilatticeSup₁ ⦄ : SemilatticeSup α₀
    inf₂ : α₀ → α₀ → α₀
    infleleft₃ : (a₃ : α₀) → (b₄ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ SemilatticeSup:toPartialOrder {α₀} ⦃ toSemilatticeSup₁ ⦄ ⦄ ⦄ ⦄ (inf₂ a₃ b₄) a₃
    infleright₄ : (a₄ : α₀) → (b₅ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ SemilatticeSup:toPartialOrder {α₀} ⦃ toSemilatticeSup₁ ⦄ ⦄ ⦄ ⦄ (inf₂ a₄ b₅) b₅
    leinf₅ : (a₅ : α₀) → (b₆ : α₀) → (c₇ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ SemilatticeSup:toPartialOrder {α₀} ⦃ toSemilatticeSup₁ ⦄ ⦄ ⦄ ⦄ a₅ b₆ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ SemilatticeSup:toPartialOrder {α₀} ⦃ toSemilatticeSup₁ ⦄ ⦄ ⦄ ⦄ a₅ c₇ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ SemilatticeSup:toPartialOrder {α₀} ⦃ toSemilatticeSup₁ ⦄ ⦄ ⦄ ⦄ a₅ (inf₂ b₆ c₇)

-- recursor
Lattice:rec : {α₀ : Set} → {motive₁ : Lattice α₀ → Set} → (⦃ toSemilatticeSup₂ : SemilatticeSup α₀ ⦄ → (inf₃ : α₀ → α₀ → α₀) → (infleleft₄ : (a₄ : α₀) → (b₅ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ SemilatticeSup:toPartialOrder {α₀} ⦃ toSemilatticeSup₂ ⦄ ⦄ ⦄ ⦄ (inf₃ a₄ b₅) a₄) → (infleright₅ : (a₅ : α₀) → (b₆ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ SemilatticeSup:toPartialOrder {α₀} ⦃ toSemilatticeSup₂ ⦄ ⦄ ⦄ ⦄ (inf₃ a₅ b₆) b₆) → (leinf₆ : (a₆ : α₀) → (b₇ : α₀) → (c₈ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ SemilatticeSup:toPartialOrder {α₀} ⦃ toSemilatticeSup₂ ⦄ ⦄ ⦄ ⦄ a₆ b₇ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ SemilatticeSup:toPartialOrder {α₀} ⦃ toSemilatticeSup₂ ⦄ ⦄ ⦄ ⦄ a₆ c₈ → U.Init.Prelude.LE:le {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.Preorder:toLE {α₀} ⦃ U.Mathlib.Order.Defs.PartialOrder.PartialOrder:toPreorder {α₀} ⦃ SemilatticeSup:toPartialOrder {α₀} ⦃ toSemilatticeSup₂ ⦄ ⦄ ⦄ ⦄ a₆ (inf₃ b₇ c₈)) → motive₁ (Lattice:mk {α₀} ⦃ toSemilatticeSup₂ ⦄ inf₃ infleleft₄ infleright₅ leinf₆)) → (t₂ : Lattice α₀) → motive₁ t₂
Lattice:rec {α₀} {motive₁} mk₂ (Lattice:mk ⦃ toSemilatticeSup₃ ⦄ inf₄ infleleft₅ infleright₆ leinf₇) = mk₂ ⦃ toSemilatticeSup₃ ⦄ inf₄ infleleft₅ infleright₆ leinf₇

Lattice:toSemilatticeSup : {α₀ : Set} → ⦃ _ : Lattice α₀ ⦄ → SemilatticeSup α₀
Lattice:toSemilatticeSup {α₀} ⦃ self₁ ⦄ = Lattice.toSemilatticeSup₁ {α₀} self₁
