{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.Defs.PartialOrder
module U.Mathlib.Order.Defs.PartialOrder where
import U.Init.Core
import U.Init.Prelude
import U.Init.Tactics

Preorder:lt~uiff~ule~unot~uge:~uautoParam : U.Init.Prelude.Lean:Syntax
Preorder:lt~uiff~ule~unot~uge:~uautoParam = U.Init.Prelude.Lean:Syntax:node U.Init.Prelude.Lean:SourceInfo:none (U.Init.Prelude.Lean:Name:mkStr4 "Lean" "Parser" "Tactic" "tacticSeq") (U.Init.Prelude.Array:push {U.Init.Prelude.Lean:Syntax} (U.Init.Prelude.Array:empty {U.Init.Prelude.Lean:Syntax}) (U.Init.Prelude.Lean:Syntax:node U.Init.Prelude.Lean:SourceInfo:none (U.Init.Prelude.Lean:Name:mkStr4 "Lean" "Parser" "Tactic" "tacticSeq1Indented") (U.Init.Prelude.Array:push {U.Init.Prelude.Lean:Syntax} (U.Init.Prelude.Array:empty {U.Init.Prelude.Lean:Syntax}) (U.Init.Prelude.Lean:Syntax:node U.Init.Prelude.Lean:SourceInfo:none (U.Init.Prelude.Lean:Name:mkStr1 "null") (U.Init.Prelude.Array:push {U.Init.Prelude.Lean:Syntax} (U.Init.Prelude.Array:push {U.Init.Prelude.Lean:Syntax} (U.Init.Prelude.Array:push {U.Init.Prelude.Lean:Syntax} (U.Init.Prelude.Array:empty {U.Init.Prelude.Lean:Syntax}) (U.Init.Prelude.Lean:Syntax:node U.Init.Prelude.Lean:SourceInfo:none (U.Init.Prelude.Lean:Name:mkStr4 "Lean" "Parser" "Tactic" "intros") (U.Init.Prelude.Array:push {U.Init.Prelude.Lean:Syntax} (U.Init.Prelude.Array:push {U.Init.Prelude.Lean:Syntax} (U.Init.Prelude.Array:empty {U.Init.Prelude.Lean:Syntax}) (U.Init.Prelude.Lean:mkAtom "intros")) (U.Init.Prelude.Lean:Syntax:node U.Init.Prelude.Lean:SourceInfo:none (U.Init.Prelude.Lean:Name:mkStr1 "null") (U.Init.Prelude.Array:empty {U.Init.Prelude.Lean:Syntax}))))) (U.Init.Prelude.Lean:mkAtom ";")) (U.Init.Prelude.Lean:Syntax:node U.Init.Prelude.Lean:SourceInfo:none (U.Init.Prelude.Lean:Name:mkStr4 "Lean" "Parser" "Tactic" "tacticRfl") (U.Init.Prelude.Array:push {U.Init.Prelude.Lean:Syntax} (U.Init.Prelude.Array:empty {U.Init.Prelude.Lean:Syntax}) (U.Init.Prelude.Lean:mkAtom "rfl"))))))))

record Preorder (α₀ : Set) : Set where
  constructor Preorder:mk
  field
    ⦃ toLE₁ ⦄ : U.Init.Prelude.LE α₀
    ⦃ toLT₂ ⦄ : U.Init.Prelude.LT α₀
    lerefl₃ : (a₃ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ toLE₁ ⦄ a₃ a₃
    letrans₄ : (a₄ : α₀) → (b₅ : α₀) → (c₆ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ toLE₁ ⦄ a₄ b₅ → U.Init.Prelude.LE:le {α₀} ⦃ toLE₁ ⦄ b₅ c₆ → U.Init.Prelude.LE:le {α₀} ⦃ toLE₁ ⦄ a₄ c₆
    ltifflenotge₅ : U.Init.Tactics.autoParam ((a₅ : α₀) → (b₆ : α₀) → U.Init.Core.Iff (U.Init.Prelude.LT:lt {α₀} ⦃ toLT₂ ⦄ a₅ b₆) (U.Init.Prelude.And (U.Init.Prelude.LE:le {α₀} ⦃ toLE₁ ⦄ a₅ b₆) (U.Init.Prelude.Not (U.Init.Prelude.LE:le {α₀} ⦃ toLE₁ ⦄ b₆ a₅)))) Preorder:lt~uiff~ule~unot~uge:~uautoParam

-- recursor
Preorder:rec : {α₀ : Set} → {motive₁ : Preorder α₀ → Set} → (⦃ toLE₂ : U.Init.Prelude.LE α₀ ⦄ → ⦃ toLT₃ : U.Init.Prelude.LT α₀ ⦄ → (lerefl₄ : (a₄ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ toLE₂ ⦄ a₄ a₄) → (letrans₅ : (a₅ : α₀) → (b₆ : α₀) → (c₇ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ toLE₂ ⦄ a₅ b₆ → U.Init.Prelude.LE:le {α₀} ⦃ toLE₂ ⦄ b₆ c₇ → U.Init.Prelude.LE:le {α₀} ⦃ toLE₂ ⦄ a₅ c₇) → (ltifflenotge₆ : (a₆ : α₀) → (b₇ : α₀) → U.Init.Core.Iff (U.Init.Prelude.LT:lt {α₀} ⦃ toLT₃ ⦄ a₆ b₇) (U.Init.Prelude.And (U.Init.Prelude.LE:le {α₀} ⦃ toLE₂ ⦄ a₆ b₇) (U.Init.Prelude.Not (U.Init.Prelude.LE:le {α₀} ⦃ toLE₂ ⦄ b₇ a₆)))) → motive₁ (Preorder:mk {α₀} ⦃ toLE₂ ⦄ ⦃ toLT₃ ⦄ lerefl₄ letrans₅ ltifflenotge₆)) → (t₂ : Preorder α₀) → motive₁ t₂
Preorder:rec {α₀} {motive₁} mk₂ (Preorder:mk ⦃ toLE₃ ⦄ ⦃ toLT₄ ⦄ lerefl₅ letrans₆ ltifflenotge₇) = mk₂ ⦃ toLE₃ ⦄ ⦃ toLT₄ ⦄ lerefl₅ letrans₆ ltifflenotge₇

Preorder:toLE : {α₀ : Set} → ⦃ _ : Preorder α₀ ⦄ → U.Init.Prelude.LE α₀
Preorder:toLE {α₀} ⦃ self₁ ⦄ = Preorder.toLE₁ {α₀} self₁

record PartialOrder (α₀ : Set) : Set where
  constructor PartialOrder:mk
  field
    ⦃ toPreorder₁ ⦄ : Preorder α₀
    leantisymm₂ : (a₂ : α₀) → (b₃ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ toPreorder₁ ⦄ ⦄ a₂ b₃ → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ toPreorder₁ ⦄ ⦄ b₃ a₂ → U.Init.Prelude.Eq {α₀} a₂ b₃

-- recursor
PartialOrder:rec : {α₀ : Set} → {motive₁ : PartialOrder α₀ → Set} → (⦃ toPreorder₂ : Preorder α₀ ⦄ → (leantisymm₃ : (a₃ : α₀) → (b₄ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ toPreorder₂ ⦄ ⦄ a₃ b₄ → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ toPreorder₂ ⦄ ⦄ b₄ a₃ → U.Init.Prelude.Eq {α₀} a₃ b₄) → motive₁ (PartialOrder:mk {α₀} ⦃ toPreorder₂ ⦄ leantisymm₃)) → (t₂ : PartialOrder α₀) → motive₁ t₂
PartialOrder:rec {α₀} {motive₁} mk₂ (PartialOrder:mk ⦃ toPreorder₃ ⦄ leantisymm₄) = mk₂ ⦃ toPreorder₃ ⦄ leantisymm₄

PartialOrder:toPreorder : {α₀ : Set} → ⦃ _ : PartialOrder α₀ ⦄ → Preorder α₀
PartialOrder:toPreorder {α₀} ⦃ self₁ ⦄ = PartialOrder.toPreorder₁ {α₀} self₁

Preorder:toLT : {α₀ : Set} → ⦃ _ : Preorder α₀ ⦄ → U.Init.Prelude.LT α₀
Preorder:toLT {α₀} ⦃ self₁ ⦄ = Preorder.toLT₂ {α₀} self₁

-- theorem
opaque
  Preorder:lt~uiff~ule~unot~uge : {α₀ : Set} → ⦃ self₁ : Preorder α₀ ⦄ → (a₂ : α₀) → (b₃ : α₀) → U.Init.Core.Iff (U.Init.Prelude.LT:lt {α₀} ⦃ Preorder:toLT {α₀} ⦃ self₁ ⦄ ⦄ a₂ b₃) (U.Init.Prelude.And (U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ self₁ ⦄ ⦄ a₂ b₃) (U.Init.Prelude.Not (U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ self₁ ⦄ ⦄ b₃ a₂)))
  Preorder:lt~uiff~ule~unot~uge {α₀} ⦃ self₁ ⦄ = Preorder.ltifflenotge₅ {α₀} self₁

-- theorem
opaque
  lt~uiff~ule~unot~uge : {α₀ : Set} → ⦃ inst₁ : Preorder α₀ ⦄ → {a₂ : α₀} → {b₃ : α₀} → U.Init.Core.Iff (U.Init.Prelude.LT:lt {α₀} ⦃ Preorder:toLT {α₀} ⦃ inst₁ ⦄ ⦄ a₂ b₃) (U.Init.Prelude.And (U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ a₂ b₃) (U.Init.Prelude.Not (U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ b₃ a₂)))
  lt~uiff~ule~unot~uge {α₀} ⦃ inst₁ ⦄ {a₂} {b₃} = Preorder:lt~uiff~ule~unot~uge {α₀} ⦃ inst₁ ⦄ a₂ b₃

-- theorem
opaque
  Preorder:le~urefl : {α₀ : Set} → ⦃ self₁ : Preorder α₀ ⦄ → (a₂ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ self₁ ⦄ ⦄ a₂ a₂
  Preorder:le~urefl {α₀} ⦃ self₁ ⦄ = Preorder.lerefl₃ {α₀} self₁

-- theorem
opaque
  le~urefl : {α₀ : Set} → ⦃ inst₁ : Preorder α₀ ⦄ → (a₂ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ a₂ a₂
  le~urefl {α₀} ⦃ inst₁ ⦄ = Preorder:le~urefl {α₀} ⦃ inst₁ ⦄

-- theorem
opaque
  Preorder:le~utrans : {α₀ : Set} → ⦃ self₁ : Preorder α₀ ⦄ → (a₂ : α₀) → (b₃ : α₀) → (c₄ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ self₁ ⦄ ⦄ a₂ b₃ → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ self₁ ⦄ ⦄ b₃ c₄ → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ self₁ ⦄ ⦄ a₂ c₄
  Preorder:le~utrans {α₀} ⦃ self₁ ⦄ = Preorder.letrans₄ {α₀} self₁

-- theorem
opaque
  le~utrans : {α₀ : Set} → ⦃ inst₁ : Preorder α₀ ⦄ → {a₂ : α₀} → {b₃ : α₀} → {c₄ : α₀} → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ a₂ b₃ → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ b₃ c₄ → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ a₂ c₄
  le~utrans {α₀} ⦃ inst₁ ⦄ {a₂} {b₃} {c₄} = Preorder:le~utrans {α₀} ⦃ inst₁ ⦄ a₂ b₃ c₄

-- theorem
opaque
  ge~utrans : {α₀ : Set} → ⦃ inst₁ : Preorder α₀ ⦄ → {a₂ : α₀} → {b₃ : α₀} → {c₄ : α₀} → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ b₃ a₂ → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ c₄ b₃ → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ c₄ a₂
  ge~utrans {α₀} ⦃ inst₁ ⦄ {a₂} {b₃} {c₄} = U.Init.Core.flip {U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ c₄ b₃} {U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ b₃ a₂} {U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ c₄ a₂} (le~utrans {α₀} ⦃ inst₁ ⦄ {c₄} {b₃} {a₂})

-- theorem
opaque
  PartialOrder:le~uantisymm : {α₀ : Set} → ⦃ self₁ : PartialOrder α₀ ⦄ → (a₂ : α₀) → (b₃ : α₀) → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ PartialOrder:toPreorder {α₀} ⦃ self₁ ⦄ ⦄ ⦄ a₂ b₃ → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ PartialOrder:toPreorder {α₀} ⦃ self₁ ⦄ ⦄ ⦄ b₃ a₂ → U.Init.Prelude.Eq {α₀} a₂ b₃
  PartialOrder:le~uantisymm {α₀} ⦃ self₁ ⦄ = PartialOrder.leantisymm₂ {α₀} self₁

-- theorem
opaque
  le~uantisymm : {α₀ : Set} → ⦃ inst₁ : PartialOrder α₀ ⦄ → {a₂ : α₀} → {b₃ : α₀} → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ PartialOrder:toPreorder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ a₂ b₃ → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ PartialOrder:toPreorder {α₀} ⦃ inst₁ ⦄ ⦄ ⦄ b₃ a₂ → U.Init.Prelude.Eq {α₀} a₂ b₃
  le~uantisymm {α₀} ⦃ inst₁ ⦄ {a₂} {b₃} = PartialOrder:le~uantisymm {α₀} ⦃ inst₁ ⦄ a₂ b₃

-- theorem
opaque
  le~urfl : {α₀ : Set} → ⦃ inst₁ : Preorder α₀ ⦄ → {a₂ : α₀} → U.Init.Prelude.LE:le {α₀} ⦃ Preorder:toLE {α₀} ⦃ inst₁ ⦄ ⦄ a₂ a₂
  le~urfl {α₀} ⦃ inst₁ ⦄ {a₂} = le~urefl {α₀} ⦃ inst₁ ⦄ a₂
