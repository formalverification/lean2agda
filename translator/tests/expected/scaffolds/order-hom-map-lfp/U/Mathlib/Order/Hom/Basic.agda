{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of OrderHom:map~ulfp
-- Lean module Mathlib.Order.Hom.Basic
module U.Mathlib.Order.Hom.Basic where
import U.Init.Prelude
import U.Mathlib.Data.FunLike.Basic
import U.Mathlib.Order.Basic
import U.Mathlib.Order.Defs.PartialOrder
import U.Mathlib.Order.Monotone.Defs

record OrderHom (α₀ : Set) (β₁ : Set) ⦃ inst₂ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ ⦃ inst₃ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ : Set where
  constructor OrderHom:mk
  field
    toFun₄ : α₀ → β₁
    monotone₅ : U.Mathlib.Order.Monotone.Defs.Monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₄

-- recursor
OrderHom:rec : {α₀ : Set} → {β₁ : Set} → ⦃ inst₂ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → ⦃ inst₃ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ → {motive₄ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ → Set} → ((toFun₅ : α₀ → β₁) → (monotone₆ : U.Mathlib.Order.Monotone.Defs.Monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₅) → motive₄ (OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₅ monotone₆)) → (t₅ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → motive₄ t₅
OrderHom:rec {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ {motive₄} mk₅ (OrderHom:mk toFun₆ monotone₇) = mk₅ toFun₆ monotone₇

OrderHom:casesOn : {α₀ : Set} → {β₁ : Set} → ⦃ inst₂ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → ⦃ inst₃ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ → {motive₄ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ → Set} → (t₅ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → ((toFun₆ : α₀ → β₁) → (monotone₇ : U.Mathlib.Order.Monotone.Defs.Monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₆) → motive₄ (OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₆ monotone₇)) → motive₄ t₅
OrderHom:casesOn {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ {motive₄} t₅ mk₆ = OrderHom:rec {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ {motive₄} (λ (toFun₇ : α₀ → β₁) → λ (monotone₈ : U.Mathlib.Order.Monotone.Defs.Monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇) → mk₆ toFun₇ monotone₈) t₅

OrderHom:toFun : {α₀ : Set} → {β₁ : Set} → ⦃ inst₂ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → ⦃ inst₃ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ → OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ → α₀ → β₁
OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ self₄ = OrderHom.toFun₄ {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ self₄

-- theorem
opaque
  OrderHom:instFunLike:~uproof~u1 : {α₀ : Set} → {β₁ : Set} → ⦃ inst₂ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → ⦃ inst₃ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ → (f₄ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → (g₅ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → U.Init.Prelude.Eq {α₀ → β₁} (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ f₄) (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ g₅) → U.Init.Prelude.Eq {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} f₄ g₅
  OrderHom:instFunLike:~uproof~u1 {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ f₄ g₅ h₆ = OrderHom:casesOn {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ {λ (t₇ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → U.Init.Prelude.Eq {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} f₄ t₇ → U.Init.Prelude.Eq {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} f₄ g₅} f₄ (λ (toFun₇ : α₀ → β₁) → λ (monotone₈ : U.Mathlib.Order.Monotone.Defs.Monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇) → λ (h₉ : U.Init.Prelude.Eq {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} f₄ (OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇ monotone₈)) → U.Init.Prelude.Eq:ndrec {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} {OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇ monotone₈} {λ (f₁₀ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → U.Init.Prelude.Eq {α₀ → β₁} (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ f₁₀) (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ g₅) → U.Init.Prelude.Eq {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} f₁₀ g₅} (λ (h₁₀ : U.Init.Prelude.Eq {α₀ → β₁} (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ (OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇ monotone₈)) (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ g₅)) → OrderHom:casesOn {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ {λ (t₁₁ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → U.Init.Prelude.Eq {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} g₅ t₁₁ → U.Init.Prelude.Eq {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} (OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇ monotone₈) g₅} g₅ (λ (toFun₁₁ : α₀ → β₁) → λ (monotone₁₂ : U.Mathlib.Order.Monotone.Defs.Monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₁₁) → λ (h₁₃ : U.Init.Prelude.Eq {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} g₅ (OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₁₁ monotone₁₂)) → U.Init.Prelude.Eq:ndrec {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} {OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₁₁ monotone₁₂} {λ (g₁₄ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → U.Init.Prelude.Eq {α₀ → β₁} (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ (OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇ monotone₈)) (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ g₁₄) → U.Init.Prelude.Eq {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} (OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇ monotone₈) g₁₄} (λ (h₁₄ : U.Init.Prelude.Eq {α₀ → β₁} (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ (OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇ monotone₈)) (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ (OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₁₁ monotone₁₂))) → (λ {α₁₅ : Set} → λ {β₁₆ : Set} → λ ⦃ inst₁₇ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₁₅ ⦄ → λ ⦃ inst₁₈ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁₆ ⦄ → λ (toFun₁₉ : α₁₅ → β₁₆) → λ (toFun₂₀ : α₁₅ → β₁₆) → λ (etoFun₂₁ : U.Init.Prelude.Eq {α₁₅ → β₁₆} toFun₁₉ toFun₂₀) → U.Init.Prelude.Eq:rec {α₁₅ → β₁₆} {toFun₁₉} {λ (toFun₂₂ : α₁₅ → β₁₆) → λ (etoFun₂₃ : U.Init.Prelude.Eq {α₁₅ → β₁₆} toFun₁₉ toFun₂₂) → (monotone₂₄ : U.Mathlib.Order.Monotone.Defs.Monotone {α₁₅} {β₁₆} ⦃ inst₁₇ ⦄ ⦃ inst₁₈ ⦄ toFun₁₉) → U.Init.Prelude.Eq {OrderHom α₁₅ β₁₆ ⦃ inst₁₇ ⦄ ⦃ inst₁₈ ⦄} (OrderHom:mk {α₁₅} {β₁₆} ⦃ inst₁₇ ⦄ ⦃ inst₁₈ ⦄ toFun₁₉ monotone₂₄) (OrderHom:mk {α₁₅} {β₁₆} ⦃ inst₁₇ ⦄ ⦃ inst₁₈ ⦄ toFun₂₂ (U.Init.Prelude.Eq:ndrec {α₁₅ → β₁₆} {toFun₁₉} {λ (toFun₂₅ : α₁₅ → β₁₆) → U.Mathlib.Order.Monotone.Defs.Monotone {α₁₅} {β₁₆} ⦃ inst₁₇ ⦄ ⦃ inst₁₈ ⦄ toFun₂₅} monotone₂₄ {toFun₂₂} etoFun₂₃))} (λ (monotone₂₂ : U.Mathlib.Order.Monotone.Defs.Monotone {α₁₅} {β₁₆} ⦃ inst₁₇ ⦄ ⦃ inst₁₈ ⦄ toFun₁₉) → U.Init.Prelude.Eq:refl {OrderHom α₁₅ β₁₆ ⦃ inst₁₇ ⦄ ⦃ inst₁₈ ⦄} (OrderHom:mk {α₁₅} {β₁₆} ⦃ inst₁₇ ⦄ ⦃ inst₁₈ ⦄ toFun₁₉ monotone₂₂)) {toFun₂₀} etoFun₂₁) {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇ toFun₁₁ h₁₄ monotone₈) {g₅} (U.Init.Prelude.Eq:symm {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} {g₅} {OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₁₁ monotone₁₂} h₁₃) h₁₀) (U.Init.Prelude.Eq:refl {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} g₅)) {f₄} (U.Init.Prelude.Eq:symm {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} {f₄} {OrderHom:mk {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ toFun₇ monotone₈} h₉) h₆) (U.Init.Prelude.Eq:refl {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} f₄)

OrderHom:instFunLike : {α₀ : Set} → {β₁ : Set} → ⦃ inst₂ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → ⦃ inst₃ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ → U.Mathlib.Data.FunLike.Basic.FunLike (OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) α₀ β₁
OrderHom:instFunLike {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ = U.Mathlib.Data.FunLike.Basic.DFunLike:mk {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} {α₀} {λ (x₄ : α₀) → β₁} (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) (λ {f₄ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} → λ {g₅ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} → λ (h₆ : U.Init.Prelude.Eq {α₀ → β₁} (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ f₄) (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ g₅)) → OrderHom:instFunLike:~uproof~u1 {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ f₄ g₅ h₆)

OrderHom:instPreorder : {α₀ : Set} → {β₁ : Set} → ⦃ inst₂ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → ⦃ inst₃ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ → U.Mathlib.Order.Defs.PartialOrder.Preorder (OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄)
OrderHom:instPreorder {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ = U.Mathlib.Order.Basic.Preorder:lift {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} {α₀ → β₁} ⦃ U.Mathlib.Order.Basic.Pi:preorder {α₀} {λ (a₄ : α₀) → β₁} ⦃ λ (i₄ : α₀) → inst₃ ⦄ ⦄ (U.Mathlib.Data.FunLike.Basic.DFunLike:coe {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} {α₀} {λ (a₄ : α₀) → β₁} ⦃ OrderHom:instFunLike {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ ⦄)

-- theorem
opaque
  OrderHom:monotone~x27~ : {α₀ : Set} → {β₁ : Set} → ⦃ inst₂ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → ⦃ inst₃ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ → (self₄ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → U.Mathlib.Order.Monotone.Defs.Monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ (OrderHom:toFun {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ self₄)
  OrderHom:monotone~x27~ {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ self₄ = OrderHom.monotone₅ {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ self₄

-- theorem
opaque
  OrderHom:monotone : {α₀ : Set} → {β₁ : Set} → ⦃ inst₂ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → ⦃ inst₃ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ → (f₄ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → U.Mathlib.Order.Monotone.Defs.Monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ (U.Mathlib.Data.FunLike.Basic.DFunLike:coe {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} {α₀} {λ (x₅ : α₀) → β₁} ⦃ OrderHom:instFunLike {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ ⦄ f₄)
  OrderHom:monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ f₄ = OrderHom:monotone~x27~ {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ f₄

-- theorem
opaque
  OrderHom:mono : {α₀ : Set} → {β₁ : Set} → ⦃ inst₂ : U.Mathlib.Order.Defs.PartialOrder.Preorder α₀ ⦄ → ⦃ inst₃ : U.Mathlib.Order.Defs.PartialOrder.Preorder β₁ ⦄ → (f₄ : OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄) → U.Mathlib.Order.Monotone.Defs.Monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ (U.Mathlib.Data.FunLike.Basic.DFunLike:coe {OrderHom α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄} {α₀} {λ (x₅ : α₀) → β₁} ⦃ OrderHom:instFunLike {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ ⦄ f₄)
  OrderHom:mono {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ f₄ = OrderHom:monotone {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ f₄
