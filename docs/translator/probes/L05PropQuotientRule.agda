-- Outcome on 2026-11-24 with Agda 2.8.0: rejected, [UnequalTerms] at the last definition, after the warning [RewriteVariablesNotBoundByLHS] at the pragma
{-# OPTIONS --prop --type-in-type --rewriting #-}
module L05PropQuotientRule where

-- Under the measurement's `Prop` printing, the quotient of a proposition
-- is a proposition: Lean's `Quot.{0} r : Prop`, here `Quot#z`.  The
-- computation rule of `Quot.lift` at that instance has `Quot:mk#z r a` on
-- its left, a proof, and Agda compares no two proofs, so the rule's `a`
-- is bound nowhere it can match: Agda accepts the postulate, warns that
-- the rule "is not a legal rewrite rule, since the following variables
-- are not bound by the left hand side: a₅", and installs nothing.  An
-- equation that Lean's kernel accepts by the rule is then refused.  The
-- same rule over a quotient of a type fires (L03PropRewriteRelation, and
-- the scaffold's `quotients` tree).
data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat

data Eq#n {α₀ : Set} : α₀ → α₀ → Prop where
  Eq:refl#n : (a₁ : α₀) → Eq#n {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq#n #-}

postulate Quot#z : {α₀ : Prop} → (α₀ → α₀ → Prop) → Prop
postulate Quot:mk#z : {α₀ : Prop} → (r₁ : α₀ → α₀ → Prop) → α₀ → Quot#z {α₀} r₁
postulate Quot:lift#zn : {α₀ : Prop} → {r₁ : α₀ → α₀ → Prop} → {β₂ : Set} → (f₃ : α₀ → β₂) → ((a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq#n {β₂} (f₃ a₄) (f₃ b₅)) → Quot#z {α₀} r₁ → β₂
postulate Quot:lift#zn-β : {α₀ : Prop} → {r₁ : α₀ → α₀ → Prop} → {β₂ : Set} → (f₃ : α₀ → β₂) → (h₄ : (a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq#n {β₂} (f₃ a₄) (f₃ b₅)) → (a₅ : α₀) → Eq#n {β₂} (Quot:lift#zn {α₀} {r₁} {β₂} f₃ h₄ (Quot:mk#z {α₀} r₁ a₅)) (f₃ a₅)
{-# REWRITE Quot:lift#zn-β #-}

postulate True : Prop

fromProofs : Quot#z {True} (λ (x₀ : True) → λ (x₁ : True) → True) → Nat
fromProofs q₀ = Quot:lift#zn {True} {λ (x₁ : True) → λ (x₂ : True) → True} {Nat} (λ (x₁ : True) → Nat:zero) (λ (x₁ : True) → λ (x₂ : True) → λ (x₃ : True) → Eq:refl#n Nat:zero) q₀

fromProofs-mk : (h₀ : True) → Eq#n {Nat} (fromProofs (Quot:mk#z {True} (λ (x₁ : True) → λ (x₂ : True) → True) h₀)) Nat:zero
fromProofs-mk h₀ = Eq:refl#n Nat:zero
