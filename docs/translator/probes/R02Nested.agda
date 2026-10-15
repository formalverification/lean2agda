-- Outcome on 2026-10-13 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type #-}
module R02Nested where

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : (head₁ : α₀) → (tail₂ : List α₀) → List α₀

record Array (α₀ : Set) : Set where
  constructor Array:mk
  field
    toList₁ : List α₀

-- Nested through Array, a record with eta, and List, as Lean.Syntax.
data Syntax : Set where
  Syntax:missing : Syntax
  Syntax:atom : Nat → Syntax
  Syntax:node : (kind₀ : Nat) → (args₁ : Array Syntax) → Syntax

-- The three recursors of Lean's block, one mutual definition: each
-- matches its major premise on the nested type's constructors and calls
-- its sibling on each recursive field.
mutual
  Syntax:rec : {motive₀ : Syntax → Set} → {motive₁ : Array Syntax → Set} → {motive₂ : List Syntax → Set} → motive₀ Syntax:missing → ((n₃ : Nat) → motive₀ (Syntax:atom n₃)) → ((kind₄ : Nat) → (args₅ : Array Syntax) → motive₁ args₅ → motive₀ (Syntax:node kind₄ args₅)) → ((toList₅ : List Syntax) → motive₂ toList₅ → motive₁ (Array:mk {Syntax} toList₅)) → motive₂ (List:nil {Syntax}) → ((head₇ : Syntax) → (tail₈ : List Syntax) → motive₀ head₇ → motive₂ tail₈ → motive₂ (List:cons {Syntax} head₇ tail₈)) → (t₇ : Syntax) → motive₀ t₇
  Syntax:rec~u1 : {motive₀ : Syntax → Set} → {motive₁ : Array Syntax → Set} → {motive₂ : List Syntax → Set} → motive₀ Syntax:missing → ((n₃ : Nat) → motive₀ (Syntax:atom n₃)) → ((kind₄ : Nat) → (args₅ : Array Syntax) → motive₁ args₅ → motive₀ (Syntax:node kind₄ args₅)) → ((toList₅ : List Syntax) → motive₂ toList₅ → motive₁ (Array:mk {Syntax} toList₅)) → motive₂ (List:nil {Syntax}) → ((head₇ : Syntax) → (tail₈ : List Syntax) → motive₀ head₇ → motive₂ tail₈ → motive₂ (List:cons {Syntax} head₇ tail₈)) → (t₇ : Array Syntax) → motive₁ t₇
  Syntax:rec~u2 : {motive₀ : Syntax → Set} → {motive₁ : Array Syntax → Set} → {motive₂ : List Syntax → Set} → motive₀ Syntax:missing → ((n₃ : Nat) → motive₀ (Syntax:atom n₃)) → ((kind₄ : Nat) → (args₅ : Array Syntax) → motive₁ args₅ → motive₀ (Syntax:node kind₄ args₅)) → ((toList₅ : List Syntax) → motive₂ toList₅ → motive₁ (Array:mk {Syntax} toList₅)) → motive₂ (List:nil {Syntax}) → ((head₇ : Syntax) → (tail₈ : List Syntax) → motive₀ head₇ → motive₂ tail₈ → motive₂ (List:cons {Syntax} head₇ tail₈)) → (t₇ : List Syntax) → motive₂ t₇
  Syntax:rec {motive₀} {motive₁} {motive₂} missing₃ atom₄ node₅ mk₆ nil₇ cons₈ Syntax:missing = missing₃
  Syntax:rec {motive₀} {motive₁} {motive₂} missing₃ atom₄ node₅ mk₆ nil₇ cons₈ (Syntax:atom n₉) = atom₄ n₉
  Syntax:rec {motive₀} {motive₁} {motive₂} missing₃ atom₄ node₅ mk₆ nil₇ cons₈ (Syntax:node kind₉ args₁₀) = node₅ kind₉ args₁₀ (Syntax:rec~u1 {motive₀} {motive₁} {motive₂} missing₃ atom₄ node₅ mk₆ nil₇ cons₈ args₁₀)
  Syntax:rec~u1 {motive₀} {motive₁} {motive₂} missing₃ atom₄ node₅ mk₆ nil₇ cons₈ (Array:mk toList₉) = mk₆ toList₉ (Syntax:rec~u2 {motive₀} {motive₁} {motive₂} missing₃ atom₄ node₅ mk₆ nil₇ cons₈ toList₉)
  Syntax:rec~u2 {motive₀} {motive₁} {motive₂} missing₃ atom₄ node₅ mk₆ nil₇ cons₈ List:nil = nil₇
  Syntax:rec~u2 {motive₀} {motive₁} {motive₂} missing₃ atom₄ node₅ mk₆ nil₇ cons₈ (List:cons head₉ tail₁₀) = cons₈ head₉ tail₁₀ (Syntax:rec {motive₀} {motive₁} {motive₂} missing₃ atom₄ node₅ mk₆ nil₇ cons₈ head₉) (Syntax:rec~u2 {motive₀} {motive₁} {motive₂} missing₃ atom₄ node₅ mk₆ nil₇ cons₈ tail₁₀)

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

-- Counting atoms computes through all three.
atoms : Syntax → Nat
atoms = Syntax:rec {λ _ → Nat} {λ _ → Nat} {λ _ → Nat} 0 (λ _ → 1) (λ _ _ n → n) (λ _ n → n) 0 (λ _ _ m n → plus m n)
  where
    plus : Nat → Nat → Nat
    plus Nat:zero n = n
    plus (Nat:succ m) n = Nat:succ (plus m n)

example : Syntax
example = Syntax:node 0 (Array:mk (List:cons (Syntax:atom 1) (List:cons Syntax:missing (List:cons (Syntax:node 2 (Array:mk (List:cons (Syntax:atom 3) List:nil))) List:nil))))

computes : Eq {Nat} (atoms example) 2
computes = Eq:refl 2

-- Lean's struct eta for recursors: rec~u1 reduces on an array variable.
eta : (a : Array Syntax) → Eq {Nat} (Syntax:rec~u1 {λ _ → Nat} {λ _ → Nat} {λ _ → Nat} 0 (λ _ → 1) (λ _ _ n → n) (λ _ n → n) 0 (λ _ _ m n → m) a) (Syntax:rec~u2 {λ _ → Nat} {λ _ → Nat} {λ _ → Nat} 0 (λ _ → 1) (λ _ _ n → n) (λ _ n → n) 0 (λ _ _ m n → m) (Array.toList₁ a))
eta a = Eq:refl _
