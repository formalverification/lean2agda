-- Outcome on 2026-10-13 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type #-}
module R03Structural where

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : (head₁ : α₀) → (tail₂ : List α₀) → List α₀

-- Acc: the recursive field is a function, and the recursor's call on
-- `h₅ y₆ a₇` is structural, as Agda's termination checker counts it.
data Acc {α₀ : Set} (r₁ : α₀ → α₀ → Set) : α₀ → Set where
  Acc:intro : (x₂ : α₀) → (h₃ : (y₃ : α₀) → r₁ y₃ x₂ → Acc {α₀} r₁ y₃) → Acc {α₀} r₁ x₂

Acc:rec : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {motive₂ : (a₂ : α₀) → Acc {α₀} r₁ a₂ → Set} → ((x₃ : α₀) → (h₄ : (y₄ : α₀) → r₁ y₄ x₃ → Acc {α₀} r₁ y₄) → ((y₅ : α₀) → (a₆ : r₁ y₅ x₃) → motive₂ y₅ (h₄ y₅ a₆)) → motive₂ x₃ (Acc:intro {α₀} {r₁} x₃ h₄)) → {a₄ : α₀} → (t₅ : Acc {α₀} r₁ a₄) → motive₂ a₄ t₅
Acc:rec {α₀} {r₁} {motive₂} intro₃ {_} (Acc:intro x₄ h₅) = intro₃ x₄ h₅ (λ (y₆ : α₀) → λ (a₇ : r₁ y₆ x₄) → Acc:rec {α₀} {r₁} {motive₂} intro₃ {y₆} (h₅ y₆ a₇))

-- A mutual pair, as Lean's mutual blocks: each recursor takes both
-- motives and calls the other on the other type's fields.
mutual
  data Even : Set where
    Even:zero : Even
    Even:succ : Odd → Even
  data Odd : Set where
    Odd:succ : Even → Odd

mutual
  Even:rec : {motive₀ : Even → Set} → {motive₁ : Odd → Set} → motive₀ Even:zero → ((a₂ : Odd) → motive₁ a₂ → motive₀ (Even:succ a₂)) → ((a₃ : Even) → motive₀ a₃ → motive₁ (Odd:succ a₃)) → (t₄ : Even) → motive₀ t₄
  Odd:rec : {motive₀ : Even → Set} → {motive₁ : Odd → Set} → motive₀ Even:zero → ((a₂ : Odd) → motive₁ a₂ → motive₀ (Even:succ a₂)) → ((a₃ : Even) → motive₀ a₃ → motive₁ (Odd:succ a₃)) → (t₄ : Odd) → motive₁ t₄
  Even:rec {motive₀} {motive₁} zero₂ succ₃ succ₄ Even:zero = zero₂
  Even:rec {motive₀} {motive₁} zero₂ succ₃ succ₄ (Even:succ a₅) = succ₃ a₅ (Odd:rec {motive₀} {motive₁} zero₂ succ₃ succ₄ a₅)
  Odd:rec {motive₀} {motive₁} zero₂ succ₃ succ₄ (Odd:succ a₅) = succ₄ a₅ (Even:rec {motive₀} {motive₁} zero₂ succ₃ succ₄ a₅)

-- A recursive record, `inductive`, `no-eta-equality` and `pattern`, as
-- issue M2-4 declares one: its recursor matches on the constructor, through a
-- nested List, with an implicit field.
mutual
  record Tree : Set where
    inductive
    no-eta-equality
    pattern
    constructor Tree:mk
    field
      {label₀} : Nat
      children₁ : List Tree

mutual
  Tree:rec : {motive₀ : Tree → Set} → {motive₁ : List Tree → Set} → ({label₂ : Nat} → (children₃ : List Tree) → motive₁ children₃ → motive₀ (Tree:mk {label₂} children₃)) → motive₁ (List:nil {Tree}) → ((head₃ : Tree) → (tail₄ : List Tree) → motive₀ head₃ → motive₁ tail₄ → motive₁ (List:cons {Tree} head₃ tail₄)) → (t₄ : Tree) → motive₀ t₄
  Tree:rec~u1 : {motive₀ : Tree → Set} → {motive₁ : List Tree → Set} → ({label₂ : Nat} → (children₃ : List Tree) → motive₁ children₃ → motive₀ (Tree:mk {label₂} children₃)) → motive₁ (List:nil {Tree}) → ((head₃ : Tree) → (tail₄ : List Tree) → motive₀ head₃ → motive₁ tail₄ → motive₁ (List:cons {Tree} head₃ tail₄)) → (t₄ : List Tree) → motive₁ t₄
  Tree:rec {motive₀} {motive₁} mk₂ nil₃ cons₄ (Tree:mk {label₅} children₆) = mk₂ {label₅} children₆ (Tree:rec~u1 {motive₀} {motive₁} mk₂ nil₃ cons₄ children₆)
  Tree:rec~u1 {motive₀} {motive₁} mk₂ nil₃ cons₄ List:nil = nil₃
  Tree:rec~u1 {motive₀} {motive₁} mk₂ nil₃ cons₄ (List:cons head₅ tail₆) = cons₄ head₅ tail₆ (Tree:rec {motive₀} {motive₁} mk₂ nil₃ cons₄ head₅) (Tree:rec~u1 {motive₀} {motive₁} mk₂ nil₃ cons₄ tail₆)

data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁

-- A well-founded relation on Nat, and Acc.rec computing on a closed
-- proof of accessibility.
data Lt : Nat → Nat → Set where
  Lt:base : {n₀ : Nat} → Lt n₀ (Nat:succ n₀)

accZero : Acc {Nat} Lt 0
accZero = Acc:intro 0 (λ y ())

accOne : Acc {Nat} Lt 1
accOne = Acc:intro 1 (λ { .0 Lt:base → accZero })

depth : (n : Nat) → Acc {Nat} Lt n → Nat
depth n a = Acc:rec {Nat} {Lt} {λ _ _ → Nat} (λ x h ih → ih' x ih) {n} a
  where
    ih' : (x : Nat) → ((y : Nat) → Lt y x → Nat) → Nat
    ih' Nat:zero ih = 0
    ih' (Nat:succ x) ih = Nat:succ (ih x Lt:base)

computes : Eq {Nat} (depth 1 accOne) 1
computes = Eq:refl 1
