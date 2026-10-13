-- Outcome on 2026-10-13 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type #-}
module I03NestedMutual where

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

-- A type nested through a record that holds a list, as Lean.Syntax is
-- nested through Array.
record Array (α₀ : Set) : Set where
  constructor Array:mk
  field
    toList₁ : List α₀

data Syntax : Set where
  Syntax:missing : Syntax
  Syntax:node : Array Syntax → Syntax

-- A mutual block holding a data type and a record.
mutual
  data Tree : Set where
    Tree:leaf : Tree
    Tree:node : Forest → Tree
  record Forest : Set where
    inductive
    constructor Forest:mk
    field
      trees₀ : List Tree

-- A forward-declared data type, with a definition between its signature
-- and its constructors that mentions it.
data Rose : Set

aux : Set
aux = List Rose

data Rose where
  Rose:node : aux → Rose

-- The same inside one mutual block, with the definition last.
mutual
  data Rose2 : Set where
    Rose2:node : aux2 → Rose2
  aux2 : Set
  aux2 = List Rose2

-- A parameter that varies in a recursive argument: Agda needs uniform
-- parameters only in constructors' targets (Lean's are uniform everywhere).
data Nest (α₀ : Set) : Set where
  Nest:nil : Nest α₀
  Nest:cons : α₀ → Nest (List α₀) → Nest α₀

-- A record parameter typed by a transparent abbreviation.
outParam : Set → Set
outParam α₀ = α₀

record HAdd (α₀ : Set) (β₁ : Set) (γ₂ : outParam Set) : Set where
  constructor HAdd:mk
  field
    hAdd₃ : α₀ → β₁ → γ₂

HAdd:hAdd : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam Set} → ⦃ _ : HAdd α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HAdd:hAdd {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HAdd.hAdd₃ {α₀} {β₁} {γ₂} self₃
