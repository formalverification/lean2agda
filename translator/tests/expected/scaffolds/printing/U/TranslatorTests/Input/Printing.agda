{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of PrintFixtures:Dependent:value PrintFixtures:Pair:first PrintFixtures:alignedDeep PrintFixtures:alignedTop PrintFixtures:doubling and 11 more
-- Lean module TranslatorTests.Input.Printing
module U.TranslatorTests.Input.Printing where
import U.Init.Prelude

record PrintFixtures:Dependent : Set where
  constructor PrintFixtures:Dependent:mk
  field
    size₀ : U.Init.Prelude.Nat
    value₁ : U.Init.Prelude.Fin size₀

-- recursor
PrintFixtures:Dependent:rec : {motive₀ : PrintFixtures:Dependent → Set} → ((size₁ : U.Init.Prelude.Nat) → (value₂ : U.Init.Prelude.Fin size₁) → motive₀ (PrintFixtures:Dependent:mk size₁ value₂)) → (t₁ : PrintFixtures:Dependent) → motive₀ t₁
PrintFixtures:Dependent:rec {motive₀} mk₁ (PrintFixtures:Dependent:mk size₂ value₃) = mk₁ size₂ value₃

PrintFixtures:Dependent:size : PrintFixtures:Dependent → U.Init.Prelude.Nat
PrintFixtures:Dependent:size self₀ = PrintFixtures:Dependent.size₀ self₀

PrintFixtures:Dependent:value : (self₀ : PrintFixtures:Dependent) → U.Init.Prelude.Fin (PrintFixtures:Dependent:size self₀)
PrintFixtures:Dependent:value self₀ = PrintFixtures:Dependent.value₁ self₀

record PrintFixtures:Pair : Set where
  constructor PrintFixtures:Pair:mk
  field
    first₀ : U.Init.Prelude.Nat
    second₁ : U.Init.Prelude.Nat

-- recursor
PrintFixtures:Pair:rec : {motive₀ : PrintFixtures:Pair → Set} → ((first₁ : U.Init.Prelude.Nat) → (second₂ : U.Init.Prelude.Nat) → motive₀ (PrintFixtures:Pair:mk first₁ second₂)) → (t₁ : PrintFixtures:Pair) → motive₀ t₁
PrintFixtures:Pair:rec {motive₀} mk₁ (PrintFixtures:Pair:mk first₂ second₃) = mk₁ first₂ second₃

PrintFixtures:Pair:first : PrintFixtures:Pair → U.Init.Prelude.Nat
PrintFixtures:Pair:first self₀ = PrintFixtures:Pair.first₀ self₀

PrintFixtures:applyImplicit : ({α₀ : Set} → α₀ → α₀) → U.Init.Prelude.Nat
PrintFixtures:applyImplicit f₀ = f₀ {U.Init.Prelude.Nat} (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 3 ⦃ U.Init.Prelude.instOfNatNat 3 ⦄)

PrintFixtures:alignedDeep : U.Init.Prelude.Nat
PrintFixtures:alignedDeep = PrintFixtures:applyImplicit (λ {α₀ : Set} → λ (a₁ : α₀) → a₁)

PrintFixtures:alignedTop : {α₀ : Set} → α₀ → α₀
PrintFixtures:alignedTop {α₀} a₁ = a₁

PrintFixtures:applyExplicit : ((α₀ : Set) → α₀ → α₀) → U.Init.Prelude.Nat
PrintFixtures:applyExplicit f₀ = f₀ U.Init.Prelude.Nat (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 3 ⦃ U.Init.Prelude.instOfNatNat 3 ⦄)

PrintFixtures:applyHidden : ({_ : U.Init.Prelude.Nat} → ⦃ _ : U.Init.Prelude.Inhabited U.Init.Prelude.Nat ⦄ → U.Init.Prelude.Nat) → U.Init.Prelude.Nat
PrintFixtures:applyHidden f₀ = f₀ {U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄} ⦃ U.Init.Prelude.Inhabited:mk {U.Init.Prelude.Nat} (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) ⦄

PrintFixtures:applyInstance : (⦃ _ : U.Init.Prelude.Inhabited U.Init.Prelude.Nat ⦄ → U.Init.Prelude.Nat) → U.Init.Prelude.Nat
PrintFixtures:applyInstance f₀ = f₀ ⦃ U.Init.Prelude.Inhabited:mk {U.Init.Prelude.Nat} (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) ⦄

PrintFixtures:doubling:~ushare:~n1 : U.Init.Prelude.Nat
PrintFixtures:doubling:~ushare:~n1 = U.Init.Prelude.Nat:add (U.Init.Prelude.Nat:add (U.Init.Prelude.Nat:add (U.Init.Prelude.Nat:add U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero) (U.Init.Prelude.Nat:add U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero)) (U.Init.Prelude.Nat:add (U.Init.Prelude.Nat:add U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero) (U.Init.Prelude.Nat:add U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero))) (U.Init.Prelude.Nat:add (U.Init.Prelude.Nat:add (U.Init.Prelude.Nat:add U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero) (U.Init.Prelude.Nat:add U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero)) (U.Init.Prelude.Nat:add (U.Init.Prelude.Nat:add U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero) (U.Init.Prelude.Nat:add U.Init.Prelude.Nat:zero U.Init.Prelude.Nat:zero)))

PrintFixtures:doubling:~ushare:~n2 : U.Init.Prelude.Nat
PrintFixtures:doubling:~ushare:~n2 = U.Init.Prelude.Nat:add PrintFixtures:doubling:~ushare:~n1 PrintFixtures:doubling:~ushare:~n1

PrintFixtures:doubling:~ushare:~n3 : U.Init.Prelude.Nat
PrintFixtures:doubling:~ushare:~n3 = U.Init.Prelude.Nat:add PrintFixtures:doubling:~ushare:~n2 PrintFixtures:doubling:~ushare:~n2

PrintFixtures:doubling:~ushare:~n4 : U.Init.Prelude.Nat
PrintFixtures:doubling:~ushare:~n4 = U.Init.Prelude.Nat:add PrintFixtures:doubling:~ushare:~n3 PrintFixtures:doubling:~ushare:~n3

PrintFixtures:doubling:~ushare:~n5 : U.Init.Prelude.Nat
PrintFixtures:doubling:~ushare:~n5 = U.Init.Prelude.Nat:add PrintFixtures:doubling:~ushare:~n4 PrintFixtures:doubling:~ushare:~n4

PrintFixtures:doubling:~ushare:~n6 : U.Init.Prelude.Nat
PrintFixtures:doubling:~ushare:~n6 = U.Init.Prelude.Nat:add PrintFixtures:doubling:~ushare:~n5 PrintFixtures:doubling:~ushare:~n5

PrintFixtures:doubling : U.Init.Prelude.Nat
PrintFixtures:doubling = U.Init.Prelude.Nat:add PrintFixtures:doubling:~ushare:~n6 PrintFixtures:doubling:~ushare:~n6

PrintFixtures:implicitId : {α₀ : Set} → α₀ → α₀
PrintFixtures:implicitId {α₀} a₁ = a₁

PrintFixtures:etaRepaired : U.Init.Prelude.Nat
PrintFixtures:etaRepaired = PrintFixtures:applyExplicit (λ (α₀ : Set) → λ (a₁ : α₀) → PrintFixtures:implicitId {α₀} a₁)

PrintFixtures:greeting : U.Init.Prelude.String
PrintFixtures:greeting = "a\"b\\c\10\&\955\&\10013\&"

PrintFixtures:hiddenInstanceRepaired : ({_ : U.Init.Prelude.Nat} → ⦃ _ : U.Init.Prelude.Inhabited U.Init.Prelude.Nat ⦄ → U.Init.Prelude.Nat) → U.Init.Prelude.Nat
PrintFixtures:hiddenInstanceRepaired g₀ = PrintFixtures:applyHidden (λ {n₁ : U.Init.Prelude.Nat} → λ ⦃ inst₂ : U.Init.Prelude.Inhabited U.Init.Prelude.Nat ⦄ → g₀ {n₁} ⦃ inst₂ ⦄)

PrintFixtures:higher : (U.Init.Prelude.Nat → U.Init.Prelude.Nat) → ((U.Init.Prelude.Nat → U.Init.Prelude.Nat) → U.Init.Prelude.Nat) → U.Init.Prelude.Nat
PrintFixtures:higher f₀ g₁ = g₁ f₀

PrintFixtures:instanceRepaired : (⦃ _ : U.Init.Prelude.Inhabited U.Init.Prelude.Nat ⦄ → U.Init.Prelude.Nat) → U.Init.Prelude.Nat
PrintFixtures:instanceRepaired g₀ = PrintFixtures:applyInstance (λ ⦃ inst₁ : U.Init.Prelude.Inhabited U.Init.Prelude.Nat ⦄ → g₀ ⦃ inst₁ ⦄)

PrintFixtures:large : U.Init.Prelude.Nat
PrintFixtures:large = U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 18446744073709551616 ⦃ U.Init.Prelude.instOfNatNat 18446744073709551616 ⦄

PrintFixtures:pick : (α₀ : Set) → ⦃ _ : U.Init.Prelude.Inhabited α₀ ⦄ → α₀
PrintFixtures:pick α₀ ⦃ inst₁ ⦄ = U.Init.Prelude.Inhabited:default {α₀} ⦃ inst₁ ⦄

PrintFixtures:redex : U.Init.Prelude.Nat
PrintFixtures:redex = (λ (x₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Nat:succ x₀) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 3 ⦃ U.Init.Prelude.instOfNatNat 3 ⦄)

PrintFixtures:sorts : Set → Set → Set
PrintFixtures:sorts α₀ x₁ = α₀

PrintFixtures:strict : {n₀ : U.Init.Prelude.Nat} → U.Init.Prelude.Eq {U.Init.Prelude.Nat} n₀ n₀ → U.Init.Prelude.Nat
PrintFixtures:strict {n₀} x₁ = n₀

PrintFixtures:withLet : U.Init.Prelude.Nat → U.Init.Prelude.Nat
PrintFixtures:withLet n₀ = let m₁ : U.Init.Prelude.Nat; m₁ = U.Init.Prelude.Nat:add n₀ n₀ in U.Init.Prelude.Nat:add m₁ m₁
