{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of InductiveFixtures:Bad InductiveFixtures:Packed InductiveFixtures:Packed:fits InductiveFixtures:Packed:measured InductiveFixtures:Packed:value and 12 more
-- Lean module TranslatorTests.Input.Inductives
-- refused 3 declarations; refusals.txt names each with its reason
module U.TranslatorTests.Input.Inductives where
import U.Init.Prelude

record InductiveFixtures:Measure (α₀ : Set) : Set where
  constructor InductiveFixtures:Measure:mk
  field
    measure₁ : α₀ → U.Init.Prelude.Nat

-- recursor
InductiveFixtures:Measure:rec : {α₀ : Set} → {motive₁ : InductiveFixtures:Measure α₀ → Set} → ((measure₂ : α₀ → U.Init.Prelude.Nat) → motive₁ (InductiveFixtures:Measure:mk {α₀} measure₂)) → (t₂ : InductiveFixtures:Measure α₀) → motive₁ t₂
InductiveFixtures:Measure:rec {α₀} {motive₁} mk₂ (InductiveFixtures:Measure:mk measure₃) = mk₂ measure₃

InductiveFixtures:Measure:measure : {α₀ : Set} → ⦃ _ : InductiveFixtures:Measure α₀ ⦄ → α₀ → U.Init.Prelude.Nat
InductiveFixtures:Measure:measure {α₀} ⦃ self₁ ⦄ = InductiveFixtures:Measure.measure₁ {α₀} self₁

record InductiveFixtures:Packed (α₀ : Set) ⦃ inst₁ : U.Init.Prelude.BEq α₀ ⦄ : Set where
  constructor InductiveFixtures:Packed:mk
  field
    {width₂} : U.Init.Prelude.Nat
    ⦃ measured₃ ⦄ : InductiveFixtures:Measure α₀
    value₄ : α₀
    fits₅ : U.Init.Prelude.LE:le {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLENat ⦄ (InductiveFixtures:Measure:measure {α₀} ⦃ measured₃ ⦄ value₄) width₂

-- recursor
InductiveFixtures:Packed:rec : {α₀ : Set} → ⦃ inst₁ : U.Init.Prelude.BEq α₀ ⦄ → {motive₂ : InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄ → Set} → ({width₃ : U.Init.Prelude.Nat} → ⦃ measured₄ : InductiveFixtures:Measure α₀ ⦄ → (value₅ : α₀) → (fits₆ : U.Init.Prelude.LE:le {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLENat ⦄ (InductiveFixtures:Measure:measure {α₀} ⦃ measured₄ ⦄ value₅) width₃) → motive₂ (InductiveFixtures:Packed:mk {α₀} ⦃ inst₁ ⦄ {width₃} ⦃ measured₄ ⦄ value₅ fits₆)) → (t₃ : InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄) → motive₂ t₃
InductiveFixtures:Packed:rec {α₀} ⦃ inst₁ ⦄ {motive₂} mk₃ (InductiveFixtures:Packed:mk {width₄} ⦃ measured₅ ⦄ value₆ fits₇) = mk₃ {width₄} ⦃ measured₅ ⦄ value₆ fits₇

InductiveFixtures:Packed:measured : {α₀ : Set} → ⦃ inst₁ : U.Init.Prelude.BEq α₀ ⦄ → InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄ → InductiveFixtures:Measure α₀
InductiveFixtures:Packed:measured {α₀} ⦃ inst₁ ⦄ self₂ = InductiveFixtures:Packed.measured₃ {α₀} ⦃ inst₁ ⦄ self₂

InductiveFixtures:Packed:value : {α₀ : Set} → ⦃ inst₁ : U.Init.Prelude.BEq α₀ ⦄ → InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄ → α₀
InductiveFixtures:Packed:value {α₀} ⦃ inst₁ ⦄ self₂ = InductiveFixtures:Packed.value₄ {α₀} ⦃ inst₁ ⦄ self₂

InductiveFixtures:Packed:width : {α₀ : Set} → ⦃ inst₁ : U.Init.Prelude.BEq α₀ ⦄ → InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄ → U.Init.Prelude.Nat
InductiveFixtures:Packed:width {α₀} ⦃ inst₁ ⦄ self₂ = InductiveFixtures:Packed.width₂ {α₀} ⦃ inst₁ ⦄ self₂

-- theorem
opaque
  InductiveFixtures:Packed:fits : {α₀ : Set} → ⦃ inst₁ : U.Init.Prelude.BEq α₀ ⦄ → (self₂ : InductiveFixtures:Packed α₀ ⦃ inst₁ ⦄) → U.Init.Prelude.LE:le {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLENat ⦄ (InductiveFixtures:Measure:measure {α₀} ⦃ InductiveFixtures:Packed:measured {α₀} ⦃ inst₁ ⦄ self₂ ⦄ (InductiveFixtures:Packed:value {α₀} ⦃ inst₁ ⦄ self₂)) (InductiveFixtures:Packed:width {α₀} ⦃ inst₁ ⦄ self₂)
  InductiveFixtures:Packed:fits {α₀} ⦃ inst₁ ⦄ self₂ = InductiveFixtures:Packed.fits₅ {α₀} ⦃ inst₁ ⦄ self₂

mutual
  data InductiveFixtures:Term : Set where
    InductiveFixtures:Term:lit : U.Init.Prelude.Nat → InductiveFixtures:Term
    InductiveFixtures:Term:pair : InductiveFixtures:Pair → InductiveFixtures:Term
  record InductiveFixtures:Pair : Set where
    inductive
    no-eta-equality
    pattern
    constructor InductiveFixtures:Pair:mk
    field
      left₀ : InductiveFixtures:Term
      right₁ : InductiveFixtures:Term

-- recursor
mutual
  InductiveFixtures:Term:rec : {motive1₀ : InductiveFixtures:Term → Set} → {motive2₁ : InductiveFixtures:Pair → Set} → ((a₂ : U.Init.Prelude.Nat) → motive1₀ (InductiveFixtures:Term:lit a₂)) → ((a₂ : InductiveFixtures:Pair) → motive2₁ a₂ → motive1₀ (InductiveFixtures:Term:pair a₂)) → ((left₂ : InductiveFixtures:Term) → (right₃ : InductiveFixtures:Term) → motive1₀ left₂ → motive1₀ right₃ → motive2₁ (InductiveFixtures:Pair:mk left₂ right₃)) → (t₂ : InductiveFixtures:Term) → motive1₀ t₂
  InductiveFixtures:Pair:rec : {motive1₀ : InductiveFixtures:Term → Set} → {motive2₁ : InductiveFixtures:Pair → Set} → ((a₂ : U.Init.Prelude.Nat) → motive1₀ (InductiveFixtures:Term:lit a₂)) → ((a₂ : InductiveFixtures:Pair) → motive2₁ a₂ → motive1₀ (InductiveFixtures:Term:pair a₂)) → ((left₂ : InductiveFixtures:Term) → (right₃ : InductiveFixtures:Term) → motive1₀ left₂ → motive1₀ right₃ → motive2₁ (InductiveFixtures:Pair:mk left₂ right₃)) → (t₂ : InductiveFixtures:Pair) → motive2₁ t₂
  InductiveFixtures:Term:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ (InductiveFixtures:Term:lit a₅) = lit₂ a₅
  InductiveFixtures:Term:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ (InductiveFixtures:Term:pair a₅) = pair₃ a₅ (InductiveFixtures:Pair:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ a₅)
  InductiveFixtures:Pair:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ (InductiveFixtures:Pair:mk left₅ right₆) = mk₄ left₅ right₆ (InductiveFixtures:Term:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ left₅) (InductiveFixtures:Term:rec {motive1₀} {motive2₁} lit₂ pair₃ mk₄ right₆)

record InductiveFixtures:Rose : Set where
  inductive
  no-eta-equality
  pattern
  constructor InductiveFixtures:Rose:mk
  field
    label₀ : U.Init.Prelude.Nat
    children₁ : U.Init.Prelude.List InductiveFixtures:Rose

-- recursor
mutual
  InductiveFixtures:Rose:rec : {motive1₀ : InductiveFixtures:Rose → Set} → {motive2₁ : U.Init.Prelude.List InductiveFixtures:Rose → Set} → ((label₂ : U.Init.Prelude.Nat) → (children₃ : U.Init.Prelude.List InductiveFixtures:Rose) → motive2₁ children₃ → motive1₀ (InductiveFixtures:Rose:mk label₂ children₃)) → motive2₁ (U.Init.Prelude.List:nil {InductiveFixtures:Rose}) → ((head₂ : InductiveFixtures:Rose) → (tail₃ : U.Init.Prelude.List InductiveFixtures:Rose) → motive1₀ head₂ → motive2₁ tail₃ → motive2₁ (U.Init.Prelude.List:cons {InductiveFixtures:Rose} head₂ tail₃)) → (t₂ : InductiveFixtures:Rose) → motive1₀ t₂
  InductiveFixtures:Rose:rec~u1 : {motive1₀ : InductiveFixtures:Rose → Set} → {motive2₁ : U.Init.Prelude.List InductiveFixtures:Rose → Set} → ((label₂ : U.Init.Prelude.Nat) → (children₃ : U.Init.Prelude.List InductiveFixtures:Rose) → motive2₁ children₃ → motive1₀ (InductiveFixtures:Rose:mk label₂ children₃)) → motive2₁ (U.Init.Prelude.List:nil {InductiveFixtures:Rose}) → ((head₂ : InductiveFixtures:Rose) → (tail₃ : U.Init.Prelude.List InductiveFixtures:Rose) → motive1₀ head₂ → motive2₁ tail₃ → motive2₁ (U.Init.Prelude.List:cons {InductiveFixtures:Rose} head₂ tail₃)) → (t₂ : U.Init.Prelude.List InductiveFixtures:Rose) → motive2₁ t₂
  InductiveFixtures:Rose:rec {motive1₀} {motive2₁} mk₂ nil₃ cons₄ (InductiveFixtures:Rose:mk label₅ children₆) = mk₂ label₅ children₆ (InductiveFixtures:Rose:rec~u1 {motive1₀} {motive2₁} mk₂ nil₃ cons₄ children₆)
  InductiveFixtures:Rose:rec~u1 {motive1₀} {motive2₁} mk₂ nil₃ cons₄ U.Init.Prelude.List:nil = nil₃
  InductiveFixtures:Rose:rec~u1 {motive1₀} {motive2₁} mk₂ nil₃ cons₄ (U.Init.Prelude.List:cons head₅ tail₆) = cons₄ head₅ tail₆ (InductiveFixtures:Rose:rec {motive1₀} {motive2₁} mk₂ nil₃ cons₄ head₅) (InductiveFixtures:Rose:rec~u1 {motive1₀} {motive2₁} mk₂ nil₃ cons₄ tail₆)

InductiveFixtures:Rose:children : InductiveFixtures:Rose → U.Init.Prelude.List InductiveFixtures:Rose
InductiveFixtures:Rose:children self₀ = InductiveFixtures:Rose.children₁ self₀

InductiveFixtures:Rose:label : InductiveFixtures:Rose → U.Init.Prelude.Nat
InductiveFixtures:Rose:label self₀ = InductiveFixtures:Rose.label₀ self₀

data InductiveFixtures:Same {α₀ : Set} : α₀ → α₀ → Set where
  InductiveFixtures:Same:refl : (a₁ : α₀) → InductiveFixtures:Same {α₀} a₁ a₁

-- recursor
InductiveFixtures:Same:rec : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → InductiveFixtures:Same {α₀} a₁ a₂ → Set} → motive₂ a₁ (InductiveFixtures:Same:refl {α₀} a₁) → {a₃ : α₀} → (t₄ : InductiveFixtures:Same {α₀} a₁ a₃) → motive₂ a₃ t₄
InductiveFixtures:Same:rec {α₀} {a₁} {motive₂} refl₃ {_} (InductiveFixtures:Same:refl _) = refl₃

data InductiveFixtures:Sized : U.Init.Prelude.Nat → Set where
  InductiveFixtures:Sized:mk : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Fin n₀ → InductiveFixtures:Sized n₀

-- recursor
InductiveFixtures:Sized:rec : {a₀ : U.Init.Prelude.Nat} → {motive₁ : InductiveFixtures:Sized a₀ → Set} → ((value₂ : U.Init.Prelude.Fin a₀) → motive₁ (InductiveFixtures:Sized:mk a₀ value₂)) → (t₂ : InductiveFixtures:Sized a₀) → motive₁ t₂
InductiveFixtures:Sized:rec {a₀} {motive₁} mk₂ (InductiveFixtures:Sized:mk _ value₃) = mk₂ value₃

record InductiveFixtures:Stream~x27~ : Set where
  inductive
  no-eta-equality
  pattern
  constructor InductiveFixtures:Stream~x27~:mk
  field
    head₀ : U.Init.Prelude.Nat
    tail₁ : U.Init.Prelude.Nat → InductiveFixtures:Stream~x27~

-- recursor
InductiveFixtures:Stream~x27~:rec : {motive₀ : InductiveFixtures:Stream~x27~ → Set} → ((head₁ : U.Init.Prelude.Nat) → (tail₂ : U.Init.Prelude.Nat → InductiveFixtures:Stream~x27~) → ((a₃ : U.Init.Prelude.Nat) → motive₀ (tail₂ a₃)) → motive₀ (InductiveFixtures:Stream~x27~:mk head₁ tail₂)) → (t₁ : InductiveFixtures:Stream~x27~) → motive₀ t₁
InductiveFixtures:Stream~x27~:rec {motive₀} mk₁ (InductiveFixtures:Stream~x27~:mk head₂ tail₃) = mk₁ head₂ tail₃ (λ (a₄ : U.Init.Prelude.Nat) → InductiveFixtures:Stream~x27~:rec {motive₀} mk₁ (tail₃ a₄))

record InductiveFixtures:Token : Set where
  constructor InductiveFixtures:Token:mk

-- recursor
InductiveFixtures:Token:rec : {motive₀ : InductiveFixtures:Token → Set} → motive₀ InductiveFixtures:Token:mk → (t₁ : InductiveFixtures:Token) → motive₀ t₁
InductiveFixtures:Token:rec {motive₀} mk₁ InductiveFixtures:Token:mk = mk₁

data InductiveFixtures:Vec (α₀ : Set) : U.Init.Prelude.Nat → Set where
  InductiveFixtures:Vec:nil : InductiveFixtures:Vec α₀ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)
  InductiveFixtures:Vec:cons : {n₁ : U.Init.Prelude.Nat} → α₀ → InductiveFixtures:Vec α₀ n₁ → InductiveFixtures:Vec α₀ (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ n₁ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄))

-- recursor
InductiveFixtures:Vec:rec : {α₀ : Set} → {motive₁ : (a₁ : U.Init.Prelude.Nat) → InductiveFixtures:Vec α₀ a₁ → Set} → motive₁ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) (InductiveFixtures:Vec:nil {α₀}) → ({n₂ : U.Init.Prelude.Nat} → (head₃ : α₀) → (tail₄ : InductiveFixtures:Vec α₀ n₂) → motive₁ n₂ tail₄ → motive₁ (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ n₂ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)) (InductiveFixtures:Vec:cons {α₀} {n₂} head₃ tail₄)) → {a₂ : U.Init.Prelude.Nat} → (t₃ : InductiveFixtures:Vec α₀ a₂) → motive₁ a₂ t₃
InductiveFixtures:Vec:rec {α₀} {motive₁} nil₂ cons₃ {_} InductiveFixtures:Vec:nil = nil₂
InductiveFixtures:Vec:rec {α₀} {motive₁} nil₂ cons₃ {_} (InductiveFixtures:Vec:cons {n₅} head₆ tail₇) = cons₃ {n₅} head₆ tail₇ (InductiveFixtures:Vec:rec {α₀} {motive₁} nil₂ cons₃ {n₅} tail₇)

InductiveFixtures:Wide:node:~ushare:~n1 : Set
InductiveFixtures:Wide:node:~ushare:~n1 = U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat

InductiveFixtures:Wide:rec:~ushare:~n2 : Set
InductiveFixtures:Wide:rec:~ushare:~n2 = U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat

data InductiveFixtures:Wide : Set where
  InductiveFixtures:Wide:leaf : InductiveFixtures:Wide
  InductiveFixtures:Wide:node : (U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → InductiveFixtures:Wide) → (U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → InductiveFixtures:Wide) → InductiveFixtures:Wide:node:~ushare:~n1 → InductiveFixtures:Wide:node:~ushare:~n1 → InductiveFixtures:Wide

InductiveFixtures:Wide:rec:~ushare:~n1 : Set
InductiveFixtures:Wide:rec:~ushare:~n1 = U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → U.Init.Prelude.Nat → InductiveFixtures:Wide

-- recursor
InductiveFixtures:Wide:rec : {motive₀ : InductiveFixtures:Wide → Set} → motive₀ InductiveFixtures:Wide:leaf → ((f₁ : InductiveFixtures:Wide:rec:~ushare:~n1) → (g₂ : InductiveFixtures:Wide:rec:~ushare:~n1) → (h₃ : InductiveFixtures:Wide:rec:~ushare:~n2) → (k₄ : InductiveFixtures:Wide:rec:~ushare:~n2) → ((a₅ : U.Init.Prelude.Nat) → (a₆ : U.Init.Prelude.Nat) → (a₇ : U.Init.Prelude.Nat) → (a₈ : U.Init.Prelude.Nat) → (a₉ : U.Init.Prelude.Nat) → (a₁₀ : U.Init.Prelude.Nat) → (a₁₁ : U.Init.Prelude.Nat) → (a₁₂ : U.Init.Prelude.Nat) → (a₁₃ : U.Init.Prelude.Nat) → (a₁₄ : U.Init.Prelude.Nat) → (a₁₅ : U.Init.Prelude.Nat) → (a₁₆ : U.Init.Prelude.Nat) → (a₁₇ : U.Init.Prelude.Nat) → (a₁₈ : U.Init.Prelude.Nat) → (a₁₉ : U.Init.Prelude.Nat) → (a₂₀ : U.Init.Prelude.Nat) → motive₀ (f₁ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀)) → ((a₅ : U.Init.Prelude.Nat) → (a₆ : U.Init.Prelude.Nat) → (a₇ : U.Init.Prelude.Nat) → (a₈ : U.Init.Prelude.Nat) → (a₉ : U.Init.Prelude.Nat) → (a₁₀ : U.Init.Prelude.Nat) → (a₁₁ : U.Init.Prelude.Nat) → (a₁₂ : U.Init.Prelude.Nat) → (a₁₃ : U.Init.Prelude.Nat) → (a₁₄ : U.Init.Prelude.Nat) → (a₁₅ : U.Init.Prelude.Nat) → (a₁₆ : U.Init.Prelude.Nat) → (a₁₇ : U.Init.Prelude.Nat) → (a₁₈ : U.Init.Prelude.Nat) → (a₁₉ : U.Init.Prelude.Nat) → (a₂₀ : U.Init.Prelude.Nat) → motive₀ (g₂ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀)) → motive₀ (InductiveFixtures:Wide:node f₁ g₂ h₃ k₄)) → (t₁ : InductiveFixtures:Wide) → motive₀ t₁
InductiveFixtures:Wide:rec {motive₀} leaf₁ node₂ InductiveFixtures:Wide:leaf = leaf₁
InductiveFixtures:Wide:rec {motive₀} leaf₁ node₂ (InductiveFixtures:Wide:node f₃ g₄ h₅ k₆) = node₂ f₃ g₄ h₅ k₆ (λ (a₇ : U.Init.Prelude.Nat) → λ (a₈ : U.Init.Prelude.Nat) → λ (a₉ : U.Init.Prelude.Nat) → λ (a₁₀ : U.Init.Prelude.Nat) → λ (a₁₁ : U.Init.Prelude.Nat) → λ (a₁₂ : U.Init.Prelude.Nat) → λ (a₁₃ : U.Init.Prelude.Nat) → λ (a₁₄ : U.Init.Prelude.Nat) → λ (a₁₅ : U.Init.Prelude.Nat) → λ (a₁₆ : U.Init.Prelude.Nat) → λ (a₁₇ : U.Init.Prelude.Nat) → λ (a₁₈ : U.Init.Prelude.Nat) → λ (a₁₉ : U.Init.Prelude.Nat) → λ (a₂₀ : U.Init.Prelude.Nat) → λ (a₂₁ : U.Init.Prelude.Nat) → λ (a₂₂ : U.Init.Prelude.Nat) → InductiveFixtures:Wide:rec {motive₀} leaf₁ node₂ (f₃ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂)) (λ (a₇ : U.Init.Prelude.Nat) → λ (a₈ : U.Init.Prelude.Nat) → λ (a₉ : U.Init.Prelude.Nat) → λ (a₁₀ : U.Init.Prelude.Nat) → λ (a₁₁ : U.Init.Prelude.Nat) → λ (a₁₂ : U.Init.Prelude.Nat) → λ (a₁₃ : U.Init.Prelude.Nat) → λ (a₁₄ : U.Init.Prelude.Nat) → λ (a₁₅ : U.Init.Prelude.Nat) → λ (a₁₆ : U.Init.Prelude.Nat) → λ (a₁₇ : U.Init.Prelude.Nat) → λ (a₁₈ : U.Init.Prelude.Nat) → λ (a₁₉ : U.Init.Prelude.Nat) → λ (a₂₀ : U.Init.Prelude.Nat) → λ (a₂₁ : U.Init.Prelude.Nat) → λ (a₂₂ : U.Init.Prelude.Nat) → InductiveFixtures:Wide:rec {motive₀} leaf₁ node₂ (g₄ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉ a₂₀ a₂₁ a₂₂))
