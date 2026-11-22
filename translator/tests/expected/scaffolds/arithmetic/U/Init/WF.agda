{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of ArithmeticFixtures:add~uone ArithmeticFixtures:add~usucc ArithmeticFixtures:add~uzero ArithmeticFixtures:beq~usucc~usucc ArithmeticFixtures:beq~usucc~uzero and 49 more
-- Lean module Init.WF
module U.Init.WF where
import U.Init.Core
import U.Init.Data.Nat.Basic
import U.Init.Prelude
import U.Init.SimpLemmas

data Acc {α₀ : Set} (r₁ : α₀ → α₀ → Set) : α₀ → Set where
  Acc:intro : (x₂ : α₀) → ((y₃ : α₀) → r₁ y₃ x₂ → Acc {α₀} r₁ y₃) → Acc {α₀} r₁ x₂

-- recursor
Acc:rec : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {motive₂ : (a₂ : α₀) → Acc {α₀} r₁ a₂ → Set} → ((x₃ : α₀) → (h₄ : (y₄ : α₀) → r₁ y₄ x₃ → Acc {α₀} r₁ y₄) → ((y₅ : α₀) → (a₆ : r₁ y₅ x₃) → motive₂ y₅ (h₄ y₅ a₆)) → motive₂ x₃ (Acc:intro {α₀} {r₁} x₃ h₄)) → {a₃ : α₀} → (t₄ : Acc {α₀} r₁ a₃) → motive₂ a₃ t₄
Acc:rec {α₀} {r₁} {motive₂} intro₃ {_} (Acc:intro x₅ h₆) = intro₃ x₅ h₆ (λ (y₇ : α₀) → λ (a₈ : r₁ y₇ x₅) → Acc:rec {α₀} {r₁} {motive₂} intro₃ {y₇} (h₆ y₇ a₈))

Acc:recOn : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {motive₂ : (a₂ : α₀) → Acc {α₀} r₁ a₂ → Set} → {a₃ : α₀} → (t₄ : Acc {α₀} r₁ a₃) → ((x₅ : α₀) → (h₆ : (y₆ : α₀) → r₁ y₆ x₅ → Acc {α₀} r₁ y₆) → ((y₇ : α₀) → (a₈ : r₁ y₇ x₅) → motive₂ y₇ (h₆ y₇ a₈)) → motive₂ x₅ (Acc:intro {α₀} {r₁} x₅ h₆)) → motive₂ a₃ t₄
Acc:recOn {α₀} {r₁} {motive₂} {a₃} t₄ intro₅ = Acc:rec {α₀} {r₁} {motive₂} intro₅ {a₃} t₄

-- theorem
opaque
  Acc:inv : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {x₂ : α₀} → {y₃ : α₀} → Acc {α₀} r₁ x₂ → r₁ y₃ x₂ → Acc {α₀} r₁ y₃
  Acc:inv {α₀} {r₁} {x₂} {y₃} h₄ h₅ = Acc:recOn {α₀} {r₁} {λ (x₆ : α₀) → λ (x₇ : Acc {α₀} r₁ x₆) → r₁ y₃ x₆ → Acc {α₀} r₁ y₃} {x₂} h₄ (λ (x₆ : α₀) → λ (ac₇ : (y₇ : α₀) → r₁ y₇ x₆ → Acc {α₀} r₁ y₇) → λ (x₈ : (y₈ : α₀) → r₁ y₈ x₆ → r₁ y₃ y₈ → Acc {α₀} r₁ y₃) → λ (h₉ : r₁ y₃ x₆) → ac₇ y₃ h₉) h₅

WellFounded:Nat:eager : U.Init.Prelude.Nat → U.Init.Prelude.Nat
WellFounded:Nat:eager n₀ = U.Init.Prelude.ite {U.Init.Prelude.Nat} (U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:beq n₀ n₀) U.Init.Prelude.Bool:true) ⦃ U.Init.Prelude.instDecidableEqBool (U.Init.Prelude.Nat:beq n₀ n₀) U.Init.Prelude.Bool:true ⦄ n₀ n₀

-- theorem
opaque
  WellFounded:Nat:eager~ueq : (n₀ : U.Init.Prelude.Nat) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (WellFounded:Nat:eager n₀) n₀
  WellFounded:Nat:eager~ueq n₀ = U.Init.SimpLemmas.ite~uself {U.Init.Prelude.Nat} {U.Init.Prelude.Eq {U.Init.Prelude.Bool} (U.Init.Prelude.Nat:beq n₀ n₀) U.Init.Prelude.Bool:true} {U.Init.Prelude.instDecidableEqBool (U.Init.Prelude.Nat:beq n₀ n₀) U.Init.Prelude.Bool:true} n₀

-- theorem
opaque
  WellFounded:Nat:fix:~uproof~u2 : {α₀ : Set} → (h₁ : α₀ → U.Init.Prelude.Nat) → (x₂ : α₀) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (h₁ x₂) (WellFounded:Nat:eager (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (h₁ x₂) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)))
  WellFounded:Nat:fix:~uproof~u2 {α₀} h₁ x₂ = U.Init.Prelude.Eq:rec {U.Init.Prelude.Nat} {U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (h₁ x₂) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)} {λ (x₃ : U.Init.Prelude.Nat) → λ (h₄ : U.Init.Prelude.Eq {U.Init.Prelude.Nat} (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (h₁ x₂) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)) x₃) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (h₁ x₂) x₃} (U.Init.Prelude.Nat:lt~uadd~uone (h₁ x₂)) {WellFounded:Nat:eager (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (h₁ x₂) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄))} (U.Init.Prelude.Eq:symm {U.Init.Prelude.Nat} {WellFounded:Nat:eager (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (h₁ x₂) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄))} {U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (h₁ x₂) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄)} (WellFounded:Nat:eager~ueq (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (h₁ x₂) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄))))

-- theorem
opaque
  WellFounded:Nat:fix:~uproof~u1 : {α₀ : Set} → (h₁ : α₀ → U.Init.Prelude.Nat) → (x₂ : U.Init.Prelude.Nat) → (x₃ : α₀) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (h₁ x₃) (U.Init.Prelude.Nat:succ x₂) → (y₄ : α₀) → U.Init.Core.InvImage {α₀} {U.Init.Prelude.Nat} (λ (x1₅ : U.Init.Prelude.Nat) → λ (x2₆ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₅ x2₆) h₁ y₄ x₃ → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (h₁ y₄) x₂
  WellFounded:Nat:fix:~uproof~u1 {α₀} h₁ x₂ x₃ hfuel₄ y₅ hy₆ = U.Init.Prelude.Nat:lt~uof~ult~uof~ule {h₁ y₅} {h₁ x₃} {x₂} hy₆ (U.Init.Data.Nat.Basic.Nat:le~uof~ult~uadd~uone {h₁ x₃} {x₂} hfuel₄)

-- theorem
opaque
  WellFounded:Nat:fix:go:~uproof~u1 : {α₀ : Set} → (h₁ : α₀ → U.Init.Prelude.Nat) → (x₂ : α₀) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (h₁ x₂) U.Init.Prelude.Nat:zero → U.Init.Prelude.False
  WellFounded:Nat:fix:go:~uproof~u1 {α₀} h₁ x₂ hfuel₃ = U.Init.Prelude.Nat:not~usucc~ule~uzero (h₁ x₂) hfuel₃

WellFounded:Nat:fix:go : {α₀ : Set} → {motive₁ : α₀ → Set} → (h₂ : α₀ → U.Init.Prelude.Nat) → ((x₃ : α₀) → ((y₄ : α₀) → U.Init.Core.InvImage {α₀} {U.Init.Prelude.Nat} (λ (x1₅ : U.Init.Prelude.Nat) → λ (x2₆ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₅ x2₆) h₂ y₄ x₃ → motive₁ y₄) → motive₁ x₃) → (fuel₃ : U.Init.Prelude.Nat) → (x₄ : α₀) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (h₂ x₄) fuel₃ → motive₁ x₄
WellFounded:Nat:fix:go {α₀} {motive₁} h₂ F₃ fuel₄ = U.Init.Prelude.Nat:rec {λ (x₅ : U.Init.Prelude.Nat) → (x₆ : α₀) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (h₂ x₆) x₅ → motive₁ x₆} (λ (x₅ : α₀) → λ (hfuel₆ : U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (h₂ x₅) U.Init.Prelude.Nat:zero) → U.Init.Prelude.False:elim {motive₁ x₅} (WellFounded:Nat:fix:go:~uproof~u1 {α₀} h₂ x₅ hfuel₆)) (λ (x₅ : U.Init.Prelude.Nat) → λ (ih₆ : (x₆ : α₀) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (h₂ x₆) x₅ → motive₁ x₆) → λ (x₇ : α₀) → λ (hfuel₈ : U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ (h₂ x₇) (U.Init.Prelude.Nat:succ x₅)) → F₃ x₇ (λ (y₉ : α₀) → λ (hy₁₀ : U.Init.Core.InvImage {α₀} {U.Init.Prelude.Nat} (λ (x1₁₀ : U.Init.Prelude.Nat) → λ (x2₁₁ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₁₀ x2₁₁) h₂ y₉ x₇) → ih₆ y₉ (WellFounded:Nat:fix:~uproof~u1 {α₀} h₂ x₅ x₇ hfuel₈ y₉ hy₁₀))) fuel₄

WellFounded:Nat:fix : {α₀ : Set} → {motive₁ : α₀ → Set} → (h₂ : α₀ → U.Init.Prelude.Nat) → ((x₃ : α₀) → ((y₄ : α₀) → U.Init.Core.InvImage {α₀} {U.Init.Prelude.Nat} (λ (x1₅ : U.Init.Prelude.Nat) → λ (x2₆ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₅ x2₆) h₂ y₄ x₃ → motive₁ y₄) → motive₁ x₃) → (x₃ : α₀) → motive₁ x₃
WellFounded:Nat:fix {α₀} {motive₁} h₂ F₃ x₄ = WellFounded:Nat:fix:go {α₀} {motive₁} h₂ F₃ (WellFounded:Nat:eager (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (h₂ x₄) (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄))) x₄ (WellFounded:Nat:fix:~uproof~u2 {α₀} h₂ x₄)

record WellFounded {α₀ : Set} (r₁ : α₀ → α₀ → Set) : Set where
  constructor WellFounded:intro
  field
    h₂ : (a₂ : α₀) → Acc {α₀} r₁ a₂

-- recursor
WellFounded:rec : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {motive₂ : WellFounded {α₀} r₁ → Set} → ((h₃ : (a₃ : α₀) → Acc {α₀} r₁ a₃) → motive₂ (WellFounded:intro {α₀} {r₁} h₃)) → (t₃ : WellFounded {α₀} r₁) → motive₂ t₃
WellFounded:rec {α₀} {r₁} {motive₂} intro₃ (WellFounded:intro h₄) = intro₃ h₄

~uprivate:Init:WF:~n0:Nat:lt~uwfRel:match~u1 : (n₀ : U.Init.Prelude.Nat) → (m₁ : U.Init.Prelude.Nat) → (motive₂ : U.Init.Prelude.Or (U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₁ n₀) (U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₁ n₀) → Set) → (this₃ : U.Init.Prelude.Or (U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₁ n₀) (U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₁ n₀)) → ((e₄ : U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₁ n₀) → motive₂ (U.Init.Prelude.Or:inl {U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₁ n₀} {U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₁ n₀} e₄)) → ((e₄ : U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₁ n₀) → motive₂ (U.Init.Prelude.Or:inr {U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₁ n₀} {U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₁ n₀} e₄)) → motive₂ this₃
~uprivate:Init:WF:~n0:Nat:lt~uwfRel:match~u1 n₀ m₁ motive₂ this₃ h1₄ h2₅ = U.Init.Prelude.Or:casesOn {U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₁ n₀} {U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₁ n₀} {λ (x₆ : U.Init.Prelude.Or (U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₁ n₀) (U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₁ n₀)) → motive₂ x₆} this₃ (λ (h₆ : U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₁ n₀) → h1₄ h₆) (λ (h₆ : U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₁ n₀) → h2₅ h₆)

-- theorem
opaque
  Nat:lt~uwfRel:~uproof~u3 : WellFounded {U.Init.Prelude.Nat} (λ (x1₀ : U.Init.Prelude.Nat) → λ (x2₁ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₀ x2₁)
  Nat:lt~uwfRel:~uproof~u3 = WellFounded:intro {U.Init.Prelude.Nat} {λ (x1₀ : U.Init.Prelude.Nat) → λ (x2₁ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₀ x2₁} (λ (n₀ : U.Init.Prelude.Nat) → U.Init.Data.Nat.Basic.Nat:recAux {λ (n₁ : U.Init.Prelude.Nat) → Acc {U.Init.Prelude.Nat} (λ (x1₂ : U.Init.Prelude.Nat) → λ (x2₃ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₂ x2₃) n₁} (Acc:intro {U.Init.Prelude.Nat} {λ (x1₁ : U.Init.Prelude.Nat) → λ (x2₂ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₁ x2₂} (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄) (λ (y₁ : U.Init.Prelude.Nat) → λ (h₂ : U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ y₁ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)) → U.Init.Prelude.absurd {U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ y₁ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)} {Acc {U.Init.Prelude.Nat} (λ (x1₃ : U.Init.Prelude.Nat) → λ (x2₄ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₃ x2₄) y₁} h₂ (U.Init.Prelude.Nat:not~ult~uzero y₁))) (λ (n₁ : U.Init.Prelude.Nat) → λ (ih₂ : Acc {U.Init.Prelude.Nat} (λ (x1₂ : U.Init.Prelude.Nat) → λ (x2₃ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₂ x2₃) n₁) → Acc:intro {U.Init.Prelude.Nat} {λ (x1₃ : U.Init.Prelude.Nat) → λ (x2₄ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₃ x2₄} (U.Init.Prelude.Nat:succ n₁) (λ (m₃ : U.Init.Prelude.Nat) → λ (h₄ : U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₃ (U.Init.Prelude.Nat:succ n₁)) → let this₅ : U.Init.Prelude.Or (U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₃ n₁) (U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₃ n₁); this₅ = U.Init.Prelude.Nat:eq~uor~ult~uof~ule {m₃} {n₁} (U.Init.Prelude.Nat:le~uof~usucc~ule~usucc {m₃} {n₁} h₄) in ~uprivate:Init:WF:~n0:Nat:lt~uwfRel:match~u1 n₁ m₃ (λ (this₆ : U.Init.Prelude.Or (U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₃ n₁) (U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₃ n₁)) → Acc {U.Init.Prelude.Nat} (λ (x1₇ : U.Init.Prelude.Nat) → λ (x2₈ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₇ x2₈) m₃) this₅ (λ (e₆ : U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₃ n₁) → U.Init.Prelude.Eq:ndrec {U.Init.Prelude.Nat} {m₃} {λ (n₇ : U.Init.Prelude.Nat) → Acc {U.Init.Prelude.Nat} (λ (x1₈ : U.Init.Prelude.Nat) → λ (x2₉ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₈ x2₉) n₇ → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₃ (U.Init.Prelude.Nat:succ n₇) → U.Init.Prelude.Or (U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₃ n₇) (U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₃ n₇) → Acc {U.Init.Prelude.Nat} (λ (x1₈ : U.Init.Prelude.Nat) → λ (x2₉ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₈ x2₉) m₃} (λ (ih₇ : Acc {U.Init.Prelude.Nat} (λ (x1₇ : U.Init.Prelude.Nat) → λ (x2₈ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₇ x2₈) m₃) → λ (h₈ : U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₃ (U.Init.Prelude.Nat:succ m₃)) → λ (this₉ : U.Init.Prelude.Or (U.Init.Prelude.Eq {U.Init.Prelude.Nat} m₃ m₃) (U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₃ m₃)) → ih₇) {n₁} e₆ ih₂ h₄ this₅) (λ (e₆ : U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₃ n₁) → Acc:inv {U.Init.Prelude.Nat} {λ (x1₇ : U.Init.Prelude.Nat) → λ (x2₈ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₇ x2₈} {n₁} {m₃} ih₂ e₆))) n₀)

record WellFoundedRelation (α₀ : Set) : Set where
  constructor WellFoundedRelation:mk
  field
    rel₁ : α₀ → α₀ → Set
    wf₂ : WellFounded {α₀} rel₁

-- recursor
WellFoundedRelation:rec : {α₀ : Set} → {motive₁ : WellFoundedRelation α₀ → Set} → ((rel₂ : α₀ → α₀ → Set) → (wf₃ : WellFounded {α₀} rel₂) → motive₁ (WellFoundedRelation:mk {α₀} rel₂ wf₃)) → (t₂ : WellFoundedRelation α₀) → motive₁ t₂
WellFoundedRelation:rec {α₀} {motive₁} mk₂ (WellFoundedRelation:mk rel₃ wf₄) = mk₂ rel₃ wf₄

Nat:lt~uwfRel : WellFoundedRelation U.Init.Prelude.Nat
Nat:lt~uwfRel = WellFoundedRelation:mk {U.Init.Prelude.Nat} (λ (x1₀ : U.Init.Prelude.Nat) → λ (x2₁ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ x1₀ x2₁) Nat:lt~uwfRel:~uproof~u3

-- theorem
opaque
  WellFounded:apply : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → WellFounded {α₀} r₁ → (a₂ : α₀) → Acc {α₀} r₁ a₂
  WellFounded:apply {α₀} {r₁} wf₂ a₃ = WellFounded:rec {α₀} {r₁} {λ (x₄ : WellFounded {α₀} r₁) → (x₅ : α₀) → Acc {α₀} r₁ x₅} (λ (p₄ : (a₄ : α₀) → Acc {α₀} r₁ a₄) → p₄) wf₂ a₃

WellFounded:fixF : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {C₂ : α₀ → Set} → ((x₃ : α₀) → ((y₄ : α₀) → r₁ y₄ x₃ → C₂ y₄) → C₂ x₃) → (x₃ : α₀) → Acc {α₀} r₁ x₃ → C₂ x₃
WellFounded:fixF {α₀} {r₁} {C₂} F₃ x₄ a₅ = Acc:rec {α₀} {r₁} {λ (x₆ : α₀) → λ (a₇ : Acc {α₀} r₁ x₆) → C₂ x₆} (λ (x₆ : α₀) → λ (h₇ : (y₇ : α₀) → r₁ y₇ x₆ → Acc {α₀} r₁ y₇) → λ (ih₈ : (y₈ : α₀) → r₁ y₈ x₆ → C₂ y₈) → F₃ x₆ ih₈) {x₄} a₅

WellFounded:fix : {α₀ : Set} → {C₁ : α₀ → Set} → {r₂ : α₀ → α₀ → Set} → WellFounded {α₀} r₂ → ((x₃ : α₀) → ((y₄ : α₀) → r₂ y₄ x₃ → C₁ y₄) → C₁ x₃) → (x₃ : α₀) → C₁ x₃
WellFounded:fix {α₀} {C₁} {r₂} hwf₃ F₄ x₅ = WellFounded:fixF {α₀} {r₂} {C₁} F₄ x₅ (WellFounded:apply {α₀} {r₂} hwf₃ x₅)

WellFoundedRelation:rel : {α₀ : Set} → ⦃ _ : WellFoundedRelation α₀ ⦄ → α₀ → α₀ → Set
WellFoundedRelation:rel {α₀} ⦃ self₁ ⦄ = WellFoundedRelation.rel₁ {α₀} self₁

-- theorem
opaque
  WellFoundedRelation:wf : {α₀ : Set} → ⦃ self₁ : WellFoundedRelation α₀ ⦄ → WellFounded {α₀} (WellFoundedRelation:rel {α₀} ⦃ self₁ ⦄)
  WellFoundedRelation:wf {α₀} ⦃ self₁ ⦄ = WellFoundedRelation.wf₂ {α₀} self₁

Nat:strongRecOn : {motive₀ : U.Init.Prelude.Nat → Set} → (n₁ : U.Init.Prelude.Nat) → ((n₂ : U.Init.Prelude.Nat) → ((m₃ : U.Init.Prelude.Nat) → U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ m₃ n₂ → motive₀ m₃) → motive₀ n₂) → motive₀ n₁
Nat:strongRecOn {motive₀} n₁ ind₂ = WellFounded:fix {U.Init.Prelude.Nat} {motive₀} {WellFoundedRelation:rel {U.Init.Prelude.Nat} ⦃ Nat:lt~uwfRel ⦄} (WellFoundedRelation:wf {U.Init.Prelude.Nat} ⦃ Nat:lt~uwfRel ⦄) ind₂ n₁
