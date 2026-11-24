{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of LevelFixtures:Box LevelFixtures:Box:~usizeOf~u1 LevelFixtures:Box:~usizeOf~uinst LevelFixtures:Box:casesOn LevelFixtures:Box:ctorIdx and 149 more
-- Lean module Init.SizeOf
module U.Init.SizeOf where
import U.Init.Prelude

record SizeOf#n (α₀ : Set) : Set where
  constructor SizeOf:mk#n
  field
    sizeOf₁ : α₀ → U.Init.Prelude.Nat

SizeOf:sizeOf#n : {α₀ : Set} → ⦃ _ : SizeOf#n α₀ ⦄ → α₀ → U.Init.Prelude.Nat
SizeOf:sizeOf#n {α₀} ⦃ self₁ ⦄ = SizeOf#n.sizeOf₁ {α₀} self₁

record SizeOf#z (α₀ : Set) : Set where
  constructor SizeOf:mk#z
  field
    sizeOf₁ : α₀ → U.Init.Prelude.Nat

SizeOf:sizeOf#z : {α₀ : Set} → ⦃ _ : SizeOf#z α₀ ⦄ → α₀ → U.Init.Prelude.Nat
SizeOf:sizeOf#z {α₀} ⦃ self₁ ⦄ = SizeOf#z.sizeOf₁ {α₀} self₁

default:sizeOf:match~u1#nn : (α₀ : Set) → (motive₁ : α₀ → Set) → (x₂ : α₀) → ((x₃ : α₀) → motive₁ x₃) → motive₁ x₂
default:sizeOf:match~u1#nn α₀ motive₁ x₂ h1₃ = h1₃ x₂

default:sizeOf#n : (α₀ : Set) → α₀ → U.Init.Prelude.Nat
default:sizeOf#n α₀ x₁ = default:sizeOf:match~u1#nn α₀ (λ (x₂ : α₀) → U.Init.Prelude.Nat) x₁ (λ (x₂ : α₀) → U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)

instSizeOfDefault#n : (α₀ : Set) → SizeOf#n α₀
instSizeOfDefault#n α₀ = SizeOf:mk#n {α₀} (default:sizeOf#n α₀)

default:sizeOf:match~u1#nz : (α₀ : Set) → (motive₁ : α₀ → Set) → (x₂ : α₀) → ((x₃ : α₀) → motive₁ x₃) → motive₁ x₂
default:sizeOf:match~u1#nz α₀ motive₁ x₂ h1₃ = h1₃ x₂

default:sizeOf#z : (α₀ : Set) → α₀ → U.Init.Prelude.Nat
default:sizeOf#z α₀ x₁ = default:sizeOf:match~u1#nz α₀ (λ (x₂ : α₀) → U.Init.Prelude.Nat) x₁ (λ (x₂ : α₀) → U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)

instSizeOfDefault#z : (α₀ : Set) → SizeOf#z α₀
instSizeOfDefault#z α₀ = SizeOf:mk#z {α₀} (default:sizeOf#z α₀)

List:~usizeOf~u1 : {α₀ : Set} → ⦃ _ : SizeOf#n α₀ ⦄ → U.Init.Prelude.List α₀ → U.Init.Prelude.Nat
List:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ t₂ = U.Init.Prelude.List:rec#n {α₀} {λ (t₃ : U.Init.Prelude.List α₀) → U.Init.Prelude.Nat} (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (λ (head₃ : α₀) → λ (tail₄ : U.Init.Prelude.List α₀) → λ (tailih₅ : U.Init.Prelude.Nat) → U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf#n {α₀} ⦃ inst₁ ⦄ head₃)) tailih₅) t₂

List:~usizeOf~uinst : (α₀ : Set) → ⦃ _ : SizeOf#n α₀ ⦄ → SizeOf#n (U.Init.Prelude.List α₀)
List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ = SizeOf:mk#n {U.Init.Prelude.List α₀} (λ (m₂ : U.Init.Prelude.List α₀) → List:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ m₂)

-- theorem
opaque
  List:cons:sizeOf~uspec : {α₀ : Set} → ⦃ inst₁ : SizeOf#n α₀ ⦄ → (head₂ : α₀) → (tail₃ : U.Init.Prelude.List α₀) → U.Init.Prelude.Eq#n {U.Init.Prelude.Nat} (SizeOf:sizeOf#n {U.Init.Prelude.List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ (U.Init.Prelude.List:cons {α₀} head₂ tail₃)) (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf#n {α₀} ⦃ inst₁ ⦄ head₂)) (SizeOf:sizeOf#n {U.Init.Prelude.List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ tail₃))
  List:cons:sizeOf~uspec {α₀} ⦃ inst₁ ⦄ head₂ tail₃ = U.Init.Prelude.Eq:refl#n {U.Init.Prelude.Nat} (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf#n {α₀} ⦃ inst₁ ⦄ head₂)) (SizeOf:sizeOf#n {U.Init.Prelude.List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ tail₃))
