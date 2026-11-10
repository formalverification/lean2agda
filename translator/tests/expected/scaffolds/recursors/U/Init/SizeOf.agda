{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of RecursorFixtures:Doc RecursorFixtures:Doc:~usizeOf~u1 RecursorFixtures:Doc:~usizeOf~u2 RecursorFixtures:Doc:~usizeOf~u2~ueq RecursorFixtures:Doc:~usizeOf~u3 and 251 more
-- Lean module Init.SizeOf
module U.Init.SizeOf where
import U.Init.Prelude

record SizeOf (α₀ : Set) : Set where
  constructor SizeOf:mk
  field
    sizeOf₁ : α₀ → U.Init.Prelude.Nat

-- recursor
SizeOf:rec : {α₀ : Set} → {motive₁ : SizeOf α₀ → Set} → ((sizeOf₂ : α₀ → U.Init.Prelude.Nat) → motive₁ (SizeOf:mk {α₀} sizeOf₂)) → (t₂ : SizeOf α₀) → motive₁ t₂
SizeOf:rec {α₀} {motive₁} mk₂ (SizeOf:mk sizeOf₃) = mk₂ sizeOf₃

SizeOf:sizeOf : {α₀ : Set} → ⦃ _ : SizeOf α₀ ⦄ → α₀ → U.Init.Prelude.Nat
SizeOf:sizeOf {α₀} ⦃ self₁ ⦄ = SizeOf.sizeOf₁ {α₀} self₁

List:~usizeOf~u1 : {α₀ : Set} → ⦃ _ : SizeOf α₀ ⦄ → U.Init.Prelude.List α₀ → U.Init.Prelude.Nat
List:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ t₂ = U.Init.Prelude.List:rec {α₀} {λ (t₃ : U.Init.Prelude.List α₀) → U.Init.Prelude.Nat} (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (λ (head₃ : α₀) → λ (tail₄ : U.Init.Prelude.List α₀) → λ (tailih₅ : U.Init.Prelude.Nat) → U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf {α₀} ⦃ inst₁ ⦄ head₃)) tailih₅) t₂

List:~usizeOf~uinst : (α₀ : Set) → ⦃ _ : SizeOf α₀ ⦄ → SizeOf (U.Init.Prelude.List α₀)
List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ = SizeOf:mk {U.Init.Prelude.List α₀} (λ (m₂ : U.Init.Prelude.List α₀) → List:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ m₂)

Array:~usizeOf~u1 : {α₀ : Set} → ⦃ _ : SizeOf α₀ ⦄ → U.Init.Prelude.Array α₀ → U.Init.Prelude.Nat
Array:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ t₂ = U.Init.Prelude.Array:rec {α₀} {λ (t₃ : U.Init.Prelude.Array α₀) → U.Init.Prelude.Nat} (λ (toList₃ : U.Init.Prelude.List α₀) → U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf {U.Init.Prelude.List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ toList₃)) t₂

Array:~usizeOf~uinst : (α₀ : Set) → ⦃ _ : SizeOf α₀ ⦄ → SizeOf (U.Init.Prelude.Array α₀)
Array:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ = SizeOf:mk {U.Init.Prelude.Array α₀} (λ (m₂ : U.Init.Prelude.Array α₀) → Array:~usizeOf~u1 {α₀} ⦃ inst₁ ⦄ m₂)

-- theorem
opaque
  Array:mk:sizeOf~uspec : {α₀ : Set} → ⦃ inst₁ : SizeOf α₀ ⦄ → (toList₂ : U.Init.Prelude.List α₀) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (SizeOf:sizeOf {U.Init.Prelude.Array α₀} ⦃ Array:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ (U.Init.Prelude.Array:mk {α₀} toList₂)) (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf {U.Init.Prelude.List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ toList₂))
  Array:mk:sizeOf~uspec {α₀} ⦃ inst₁ ⦄ toList₂ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf {U.Init.Prelude.List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ toList₂))

default:sizeOf:match~u1 : (α₀ : Set) → (motive₁ : α₀ → Set) → (x₂ : α₀) → ((x₃ : α₀) → motive₁ x₃) → motive₁ x₂
default:sizeOf:match~u1 α₀ motive₁ x₂ h1₃ = h1₃ x₂

default:sizeOf : (α₀ : Set) → α₀ → U.Init.Prelude.Nat
default:sizeOf α₀ x₁ = default:sizeOf:match~u1 α₀ (λ (x₂ : α₀) → U.Init.Prelude.Nat) x₁ (λ (x₂ : α₀) → U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 0 ⦃ U.Init.Prelude.instOfNatNat 0 ⦄)

instSizeOfDefault : (α₀ : Set) → SizeOf α₀
instSizeOfDefault α₀ = SizeOf:mk {α₀} (default:sizeOf α₀)

instSizeOfNat : SizeOf U.Init.Prelude.Nat
instSizeOfNat = SizeOf:mk {U.Init.Prelude.Nat} (λ (n₀ : U.Init.Prelude.Nat) → n₀)

Fin:~usizeOf~u1 : {n₀ : U.Init.Prelude.Nat} → U.Init.Prelude.Fin n₀ → U.Init.Prelude.Nat
Fin:~usizeOf~u1 {n₀} t₁ = U.Init.Prelude.Fin:rec {n₀} {λ (t₂ : U.Init.Prelude.Fin n₀) → U.Init.Prelude.Nat} (λ (val₂ : U.Init.Prelude.Nat) → λ (isLt₃ : U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ val₂ n₀) → U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf {U.Init.Prelude.Nat} ⦃ instSizeOfNat ⦄ val₂)) (SizeOf:sizeOf {U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ val₂ n₀} ⦃ instSizeOfDefault (U.Init.Prelude.LT:lt {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instLTNat ⦄ val₂ n₀) ⦄ isLt₃)) t₁

Fin:~usizeOf~uinst : (n₀ : U.Init.Prelude.Nat) → SizeOf (U.Init.Prelude.Fin n₀)
Fin:~usizeOf~uinst n₀ = SizeOf:mk {U.Init.Prelude.Fin n₀} (λ (m₁ : U.Init.Prelude.Fin n₀) → Fin:~usizeOf~u1 {n₀} m₁)

-- theorem
opaque
  List:cons:sizeOf~uspec : {α₀ : Set} → ⦃ inst₁ : SizeOf α₀ ⦄ → (head₂ : α₀) → (tail₃ : U.Init.Prelude.List α₀) → U.Init.Prelude.Eq {U.Init.Prelude.Nat} (SizeOf:sizeOf {U.Init.Prelude.List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ (U.Init.Prelude.List:cons {α₀} head₂ tail₃)) (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf {α₀} ⦃ inst₁ ⦄ head₂)) (SizeOf:sizeOf {U.Init.Prelude.List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ tail₃))
  List:cons:sizeOf~uspec {α₀} ⦃ inst₁ ⦄ head₂ tail₃ = U.Init.Prelude.Eq:refl {U.Init.Prelude.Nat} (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf {α₀} ⦃ inst₁ ⦄ head₂)) (SizeOf:sizeOf {U.Init.Prelude.List α₀} ⦃ List:~usizeOf~uinst α₀ ⦃ inst₁ ⦄ ⦄ tail₃))

Prod:~usizeOf~u1 : {α₀ : Set} → {β₁ : Set} → ⦃ _ : SizeOf α₀ ⦄ → ⦃ _ : SizeOf β₁ ⦄ → U.Init.Prelude.Prod α₀ β₁ → U.Init.Prelude.Nat
Prod:~usizeOf~u1 {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ t₄ = U.Init.Prelude.Prod:rec {α₀} {β₁} {λ (t₅ : U.Init.Prelude.Prod α₀ β₁) → U.Init.Prelude.Nat} (λ (fst₅ : α₀) → λ (snd₆ : β₁) → U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.HAdd:hAdd {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instHAdd {U.Init.Prelude.Nat} ⦃ U.Init.Prelude.instAddNat ⦄ ⦄ (U.Init.Prelude.OfNat:ofNat {U.Init.Prelude.Nat} 1 ⦃ U.Init.Prelude.instOfNatNat 1 ⦄) (SizeOf:sizeOf {α₀} ⦃ inst₂ ⦄ fst₅)) (SizeOf:sizeOf {β₁} ⦃ inst₃ ⦄ snd₆)) t₄

Prod:~usizeOf~uinst : (α₀ : Set) → (β₁ : Set) → ⦃ _ : SizeOf α₀ ⦄ → ⦃ _ : SizeOf β₁ ⦄ → SizeOf (U.Init.Prelude.Prod α₀ β₁)
Prod:~usizeOf~uinst α₀ β₁ ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ = SizeOf:mk {U.Init.Prelude.Prod α₀ β₁} (λ (m₄ : U.Init.Prelude.Prod α₀ β₁) → Prod:~usizeOf~u1 {α₀} {β₁} ⦃ inst₂ ⦄ ⦃ inst₃ ⦄ m₄)
