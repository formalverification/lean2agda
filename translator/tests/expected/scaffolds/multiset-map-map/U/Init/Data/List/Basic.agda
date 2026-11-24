{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of Multiset:map~umap
-- Lean module Init.Data.List.Basic
module U.Init.Data.List.Basic where
import U.Init.Prelude

data List:Perm {α₀ : Set} : U.Init.Prelude.List α₀ → U.Init.Prelude.List α₀ → Set where
  List:Perm:nil : List:Perm {α₀} (U.Init.Prelude.List:nil {α₀}) (U.Init.Prelude.List:nil {α₀})
  List:Perm:cons : (x₁ : α₀) → {l₂ : U.Init.Prelude.List α₀} → {l₃ : U.Init.Prelude.List α₀} → List:Perm {α₀} l₂ l₃ → List:Perm {α₀} (U.Init.Prelude.List:cons {α₀} x₁ l₂) (U.Init.Prelude.List:cons {α₀} x₁ l₃)
  List:Perm:swap : (x₁ : α₀) → (y₂ : α₀) → (l₃ : U.Init.Prelude.List α₀) → List:Perm {α₀} (U.Init.Prelude.List:cons {α₀} y₂ (U.Init.Prelude.List:cons {α₀} x₁ l₃)) (U.Init.Prelude.List:cons {α₀} x₁ (U.Init.Prelude.List:cons {α₀} y₂ l₃))
  List:Perm:trans : {l₁ : U.Init.Prelude.List α₀} → {l₂ : U.Init.Prelude.List α₀} → {l₃ : U.Init.Prelude.List α₀} → List:Perm {α₀} l₁ l₂ → List:Perm {α₀} l₂ l₃ → List:Perm {α₀} l₁ l₃

-- recursor
List:Perm:rec : {α₀ : Set} → {motive₁ : (a₁ : U.Init.Prelude.List α₀) → (a₂ : U.Init.Prelude.List α₀) → List:Perm {α₀} a₁ a₂ → Set} → motive₁ (U.Init.Prelude.List:nil {α₀}) (U.Init.Prelude.List:nil {α₀}) (List:Perm:nil {α₀}) → ((x₂ : α₀) → {l₃ : U.Init.Prelude.List α₀} → {l₄ : U.Init.Prelude.List α₀} → (a₅ : List:Perm {α₀} l₃ l₄) → motive₁ l₃ l₄ a₅ → motive₁ (U.Init.Prelude.List:cons {α₀} x₂ l₃) (U.Init.Prelude.List:cons {α₀} x₂ l₄) (List:Perm:cons {α₀} x₂ {l₃} {l₄} a₅)) → ((x₂ : α₀) → (y₃ : α₀) → (l₄ : U.Init.Prelude.List α₀) → motive₁ (U.Init.Prelude.List:cons {α₀} y₃ (U.Init.Prelude.List:cons {α₀} x₂ l₄)) (U.Init.Prelude.List:cons {α₀} x₂ (U.Init.Prelude.List:cons {α₀} y₃ l₄)) (List:Perm:swap {α₀} x₂ y₃ l₄)) → ({l₂ : U.Init.Prelude.List α₀} → {l₃ : U.Init.Prelude.List α₀} → {l₄ : U.Init.Prelude.List α₀} → (a₅ : List:Perm {α₀} l₂ l₃) → (a₆ : List:Perm {α₀} l₃ l₄) → motive₁ l₂ l₃ a₅ → motive₁ l₃ l₄ a₆ → motive₁ l₂ l₄ (List:Perm:trans {α₀} {l₂} {l₃} {l₄} a₅ a₆)) → {a₂ : U.Init.Prelude.List α₀} → {a₃ : U.Init.Prelude.List α₀} → (t₄ : List:Perm {α₀} a₂ a₃) → motive₁ a₂ a₃ t₄
List:Perm:rec {α₀} {motive₁} nil₂ cons₃ swap₄ trans₅ {_} {_} List:Perm:nil = nil₂
List:Perm:rec {α₀} {motive₁} nil₂ cons₃ swap₄ trans₅ {_} {_} (List:Perm:cons x₈ {l₉} {l₁₀} a₁₁) = cons₃ x₈ {l₉} {l₁₀} a₁₁ (List:Perm:rec {α₀} {motive₁} nil₂ cons₃ swap₄ trans₅ {l₉} {l₁₀} a₁₁)
List:Perm:rec {α₀} {motive₁} nil₂ cons₃ swap₄ trans₅ {_} {_} (List:Perm:swap x₈ y₉ l₁₀) = swap₄ x₈ y₉ l₁₀
List:Perm:rec {α₀} {motive₁} nil₂ cons₃ swap₄ trans₅ {_} {_} (List:Perm:trans {l₈} {l₉} {l₁₀} a₁₁ a₁₂) = trans₅ {l₈} {l₉} {l₁₀} a₁₁ a₁₂ (List:Perm:rec {α₀} {motive₁} nil₂ cons₃ swap₄ trans₅ {l₈} {l₉} a₁₁) (List:Perm:rec {α₀} {motive₁} nil₂ cons₃ swap₄ trans₅ {l₉} {l₁₀} a₁₂)

List:filterMap:match~u1 : {β₀ : Set} → (motive₁ : U.Init.Prelude.Option β₀ → Set) → (x₂ : U.Init.Prelude.Option β₀) → (U.Init.Prelude.Unit → motive₁ (U.Init.Prelude.Option:none {β₀})) → ((b₃ : β₀) → motive₁ (U.Init.Prelude.Option:some {β₀} b₃)) → motive₁ x₂
List:filterMap:match~u1 {β₀} motive₁ x₂ h1₃ h2₄ = U.Init.Prelude.Option:casesOn {β₀} {λ (x₅ : U.Init.Prelude.Option β₀) → motive₁ x₅} x₂ (h1₃ U.Init.Prelude.Unit:unit) (λ (val₅ : β₀) → h2₄ val₅)

List:getLast~x3f~:match~u1 : {α₀ : Set} → (motive₁ : U.Init.Prelude.List α₀ → Set) → (x₂ : U.Init.Prelude.List α₀) → (U.Init.Prelude.Unit → motive₁ (U.Init.Prelude.List:nil {α₀})) → ((a₃ : α₀) → (as₄ : U.Init.Prelude.List α₀) → motive₁ (U.Init.Prelude.List:cons {α₀} a₃ as₄)) → motive₁ x₂
List:getLast~x3f~:match~u1 {α₀} motive₁ x₂ h1₃ h2₄ = U.Init.Prelude.List:casesOn {α₀} {λ (x₅ : U.Init.Prelude.List α₀) → motive₁ x₅} x₂ (h1₃ U.Init.Prelude.Unit:unit) (λ (head₅ : α₀) → λ (tail₆ : U.Init.Prelude.List α₀) → h2₄ head₅ tail₆)

List:filterMap:~uf : {α₀ : Set} → {β₁ : Set} → (α₀ → U.Init.Prelude.Option β₁) → (x₂ : U.Init.Prelude.List α₀) → U.Init.Prelude.List:below {α₀} {λ (x₃ : U.Init.Prelude.List α₀) → U.Init.Prelude.List β₁} x₂ → U.Init.Prelude.List β₁
List:filterMap:~uf {α₀} {β₁} f₂ x₃ f₄ = List:getLast~x3f~:match~u1 {α₀} (λ (x₅ : U.Init.Prelude.List α₀) → U.Init.Prelude.List:below {α₀} {λ (x₆ : U.Init.Prelude.List α₀) → U.Init.Prelude.List β₁} x₅ → U.Init.Prelude.List β₁) x₃ (λ (x₅ : U.Init.Prelude.Unit) → λ (x₆ : U.Init.Prelude.List:below {α₀} {λ (x₆ : U.Init.Prelude.List α₀) → U.Init.Prelude.List β₁} (U.Init.Prelude.List:nil {α₀})) → U.Init.Prelude.List:nil {β₁}) (λ (a₅ : α₀) → λ (as₆ : U.Init.Prelude.List α₀) → λ (x₇ : U.Init.Prelude.List:below {α₀} {λ (x₇ : U.Init.Prelude.List α₀) → U.Init.Prelude.List β₁} (U.Init.Prelude.List:cons {α₀} a₅ as₆)) → List:filterMap:match~u1 {β₁} (λ (x₈ : U.Init.Prelude.Option β₁) → U.Init.Prelude.List β₁) (f₂ a₅) (λ (x₈ : U.Init.Prelude.Unit) → U.Init.Prelude.PProd.fst₂ {(λ (x₉ : U.Init.Prelude.List α₀) → U.Init.Prelude.List β₁) as₆} {U.Init.Prelude.List:rec {α₀} {λ (t₉ : U.Init.Prelude.List α₀) → Set} U.Init.Prelude.PUnit (λ (head₉ : α₀) → λ (tail₁₀ : U.Init.Prelude.List α₀) → λ (tailih₁₁ : Set) → U.Init.Prelude.PProd ((λ (x₁₂ : U.Init.Prelude.List α₀) → U.Init.Prelude.List β₁) tail₁₀) tailih₁₁) as₆} x₇) (λ (b₈ : β₁) → U.Init.Prelude.List:cons {β₁} b₈ (U.Init.Prelude.PProd.fst₂ {(λ (x₉ : U.Init.Prelude.List α₀) → U.Init.Prelude.List β₁) as₆} {U.Init.Prelude.List:rec {α₀} {λ (t₉ : U.Init.Prelude.List α₀) → Set} U.Init.Prelude.PUnit (λ (head₉ : α₀) → λ (tail₁₀ : U.Init.Prelude.List α₀) → λ (tailih₁₁ : Set) → U.Init.Prelude.PProd ((λ (x₁₂ : U.Init.Prelude.List α₀) → U.Init.Prelude.List β₁) tail₁₀) tailih₁₁) as₆} x₇))) f₄

List:filterMap : {α₀ : Set} → {β₁ : Set} → (α₀ → U.Init.Prelude.Option β₁) → U.Init.Prelude.List α₀ → U.Init.Prelude.List β₁
List:filterMap {α₀} {β₁} f₂ x₃ = U.Init.Prelude.List:brecOn {α₀} {λ (x₄ : U.Init.Prelude.List α₀) → U.Init.Prelude.List β₁} x₃ (List:filterMap:~uf {α₀} {β₁} f₂)

-- theorem
opaque
  List:map~ucons : {α₀ : Set} → {β₁ : Set} → {f₂ : α₀ → β₁} → {a₃ : α₀} → {l₄ : U.Init.Prelude.List α₀} → U.Init.Prelude.Eq {U.Init.Prelude.List β₁} (U.Init.Prelude.List:map {α₀} {β₁} f₂ (U.Init.Prelude.List:cons {α₀} a₃ l₄)) (U.Init.Prelude.List:cons {β₁} (f₂ a₃) (U.Init.Prelude.List:map {α₀} {β₁} f₂ l₄))
  List:map~ucons {α₀} {β₁} {f₂} {a₃} {l₄} = U.Init.Prelude.id {U.Init.Prelude.Eq {U.Init.Prelude.List β₁} (U.Init.Prelude.List:map {α₀} {β₁} f₂ (U.Init.Prelude.List:cons {α₀} a₃ l₄)) (U.Init.Prelude.List:cons {β₁} (f₂ a₃) (U.Init.Prelude.List:map {α₀} {β₁} f₂ l₄))} (U.Init.Prelude.rfl {U.Init.Prelude.List β₁} {U.Init.Prelude.List:map {α₀} {β₁} f₂ (U.Init.Prelude.List:cons {α₀} a₃ l₄)})

-- theorem
opaque
  List:map~unil : {α₀ : Set} → {β₁ : Set} → {f₂ : α₀ → β₁} → U.Init.Prelude.Eq {U.Init.Prelude.List β₁} (U.Init.Prelude.List:map {α₀} {β₁} f₂ (U.Init.Prelude.List:nil {α₀})) (U.Init.Prelude.List:nil {β₁})
  List:map~unil {α₀} {β₁} {f₂} = U.Init.Prelude.id {U.Init.Prelude.Eq {U.Init.Prelude.List β₁} (U.Init.Prelude.List:map {α₀} {β₁} f₂ (U.Init.Prelude.List:nil {α₀})) (U.Init.Prelude.List:nil {β₁})} (U.Init.Prelude.rfl {U.Init.Prelude.List β₁} {U.Init.Prelude.List:map {α₀} {β₁} f₂ (U.Init.Prelude.List:nil {α₀})})
