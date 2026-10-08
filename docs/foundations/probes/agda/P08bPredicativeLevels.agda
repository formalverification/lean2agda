-- Outcome on 2026-10-07 with Agda 2.8.0: accepted
{-# OPTIONS --safe --prop #-}
module P08bPredicativeLevels where
open import Agda.Primitive
data Squash (A : Set) : Prop where
  sq : A → Squash A
-- the same type lives one level up
AllInhabited : Prop₁
AllInhabited = (A : Set) → Squash A
-- and a Set-valued quantification over Set lands in Set₁
Id : Set₁
Id = (A : Set) → A → A
-- level arithmetic: ⊔ and lsuc only, idempotent and absorbing by computation
_ : {a : Level} → Set (a ⊔ a) → Set a
_ = λ x → x
_ : {a : Level} → Set (lsuc a ⊔ a) → Set (lsuc a)
_ = λ x → x
_ : {a b : Level} → Set (a ⊔ b) → Set (b ⊔ a)
_ = λ x → x
