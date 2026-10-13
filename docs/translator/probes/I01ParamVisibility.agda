-- Outcome on 2026-10-13 with Agda 2.8.0: accepted
{-# OPTIONS --type-in-type #-}
module I01ParamVisibility where

postulate C : Set

-- A data type's constructors take its explicit and implicit parameters
-- implicitly and its instance parameters as instance arguments; an
-- instance parameter passed as an implicit argument, {c}, fails with
-- WrongNamedArgument.
data D (A : Set) {B : Set} ⦃ c : C ⦄ : Set where
  D:c : A → D A {B} ⦃ c ⦄

q1 : {A B : Set} ⦃ c : C ⦄ → A → D A {B} ⦃ c ⦄
q1 {A} {B} ⦃ c ⦄ a = D:c {A} {B} ⦃ c ⦄ a

-- A record's constructor and projections take its parameters the same
-- way, the record itself explicitly.
record R (A : Set) {B : Set} ⦃ c : C ⦄ : Set where
  constructor R:mk
  field
    f₀ : A
    g₁ : B

q2 : {A B : Set} ⦃ c : C ⦄ → A → B → R A {B} ⦃ c ⦄
q2 {A} {B} ⦃ c ⦄ a b = R:mk {A} {B} ⦃ c ⦄ a b

q3 : {A B : Set} ⦃ c : C ⦄ → R A {B} ⦃ c ⦄ → A
q3 {A} {B} ⦃ c ⦄ r = R.f₀ {A} {B} ⦃ c ⦄ r
