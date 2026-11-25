{-# OPTIONS --type-in-type --rewriting #-}
-- lean2agda, profile U: the scaffold of the closure of LevelFixtures:Box LevelFixtures:Box:~usizeOf~u1 LevelFixtures:Box:~usizeOf~uinst LevelFixtures:Box:casesOn LevelFixtures:Box:ctorIdx and 149 more
-- Lean module Init.Prelude
module U.Init.Prelude where

record Add (α₀ : Set) : Set where
  constructor Add:mk
  field
    add₁ : α₀ → α₀ → α₀

Add:add : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → α₀ → α₀ → α₀
Add:add {α₀} ⦃ self₁ ⦄ = Add.add₁ {α₀} self₁

record And (a₀ : Set) (b₁ : Set) : Set where
  constructor And:intro
  field
    left₂ : a₀
    right₃ : b₁

-- recursor
And:rec#z : {a₀ : Set} → {b₁ : Set} → {motive₂ : And a₀ b₁ → Set} → ((left₃ : a₀) → (right₄ : b₁) → motive₂ (And:intro {a₀} {b₁} left₃ right₄)) → (t₃ : And a₀ b₁) → motive₂ t₃
And:rec#z {a₀} {b₁} {motive₂} intro₃ (And:intro left₄ right₅) = intro₃ left₄ right₅

And:casesOn#z : {a₀ : Set} → {b₁ : Set} → {motive₂ : And a₀ b₁ → Set} → (t₃ : And a₀ b₁) → ((left₄ : a₀) → (right₅ : b₁) → motive₂ (And:intro {a₀} {b₁} left₄ right₅)) → motive₂ t₃
And:casesOn#z {a₀} {b₁} {motive₂} t₃ intro₄ = And:rec#z {a₀} {b₁} {motive₂} (λ (left₅ : a₀) → λ (right₆ : b₁) → intro₄ left₅ right₆) t₃

data Bool : Set where
  Bool:false : Bool
  Bool:true : Bool
{-# BUILTIN BOOL Bool #-}
{-# BUILTIN FALSE Bool:false #-}
{-# BUILTIN TRUE Bool:true #-}

-- recursor
Bool:rec#n : {motive₀ : Bool → Set} → motive₀ Bool:false → motive₀ Bool:true → (t₁ : Bool) → motive₀ t₁
Bool:rec#n {motive₀} false₁ true₂ Bool:false = false₁
Bool:rec#n {motive₀} false₁ true₂ Bool:true = true₂

Bool:casesOn#n : {motive₀ : Bool → Set} → (t₁ : Bool) → motive₀ Bool:false → motive₀ Bool:true → motive₀ t₁
Bool:casesOn#n {motive₀} t₁ false₂ true₃ = Bool:rec#n {motive₀} false₂ true₃ t₁

data Eq#n {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl#n : (a₁ : α₀) → Eq#n {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq#n #-}

-- recursor
Eq:rec#nn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq#n {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl#n {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq#n {α₀} a₁ a₃) → motive₂ a₃ t₄
Eq:rec#nn {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl#n _) = refl₃

Eq:ndrec#nn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → Eq#n {α₀} a₁ b₃ → motive₂ b₃
Eq:ndrec#nn {α₀} {a₁} {motive₂} m₃ {b₄} h₅ = Eq:rec#nn {α₀} {a₁} {λ (x₆ : α₀) → λ (x₇ : Eq#n {α₀} a₁ x₆) → motive₂ x₆} m₃ {b₄} h₅

-- recursor
Eq:rec#zn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq#n {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl#n {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq#n {α₀} a₁ a₃) → motive₂ a₃ t₄
Eq:rec#zn {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl#n _) = refl₃

Eq:ndrec#zn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → Eq#n {α₀} a₁ b₃ → motive₂ b₃
Eq:ndrec#zn {α₀} {a₁} {motive₂} m₃ {b₄} h₅ = Eq:rec#zn {α₀} {a₁} {λ (x₆ : α₀) → λ (x₇ : Eq#n {α₀} a₁ x₆) → motive₂ x₆} m₃ {b₄} h₅

data Eq#z {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl#z : (a₁ : α₀) → Eq#z {α₀} a₁ a₁
{-# BUILTIN REWRITE Eq#z #-}

-- recursor
Eq:rec#zz : {α₀ : Set} → {a₁ : α₀} → {motive₂ : (a₂ : α₀) → Eq#z {α₀} a₁ a₂ → Set} → motive₂ a₁ (Eq:refl#z {α₀} a₁) → {a₃ : α₀} → (t₄ : Eq#z {α₀} a₁ a₃) → motive₂ a₃ t₄
Eq:rec#zz {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl#z _) = refl₃

Eq:ndrec#zz : {α₀ : Set} → {a₁ : α₀} → {motive₂ : α₀ → Set} → motive₂ a₁ → {b₃ : α₀} → Eq#z {α₀} a₁ b₃ → motive₂ b₃
Eq:ndrec#zz {α₀} {a₁} {motive₂} m₃ {b₄} h₅ = Eq:rec#zz {α₀} {a₁} {λ (x₆ : α₀) → λ (x₇ : Eq#z {α₀} a₁ x₆) → motive₂ x₆} m₃ {b₄} h₅

-- theorem
opaque
  Eq:subst#n : {α₀ : Set} → {motive₁ : α₀ → Set} → {a₂ : α₀} → {b₃ : α₀} → Eq#n {α₀} a₂ b₃ → motive₁ a₂ → motive₁ b₃
  Eq:subst#n {α₀} {motive₁} {a₂} {b₃} h₄ h₅ = Eq:ndrec#zn {α₀} {a₂} {motive₁} h₅ {b₃} h₄

rfl#n : {α₀ : Set} → {a₁ : α₀} → Eq#n {α₀} a₁ a₁
rfl#n {α₀} {a₁} = Eq:refl#n {α₀} a₁

-- theorem
opaque
  Eq:symm#n : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → Eq#n {α₀} a₁ b₂ → Eq#n {α₀} b₂ a₁
  Eq:symm#n {α₀} {a₁} {b₂} h₃ = Eq:rec#zn {α₀} {a₁} {λ (x₄ : α₀) → λ (h₅ : Eq#n {α₀} a₁ x₄) → Eq#n {α₀} x₄ a₁} (rfl#n {α₀} {a₁}) {b₂} h₃

-- theorem
opaque
  Eq:trans#n : {α₀ : Set} → {a₁ : α₀} → {b₂ : α₀} → {c₃ : α₀} → Eq#n {α₀} a₁ b₂ → Eq#n {α₀} b₂ c₃ → Eq#n {α₀} a₁ c₃
  Eq:trans#n {α₀} {a₁} {b₂} {c₃} h₄ h₅ = Eq:rec#zn {α₀} {b₂} {λ (x₆ : α₀) → λ (h₇ : Eq#n {α₀} b₂ x₆) → Eq#n {α₀} a₁ x₆} h₄ {c₃} h₅

outParam#n : Set → Set
outParam#n α₀ = α₀

record HAdd (α₀ : Set) (β₁ : Set) (γ₂ : outParam#n Set) : Set where
  constructor HAdd:mk
  field
    hAdd₃ : α₀ → β₁ → γ₂

HAdd:hAdd : {α₀ : Set} → {β₁ : Set} → {γ₂ : outParam#n Set} → ⦃ _ : HAdd α₀ β₁ γ₂ ⦄ → α₀ → β₁ → γ₂
HAdd:hAdd {α₀} {β₁} {γ₂} ⦃ self₃ ⦄ = HAdd.hAdd₃ {α₀} {β₁} {γ₂} self₃

data HEq#n {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where
  HEq:refl#n : (a₁ : α₀) → HEq#n {α₀} a₁ {α₀} a₁

-- recursor
HEq:rec#zn : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq#n {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl#n {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq#n {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅
HEq:rec#zn {α₀} {a₁} {motive₂} refl₃ {_} {_} (HEq:refl#n _) = refl₃

cast#n : {α₀ : Set} → {β₁ : Set} → Eq#n {Set} α₀ β₁ → α₀ → β₁
cast#n {α₀} {β₁} h₂ a₃ = Eq:rec#nn {Set} {α₀} {λ (x₄ : Set) → λ (x₅ : Eq#n {Set} α₀ x₄) → x₄} a₃ {β₁} h₂

-- theorem
opaque
  eq~uof~uheq#n : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → HEq#n {α₀} a₁ {α₀} a₂ → Eq#n {α₀} a₁ a₂
  eq~uof~uheq#n {α₀} {a₁} {a₂} h₃ = let this₄ : (α₄ : Set) → (β₅ : Set) → (a₆ : α₄) → (b₇ : β₅) → HEq#n {α₄} a₆ {β₅} b₇ → (h₈ : Eq#n {Set} α₄ β₅) → Eq#n {β₅} (cast#n {α₄} {β₅} h₈ a₆) b₇; this₄ = λ (x₄ : Set) → λ (x₅ : Set) → λ (x₆ : x₄) → λ (x₇ : x₅) → λ (h₈ : HEq#n {x₄} x₆ {x₅} x₇) → HEq:rec#zn {x₄} {x₆} {λ {x₉ : Set} → λ (x₁₀ : x₉) → λ (x₁₁ : HEq#n {x₄} x₆ {x₉} x₁₀) → (h₁₂ : Eq#n {Set} x₄ x₉) → Eq#n {x₉} (cast#n {x₄} {x₉} h₁₂ x₆) x₁₀} (λ (x₉ : Eq#n {Set} x₄ x₄) → rfl#n {x₄} {cast#n {x₄} {x₄} x₉ x₆}) {x₅} {x₇} h₈ in this₄ α₀ α₀ a₁ a₂ h₃ (rfl#n {Set} {α₀})

data HEq#z {α₀ : Set} : α₀ → {β₁ : Set} → β₁ → Set where
  HEq:refl#z : (a₁ : α₀) → HEq#z {α₀} a₁ {α₀} a₁

-- recursor
HEq:rec#zz : {α₀ : Set} → {a₁ : α₀} → {motive₂ : {β₂ : Set} → (a₃ : β₂) → HEq#z {α₀} a₁ {β₂} a₃ → Set} → motive₂ {α₀} a₁ (HEq:refl#z {α₀} a₁) → {β₃ : Set} → {a₄ : β₃} → (t₅ : HEq#z {α₀} a₁ {β₃} a₄) → motive₂ {β₃} a₄ t₅
HEq:rec#zz {α₀} {a₁} {motive₂} refl₃ {_} {_} (HEq:refl#z _) = refl₃

cast#z : {α₀ : Set} → {β₁ : Set} → Eq#n {Set} α₀ β₁ → α₀ → β₁
cast#z {α₀} {β₁} h₂ a₃ = Eq:rec#zn {Set} {α₀} {λ (x₄ : Set) → λ (x₅ : Eq#n {Set} α₀ x₄) → x₄} a₃ {β₁} h₂

rfl#z : {α₀ : Set} → {a₁ : α₀} → Eq#z {α₀} a₁ a₁
rfl#z {α₀} {a₁} = Eq:refl#z {α₀} a₁

-- theorem
opaque
  eq~uof~uheq#z : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → HEq#z {α₀} a₁ {α₀} a₂ → Eq#z {α₀} a₁ a₂
  eq~uof~uheq#z {α₀} {a₁} {a₂} h₃ = let this₄ : (α₄ : Set) → (β₅ : Set) → (a₆ : α₄) → (b₇ : β₅) → HEq#z {α₄} a₆ {β₅} b₇ → (h₈ : Eq#n {Set} α₄ β₅) → Eq#z {β₅} (cast#z {α₄} {β₅} h₈ a₆) b₇; this₄ = λ (x₄ : Set) → λ (x₅ : Set) → λ (x₆ : x₄) → λ (x₇ : x₅) → λ (h₈ : HEq#z {x₄} x₆ {x₅} x₇) → HEq:rec#zz {x₄} {x₆} {λ {x₉ : Set} → λ (x₁₀ : x₉) → λ (x₁₁ : HEq#z {x₄} x₆ {x₉} x₁₀) → (h₁₂ : Eq#n {Set} x₄ x₉) → Eq#z {x₉} (cast#z {x₄} {x₉} h₁₂ x₆) x₁₀} (λ (x₉ : Eq#n {Set} x₄ x₄) → rfl#z {x₄} {cast#z {x₄} {x₄} x₉ x₆}) {x₅} {x₇} h₈ in this₄ α₀ α₀ a₁ a₂ h₃ (rfl#n {Set} {α₀})

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

record OfNat (α₀ : Set) (x₁ : Nat) : Set where
  constructor OfNat:mk
  field
    ofNat₂ : α₀

OfNat:ofNat : {α₀ : Set} → (x₁ : Nat) → ⦃ _ : OfNat α₀ x₁ ⦄ → α₀
OfNat:ofNat {α₀} x₁ ⦃ self₂ ⦄ = OfNat.ofNat₂ {α₀} {x₁} self₂

-- recursor
Nat:rec#n : {motive₀ : Nat → Set} → motive₀ Nat:zero → ((n₁ : Nat) → motive₀ n₁ → motive₀ (Nat:succ n₁)) → (t₁ : Nat) → motive₀ t₁
Nat:rec#n {motive₀} zero₁ succ₂ Nat:zero = zero₁
Nat:rec#n {motive₀} zero₁ succ₂ (Nat:succ n₃) = succ₂ n₃ (Nat:rec#n {motive₀} zero₁ succ₂ n₃)

Nat:casesOn#n : {motive₀ : Nat → Set} → (t₁ : Nat) → motive₀ Nat:zero → ((n₂ : Nat) → motive₀ (Nat:succ n₂)) → motive₀ t₁
Nat:casesOn#n {motive₀} t₁ zero₂ succ₃ = Nat:rec#n {motive₀} zero₂ (λ (n₄ : Nat) → λ (nih₅ : motive₀ n₄) → succ₃ n₄) t₁

Nat:add:match~u1#n : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((a₃ : Nat) → motive₀ a₃ Nat:zero) → ((a₃ : Nat) → (b₄ : Nat) → motive₀ a₃ (Nat:succ b₄)) → motive₀ x₁ x₂
Nat:add:match~u1#n motive₀ x₁ x₂ h1₃ h2₄ = Nat:casesOn#n {λ (x₅ : Nat) → motive₀ x₁ x₅} x₂ (h1₃ x₁) (λ (n₅ : Nat) → h2₄ x₁ n₅)

record PProd#nn (α₀ : Set) (β₁ : Set) : Set where
  constructor PProd:mk#nn
  field
    fst₂ : α₀
    snd₃ : β₁

record PUnit#n : Set where
  constructor PUnit:unit#n

Nat:below#n : {_ : Nat → Set} → Nat → Set
Nat:below#n {motive₀} t₁ = Nat:rec#n {λ (t₂ : Nat) → Set} PUnit#n (λ (n₂ : Nat) → λ (nih₃ : Set) → PProd#nn (motive₀ n₂) nih₃) t₁

Nat:add:~uf : (x₀ : Nat) → Nat:below#n {λ (x₁ : Nat) → Nat → Nat} x₀ → Nat → Nat
Nat:add:~uf x₀ f₁ x₂ = Nat:add:match~u1#n (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below#n {λ (x₅ : Nat) → Nat → Nat} x₄ → Nat) x₂ x₀ (λ (a₃ : Nat) → λ (x₄ : Nat:below#n {λ (x₄ : Nat) → Nat → Nat} Nat:zero) → a₃) (λ (a₃ : Nat) → λ (b₄ : Nat) → λ (x₅ : Nat:below#n {λ (x₅ : Nat) → Nat → Nat} (Nat:succ b₄)) → Nat:succ (PProd#nn.fst₂ {(λ (x₆ : Nat) → Nat → Nat) b₄} {Nat:rec#n {λ (t₆ : Nat) → Set} PUnit#n (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd#nn ((λ (x₈ : Nat) → Nat → Nat) n₆) nih₇) b₄} x₅ a₃)) f₁

Nat:brecOn:go#n : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below#n {motive₀} t₂ → motive₀ t₂) → PProd#nn (motive₀ t₁) (Nat:below#n {motive₀} t₁)
Nat:brecOn:go#n {motive₀} t₁ F1₂ = Nat:rec#n {λ (t₃ : Nat) → PProd#nn (motive₀ t₃) (Nat:below#n {motive₀} t₃)} (PProd:mk#nn {motive₀ Nat:zero} {PUnit#n} (F1₂ Nat:zero PUnit:unit#n) PUnit:unit#n) (λ (n₃ : Nat) → λ (nih₄ : PProd#nn (motive₀ n₃) (Nat:below#n {motive₀} n₃)) → PProd:mk#nn {motive₀ (Nat:succ n₃)} {PProd#nn (motive₀ n₃) (Nat:below#n {motive₀} n₃)} (F1₂ (Nat:succ n₃) nih₄) nih₄) t₁

Nat:brecOn#n : {motive₀ : Nat → Set} → (t₁ : Nat) → ((t₂ : Nat) → Nat:below#n {motive₀} t₂ → motive₀ t₂) → motive₀ t₁
Nat:brecOn#n {motive₀} t₁ F1₂ = PProd#nn.fst₂ {motive₀ t₁} {Nat:below#n {motive₀} t₁} (Nat:brecOn:go#n {motive₀} t₁ F1₂)

-- operation table
Nat:add-builtin : Nat → Nat → Nat
Nat:add-builtin Nat:zero m₁ = m₁
Nat:add-builtin (Nat:succ n₀) m₁ = Nat:succ (Nat:add-builtin n₀ m₁)
{-# BUILTIN NATPLUS Nat:add-builtin #-}

-- operation table
Nat:add : Nat → Nat → Nat
Nat:add x₀ x₁ = Nat:add-builtin x₁ x₀

instAddNat : Add Nat
instAddNat = Add:mk {Nat} Nat:add

instHAdd : {α₀ : Set} → ⦃ _ : Add α₀ ⦄ → HAdd α₀ α₀ α₀
instHAdd {α₀} ⦃ inst₁ ⦄ = HAdd:mk {α₀} {α₀} {α₀} (λ (a₂ : α₀) → λ (b₃ : α₀) → Add:add {α₀} ⦃ inst₁ ⦄ a₂ b₃)

instOfNatNat : (n₀ : Nat) → OfNat Nat n₀
instOfNatNat n₀ = OfNat:mk {Nat} {n₀} n₀

-- theorem
opaque
  heq~uof~ueq#n : {α₀ : Set} → {a₁ : α₀} → {a₂ : α₀} → Eq#n {α₀} a₁ a₂ → HEq#n {α₀} a₁ {α₀} a₂
  heq~uof~ueq#n {α₀} {a₁} {a₂} h₃ = Eq:subst#n {α₀} {HEq#n {α₀} a₁ {α₀}} {a₁} {a₂} h₃ (HEq:refl#n {α₀} a₁)

id#z : {α₀ : Set} → α₀ → α₀
id#z {α₀} a₁ = a₁

id#n : {α₀ : Set} → α₀ → α₀
id#n {α₀} a₁ = a₁

record PProd#zn (α₀ : Set) (β₁ : Set) : Set where
  constructor PProd:mk#zn
  field
    fst₂ : α₀
    snd₃ : β₁

record PUnit#z : Set where
  constructor PUnit:unit#z

Nat:ble:match~u1#n : (motive₀ : Nat → Nat → Set) → (x₁ : Nat) → (x₂ : Nat) → ((x₃ : Nat) → motive₀ Nat:zero x₃) → ((n₃ : Nat) → motive₀ (Nat:succ n₃) Nat:zero) → ((n₃ : Nat) → (m₄ : Nat) → motive₀ (Nat:succ n₃) (Nat:succ m₄)) → motive₀ x₁ x₂
Nat:ble:match~u1#n motive₀ x₁ x₂ h1₃ h2₄ h3₅ = Nat:casesOn#n {λ (x₆ : Nat) → motive₀ x₆ x₂} x₁ (h1₃ x₂) (λ (n₆ : Nat) → Nat:casesOn#n {λ (x₇ : Nat) → motive₀ (Nat:succ n₆) x₇} x₂ (h2₄ n₆) (λ (n₇ : Nat) → h3₅ n₆ n₇))

Nat:ble:~uf : (x₀ : Nat) → Nat:below#n {λ (x₁ : Nat) → Nat → Bool} x₀ → Nat → Bool
Nat:ble:~uf x₀ f₁ x₂ = Nat:ble:match~u1#n (λ (x₃ : Nat) → λ (x₄ : Nat) → Nat:below#n {λ (x₅ : Nat) → Nat → Bool} x₃ → Bool) x₀ x₂ (λ (x₃ : Nat) → λ (x₄ : Nat:below#n {λ (x₄ : Nat) → Nat → Bool} Nat:zero) → Bool:true) (λ (n₃ : Nat) → λ (x₄ : Nat:below#n {λ (x₄ : Nat) → Nat → Bool} (Nat:succ n₃)) → Bool:false) (λ (n₃ : Nat) → λ (m₄ : Nat) → λ (x₅ : Nat:below#n {λ (x₅ : Nat) → Nat → Bool} (Nat:succ n₃)) → PProd#nn.fst₂ {(λ (x₆ : Nat) → Nat → Bool) n₃} {Nat:rec#n {λ (t₆ : Nat) → Set} PUnit#n (λ (n₆ : Nat) → λ (nih₇ : Set) → PProd#nn ((λ (x₈ : Nat) → Nat → Bool) n₆) nih₇) n₃} x₅ m₄) f₁

-- operation table
Nat:blt-builtin : Nat → Nat → Bool
Nat:blt-builtin n₀ Nat:zero = Bool:false
Nat:blt-builtin Nat:zero (Nat:succ m₁) = Bool:true
Nat:blt-builtin (Nat:succ n₀) (Nat:succ m₁) = Nat:blt-builtin n₀ m₁
{-# BUILTIN NATLESS Nat:blt-builtin #-}

-- operation table
Nat:ble : Nat → Nat → Bool
Nat:ble x₀ x₁ = Nat:blt-builtin x₀ (Nat:succ x₁)

record PULift#nn (α₀ : Set) : Set where
  constructor PULift:up#nn
  field
    down₁ : α₀

Unit : Set
Unit = PUnit#n

Unit:unit : Unit
Unit:unit = PUnit:unit#n

cond:match~u1#n : (motive₀ : Bool → Set) → (c₁ : Bool) → (Unit → motive₀ Bool:true) → (Unit → motive₀ Bool:false) → motive₀ c₁
cond:match~u1#n motive₀ c₁ h1₂ h2₃ = Bool:casesOn#n {λ (x₄ : Bool) → motive₀ x₄} c₁ (h2₃ Unit:unit) (h1₂ Unit:unit)

cond#n : {α₀ : Set} → Bool → α₀ → α₀ → α₀
cond#n {α₀} c₁ x₂ y₃ = cond:match~u1#n (λ (c₄ : Bool) → α₀) c₁ (λ (x₄ : Unit) → x₂) (λ (x₄ : Unit) → y₃)

PULift:down#nn : {α₀ : Set} → PULift#nn α₀ → α₀
PULift:down#nn {α₀} self₁ = PULift#nn.down₁ {α₀} self₁

record PULift#zz (α₀ : Set) : Set where
  constructor PULift:up#zz
  field
    down₁ : α₀

PULift:down#zz : {α₀ : Set} → PULift#zz α₀ → α₀
PULift:down#zz {α₀} self₁ = PULift#zz.down₁ {α₀} self₁

data List (α₀ : Set) : Set where
  List:nil : List α₀
  List:cons : α₀ → List α₀ → List α₀

-- recursor
List:rec#n : {α₀ : Set} → {motive₁ : List α₀ → Set} → motive₁ (List:nil {α₀}) → ((head₂ : α₀) → (tail₃ : List α₀) → motive₁ tail₃ → motive₁ (List:cons {α₀} head₂ tail₃)) → (t₂ : List α₀) → motive₁ t₂
List:rec#n {α₀} {motive₁} nil₂ cons₃ List:nil = nil₂
List:rec#n {α₀} {motive₁} nil₂ cons₃ (List:cons head₄ tail₅) = cons₃ head₄ tail₅ (List:rec#n {α₀} {motive₁} nil₂ cons₃ tail₅)

-- recursor
List:rec#z : {α₀ : Set} → {motive₁ : List α₀ → Set} → motive₁ (List:nil {α₀}) → ((head₂ : α₀) → (tail₃ : List α₀) → motive₁ tail₃ → motive₁ (List:cons {α₀} head₂ tail₃)) → (t₂ : List α₀) → motive₁ t₂
List:rec#z {α₀} {motive₁} nil₂ cons₃ List:nil = nil₂
List:rec#z {α₀} {motive₁} nil₂ cons₃ (List:cons head₄ tail₅) = cons₃ head₄ tail₅ (List:rec#z {α₀} {motive₁} nil₂ cons₃ tail₅)

-- theorem
opaque
  congrArg#nn : {α₀ : Set} → {β₁ : Set} → {a₂ : α₀} → {a₃ : α₀} → (f₄ : α₀ → β₁) → Eq#n {α₀} a₂ a₃ → Eq#n {β₁} (f₄ a₂) (f₄ a₃)
  congrArg#nn {α₀} {β₁} {a₂} {a₃} f₄ h₅ = Eq:rec#zn {α₀} {a₂} {λ (x₆ : α₀) → λ (h₇ : Eq#n {α₀} a₂ x₆) → Eq#n {β₁} (f₄ a₂) (f₄ x₆)} (rfl#n {β₁} {f₄ a₂}) {a₃} h₅

List:casesOn#z : {α₀ : Set} → {motive₁ : List α₀ → Set} → (t₂ : List α₀) → motive₁ (List:nil {α₀}) → ((head₃ : α₀) → (tail₄ : List α₀) → motive₁ (List:cons {α₀} head₃ tail₄)) → motive₁ t₂
List:casesOn#z {α₀} {motive₁} t₂ nil₃ cons₄ = List:rec#z {α₀} {motive₁} nil₃ (λ (head₅ : α₀) → λ (tail₆ : List α₀) → λ (tailih₇ : motive₁ tail₆) → cons₄ head₅ tail₆) t₂

record True : Set where
  constructor True:intro

postulate Quot#z : {α₀ : Set} → (α₀ → α₀ → Set) → Set

postulate Quot:mk#z : {α₀ : Set} → (r₁ : α₀ → α₀ → Set) → α₀ → Quot#z {α₀} r₁

postulate Quot:lift#zn : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → ((a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq#n {β₂} (f₃ a₄) (f₃ b₅)) → Quot#z {α₀} r₁ → β₂

-- computation rule
postulate Quot:lift#zn-β : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → (h₄ : (a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq#n {β₂} (f₃ a₄) (f₃ b₅)) → (a₅ : α₀) → Eq#n {β₂} (Quot:lift#zn {α₀} {r₁} {β₂} f₃ h₄ (Quot:mk#z {α₀} r₁ a₅)) (f₃ a₅)
{-# REWRITE Quot:lift#zn-β #-}

record ULift (α₀ : Set) : Set where
  constructor ULift:up
  field
    down₁ : α₀

postulate Quot#n : {α₀ : Set} → (α₀ → α₀ → Set) → Set

postulate Quot:mk#n : {α₀ : Set} → (r₁ : α₀ → α₀ → Set) → α₀ → Quot#n {α₀} r₁

postulate Quot:lift#nz : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → ((a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq#z {β₂} (f₃ a₄) (f₃ b₅)) → Quot#n {α₀} r₁ → β₂

-- computation rule
postulate Quot:lift#nz-β : {α₀ : Set} → {r₁ : α₀ → α₀ → Set} → {β₂ : Set} → (f₃ : α₀ → β₂) → (h₄ : (a₄ : α₀) → (b₅ : α₀) → r₁ a₄ b₅ → Eq#z {β₂} (f₃ a₄) (f₃ b₅)) → (a₅ : α₀) → Eq#z {β₂} (Quot:lift#nz {α₀} {r₁} {β₂} f₃ h₄ (Quot:mk#n {α₀} r₁ a₅)) (f₃ a₅)
{-# REWRITE Quot:lift#nz-β #-}
