-- Outcome on 2026-11-09 with Agda 2.8.0: accepted
{-# OPTIONS --safe --cubical-compatible #-}
module P29NatOperations where
-- The operation table (docs/foundations/nat-operations.md): Lean's accelerated operations on Nat
-- as Agda definitions over Agda's builtins, in the scaffold's names.  Every equation below is one
-- that Lean's kernel accepts on variables at the pin (probes/lean/NatOps.lean), here by refl,
-- followed by computations on numerals past 2^64, which Agda's builtins do at machine speed.

data Bool : Set where
  Bool:false : Bool
  Bool:true : Bool
{-# BUILTIN BOOL Bool #-}
{-# BUILTIN FALSE Bool:false #-}
{-# BUILTIN TRUE Bool:true #-}

data Nat : Set where
  Nat:zero : Nat
  Nat:succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Agda's builtin operations, each defined as Agda.Builtin.Nat defines it; Agda computes them on
-- numerals with the host's integers and by these clauses otherwise.
Nat:add-builtin : Nat → Nat → Nat
Nat:add-builtin Nat:zero m = m
Nat:add-builtin (Nat:succ n) m = Nat:succ (Nat:add-builtin n m)
{-# BUILTIN NATPLUS Nat:add-builtin #-}

Nat:sub-builtin : Nat → Nat → Nat
Nat:sub-builtin n Nat:zero = n
Nat:sub-builtin Nat:zero (Nat:succ m) = Nat:zero
Nat:sub-builtin (Nat:succ n) (Nat:succ m) = Nat:sub-builtin n m
{-# BUILTIN NATMINUS Nat:sub-builtin #-}

Nat:mul-builtin : Nat → Nat → Nat
Nat:mul-builtin Nat:zero m = Nat:zero
Nat:mul-builtin (Nat:succ n) m = Nat:add-builtin m (Nat:mul-builtin n m)
{-# BUILTIN NATTIMES Nat:mul-builtin #-}

Nat:blt-builtin : Nat → Nat → Bool
Nat:blt-builtin n Nat:zero = Bool:false
Nat:blt-builtin Nat:zero (Nat:succ m) = Bool:true
Nat:blt-builtin (Nat:succ n) (Nat:succ m) = Nat:blt-builtin n m
{-# BUILTIN NATLESS Nat:blt-builtin #-}

Nat:div-builtin : Nat → Nat → Nat → Nat → Nat
Nat:div-builtin k m Nat:zero j = k
Nat:div-builtin k m (Nat:succ n) Nat:zero = Nat:div-builtin (Nat:succ k) m n m
Nat:div-builtin k m (Nat:succ n) (Nat:succ j) = Nat:div-builtin k m n j
{-# BUILTIN NATDIVSUCAUX Nat:div-builtin #-}

Nat:mod-builtin : Nat → Nat → Nat → Nat → Nat
Nat:mod-builtin k m Nat:zero j = k
Nat:mod-builtin k m (Nat:succ n) Nat:zero = Nat:mod-builtin Nat:zero m n m
Nat:mod-builtin k m (Nat:succ n) (Nat:succ j) = Nat:mod-builtin (Nat:succ k) m n j
{-# BUILTIN NATMODSUCAUX Nat:mod-builtin #-}

-- Lean's operations.  Nat.add, Nat.mul and Nat.ble swap or shift their arguments into the
-- builtins'; Nat.beq is Agda's _==_ itself; Nat.sub is Agda's monus, which loses one of Lean's
-- equations (probe P30); Nat.pow, the shifts and Nat.bitwise are Lean's clauses over the others.
Nat:add : Nat → Nat → Nat
Nat:add n m = Nat:add-builtin m n

Nat:sub : Nat → Nat → Nat
Nat:sub n m = Nat:sub-builtin n m

Nat:mul : Nat → Nat → Nat
Nat:mul n m = Nat:mul-builtin m n

Nat:pow : Nat → Nat → Nat
Nat:pow m Nat:zero = Nat:succ Nat:zero
Nat:pow m (Nat:succ n) = Nat:mul (Nat:pow m n) m

Nat:beq : Nat → Nat → Bool
Nat:beq Nat:zero Nat:zero = Bool:true
Nat:beq (Nat:succ n) (Nat:succ m) = Nat:beq n m
Nat:beq Nat:zero (Nat:succ m) = Bool:false
Nat:beq (Nat:succ n) Nat:zero = Bool:false
{-# BUILTIN NATEQUALS Nat:beq #-}

Nat:ble : Nat → Nat → Bool
Nat:ble n m = Nat:blt-builtin n (Nat:succ m)

Nat:pred : Nat → Nat
Nat:pred Nat:zero = Nat:zero
Nat:pred (Nat:succ n) = n

-- The fuel cores Nat.div.go and Nat.modCore.go, here without their proof arguments: for y > 0
-- and enough fuel, Lean's go computes x / y and x % y; the table's go ignores the fuel.
Nat:div-core : Nat → Nat → Nat
Nat:div-core Nat:zero x = Nat:zero
Nat:div-core (Nat:succ y) x = Nat:div-builtin Nat:zero y x y

Nat:mod-core : Nat → Nat → Nat
Nat:mod-core Nat:zero x = x
Nat:mod-core (Nat:succ y) x = Nat:mod-builtin Nat:zero y x y

Nat:shiftLeft : Nat → Nat → Nat
Nat:shiftLeft n Nat:zero = n
Nat:shiftLeft n (Nat:succ m) = Nat:shiftLeft (Nat:mul 2 n) m

Nat:shiftRight : Nat → Nat → Nat
Nat:shiftRight n Nat:zero = n
Nat:shiftRight n (Nat:succ m) = Nat:div-core 2 (Nat:shiftRight n m)

-- Nat.bitwise by fuel, the first argument plus one, each step a builtin division and remainder;
-- the recursive result occurs once, so that an evaluation never repeats it.
Nat:bitwise-pick : Bool → Nat → Nat
Nat:bitwise-pick Bool:false n = Nat:zero
Nat:bitwise-pick Bool:true n = n

Nat:bitwise-bit : Bool → Nat → Nat
Nat:bitwise-bit Bool:false r = Nat:mul 2 r
Nat:bitwise-bit Bool:true r = Nat:succ (Nat:mul 2 r)

Nat:bitwise-odd : Nat → Bool
Nat:bitwise-odd n = Nat:beq (Nat:mod-core 2 n) 1

Nat:bitwise-go : Nat → (Bool → Bool → Bool) → Nat → Nat → Nat
Nat:bitwise-go Nat:zero f n m = Nat:zero
Nat:bitwise-go (Nat:succ k) f Nat:zero m = Nat:bitwise-pick (f Bool:false Bool:true) m
Nat:bitwise-go (Nat:succ k) f (Nat:succ n) Nat:zero = Nat:bitwise-pick (f Bool:true Bool:false) (Nat:succ n)
Nat:bitwise-go (Nat:succ k) f (Nat:succ n) (Nat:succ m) =
  Nat:bitwise-bit (f (Nat:bitwise-odd (Nat:succ n)) (Nat:bitwise-odd (Nat:succ m)))
    (Nat:bitwise-go k f (Nat:div-core 2 (Nat:succ n)) (Nat:div-core 2 (Nat:succ m)))

Nat:bitwise : (Bool → Bool → Bool) → Nat → Nat → Nat
Nat:bitwise f n m = Nat:bitwise-go (Nat:succ n) f n m

and : Bool → Bool → Bool
and Bool:false b = Bool:false
and Bool:true b = b

or : Bool → Bool → Bool
or Bool:false b = b
or Bool:true b = Bool:true

bne : Bool → Bool → Bool
bne Bool:false b = b
bne Bool:true Bool:false = Bool:true
bne Bool:true Bool:true = Bool:false

Nat:land Nat:lor Nat:xor : Nat → Nat → Nat
Nat:land = Nat:bitwise and
Nat:lor = Nat:bitwise or
Nat:xor = Nat:bitwise bne

-- Lean's equations that hold on variables in Lean's kernel, each by conversion here.
module _ (n m : Nat) where
  _ : Nat:add n Nat:zero ≡ n
  _ = refl
  _ : Nat:add n (Nat:succ m) ≡ Nat:succ (Nat:add n m)
  _ = refl
  _ : Nat:sub n Nat:zero ≡ n
  _ = refl
  _ : Nat:mul n Nat:zero ≡ Nat:zero
  _ = refl
  _ : Nat:mul n (Nat:succ m) ≡ Nat:add (Nat:mul n m) n
  _ = refl
  _ : Nat:pow n Nat:zero ≡ 1
  _ = refl
  _ : Nat:pow n (Nat:succ m) ≡ Nat:mul (Nat:pow n m) n
  _ = refl
  _ : Nat:beq Nat:zero Nat:zero ≡ Bool:true
  _ = refl
  _ : Nat:beq Nat:zero (Nat:succ m) ≡ Bool:false
  _ = refl
  _ : Nat:beq (Nat:succ n) Nat:zero ≡ Bool:false
  _ = refl
  _ : Nat:beq (Nat:succ n) (Nat:succ m) ≡ Nat:beq n m
  _ = refl
  _ : Nat:ble Nat:zero m ≡ Bool:true
  _ = refl
  _ : Nat:ble (Nat:succ n) Nat:zero ≡ Bool:false
  _ = refl
  _ : Nat:ble (Nat:succ n) (Nat:succ m) ≡ Nat:ble n m
  _ = refl
  _ : Nat:ble 3 (Nat:add m 4) ≡ Bool:true
  _ = refl
  _ : Nat:shiftLeft n Nat:zero ≡ n
  _ = refl
  _ : Nat:shiftLeft n (Nat:succ m) ≡ Nat:shiftLeft (Nat:mul 2 n) m
  _ = refl
  _ : Nat:shiftRight n Nat:zero ≡ n
  _ = refl
  _ : Nat:shiftRight n (Nat:succ m) ≡ Nat:div-core 2 (Nat:shiftRight n m)
  _ = refl
  _ : Nat:land Nat:zero m ≡ Nat:zero
  _ = refl
  _ : Nat:lor Nat:zero m ≡ m
  _ = refl
  _ : Nat:xor Nat:zero m ≡ m
  _ = refl
  _ : Nat:add n 1 ≡ Nat:succ n
  _ = refl
  _ : Nat:add n 3 ≡ Nat:succ (Nat:succ (Nat:succ n))
  _ = refl
  -- the fuel cores where Lean's div and mod reduce on a variable: a numeral below an offset
  _ : Nat:div-core (Nat:add m 4) 3 ≡ 0
  _ = refl
  _ : Nat:mod-core (Nat:add m 4) 3 ≡ 3
  _ = refl
  _ : Nat:div-core (Nat:succ m) 0 ≡ 0
  _ = refl

-- Numerals past 2^64: the builtins compute them at once, and Lean's clauses over them in as many
-- steps as their recursion takes (64 for 2 ^ 64 and for the shifts by 64, one per bit for bitwise).
_ : Nat:succ 18446744073709551615 ≡ 18446744073709551616
_ = refl
_ : Nat:add 18446744073709551616 1 ≡ 18446744073709551617
_ = refl
_ : Nat:sub 340282366920938463463374607431768211456 18446744073709551616 ≡ 340282366920938463444927863358058659840
_ = refl
_ : Nat:mul 1000000007 998244353 ≡ 998244359987710471
_ = refl
_ : Nat:pow 2 64 ≡ 18446744073709551616
_ = refl
_ : Nat:pow 2 128 ≡ 340282366920938463463374607431768211456
_ = refl
_ : Nat:beq 18446744073709551616 18446744073709551616 ≡ Bool:true
_ = refl
_ : Nat:ble 18446744073709551617 18446744073709551616 ≡ Bool:false
_ = refl
_ : Nat:div-core 1000000007 998244359987710471 ≡ 998244353
_ = refl
_ : Nat:mod-core 1000000007 998244359987710471 ≡ 0
_ = refl
_ : Nat:shiftLeft 1 64 ≡ 18446744073709551616
_ = refl
_ : Nat:shiftRight 18446744073709551616 60 ≡ 16
_ = refl
_ : Nat:land 18446744073709551615 9223372036854788153 ≡ 9223372036854788153
_ = refl
_ : Nat:lor 18446744073709551615 9223372036854788153 ≡ 18446744073709551615
_ = refl
_ : Nat:xor 18446744073709551615 9223372036854788153 ≡ 9223372036854763462
_ = refl
