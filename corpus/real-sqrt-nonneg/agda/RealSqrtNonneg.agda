{-# OPTIONS --safe --cubical-compatible #-}

-- File: corpus/real-sqrt-nonneg/agda/RealSqrtNonneg.agda
--
-- Mathlib's Real.sqrt_nonneg (Mathlib.Analysis.Real.Sqrt, Mathlib v4.33.1):
--
--     @[simp] theorem sqrt_nonneg (x : ℝ) : 0 ≤ √x := by
--       unfold sqrt
--       exact NNReal.coe_nonneg _
--
-- under profile CC, with the real numbers as a module parameter: a record of
-- the operations that the statement's definitions use, and of the one law
-- that makes NNReal.sqrt a square root.  Real.sqrt, Real.toNNReal and NNReal
-- are defined below as Mathlib defines them, so that the proof is Lean's: the
-- value of NNReal.sqrt lies in the subtype of nonnegative reals, and the
-- theorem is the property that the subtype carries (see ../notes.md).

module RealSqrtNonneg where

open import Level using (Level; _⊔_; suc; 0ℓ)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Nullary.Irrelevant using (Irrelevant)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

-- What the statement needs from Lean's ℝ, which Mathlib constructs as the
-- Cauchy completion of ℚ (Real is a structure over CauSeq.Completion.Cauchy,
-- a quotient of Cauchy sequences).  Each field names the Mathlib constant it
-- stands for; Mathlib defines or proves every one of them, and here each is
-- assumed.
--
-- +  ℝ, 0ℝ, _*_ and _≤_: Real, Real.instZero, Real.instMul and Real.instLE.
--    Lean's ≤ is a Prop, so its proofs are all equal; ≤-irrelevant says so,
--    and makes the subtype below a subtype in Lean's sense.
-- +  max and ≤-max-right: Real.instMax, whose max is Real.sup, computed
--    pointwise on Cauchy sequences, and le_max_right at ℝ, which Lean proves
--    through the linear order Real.linearOrder, classical because its
--    Decidable instances come from Classical.propDecidable.
-- +  nnsqrt and nnsqrt-mul-self: NNReal.sqrt, an order isomorphism of ℝ≥0
--    that Mathlib obtains as the inverse of x ↦ x ^ 2 (NNReal.powOrderIso,
--    with the inverse picked by choice from a proof that squaring is
--    surjective, by continuity), and NNReal.mul_self_sqrt.  The proof below
--    uses only that nnsqrt lands in ℝ≥0.  The law says what nnsqrt stands
--    for; with no ring or order axioms beside it, it does not determine
--    nnsqrt.
--
-- No field is a classical principle.  The equations are Agda's _≡_, so a
-- constructive instance needs reals presented as a set whose _≡_ is
-- equality of reals: a set quotient of Cauchy sequences (under profile CC,
-- through a quotient parameter) or the HoTT book's Cauchy reals.  Bishop's
-- reals, a setoid, satisfy nnsqrt-mul-self only up to the setoid's
-- equality, and their ≤ is a proposition only with function
-- extensionality.

record Reals (r ℓ : Level) : Set (suc (r ⊔ ℓ)) where
  infix  4 _≤_
  infixl 7 _*_
  field
    ℝ               : Set r
    0ℝ              : ℝ
    _*_             : ℝ → ℝ → ℝ
    _≤_             : ℝ → ℝ → Set ℓ
    ≤-irrelevant    : {x y : ℝ} → Irrelevant (x ≤ y)
    max             : ℝ → ℝ → ℝ
    ≤-max-right     : (x y : ℝ) → y ≤ max x y
    nnsqrt          : Σ ℝ (0ℝ ≤_) → Σ ℝ (0ℝ ≤_)
    nnsqrt-mul-self : (x : Σ ℝ (0ℝ ≤_))
                    → proj₁ (nnsqrt x) * proj₁ (nnsqrt x) ≡ proj₁ x

module _ {r ℓ : Level} (R : Reals r ℓ) where
  open Reals R

  -- Lean: def NNReal := { r : ℝ // 0 ≤ r }, with the coercion
  -- NNReal.toReal = Subtype.val.

  ℝ≥0 : Set (r ⊔ ℓ)
  ℝ≥0 = Σ ℝ (0ℝ ≤_)

  toReal : ℝ≥0 → ℝ
  toReal = proj₁

  -- Lean: def Real.toNNReal (r : ℝ) : ℝ≥0 := ⟨max r 0, le_max_right r 0⟩

  toNNReal : ℝ → ℝ≥0
  toNNReal x = max x 0ℝ , ≤-max-right x 0ℝ

  -- Lean: theorem NNReal.coe_nonneg (r : ℝ≥0) : (0 : ℝ) ≤ r := r.property

  coe-nonneg : (x : ℝ≥0) → 0ℝ ≤ toReal x
  coe-nonneg = proj₂

  -- Lean: @[irreducible] noncomputable def Real.sqrt (x : ℝ) : ℝ :=
  --         NNReal.sqrt (Real.toNNReal x)
  --
  -- Lean's @[irreducible] stops the elaborator from unfolding sqrt, not the
  -- kernel; Agda's opaque stops the type checker everywhere outside an
  -- unfolding clause, so it is the stricter of the two.

  opaque
    sqrt : ℝ → ℝ
    sqrt x = toReal (nnsqrt (toNNReal x))

  -- The theorem.  Lean's kernel term is
  --
  --     fun x => id (NNReal.coe_nonneg (NNReal.sqrt x.toNNReal))
  --
  -- where id's type is 0 ≤ √x, which the kernel accepts by unfolding
  -- Real.sqrt.  Here `unfolding sqrt` plays the part of Lean's `unfold sqrt`.

  opaque
    unfolding sqrt

    sqrt-nonneg : (x : ℝ) → 0ℝ ≤ sqrt x
    sqrt-nonneg x = coe-nonneg (nnsqrt (toNNReal x))

-- The record has an instance with no classical principle and no postulate:
-- the one-point ring.  It shows that the parameter adds no logical strength,
-- not that it describes ℝ; constructive reals presented as a set (above)
-- are an instance with content, which the libraries the corpus may import
-- do not provide.

one-point : Reals 0ℓ 0ℓ
one-point = record
  { ℝ               = ⊤
  ; 0ℝ              = tt
  ; _*_             = λ _ _ → tt
  ; _≤_             = λ _ _ → ⊤
  ; ≤-irrelevant    = λ _ _ → refl
  ; max             = λ _ _ → tt
  ; ≤-max-right     = λ _ _ → tt
  ; nnsqrt          = λ x → x
  ; nnsqrt-mul-self = λ _ → refl
  }
