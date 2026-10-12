/-
File: corpus/real-sqrt-nonneg/lean/Statement.lean

The statement of `Real.sqrt_nonneg`, quoted from Mathlib v4.33.1,
`Mathlib/Analysis/Real/Sqrt.lean`, lines 144 to 146:

    @[simp] theorem sqrt_nonneg (x : ℝ) : 0 ≤ √x := by
      unfold sqrt
      exact NNReal.coe_nonneg _

with the definitions it is about, `NNReal.sqrt` and `Real.sqrt`, from
lines 46 and 47 and lines 112 and 113 of the same file:

    noncomputable def sqrt : ℝ≥0 ≃o ℝ≥0 :=
      OrderIso.symm <| powOrderIso 2 two_ne_zero

    @[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
      NNReal.sqrt (Real.toNNReal x)

Run from `translator/` as

    lake env lean ../corpus/real-sqrt-nonneg/lean/Statement.lean

it prints the following:

    Real.sqrt_nonneg : ∀ (x : ℝ), 0 ≤ √x
    'Real.sqrt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Real' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Real.sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]

The type `Real` itself depends on `Classical.choice` at this revision
(`../notes.md`, Tier, gives the path).  `Mathlib.Data.Real.Sqrt` is a
deprecated module that re-exports this one.
-/
import Mathlib.Analysis.Real.Sqrt

#check @Real.sqrt_nonneg
#print axioms Real.sqrt_nonneg
#print axioms Real
#print axioms Real.sqrt
