/-
File: corpus/lists-subset-refl/lean/Statement.lean

The statement of `Lists'.Subset.refl`, quoted from Mathlib v4.33.1,
`Mathlib/SetTheory/Lists.lean`, lines 168 to 170:

    @[refl]
    theorem Subset.refl {l : Lists' α true} : l ⊆ l := by
      rw [← Lists'.of_toList l]; exact ofList_subset (List.Subset.refl _)

The same file defines the family `Lists'` (lines 57 to 61), the sum
`Lists` (lines 67 to 68), `Lists'.of_toList` (lines 99 to 109), and the
mutual block of `Lists.Equiv` and `Lists'.Subset` (lines 118 to 131),
where the instance `HasSubset (Lists' α true)` of lines 137 to 138 reads
`⊆` as `Lists'.Subset`.

Run from `translator/` as

    lake env lean ../corpus/lists-subset-refl/lean/Statement.lean

it prints the following:

    @Lists'.Subset.refl : ∀ {α : Type u_1} {l : Lists' α true}, l ⊆ l
    'Lists'.Subset.refl' depends on axioms: [propext, Quot.sound]

The import needs Mathlib's cache in `translator/.lake` (`make lean-cache`).
-/
import Mathlib.SetTheory.Lists

#check @Lists'.Subset.refl
#print axioms Lists'.Subset.refl
