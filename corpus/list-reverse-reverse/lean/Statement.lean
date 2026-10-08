/-
File: corpus/list-reverse-reverse/lean/Statement.lean

The statement of `List.reverse_reverse`, quoted from Lean v4.33.1,
`src/Init/Data/List/Lemmas.lean`, lines 2483 to 2485:

    -- The argument `as : List α` is explicit to allow rewriting from right to left.
    @[simp, grind =] theorem reverse_reverse (as : List α) : as.reverse.reverse = as := by
      simp only [reverse]; rw [reverseAux_reverseAux_nil]; rfl

Run from `translator/` as

    lake env lean ../corpus/list-reverse-reverse/lean/Statement.lean

it prints the following:

    @List.reverse_reverse : ∀ {α : Type u_1} (as : List α), as.reverse.reverse = as
    'List.reverse_reverse' depends on axioms: [propext]

The module is in Lean's core library, so the import needs no Mathlib.
-/
import Init.Data.List.Lemmas

#check @List.reverse_reverse
#print axioms List.reverse_reverse
