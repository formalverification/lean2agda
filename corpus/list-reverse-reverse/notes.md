<!-- File: corpus/list-reverse-reverse/notes.md -->

# List.reverse_reverse

The seed entry, translated by issue M1-6 ([#6]) on behalf of M1-7
([#7]) to prove the layout and the checker end to end.  Its theme is
constructive arithmetic and lists; Lean's core library declares it, in
`Init.Data.List.Lemmas`.  One Agda file, `agda/ListReverseReverse.agda`,
checks under profile CC (`--safe --cubical-compatible`).

## Statement

Lean's statement, as `#check` prints it:

    @List.reverse_reverse : ∀ {α : Type u_1} (as : List α), as.reverse.reverse = as

The Agda statement, with `a` and `A` generalized variables:

    reverse-reverse : (xs : List A) → reverse (reverse xs) ≡ xs

They match up to notation.  `Type u_1` becomes `Set a`, Lean's `=`
becomes agda-stdlib's `_≡_`, and Lean's `List` is the same inductive
type as agda-stdlib's.  The two libraries define `reverse` through
different auxiliaries, which agree clause by clause with their
arguments swapped, as follows:

+  Lean: `reverse as = reverseAux as []`, where `reverseAux [] r = r`
   and `reverseAux (a :: l) r = reverseAux l (a :: r)`, list first and
   accumulator second;
+  agda-stdlib: `reverse = reverseAcc []`, where
   `reverseAcc = foldl (flip _∷_)`, so that `reverseAcc r [] = r` and
   `reverseAcc r (a ∷ l) = reverseAcc (a ∷ r) l`, accumulator first.

So `reverse` is the same function in both libraries: equal by
computation on every closed list, and on a variable list by an
induction whose every step is `refl`.

## Tier

`#print axioms` prints `[propext]`, so the entry is T1.  The axiom
comes from a tactic, not from the mathematics.  Lean proves the
auxiliary lemma `reverseAux_reverseAux_nil` by induction, and its step
case by `simp [reverseAux, ih]`; `simp` finishes by rewriting the goal
`x = x` to `True` with `eq_self : (a = a) = True` and closing it with
`of_eq_true`, and `eq_self` is proved from `propext`.  Nothing else in
the term uses an axiom, and the Agda proofs below use none.  A
mechanical translation that turned `propext` into a module parameter
would carry the parameter for nothing; the atlas (M1-11, [#11]) can
count how many T1 declarations owe their tier to `eq_self` alone.

## What the kernel term needed

The export holds 28 declarations, as follows: the inductive types
`List`, `Eq`, `PUnit`, `PProd`, `True` and `Iff`; the definitions
`List.below`, `List.brecOn.go`, `List.brecOn`, `List.casesOn`,
`List.reverseAux.match_1`, `List.reverseAux._f`, `List.reverseAux`,
`List.reverse`, `id`, `rfl` and `Eq.mpr`; the theorems `Eq.symm`,
`congrArg`, `trivial`, `of_eq_true`, `Eq.trans`, `congrFun'`,
`eq_true`, `eq_self`, `List.reverseAux_reverseAux_nil` and
`List.reverse_reverse`; and the axiom `propext`.  By feature:

+  `axioms`: `propext`, through `eq_self` only (see Tier).  The Agda
   version needs no axiom.
+  `universe-levels`: one level parameter, `u_1`, for `α : Type u_1`,
   which becomes `A : Set a`; no `imax`, and no instantiation at `Prop`.
   The proof also states equalities between propositions
   (`@Eq Prop P Q`, one universe up), which a mechanical translation
   would render as `_≡_` on `Set`; the idiomatic proof has none.
+  `projections-and-let`: two projection expressions, each the first
   field of a `PProd`, in the course-of-values recursion that
   `List.brecOn` compiles `reverseAux` into; no `let`.  Agda defines
   `reverseAcc` by pattern matching (through `foldl`), so neither
   `brecOn` nor a projection appears.

Two constructions outside the gap catalog are recorded for the
translator: structural recursion compiled to `List.brecOn` and
`List.below` (with `PProd` and `PUnit`), and an induction by `List.rec`
whose motive quantifies over an implicit argument (`∀ {bs}, ...`).
Agda's pattern matching replaces both.  Reading the term finds no use
of definitional proof irrelevance, K-like reduction, large elimination
from `Prop` (`Eq.mpr` is used at `Prop`, not into a type), quotients,
literals or eta; Lean4Less (M3-1) will measure that mechanically.

## Instance arguments

No instance arguments, in the statement or in the proof.

## The Agda version

One file, `agda/ListReverseReverse.agda`, profile CC
(`--safe --cubical-compatible`), with two proofs of the statement, as
follows:

+  `reverse-reverse`, the idiomatic one, is agda-stdlib's
   `reverse-involutive` from `Data.List.Properties`, whose type
   `Involutive _≡_ reverse` unfolds to the statement.
+  `reverse-reverse-direct` follows Lean's kernel term.  Its lemma
   `reverseAcc-reverseAcc-nil` is Lean's `reverseAux_reverseAux_nil`
   with the arguments swapped, by induction on the list; the step case
   is the induction hypothesis at `x ∷ ys`, which type-checks by
   computation where Lean's `simp` needed `eq_self`.  The theorem is
   the lemma at `ys = []`, with no rewrite where Lean used `Eq.mpr`.

The direct proof shows what the translation of this entry removes:
`brecOn` and `rec` become pattern matching, two rewrites become
computation, and the axiom goes.  Nothing had to be made explicit.

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 56,062 |
| Export, records | 1,073 |
| Export, expression records | 835 |
| Export, declarations | 28: 6 inductive, 11 def, 10 thm, 1 axiom |
| Agda, lines per file | 50, of which 18 are code and the rest comments and blank lines |
| Agda, check time | 4.8 seconds (Agda 2.8.0, no `.agdai` files) |

## Remarks

The export was made on 2026-10-07 with lean4export v4.33.0 (format
3.1.0) under Lean v4.33.1 (commit `819816b`), the pins of
[`docs/pinning.md`](../../docs/pinning.md).  Two runs gave the same
bytes (SHA-256 `b3a0ce45...4214d1ac2`), so the export is a stable
reference for the translator's golden test (M2-9, [#23]).

[#6]: https://github.com/formalverification/lean2agda/issues/6
[#7]: https://github.com/formalverification/lean2agda/issues/7
[#11]: https://github.com/formalverification/lean2agda/issues/11
[#23]: https://github.com/formalverification/lean2agda/issues/23
