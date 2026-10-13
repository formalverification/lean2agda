<!-- File: docs/reports/opaque-theorems-2026-10-13.md -->

# Theorems opaque, definitions transparent, 2026-10-13

What Agda checks of a profile U scaffold once every definition is
transparent, every theorem sits in an `opaque` block, and a theorem is
unfolded only when Agda's complaint names it: the measurements of issue
[#20], taken on 2026-10-13.  [`printing.md`][printing] states the rules
these numbers decided and the vocabulary of refusals; the earlier report
[`printing-blowup`][blowup] measured the scaffold before the rules, when
it printed every type and the root's value only, and a probe of it
printed every value as a transparent definition.  The code is the
translator at this report's commit, under Lean v4.33.1 and Agda 2.8.0,
on a 20-thread Intel i9-12900H with 62 GB of memory, which other sessions
shared; the load averages are given with each run.

## Terms

+  **Values** are the declarations printed with a value: definitions,
   theorems and opaque constants, auxiliary definitions included.  A value
   is **checked** when Agda accepted its clause, **refused** when
   `scaffold_check.py` had to postulate its signature (`refused value`),
   and **behind a refused type** when its declaration was dropped with a
   type Agda refused (`refused type`, `dropped`).
+  **Unfolded** counts the theorems the fallback re-emitted transparently
   because an error's message named them, and **in vain** those whose
   dependent was refused all the same.
+  **Runs** are the Agda runs the checker made; the last one checked what
   remained.
+  **Data types and records** are the inductive types the scaffold
   declares as such since [#18]; a block of them is one declaration.

## The goldens

`make test-translator` regenerates these.  The code is the translator
rebased onto the records and data types of [#18] (pull request 80); the
times are from one run of `translator/tests/run.sh`'s inputs through the
checker at load averages 2.12, 2.40, 2.52 before and 2.18, 2.81, 2.70
after.  A declaration is a declaration of the Agda module, a data type or
a record with its constructors being one.

| Scaffold | Declarations | Data types and records | Bytes | Values | Checked | Refused | Behind a refused type | Theorems | Unfolded | Runs, seconds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | 34 | 6 | 11,988 | 21 | 17 | 4 | 0 | 10 | 0 | 5, 0.4 |
| `nat-gcd-succ` | 252 | 23 | 246,750 | 201 | 141 | 49 | 11 | 65 | 0 | 51, 49.7 |
| `nat-gcd-self` | 320 | 24 | 404,406 | 266 | 182 | 62 | 22 | 103 | 0 | 65, 101.5 |
| printing fixture | 333 | 41 | 194,543 | 248 | 199 | 49 | 0 | 47 | 0 | 50, 40.6 |
| `Fixtures.selected` | 29 | 6 | 6,015 | 17 | 15 | 2 | 0 | 0 | 0 | 3, 0.2 |
| inductives fixture | 77 | 24 | 20,156 | 29 | 27 | 2 | 0 | 1 | 0 | 3, 0.4 |
| `kinds` | 333 | 41 | 197,213 | 246 | 195 | 51 | 0 | 51 | 2, one in vain | 54, 47.4 |
| `Init.Core`'s inductive types | 539 | 144 | 254,511 | 246 | 197 | 49 | 0 | 48 | 0 | 50, 53.6 |

Before the rules, the three corpus scaffolds printed the root's value, the type
abbreviations' and the auxiliaries' only, and Agda refused the root's value and
0, 5 and 6 types.  The earlier report's probe, every value printed as a
transparent definition against postulated inductive types, checked 17, 104 and
139 of 21, 201 and 266 values, refused 4, 41 and 54, and left 0, 56 and 73
behind a refused type.  With theorems opaque and the inductive types declared,
the same values are 17, 141 and 182 checked, 4, 49 and 62 refused, and 0, 11 and
22 behind a refused type: the opacity costs nothing, since no refusal names a
theorem; the four compiled matchers of the `Nat.le` lemmas, whose `n ≤ m` now
unfolds through the record projection `LE.le₁` and the transparent `instLENat`
to `Nat.le n m`, check, and 40 and 46 values that stood behind them reach Agda,
32 and 38 of which check; the other 8 and 8 are the refusals that rose, 41 to 49
and 54 to 62, each stuck on a postulated recursor.  Measured on the branch
before the rebase, with the inductive types still postulates, the same scaffolds
checked 144, 109 and 17 values and refused 54, 41 and 4, exactly the probe's
refusals.

Every refusal is an `UnequalTerms` in which a postulated recursor must
compute: `Nat.rec` under `Nat.add`, `Nat.ble`, `Nat.beq` and the `brecOn`
helpers, `Bool.rec` under `decEq`, `Decidable.rec` under the `ite` and
`dite` lemmas, `PProd.rec` and `List.rec` under structural recursion,
`Eq.rec` on `Eq.refl` in `WellFounded.Nat.fix.go.congr_simp`, the K-like
`Eq.rec` in `eq_of_heq`, and `Quot.lift` in `funext`.  The three refused
types are the compiled matcher of `Nat.zero_lt_of_ne_zero` and, in
`nat-gcd-self`, `Nat.modCore.go.eq_1`, which need `n + 1` to be
`Nat.succ n`.  The listings in
`translator/tests/expected/scaffolds/*.refusals.txt` name each.  The
fallback fired twice on `kinds`: once for the pair written to make it
fire (`useAlias`, whose argument has type `Q alias` where `Q base` is
expected, which Lean accepts by proof irrelevance; the proposition is an
equation, since `True` is a record on the Agda side, whose eta rule
identifies its elements without any unfolding), after which the pair
checks; and once in vain, on a `CannotApply` error at
`Marker.mk.noConfusion` whose message mentioned `heq_of_eq` as an
argument of a term stuck on a postulated recursor.

The translator refused nothing in the corpus goldens, three declarations
of the inductives fixture (the `unsafe` type `Bad`, its constructor and
its recursor) and six of the `kinds` fixture, as their `refused.txt`
files list: `sorryAx`, the theorem left to `sorry` and its dependent, and
three `unsafe` definitions.  On `Init.Prelude`'s closure (2,314 constants,
printed in 1 second into 1,306,906 bytes) it refuses 22, none of them a
dependent: `sorryAx`, eleven `unsafe` definitions, two `unsafe` opaque
constants and the eight `unsafe` compiler axioms; the 32 `_unsafe_rec`
companions of its `partial` definitions are postulated as cycles, and its
153 theorems and 12 other opaque constants sit in `opaque` blocks.

## `Init.Core`

`lake exe lean2agda --stats --out DIR Init.Core` selects every
declaration `Init.Core` owns and prints the closure: 2,128 constants
(1,122 definitions, 510 theorems, 9 opaque constants, 6 axioms, 145
inductive types with 185 constructors and 147 recursors, and the 4
quotient primitives) in 1,791 groups, a scaffold of 1,243,985 bytes, in
1 second.  The translator refuses nothing in it: `sorryAx` and the
`unsafe` declarations of `Init.Prelude` are not in `Init.Core`'s closure.
Agda scope-checks the module in 12 seconds, and a full run stops at its
first refusal after about 10 seconds, so the checker's cost is about
twelve seconds per refusal.  It was measured twice: on this branch before
the rebase onto [#18]'s records, with the inductive types postulates
(load averages 4.65, 2.82, 1.53 before and 1.31, 1.34, 1.93 after), and
on the rebased code (1.74, 2.46, 2.62 before and 1.33, 1.75, 1.84 after).

| Inductive types | Declarations | Values | Checked | Refused | Behind a refused type | Types refused | Theorems | Unfolded | Runs, seconds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| postulated | 2,145 | 1,660 | 1,229 | 307 | 124 | 9 | 510 | 4, all in vain | 321, 2,645 |
| declared ([#18]) | 1,963 | 1,660 | 1,344 | 312 | 4 | 1 | 510 | 6, five in vain | 320, 3,786 |

With the inductive types declared, 1,959 of the 1,963 declarations check
(the 17 beyond the closure's constants are auxiliary definitions, and
144 of 144 data types and records check); eight of the nine refused
types went, the four compiled matchers of the `Nat.le` lemmas with the
record projections, and four proof-variable comparisons whose
propositions are now records of one field, which Agda's eta rule
identifies, so that 120 values came out from behind them, 115 of which
check.  The one refused type left is `apply_eqRec` (`h₁₀ != Eq.refl b₄`),
with `Quotient.pliftOn` and two more behind it.

**The fallback fired six times on the rebased code, and once it helped.**
`Quotient.rec` is refused with `Quotient.sound p₆ != Quot.sound p₆`: Lean's
kernel accepts the two proofs by proof irrelevance, Agda needs the theorem
`Quotient.sound`, which is `Quot.sound` by definition, to unfold, and once
it does, `Quotient.rec` checks.  That is the mechanism the issue asked for,
met once in `Init.Core`.  The five in vain were `heq_of_eq` for
`Array.mk.noConfusion` (a `CannotApply` whose stuck term is a postulated
recursor's), `Quot.indepCoherent` for `Quot.liftIndepPr1` (stuck on
`PSigma.fst₂` of a term the recursor would reduce), `Setoid.refl` for
`Quotient.lift₂._proof_2`, and two `_proof_1` lemmas for
`Quotient.rel.refl` (both stuck on `Setoid.r₁ s₁ a₂ a₂` where the
instance `s₁` is a variable), each dependent refused all the same.
Before the rebase the four unfoldings were all in vain, the
`Quotient.rel.refl` and `Quot.liftIndepPr1` ones among them, and
`Quotient.rec` was refused without naming a theorem, since its
`Quotient.sound` and `Quot.sound` then sat behind postulated structures.

The 313 refusals on the rebased code are 230 `UnequalTerms`, 80
`CannotApply` and 3 `UnsolvedConstraints` (a new kind: Agda's unifier
leaves a constraint open where a record's field must be inferred), in
the following classes, counted by the constants their messages name:

+  `noConfusion` and `HEq`: 44 messages name `HEq`, and most of the 80
   `CannotApply` errors are a `noConfusionType` stuck on a postulated
   `casesOn` where a function type is expected;
+  recursor iota: `Nat.rec` (16), `Bool.rec` (14), `Decidable.rec`
   (12), `List.rec` (11), `Eq.rec` (8), `Prod.rec` and `Sum.rec` (5),
   and 24 `PULift` motives of `casesOn` definitions over `Sum`, `PSum`,
   `ForInStep` and the `DoResult` types, 31 messages naming `PUnit`
   among them;
+  `Quot.lift` and `Quot.ind` (4), [#21]'s;
+  eleven comparisons of two proof variables of one proposition
   (`property₇ != property₈ of type p₁ val₆` in `Subtype.eq` and
   `Subtype.ext`, `valid₅ != valid₆` in `Char.ext`, `isLt` in
   `Fin.eq_of_val_eq`, `h₁₀ != Eq.refl b₄` in `apply_eqRec`), which Lean
   accepts by definitional proof irrelevance and no unfolding can make
   equal: they are [#27]'s encoding of `Prop` to settle, and the four
   that were among the refused types before the rebase check now, their
   propositions being records of one field.

The instance projections that the first run refused (`HAdd.rec`,
`OfNat.rec`, `LE.rec`, `Setoid.rec`, `HasEquiv.rec`, 80 messages) are
gone with [#18]'s records, and so is the one structure eta
(`Prod.mk (Prod.fst p) (Prod.snd p) != p`).

## To rerun

Inside `nix develop`, from `translator/`:

```sh
lake exe lean2agda --out out Init.Data.Nat.Gcd -- Nat.gcd_self
python3 ../scripts/python/scaffold_check.py --messages out/U/Init/Data/Nat/Gcd.agda
lake exe lean2agda --stats --out core Init.Core
(cd core && agda --only-scope-checking U/Init/Core.agda)
python3 ../scripts/python/scaffold_check.py --messages core/U/Init/Core.agda
```

`make test-translator` regenerates and compares the six goldens.

[#18]: https://github.com/formalverification/lean2agda/issues/18
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#20]: https://github.com/formalverification/lean2agda/issues/20
[#21]: https://github.com/formalverification/lean2agda/issues/21
[printing]: ../translator/printing.md
[blowup]: printing-blowup-2026-10-12.md
