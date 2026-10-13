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

## The five goldens and the kinds fixture

`make test-translator` regenerates these; the times are from one run of
`translator/tests/run.sh`'s inputs through the checker at load averages
6.66, 12.78, 15.51 before and 9.12, 12.03, 14.77 after, with other
sessions running.

| Scaffold | Declarations | Bytes | Values | Checked | Refused | Behind a refused type | Theorems | Unfolded | Runs, seconds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | 41 | 13,008 | 21 | 17 | 4 | 0 | 10 | 0 | 5, 0.6 |
| `nat-gcd-succ` | 278 | 260,175 | 201 | 109 | 41 | 51 | 65 | 0 | 47, 35.4 |
| `nat-gcd-self` | 347 | 421,148 | 266 | 144 | 54 | 68 | 103 | 0 | 60, 65.3 |
| printing fixture | 378 | 215,681 | 248 | 158 | 42 | 48 | 47 | 0 | 47, 31.0 |
| `Fixtures.selected` | 34 | 7,047 | 17 | 15 | 2 | 0 | 0 | 0 | 3, 0.2 |
| `kinds` | 381 | 218,019 | 247 | 156 | 43 | 48 | 52 | 2, one in vain | 50, 34.0 |

Before the rules, the three corpus scaffolds held 41, 272 and 337
declarations with 1, 7 and 9 values (the root's, the type abbreviations'
and the auxiliaries'), and Agda refused the root's value and 0, 5 and 6
types.  The earlier report's probe, every value printed as a transparent
definition, checked 17, 104 and 139 of 21, 201 and 266 values, refused 4,
41 and 54, and left 0, 56 and 73 behind a refused type.  With theorems
opaque the refusals are the same 4, 41 and 54 and the checked values rise
to 17, 109 and 144: the opacity cost nothing, since no refusal names a
theorem, and the five values gained in each gcd closure are the types of
compiled matchers that now check once `LE.le` unfolds one step further
(from `LE.le n m` to `LE.rec (λ le → le) instLENat n m`), with the values
that stood behind them.  The six declarations more in each gcd scaffold are
the `partial` companions and auxiliaries that every-value printing brings
in.

Every refusal is an `UnequalTerms` in which a postulate must compute: a
recursor's iota (`Nat.rec` under `Nat.add` and the `brecOn` helpers,
`Bool.rec` under `decEq`, `Decidable.rec` under the `ite` and `dite`
lemmas, `PProd.rec` under structural recursion), an instance projection
stuck on its structure's recursor (`LE.rec … instLENat`, `OfNat.rec …
(instOfNatNat 0)` against `Nat.zero`, `HAdd.rec`), `Quot.lift` in
`funext`, and the K-like `Eq.rec` in `eq_of_heq`.  The listings in
`translator/tests/expected/scaffolds/*.refusals.txt` name each.  The
fallback fired twice on `kinds`: once for the pair written to make it fire
(`useAlias`, whose argument has type `Q alias` where `Q base` is expected,
which Lean accepts by proof irrelevance), after which the pair checks; and
once in vain, on a `CannotApply` error at `Marker.mk.noConfusion` whose
message mentioned `heq_of_eq` as an argument of a term stuck on a
postulated recursor.

The translator refused nothing in the five goldens, and six declarations
of the `kinds` fixture, as `kinds.refused.txt` lists: `sorryAx`, the
theorem left to `sorry` and its dependent, and three `unsafe` definitions.
On `Init.Prelude`'s closure (2,314 constants, printed in 1 second into
1,306,906 bytes) it refuses 22, none of them a dependent: `sorryAx`,
eleven `unsafe` definitions, two `unsafe` opaque constants and the eight
`unsafe` compiler axioms; the 32 `_unsafe_rec` companions of its
`partial` definitions are postulated as cycles, and its 153 theorems and
12 other opaque constants sit in `opaque` blocks.

## `Init.Core`

`lake exe lean2agda --stats --out DIR Init.Core` selects every
declaration `Init.Core` owns and prints the closure: 2,128 constants
(1,122 definitions, 510 theorems, 9 opaque constants, 6 axioms, 145
inductive types with 185 constructors and 147 recursors, and the 4
quotient primitives) in 1,791 groups, a scaffold of 1,308,224 bytes, in
1 second (load averages 1.72, 1.00, 0.77 before).  The translator refuses
nothing in it: `sorryAx` and the `unsafe` declarations of `Init.Prelude`
are not in `Init.Core`'s closure.  Agda scope-checks the module in 11
seconds, and a full run stops at its first refusal after 10 seconds, so
the checker's cost is about ten seconds per refusal.

`scaffold_check.py` ran Agda 321 times in 2,645 seconds (44 minutes; load
averages 4.65, 2.82, 1.53 before and 1.31, 1.34, 1.93 after, with the
session's other checks running for the first ten minutes), the last run
in 8.1 seconds, and found the following.

| Declarations | Values | Checked | Refused | Behind a refused type | Types refused | Theorems | Unfolded |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 2,145 | 1,660 | 1,229 | 307 | 124 | 9 | 510 | 4, all in vain |

So 2,010 of the 2,145 declarations check (the 17 declarations beyond the
closure's constants are auxiliary definitions), and no theorem needed to
unfold: the fallback fired four times, on `Array.mk.noConfusion`
(`heq_of_eq`, a `CannotApply` whose stuck term is a postulated
recursor's), `Quot.liftIndepPr1` (`Quot.indepCoherent`, stuck on
`PSigma.rec`) and twice on `Quotient.rel.refl` (two `_proof_1` lemmas,
stuck on `HasEquiv.rec … instHasEquivOfSetoid`), and each dependent was
refused all the same, for a postulate that must compute.  The 316
refusals are 236 `UnequalTerms` and 80 `CannotApply`, in the following
classes, counted by the constants their messages name:

+  instance projections stuck on their structure's recursor: `HAdd.rec`
   (25), `OfNat.rec` or a literal against `OfNat.ofNat` (30), `LE.rec` and
   `LT.rec` (13), `Setoid.rec` (8), `HasEquiv.rec` (4);
+  `noConfusion` and `HEq`: 44 messages name `HEq`, and most of the 80
   `CannotApply` errors are a `noConfusionType` stuck on a postulated
   `casesOn` where a function type is expected;
+  recursor iota: `Decidable.rec` (13), `List.rec` (10), `Bool.rec` (9),
   `Eq.rec` (8), `Nat.rec` (7), `Prod.rec`, `Sum.rec`, `PSigma.rec`,
   `PProd.rec`, `Sigma.rec`, `Subtype.rec`, `Array.rec` and `SizeOf.rec`
   (one to three each), and 21 `PULift` motives of `casesOn` definitions
   over `Sum`, `PSum`, `ForInStep` and the `DoResult` types;
+  `Quot.lift` and `Quot.ind` (3), [#21]'s;
+  ten comparisons of two proof variables of one proposition
   (`property₇ != property₈ of type p₁ val₆` in `Subtype.eq` and
   `Subtype.ext`, `valid₅ != valid₆` in `Char.ext`, `isLt` in
   `Fin.eq_of_val_eq`, `h₁₀ != Eq.refl b₄` in `apply_eqRec`), which Lean
   accepts by definitional proof irrelevance and no unfolding can make
   equal: five of them are among the nine refused types, and they are
   [#27]'s encoding of `Prop` to settle;
+  one structure eta, `Prod.mk (Prod.fst p) (Prod.snd p) != p`, [#18]'s
   records with eta.

Of the nine refused types, four are the compiled matchers of `Nat.le`
lemmas the goldens already show, and five are the proof-variable
comparisons.  The 124 values behind them are mostly `Nat` arithmetic
lemmas, `Subtype`, `Char` and `String` validity, and
`Lean.extractMacroScopes`'s helpers.

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
