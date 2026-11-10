<!-- File: docs/translator/recursors.md -->

# Recursors

Lean's kernel gives every inductive type a recursor and one computation
rule per constructor; Agda has no recursors.  Issue [#19] defines each
recursor by pattern matching, its clauses the kernel's rules, in
`translator/Lean2Agda/Core/Recursor.lean`, so that it computes as Lean's
kernel computes it, and the scaffold ([`printing.md`][printing], The
scaffold) declares it so.  The probes `R01` to `R04` under
[`probes/`][probes] settled the shape, run with Agda 2.8.0 on 2026-10-13
from their committed paths; each file's first line records its outcome.
`R05`, of 2026-11-09, is the smallest form of the positivity check's cost
that the last section describes.
The types the recursors eliminate are [`inductives.md`][inductives]'s.

## The clause shape

The kernel stores a recursor with one rule per constructor, whose
right-hand side is a lambda over the recursor's parameters, motives and
minor premises and the constructor's fields.  Each rule becomes one
clause, as follows:

+  the parameters, motives and minor premises are variable patterns with
   the visibilities of the recursor's Lean type, which every printed
   application of the recursor passes; the rule's own lambdas may differ
   (`Eq.rec`'s binds `a` explicitly, its type implicitly) and are not
   consulted;
+  each index is `_`, which Agda's unifier fills in from the
   constructor's target;
+  the major premise is the constructor applied to `_` for each parameter
   that Lean promoted from an index and Agda keeps as one, then to one
   variable per field, with the field's Lean visibility;
+  the right-hand side is the rule's, applied to those variables and
   printed in their scope against the motive at the constructor.

```agda
Nat:rec {motive₀} zero₁ succ₂ Nat:zero = zero₁
Nat:rec {motive₀} zero₁ succ₂ (Nat:succ n₃) =
  succ₂ n₃ (Nat:rec {motive₀} zero₁ succ₂ n₃)
Eq:rec {α₀} {a₁} {motive₂} refl₃ {_} (Eq:refl _) = refl₃
```

`Eq`'s `a` is Lean's parameter and Agda's index: the recursor binds it as
`{a₁}`, and unification identifies the constructor's `_` and the index's
with it.  That is matching with a free endpoint, which needs no K: probe
`R01Promoted` checks under `--without-K` and under `--cubical-compatible`
too (2026-11-09).  A minor premise's
induction hypothesis comes out of the rule as the recursor called on the
recursive field, `Nat:rec … n₃`, or for a field of function type under a
lambda, `λ y₇ a₈ → Acc:rec … (h₆ y₇ a₈)`; Agda's termination checker
counts both as structural (probe `R03Structural`).  A type without
constructors gets the absurd clause, `False:rec motive₀ ()`.  A record
with eta is matched through Agda's projections, so its recursor reduces
on any term, as Lean's kernel reduces a structure's that is not a
proposition: `Lean.Kernel.isDefEq` equates `Prod.rec (fun x _ => x) p`
with `p.1` for a variable `p`, and does not equate
`And.rec (motive := fun _ => Nat) (fun _ _ => 5) h` with `5` (a scratch
probe on 2026-10-15).  Agda does it for propositions too, which can only
make it accept more.  A recursive record is matched through its `pattern`
declaration, like a data type.  So is a structure-like type that Agda
receives as a data type, because its constructor binds a parameter Agda
keeps as an index (the fixture's `Tagged`): its recursor reduces on a
constructor and not on a variable, where Lean's kernel eta-expands the
major premise first, so `Tagged.rec f x = f x.1 x.2` holds by `rfl` in
Lean and is refused in Agda (a scratch probe on 2026-11-09; the gap
catalog's `structure-eta` entry records the lost eta).

Lean's `K`-like reduction does not carry over: Lean reduces `Eq.rec` on
any proof of `a = a`, Agda only on `Eq.refl` (probe `R01bKLike`, rejected
with `p != Eq:rec p h`), which is the normalizer's to supply ([#26]).

## Which recursors, and blocks of them

Every recursor of a closure is defined, the nested types' `rec_N` and the
`K`-like ones (`Eq.rec`, `HEq.rec`, `True.rec`) among them, except
`String.rec`: `String` is a postulate for `BUILTIN STRING`, and so are its
constructor and recursor.  `casesOn`, `recOn`, `below` and `brecOn` are
Lean definitions and compute through the recursor.

The recursors of one block, a mutual declaration's or a nested type's
`rec_N`, are one item under the comment `-- recursor`: a `mutual` block
with every signature first, each type's `rec` in the order of the
kernel's `all` and the `rec_N` by `N` after them.  `Lean.Syntax.rec_1`
matches `Array:mk toList₁₀` and calls `rec_2` on the list, whose
`List:cons` clause calls `Lean.Syntax.rec` on the head; the termination
checker accepts the cycle through the record's pattern (probe
`R02Nested`, which computes through all three).  The item provides every
recursor of its block and refers to the constructors it matches, so that
`orderItems` places it after their types.  Its references leave out its
own names, so that `breakCycles`, which postulates a definition that
refers to itself, leaves the recursion to the termination checker; the
item is also marked structural, which would exempt such a reference.
`scaffold_check.py` reads a block's names from its signature lines and,
when Agda refuses a clause, postulates every member.

## Termination

Agda reports refused recursion as `TerminationIssue` at a definition's
first line: its signature (probe `R04NotStructural`) or, for a block, the
`mutual` keyword; the checker then postulates the item under
`-- recursor, refused by the termination checker` and counts it on its
listing's third line:

```text
defined R of S recursors by pattern matching, T refused by the termination checker
```

T is 0 everywhere it was measured: on every golden, on `Init.Core`'s
closure (145 recursors defined), and on two scaffolds of inductive types
checked with `--types-only`, which keeps the types, their recursors and
the definitions they mention, every theorem postulated.  The scaffold of
the 616 inductive types declared under `Init` (printed in 48 s into
452 MB, since every value is printed and some of `Init`'s theorems are
omega's proofs of tens of megabytes) checked in 4 Agda runs and 296 s at
a load average near 2 (2026-10-15):
554 of its 615 data types and records and 1,823 of its 2,061
declarations, with 556 of 617 recursors defined and the rest dropped
behind `ByteArray.IsValidUTF8` with their types (`String.Pos` and the
`Std.Packages` argument structures, through their `autoParam` scripts).
`Float.Model` and `Float32.Model`, which [`inductives.md`][inductives]
left waiting for `Float.Model.Format.numBits binary64` to compute to 64,
check now.  The scaffold of the 72 nested or mutual types under `Init`,
`Std` and `Lean` in `import Lean` (printed in 66 s into 490 MB) checked in
9 Agda runs and 3,766 s at a load average near 2: 374 of its 478 data
types and records and 1,864 of its 2,135 declarations, with 439 of 595
recursors defined.  All ten mutual blocks check, and so do their recursor
blocks, 50 recursors in all, the largest of 21
(`Lean.Meta.Grind.Arith.Cutsat`); 14 nested types' blocks (`Lean.Json`,
`Lean.MessageData`, `Lean.Elab.InfoTree` and others) stand behind types
that exhausted the heap (`ByteArray.IsValidUTF8`, `Lean.Meta.Cache`,
`Lean.Server.RpcObjectStore`, `Std.DHashMap.Internal.List.HashesTo`, each
charged as the declaration Agda named last, before the checker placed an
exhaustion exactly; that charge is right for a positivity check, which
runs after the type's `Checked` line, as `ByteArray.IsValidUTF8`'s does), the
cost of the next section, which also refused four of the `UInt`
conversions' values.  The first run of this measurement refused
`Std.DTreeMap.Internal.Impl.WF.rec`'s clauses with `UnsolvedConstraints`:
its recursive call passes minor premises whose types begin
`{x₃ : α₀ → Set} → ⦃ inst₄ : LawfulEqOrd α₀ ⦄`, and Agda, inserting both
binders, found two instances, the binder and the clause's pattern variable
for the constructor's instance field.  The printer's eta repair now covers
that case ([`printing.md`][printing], Binder repair), the recursor
fixture's `Holder` tests it, and `WF.rec` is defined.

## Agda's positivity check and Lean's arithmetic

Agda's positivity check normalizes the types of every data constructor's
and record field's arguments, under `--no-positivity-check` and
`NO_POSITIVITY_CHECK` too (`Agda/TypeChecking/Positivity.hs` at 2.8.0,
lines 576 and 621), and once the recursors compute, the full normal form
of some of Lean's compiled definitions is exponential.  A structural
recursion that `brecOn` runs on a literal while matching on a variable,
`Nat.ble 20 v`, sticks at the matcher with its `below` table twice in
every level, so that a record whose field mentions `v % 8` checks at a
peak of 98 MB, one that mentions `v % 12` at 699 MB, and one that
mentions `v % 16` exhausts a 2 GB heap in about 30 s (probe `R05PositivityMod`,
measured 2026-11-09; Lean's `Nat.mod` compares through `Nat.ble`).
`ByteArray.IsValidUTF8`, whose field mentions `List.utf8Encode m`, ran
Agda out of memory wherever it was checked before the heap bound existed,
once to 23 GB before the Linux kernel's OOM killer stopped it, and with
the bound it is refused in all six scaffolds here that hold it: three
goldens, `Init.Core`'s closure and both type scaffolds.  Lean's kernel
never normalizes a type to check it, and computes `Nat.ble`, `Nat.mod`
and the rest on literals with GMP.  Agda-native definitions of `Nat.ble`
and `Nat.beq` alone do not help, since `Nat.div` and `Nat.mod` unfold
through structural recursion on a fuel argument, `Nat.brecOn` as in
`Nat.ble`; the fix is the operation table of [#31], each accelerated
operation an Agda definition that is stuck on a variable.  Until then
`scaffold_check.py` bounds Agda's heap (8G by default) and charges a run
that exhausts it to the declaration Agda died in (its section of
[`printing.md`][printing-checks] says how it knows):
`ByteArray.IsValidUTF8` is refused as a type wherever it appears, with
its recursor, `String.ofByteArray` and `String.rec` behind it, and in
`Init.Core`'s closure 70 values more.

## What Agda checks

The golden scaffolds and their counts, before and after, are in
[`printing.md`][printing-checks]'s table: every recursor of every golden is
defined but `ByteArray.IsValidUTF8.rec`, dropped with its type in the three
goldens that hold it, none is refused by the termination checker, and the
values that
check rise from 17, 142 and 183 to 21 of 21, 199 of 201 and 262 of 266 in
the three corpus closures, with nothing left behind a refused type there.
The recursor fixture checks 552 of its 554 values, each fixture theorem
among them; its two refusals are `eq_of_heq` and `Nat.modCore_lt` from the
closure.  The compiled matcher of `Nat.zero_lt_of_ne_zero` and
`Nat.modCore.go.eq_1`, which needed `n + 1` to be `Nat.succ n`, check, and
the `iota` classes of the code before (`Nat.rec` under `Nat.add`,
`Nat.ble`, `Nat.beq` and the `brecOn` helpers, `List.rec`, `Bool.rec`,
`Decidable.rec` under `ite` and `dite`, `PProd.rec`, `Eq.rec` on
`Eq.refl`), the literals against `OfNat`, and every `noConfusion` are gone.

The acceptance criterion of [#19] is that every recursor in the closure of
`Init.Core` emits, is accepted by the termination checker, and computes on
the corpus terms.  On that closure (every declaration `Init.Core` owns,
printed into 1,272,372 bytes, the quotient's two rewrite rules of [#21]
among its declarations), the checker made 24 Agda runs in 759 s at load
averages of 4.4 before and 3.1 after (2026-11-09), against the
[`quotient-rules`][report-quot] report's 311 runs in 5,016 s on the code
before [#19], which has the rules, and the
[`opaque-theorems`][report-opaque] report's 320 runs on the code before
both:

| `Init.Core`'s closure | Declarations | Values | Checked | Refused | Behind a refused type | Types refused | Unfolded | Recursors defined |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| before [#19] and [#21] | 1,963 | 1,660 | 1,344 | 312 | 4 | 1 | 6, five in vain | 0 of 146 |
| before [#19] | 1,965 | 1,660 | 1,351 | 305 | 4 | 1 | 4, one in vain | 0 of 146 |
| after | 1,963 | 1,660 | 1,570 | 16 | 74 | 2 | 5, none in vain | 145 of 146 |

The 147 recursors are 145 inductive types' and `Lean.Syntax`'s two
`rec_N`; `String.rec` stays a postulate, and `ByteArray.IsValidUTF8.rec`
is dropped with its type, so 145 of the 146 the listing counts (all but
`String.rec`) are defined, all of them accepted by the termination
checker.  The 16 refused values, with the refused type of `apply_eqRec`,
fall into the classes of the goldens: 15 comparisons of two proofs of one
proposition (`Subtype.eq`, `Subtype.ext`, `Subtype.eta`,
`Subtype.mk.injEq`, `Subtype.instDecidableEq`'s proof, `Char.ext`,
`Char.mk.injEq`, `Fin.eq_of_val_eq`, `Fin.mk.injEq`, `proof_irrel`,
`instSubsingletonDecidable`, `Nat.modCore_lt`, `dif_pos`, `dif_neg`, and
the type of `apply_eqRec`), [#27]'s; and two `K`-like reductions,
`eq_of_heq` and `cast_eq`, [#26]'s.  On the same code without [#21]'s
rules (this branch before it merged) the run refused seven values more,
the quotient's (`funext`, `Quot.liftBeta`, `Quot.indBeta`,
`Quot.liftIndepPr1`, `Quotient.exact`, `Quotient.lift₂`'s proof,
`Quotient.rel.refl`), and the two listings differ in nothing else but the
two rules and the fallback's unfoldings at those seven.  The 74 values
behind a refused type are `apply_eqRec` with the 3 behind it
(`Quot.pliftOn` and its kin, as before) and 70 behind
`ByteArray.IsValidUTF8` (`String`'s equality and its instances,
`Lean.Name.beq`, the macro scopes and `Init.Core`'s macro and unexpander
rules), [#31]'s.

The fallback fired five times, and each unfolding helped:
`Quotient.sound` for `Quotient.rec`, as before; `Setoid.refl` and
`Quotient.lift₂._proof_1` for `Quotient.lift₂._proof_2`, as with the
rules alone; and `Eq.symm` and `Nat.eq_of_beq_eq_true` for
`DoResultPRBC.noConfusion`, which the recursors made reachable.  None was
under well-founded recursion, which `Init.Core`'s closure does not
contain: `Acc` and `WellFounded.Nat.fix` are declared in `Init.WF`, which
`Init.Core` does not import.  (At the pin `WellFounded.Nat.fix` is
fuel-based in any case, its recursion `Nat.rec` on the fuel;
[gap catalog][catalog-literals].)

## Verification

`make test-translator` runs the following:

+  `tests/Recursors.lean`: the clauses of `Nat.rec` (a recursive field),
   `Eq.rec` and `HEq.rec` (a parameter Agda keeps as an index), `Acc.rec`
   (a recursive field of function type), `False.rec` (the absurd clause)
   and `Prod.rec` (a record); `String.rec` left a postulate;
   `Lean.Syntax`'s three recursors as one `mutual` item, `rec` first,
   `rec_1` matching `Array:mk` and referring to the constructors it
   matches; the fixture's mutual pair as one item in the order of `all`;
   `recursorRank`'s order; the patterns' layout; and `breakCycles`
   leaving a structural item's recursion alone while it postulates an
   ordinary cycle;
+  `tests/Scaffold.lean`: the `kinds` fixture's class recursor, defined by
   its clause;
+  `tests/Printing.lean`: the three eta repairs of the printing fixture,
   `etaRepaired`, `instanceRepaired` and `hiddenInstanceRepaired`, with
   their counts;
+  the scaffold of the fixture `tests/TranslatorTests/Input/Recursors.lean`
   (a recursive type with structural recursion through `brecOn`, an
   indexed family, a type nested through `Array` and `List`, a mutual
   pair, a `K`-like family, a structure-like data type projected through
   its recursor, a type whose constructor has an implicit and an instance
   field, and a type without constructors), against its golden file
   and listing: every recursor is defined and every `rfl` theorem about a
   value that computes through one checks;
+  `scripts/python/tests/test_scaffold_check.py`: a recursor and a mutual
   block of them parsed, their refused clauses postulated member by
   member, a refused signature dropped, the termination refusal at a
   block's first line, the listing's third line, a block of postulates,
   `--types-only` keeping the recursors and postulating the theorems they
   mention, the heap bound, and the charge of an exhausted run to the
   declaration Agda died in, through the markers: a blowup in a
   postulate, in a definition's signature, in its clauses and in a type's
   positivity check, played by a fake Agda that names declarations as
   Agda 2.8.0 does, and a run past the time bound, which is an error.

Each new check failed on the code before this change, run in a scratch
copy of `main` at `37e7feb`: 14 of the 15 new or changed tests of
`test_scaffold_check.py` (7 failures, and 7 errors against stubs of the
names `main` lacks; the fifteenth, a lone recursor's refused clause, is
handled there as any definition's); the clause checks of
`tests/Recursors.lean`, run without the names `main` lacks, at
`Nat.rec`, a postulate there; the class recursor of `tests/Scaffold.lean`;
the three eta repairs of `tests/Printing.lean`, which `main` prints as
`applyExplicit implicitId`, `applyInstance g₀` and `applyHidden g₀`; and
the recursor fixture's scaffold, in which `main` refuses about a hundred
values, every fixture theorem among them.  The last eta case was found
after the others: on the build before it, the fixture's `Holder.rec` was
refused with `UnsolvedConstraints`, and nine of its dependents with it.

## Hand-off

+  [#21], merged first: nothing here touches the quotient primitives or
   their rules, and with both every quotient refusal of the goldens and of
   `Init.Core`'s closure checks.
+  [#22]: a recursor block is one `mutual` item and must stay in one
   module; it refers to its types' constructors, so it can sit in the
   module of its block's types or in one that imports it.
+  [#26]: `K`-like reduction, `eq_of_heq` and `cast_eq`.
+  [#27]: the comparisons of two proofs of one proposition
   (`Nat.modCore_lt`, `dif_pos`, `dif_neg`, the `Subtype` and `Fin`
   extensionality lemmas).
+  [#31]: Agda-native definitions of Lean's accelerated `Nat` operations,
   which would let Agda's positivity check through
   `ByteArray.IsValidUTF8` and take the heap bound out of play; the
   minimal reproduction is a record whose field mentions `v % 16`.

[#19]: https://github.com/formalverification/lean2agda/issues/19
[#21]: https://github.com/formalverification/lean2agda/issues/21
[#22]: https://github.com/formalverification/lean2agda/issues/22
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#31]: https://github.com/formalverification/lean2agda/issues/31
[printing]: printing.md
[report-quot]: ../reports/quotient-rules-2026-11-08.md
[printing-checks]: printing.md#what-agda-checks-and-the-fallback
[report-opaque]: ../reports/opaque-theorems-2026-10-13.md
[catalog-literals]: ../foundations/gap-catalog.md#literals
[inductives]: inductives.md
[probes]: probes/
