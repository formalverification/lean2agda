<!-- File: docs/translator/inductives.md -->

# Inductive types

The translator declares each Lean inductive type in Agda as a `record` or
a `data` type whose constructors and fields keep the binder visibilities
of their Lean types, so that the printer's applications
([`printing.md`][printing]) check against them.  Issue [#18] implements it
under profile U, in `translator/Lean2Agda/Core/InductiveShape.lean`, which
decides each type's shape, and `Core/Inductive.lean`, which prints a block
of types as one declaration; the scaffold declares every inductive type of
a closure this way.  The rules below were settled by the Agda probes under
[`probes/`][probes], run with the shell's Agda 2.8.0 on 2026-10-13 from
their committed paths (`cd docs/translator/probes && agda I04Promotion.agda`);
each file's first line records its outcome.

## Records and data types

A type with one constructor and no indices is one that Lean's kernel
projects from (`Expr.proj`), and it becomes an Agda `record` unless one of
the following holds:

+  its constructor binds a parameter explicitly (the next section), since
   a record has no indices;
+  it is `String`, which stays a postulate because `BUILTIN STRING` binds
   Agda's string literals to a postulated type, so that its constructor
   `String.ofByteArray` and its recursor stay postulates too.

Every other type becomes a `data` type, `Nat` among them, followed by
`{-# BUILTIN NATURAL Nat #-}` so that literals print as decimals; an empty
type is a `data` type without constructors.

Eta follows Lean's rules, as follows:

+  A structure-like type (one constructor, no indices, not recursive) has
   eta in Lean ([`structure-eta`][catalog-eta]), and a record has eta in
   Agda.  A record with no fields is a unit-like type, any two of whose
   elements are equal in both (probe `I02RecordFields`).
+  A recursive one, such as `structure Tree where children : List Tree`,
   has no eta in Lean, and Agda would give it some as an `inductive`
   record.  It is declared `no-eta-equality`, so that it has none in Agda
   either (probe `I06bRecursiveRecordEta`, rejected with
   `t != Tree:mk (Tree.label₀ t) (Tree.children₁ t)`), and `pattern`, so
   that the recursors of [#19] can match on its constructor, which Agda
   refuses for a record without eta otherwise (probe `I06cNoEtaPattern`,
   rejected with `[SplitOnNonEtaRecord]`).  Its projections compute on its
   constructor, as Lean's kernel reduces them (probe `I06RecursiveRecord`).
   `Init` has no such type, and `import Lean` has 27, all in Lean's own
   code.
+  A structure-like type whose constructor binds a parameter explicitly
   becomes a data type with an index, and loses the eta Lean gives it:
   `Lean.Meta.CheckTactic.CheckGoalType` is the one such type in
   `import Lean`, and it is not in `Init.Core`'s closure.

A recursive type with one constructor is a record rather than a data type
because Lean projects from it too: the projection function
`Tree.children` is `fun self => self.2`, and the kernel types `Expr.proj`
on any type with one constructor and no indices.  Printed through the
recursor, as [#17] printed every projection, such a projection is
ill-typed, since a recursive type's minor premise takes the fields'
induction hypotheses as well: on the code before this rule, the scaffold
of the fixture `InductiveFixtures.Rose` refused both of its projections
with `List InductiveFixtures:Rose !=< Nat`.

## Parameters and indices

Agda's constructors take a type's parameters implicitly, or as instance
arguments where the type declares them as instances (probe
`I01ParamVisibility`), and Lean's constructors take theirs the same way,
except where Lean promoted an index to a parameter:

+  Lean promotes an index to a parameter when every constructor's target
   uses it uniformly, even when a constructor binds it explicitly:
   `Eq.refl (a : α) : Eq a a` gives `Eq` the parameters `α` and `a` and
   one index.  Declared as a parameter, `a` is implicit in Agda's
   `Eq.refl`, and the printer's application `Eq:refl {α₀} a₁` fails
   (probe `I05KeptParameter`, rejected with `[CannotApply]`).
+  An instance parameter is bound as an instance argument by both
   (probe `I01ParamVisibility`): four class constructors in `Init.Core`'s
   closure (`ReflBEq.mk`, `LawfulBEq.mk`, `LawfulSingleton.mk`,
   `Std.LawfulCommIdentity.mk`) bind six such parameters.

So the parameters that stay Agda parameters are the longest prefix of the
kernel's that every constructor binds as Agda's constructors bind
parameters (`agdaParamCount`), and the rest become indices, which each
constructor binds as Lean's does:

```agda
data Eq {α₀ : Set} : α₀ → α₀ → Set where
  Eq:refl : (a₁ : α₀) → Eq {α₀} a₁ a₁
```

Probe `I04Promotion` checks this declaration, `HEq`'s, whose type has an
implicit binder among its indices, and the postulated recursors' types
against both.  Six types of `import Lean` have a parameter bound
explicitly, all in `Init`: `Eq`, `HEq`, `CheckGoalType`,
`String.Slice.Pattern.Model.IsLongestRevMatchAtChain`, and the
`IsPlausibleIndirectSuccessorOf` of `Std.Iter` and of `Std.IterM`; in
`Init.Core`'s closure, only `Eq` and `HEq`.  Every other promotion stays:
`Nat.le n` and `Relation.TransGen r a` keep their promoted `n` and `a` as
parameters, which every constructor binds implicitly.

Uniformity never forces a promotion to be undone.  Agda needs a
parameter to be uniform only in the constructors' targets, not in their
recursive arguments (probe `I03NestedMutual`, a parameter that varies in
a recursive argument), and Lean's parameters are uniform everywhere.

## Visibilities

Every constructor and field keeps the binder visibilities of its Lean
type, parameters included, since the printer passes each argument with
the visibility of the head's Lean type.  A data constructor's type is
printed from Lean's after the Agda parameters, in the scope of the type's
parameter telescope.  A record's fields are bound as its constructor binds
them, `f : T`, `{f} : T` or `⦃ f ⦄ : T` (probe `I02RecordFields`): a
class's parent structures are instance fields (`Applicative.mk` binds
`[toFunctor : Functor f]`), and 24 constructor fields of `Init.Core`'s
closure are bound other than explicitly, among them `Nat.le.step`'s `{m}`.

A record's field is named as the printer names the constructor's binder
at its depth: the base of its Lean name followed by the subscript of the
number of parameters and fields before it, so that `Prod`'s fields are
`fst₂` and `snd₃`.  The declaration enters every parameter and field in
turn, so that a later field's type names an earlier field, and a field
named like a keyword (`ByteArray`'s `data₀`) is still a name.

## Projections

`Expr.proj S i t` for a record `S` prints as Agda's projection of the
field, applied to `S`'s parameters as Agda's projections take them
(implicitly, or as instance arguments for the parameters declared as
instances) and then to `t`:

```agda
Prod.fst₂ {Nat} {Nat} p₀
InductiveFixtures:Packed.fits₅ {Nat} ⦃ b₀ ⦄ p₁
```

It computes on a constructor and, for a record with eta, on any term.
Lean's projection functions (`Prod.fst`, `LE.le`, and the theorems that
project proposition fields, such as `Subtype.property`) have the value
`fun params self => self.i`, all 997 of `Init`'s, and the scaffold gives
each projection function of a record that value, so that it keeps its
Lean binders (`LE:le : {α₀ : Set} → ⦃ _ : LE α₀ ⦄ → α₀ → α₀ → Set`) and
unfolds to the field projection.  A type that mentions one then checks
where Agda's projection appears: the printing fixture's dependent
projection `PrintFixtures.Dependent.value`, which the scaffold of [#17]
refused, checks.

From a type with one constructor that is not a record (`String`, or a type
whose constructor binds a parameter explicitly), a projection still prints
through the type's recursor, as [#17] printed every projection.  It checks
for a field whose type mentions no earlier field, and the others wait for
the recursors of [#19] to compute.  The printer refuses a projection from
a recursive such type, whose recursor's minor premise would need the
induction hypotheses too; `import Lean` has none.

## Mutual and nested blocks

A block of inductive types is one declaration: a lone type as itself, the
types of a mutual declaration inside one `mutual` block in the order of
the kernel's `all`, each a data type or a record by the rules above.  The
scaffold orders a block after what it uses and before its recursors,
which mention its constructors.

A nested type needs nothing more.  Agda accepts an occurrence of the type
in another type's parameters (`Array Lean:Syntax`, where `Array` is a
record of a `List`) and checks its positivity through that type's
definition (probe `I03NestedMutual`).  The kernel's auxiliary mutual types
for a nested type exist only in its recursors' motives
(`Lean.Syntax.rec_1` takes motives on `Array Syntax` and `List Syntax`),
and the recursors stay postulates of their printed types until [#19]
defines them by mutual pattern matching.

`Init.Core`'s closure has `Lean.Syntax`, nested through `Array` and
`List`, and no mutual block, and neither has the rest of `Init`.
`import Lean` has 72 nested or mutual types in Lean's own code, among
them ten mutual blocks of 2 to 13 types, and the measurements below check
them.

## Positivity

Lean's kernel checks every safe inductive type for strict positivity, and
Agda's positivity checker accepted every type that reached it in the runs
below: no refusal was one of positivity.  The kernel checks no unsafe type
(`unsafe inductive Bad | mk : (Bad → Nat) → Bad` is accepted), so an
unsafe block is declared after `{-# NO_POSITIVITY_CHECK #-}`, which Agda
allows outside `--safe` (probe `I07NotPositive`, rejected with
`[NotStrictlyPositive]`, and probe `I07bNoPositivityCheck`).  `import Lean`
has four unsafe inductive types, the `State` records of unsafe folds over
expressions.  Since [#20] the scaffold refuses every `unsafe` declaration
before `inductiveDecl` sees it, an unsafe type with its constructors and
recursor among them, and names each in `refusals.txt`
([`printing.md`][printing], The scaffold); the pragma therefore reaches a
module only through a caller that declares an unsafe block itself, as
`tests/Inductives.lean` does for the fixture's `Bad`.

## Sharing in constructor types

The sharing pass rewrites the types of inductive types and constructors
too, so a constructor's type may refer to an auxiliary definition.  An
auxiliary that mentioned a type of its own block would have to sit inside
the block's declaration, or between a forward-declared signature and the
constructors, both of which Agda accepts (probe `I03NestedMutual`).  The
pass instead makes no auxiliary of a type's or a constructor's type that
mentions a type of its block, so that every auxiliary a block uses
precedes it.  Such a subterm is rare, since it must be closed, and a type
with parameters occurs in its constructors only applied to them.

Without the rule, `breakCycles` would turn such an auxiliary into a
postulate, and the constructor would silently take an opaque `Set`: the
fixture `InductiveFixtures.Wide`, whose constructor repeats
`Nat → … → Nat → Wide`, printed with the rule switched off as
`Wide:node : Wide:node:~ushare:~n1 → …` after
`postulate Wide:node:~ushare:~n1 : Set`, which Agda accepts.

## What Agda checks

The acceptance criterion of [#18] is that every inductive type of the
closure of `Init.Core` emits and checks under profile U.  That closure has
145 inductive types, 185 constructors, 6 indexed families (`Nat.le`,
`Eq`, `HEq`, `Nat.le.below`, `Relation.TransGen` and its `below`), and
115 types with one constructor and no indices, 28 of them propositions.
`translator/scripts/InductiveTypes.lean` lists them, and a scaffold with
them as its roots declares each one, with the definitions and theorems
its types need as postulates; `tests/run.sh` checks it against the listing
`tests/expected/scaffolds/init-core-inductives.refusals.txt`:

| Scaffold | Roots | Declarations, checked | Data types and records, checked | Refused |
| --- | --- | --- | --- | --- |
| `Init.Core`'s closure | 145 | 534 of 538 | 144 of 144 | 4 compiled matchers' types |
| `Init`, `--types-only` | 616 | 961 of 968 | 608 of 615 | 4 types, and 3 that use them |
| Lean's nested or mutual types, `--types-only` | 72 | 618 of 685 | 411 of 478 | 8 types, and 59 that use them |
| the fixture `TranslatorTests.Input.Inductives` | 17 | 79 of 79 | 25 of 25 | none |

The 145th inductive type of `Init.Core`'s closure is `String`, a
postulate.  The scaffold prints in 1.9 s, holds 127,134 bytes,
scope-checks in 0.9 s, and type-checks in 5 Agda runs, 3.9 s in all and
1.1 s for the last (medians of three runs on 2026-10-13, at load averages
of 8.9 before and 8.3 after).  The four matchers it refuses are
those of [`printing.md`][printing-checks], whose `n ≤ m` now unfolds to
`LE.le₁ instLENat n m` and needs [#20]'s transparent `instLENat`, with
which, in a copy of the `nat-gcd-self` scaffold, all four check.

The other two rows were printed from every inductive type declared under
`Init`, and from the nested or mutual ones under `Init`, `Std` and `Lean` in
`import Lean`; `scaffold_check.py --types-only` checks only the data types and
records and what they mention, since Agda's time grows faster than a module:
the 4.1 MB scaffold of `Init`'s types took 4 min 48 s to scope-check at a load
average near 16, and its `--types-only` part of 335 KB took 21 s for all five
runs at 4.5, after printing in 3.6 s.  Every refusal needs a definition to
unfold, the work of [#20], and one a recursor as well: `Float.Model` needs
`Float.Model.Format.numBits binary64` to compute to 64, which takes `numBits`,
`binary64` and the addition of `Nat`, whose recursor is [#19]'s (and
`Float32.Model` the same for 32); `Lean.Quote` needs `SyntaxNodeKind := Name`;
`Std.Packages.LinearOrderOfLEArgs` applies a `DecidableLE`, which is
`DecidableRel LE.le` and not a type abbreviation by the scaffold's syntactic
rule; and in `Lean`, `Std.DHashMap.Raw.WF` needs `Raw₀`,
`Lean.MetavarContext` needs `LMVarId := LevelMVarId`, and five types need
`SyntaxNodeKinds := List SyntaxNodeKind`.  None of the seven unchecked types
of `Init` is recursive.  Of Lean's 72 nested or mutual types, 62 check, among
them all ten mutual blocks; the other ten, `Lean.MessageData` and
`Lean.Elab.InfoTree` among them, sit behind those refusals.

The commands, from `translator/` in the dev shell, are as follows:

```sh
lake env lean scripts/InductiveTypes.lean > init.txt
lake exe lean2agda --out out Init -- $(cat init.txt)
python3 ../scripts/python/scaffold_check.py --messages --types-only out/U/Init/WF.agda
```

## Verification

`make test-translator` runs the following:

+  `tests/Inductives.lean`: which types become records and how many
   parameters each keeps, for `Eq`, `HEq`, `Nat.le`, `Acc`, `List`,
   `Prod`, `LawfulBEq`, `Relation.TransGen`, `Lean.Syntax`,
   `CheckGoalType` and the fixtures; the declarations of `Eq`, `HEq`,
   `Acc`, `List`, `Nat.le`, `Nat`, `Prod`, `PUnit`, `LawfulBEq` and
   `Lean.Syntax` and of the fixtures (a `Vec`-style family, a promoted
   parameter, a structure with an instance parameter and implicit,
   instance and dependent fields, a unit-like structure, two recursive
   types, a mutual block, an unsafe type), each as written above; the
   projections, from records and through recursors; which constants are
   records' projection functions; and the sharing rule, with the
   auxiliary ordered before its block;
+  the fixture's scaffold, against its golden file and listing, and the
   scaffold of `Init.Core`'s inductive types, against its listing.

Each new check failed on the code before this change, run in a scratch
copy of it: the seven new or changed checks of `test_scaffold_check.py`
(the module cannot import `types_only` there, and without that check the
other six fail on their own: records and mutual blocks parsed as
definitions, a projection `R.f₀` that named nothing, and a `RecursionError`
on a module of 5,000 declarations);
the projection case of `tests/Printing.lean`; the fixture's scaffold,
which refused `Packed.fits` and both projections of `Rose`; the sharing
rule, which made two auxiliaries of `Wide.node` where it now makes one;
and the scaffold of `Init.Core`'s inductive types, in which `Nat` was the
one data type.

## Hand-off to the emitters

+  [#19]: every constructor is an Agda constructor, of a data type or a
   record, and can be matched on: a record with eta by Agda's translation
   of record patterns into projections, one without eta through its
   `pattern` declaration (probe `I06RecursiveRecord`).  The recursors,
   the nested types' `rec_N` among them, are postulates of their printed
   types, and so are `casesOn`, `below` and `brecOn`.  A projection from
   a type with one constructor that is not a record prints through its
   recursor and computes when the recursor does.
+  [#20]: the projection functions of records are transparent already;
   the other definitions are postulates, and the refusals above are
   theirs: `instLENat` for the four matchers, and the definitions the
   positivity runs name.
+  The scaffold still holds the closure in one module, and [#22] splits
   it; Agda's time on the whole of `Init`'s types is one more reason.

[#17]: https://github.com/formalverification/lean2agda/issues/17
[#18]: https://github.com/formalverification/lean2agda/issues/18
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#20]: https://github.com/formalverification/lean2agda/issues/20
[#22]: https://github.com/formalverification/lean2agda/issues/22
[printing]: printing.md
[printing-checks]: printing.md#what-agda-checks
[probes]: probes/
[catalog-eta]: ../foundations/gap-catalog.md#structure-eta
