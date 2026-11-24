<!-- File: docs/translator/levels.md -->

# Universe levels: an instance per pattern of zero parameters

Lean's `Sort u` is `Prop` when `u` is zero, and `imax u v` is zero when `v`
is, so a universe-polymorphic constant is a different thing at each pattern
of zero and nonzero level parameters: `Eq.{u} {α : Sort u}` relates proofs
at zero and elements of a type elsewhere.  Agda has no such case analysis,
neither in `Set ℓ` nor in its levels, which have no `imax`.  The
specialization of issue [#28] (`M3-3`) therefore emits, in place of each
constant, its **instances**: the constant with each level parameter that
matters fixed as zero or as nonzero.  Only the instances something uses are
made, and inside an instance every `imax` is gone.

This note gives the rules, in the code as it stands
(`translator/Lean2Agda/Core/Levels.lean` and `Specialize.lean`), and the
measurements.  The pass is behind `--specialize`, off by default: profile
U prints no levels and every sort as `Set`, so its default output does not
need the instances, and with the switch off the translator's output is
byte for byte what it was.  What the instances are for comes later: the
level annotations of [#29], and the encoding of Lean's `Prop` by Agda's
([#27]), which the measurement below shows cannot be printed without them.

## Terms

+  A level **parameter** of a constant is one of the names in its
   `levelParams`; a parameter is **split** when the constant's instances
   fix it, and a constant's **mask** says which of its parameters are.
+  A **pattern** fixes each split parameter as zero or as nonzero; its
   **letters** are one per split parameter, in the constant's order, `z`
   for zero and `n` for nonzero.
+  An **instance** is a constant at a pattern.  A constant with no split
   parameter has one instance, at the empty pattern, which is the constant
   itself.
+  The **key** of an instance is the name the closure holds it under: the
   constant's name followed by one more component, `#` and the letters.
   The empty pattern's key is the constant's name.
+  A level's **normal form** is the maximum of a constant and of
   parameters, each under a number of successors.  A level has one once
   every `imax` in it is decided.  A parameter under no successor in a
   normal form is **bare**.

## The normal form of a level

`Levels.lean` reads a level under an assignment of its parameters
(`normalLevelWith`) into a `NormalLevel`: a natural number and one atom
`(p, k)` per parameter, standing for `max c (p₁ + k₁) … (pₙ + kₙ)`.  The
rules are as follows:

+  `0` is the constant `0`, `ℓ + 1` adds one to the constant and to every
   offset, and `max` joins: the larger constant, and each parameter at its
   larger offset.
+  `imax a b` is zero when the normal form of `b` is zero, whatever `a` is
   (so an undecided `imax` inside `a` does not matter), and `max a b` when
   the normal form of `b` is never zero, that is, when its constant or one
   of its offsets is positive.  Otherwise `b` is the maximum of bare
   parameters, zero for some values of them and not for others, and the
   level has no normal form: the answer names those parameters.
+  The canonical form keeps the atoms in the order of their names and
   drops the constant when some offset reaches it, since `p + k` is at
   least `k`.  Two levels without `imax` are equal at every value of their
   parameters exactly when their canonical forms are equal.
+  A normal form is **zero** when it has no atom and its constant is zero,
   and **never zero** when its constant or an offset is positive.  It has a
   **predecessor** (`pred?`), a level one below it at every value of its
   parameters, exactly when it is not zero and has no bare parameter:
   `max 1 u` has none, since it is one above `0` at `u = 0` and one above
   `u - 1` elsewhere.

Lean's own functions do part of this, which the probe
[`L04NonzeroParameter.lean`][probes] records at the pin: `Level.normalize`
turns `imax u (v+1)` into `max u (v+1)` and `imax u 0` into `0`, and
leaves `imax u v` as it is; substituting `0` for `u` and `v + 1` for `v`
gives `v + 1` at once, since the substitution simplifies as it goes.  The
normal form here is the translator's own so that it can say which
parameters an undecided `imax` waits for, and so that what an instance
holds does not depend on which simplifications Lean applies.

## Which parameters are split

`splitAnalysis` computes each constant's mask from the levels its
expressions hold (`levelSites`: its type, its value, and a recursor's
rules).  A constant must fix a parameter in three cases, as follows:

+  **A sort**.  `Sort ℓ` must be `Prop` or a `Type` in every instance, so
   the parameters that decide whether `ℓ` is zero are split.  `Eq`'s
   `α : Sort u_1` splits its parameter; `ULift.{r, s} : Type s → Type (max
   s r)` splits none, since `Type s` is `Sort (s + 1)`.
+  **An `imax`**.  Every level of the constant, in a sort or passed to
   another constant, must have a normal form, so the parameters an
   undecided `imax` waits for are split.
+  **A use**.  A reference `C.{ℓ₁, …}` must select one instance of `C`, so
   for each split parameter of `C` the parameters that decide whether its
   argument is zero are split.  The fixture's `passes : PUnit.{v} →
   PUnit.{v}` is split on `v` for this reason alone; `passesSucc`, which
   passes `v + 1`, is not.  A projection `Expr.proj S i t` carries no
   levels and uses `S` at those of the type of `t`, which
   `projectionTypes` reads with the kernel's inference, entering binders
   as the printer does.

Those cases are about the levels a constant writes.  The sorts the kernel
infers, which the printer reads when it writes a projection through a
recursor and which [#29] will read, are decided with them: an inferred
sort is built from the written ones by successor, by `imax` at a Pi type,
whose being zero is its codomain's, and by the type of a constant at the
levels it is used at, which the third case decides wherever the first
decided the constant's own.  That is an argument, not a test; what is
tested is every written level, and every level inferred at a projection,
over `Init`.

The masks are the least ones closed under those cases.  The closure
orders its groups with dependencies first, so each group is settled
before its users, and a group's own constants are revisited until nothing
changes; a round that changes a mask splits one more parameter, so the
rounds are bounded by the group's parameters, and a group that does not
settle within them is an error.  A block has one mask: the types and
constructors of an inductive declaration share theirs, since one Agda
declaration holds them, and so do the recursors of a block, which are one
`mutual` definition.  A recursor's mask is its types' with the motive's
parameter added (`Eq.rec.{u, u_1}`: both).

Two rules decide what "decides" means, and `--stats` counts both:

+  **zeroness** splits a parameter only when whether a level is zero
   depends on it: the bare parameters of a normal form that is neither
   zero nor never zero.
+  **predecessor**, the one instances are emitted by
   (`defaultSplitRule`), also splits every bare parameter of a level that
   is never zero, in a sort and in an argument of a split parameter.
   `wide (α : Sort (max 1 u))` is split under this rule only.  With it
   every sort of an instance is `Prop` or `Sort (ℓ + 1)` for a level `ℓ`
   the instance can write, which is Agda's `Set ℓ`, and every level passed
   to a parameter fixed as nonzero is some `ℓ + 1`, so that [#29] can give
   the instance a `Level` binder per parameter and pass `ℓ` without a
   further split.

The predecessor rule costs little: 42 more instances than zeroness in
`Init`'s 79,955, and 24 in `Init.Core`'s closure (the tables below).

## What a nonzero parameter is

In an instance a parameter fixed at zero is replaced by `0`, and one fixed
as nonzero by `u + 1`, where `u` keeps its name and now stands for the
level one below (`assignment`).  A parameter that is not split stays
itself.  The instance keeps the parameters not fixed at zero.

The alternative, keeping `u` with the assumption that it is at least one
and rewriting each `imax a u` to `max a u` by it, gives terms that Lean's
kernel refuses, since the kernel does not have the assumption: a function
into `Sort u` has a type in `Sort (imax 1 u)`, which is not `Sort (max 1
u)` at `u = 0` (probe `L04NonzeroParameter`: the kernel accepts the
constant, refuses the rewritten one, and accepts the two instances written
with `u + 1` and with `0`).  The translator calls the kernel on instance
terms, to type the subterms the sharing pass names and to read an
application's visibilities, so an instance has to be something the kernel
accepts.  Written with `u + 1`, an instance is an instantiation of the
constant, which the kernel accepts as it accepts any use of it, and the
substitution itself decides every `imax` whose second argument the
pattern fixes.

Both predecessors keep a nonzero parameter as the variable itself:
lyphyser's tool raises the constant term of each maximum by what it knows
of the pattern, and rocq-lean-import records a constraint that the
universe is above `Set` ([`related-work.md`][related-work], the two
sections).  Neither calls Lean's kernel on its instances.

## Instances are made from uses

`instanceTable` starts from every pattern of each root and follows the
uses inside each instance it makes (`instanceUses`), so an instance exists
only when a root is one or something made uses it.  A use is one of the
following:

+  a constant the instance's expressions name, at the pattern the level
   arguments select there: `z` where the argument's normal form is zero,
   `n` where it is never zero, and nothing else can occur, by the
   analysis;
+  a type projected from, at the levels of the term projected from; and,
   when that type is not an Agda record, its recursor, through which the
   printer writes the projection, at both patterns of the motive's level,
   which is the level of the field's type and is not read here (the one
   place where an instance can be made without a use, one pattern of one
   recursor a projection);
+  the companions an instance is printed with, at its own pattern: an
   inductive type's block and constructors (a constructor names its type,
   and a recursor its types and their constructors, in its own type, so
   those are uses of the first kind); `Quot.mk` for an instance of
   `Quot.lift`, whose computation rule names it; and for an instance of
   `Quot.ind` the instance of `Eq` at zero, the relation of its rule.

Two things the closure of constants follows are not followed here: an
inductive type no longer brings its recursors, and a definition no longer
brings the other definitions of its mutual declaration.  Each comes when
it is used.  One thing is followed too far: the kernel types no term of
an `unsafe` declaration, so the levels of what such a declaration
projects from are not read, and its instances use every pattern of those
types.  The scaffold refuses an `unsafe` declaration and whatever depends
on it, instance by instance, and `refusals.txt` names an instance by its
constant and its letters (`sorryAx#z`).

`specializeClosure` then writes each instance as a declaration
(`instanceInfo`): the constant's type, value and rules at the assignment
of its pattern, every level in normal form, under the instance's key, with
its dependencies the keys of what it uses.  The names inside the
expressions stay Lean's, with their level arguments, so the declaration is
not a constant of Lean's environment, and the kernel reads it as an
instantiation of one.  A constant without split parameters is written the
same way, its levels normalized.  An instance in which an `imax` survives
is an error, as is a level argument that selects no instance.

## Names

An instance's identifier is its constant's followed by `#` and the
letters: `Eq#z`, `Eq#n`, `Eq:rec#zn` (the motive's level first, as in the
recursor's parameters).  `instanceIdent` computes it from the key, and is
`agdaIdent` on a name without a pattern.  The scheme has the properties
[`naming.md`][naming] asks of an identifier, as follows:

+  **No Lean name's encoding is an instance's identifier**.  `agdaIdent`
   escapes `#` (as `~x23~`), so its output never holds one, and every
   instance's identifier does.  Agda reads `#` as a name character (probe
   `L01InstanceNames`: after a module path, in a pattern, before the `-β`
   of a computation rule, and inside a pragma).
+  **Two instances have one identifier only when they are the same**.  The
   constant's identifier is injective, and the letters follow the one `#`.
+  **The identifier does not depend on what else a run selects**.  A
   constant's mask is a function of the constant and of what it depends
   on, and the letters of the mask and the pattern.
+  **A key is never a constant's name**.  The specialization refuses a
   closure holding a Lean constant one of whose name components is `#`
   followed only by `z` and `n` (`hasPatternComponent`).  No constant of
   `Init` has one.

An auxiliary definition of the sharing pass, made from a subterm of an
instance, is named after the instance's key, and its identifier keeps the
pattern where the key has it: `A:b#n:~ushare:~n1`.

The sidecars of a closure of instances are naming version 2
([`naming.md`][naming], "Reverse maps"): the component of a key that holds
the pattern is tagged `levels` and carries the letters, after the
constant's own components.

```json
{"agda":"Eq:rec#zn","lean":[{"str":"Eq"},{"str":"rec"},{"levels":"zn"}]}
```

## What the scaffold prints

With `--specialize` the sharing pass, the sidecars and the scaffold work
on the closure of instances; the listing (`closure.txt`) stays the
closure's as loaded.  The differences from the unspecialized scaffold are
as follows:

+  **Each instance is a declaration of its own**, under its identifier,
   in its constant's module, and a block's types, constructors and
   recursors carry the block's pattern.
+  **Each reference names its instance**.  The printer asks
   `Splits.resolve` for the key the reference's levels select, also for
   the record a field is projected from and for the constructor a
   recursor's clause matches, whose levels are the major premise's.
+  **Each instance of `Eq` is a rewrite relation**.  Agda takes several
   `BUILTIN REWRITE` relations, one pragma each, and a rule over either
   fires (probe `L02RewriteRelations`).
+  **Each instance of `Quot.lift` and of `Quot.ind` has the rule of its
   own levels**, named after it (`Quot:lift#zn-β`), stated over the
   instances of `Quot.mk` and `Eq` those levels select: `Quot.lift`'s over
   the instance of `Eq` at its result's level, `Quot.ind`'s over the
   instance at zero.
+  **The operation table's rewrite rules name `Eq` at `Nat`'s level**,
   `Eq#n`, being equations between numbers.
+  **A projection written through a recursor passes the motive's real
   level**.  Without instances the level is not printed, and the printer
   passes zero; with them it selects the recursor's instance, so the
   printer takes the level the kernel infers for the field's type.
+  **Sharing is per instance**: an auxiliary definition belongs to the
   instance it was cut from.  Normal forms make more subterms equal than
   Lean's own level syntax does, so an instance can share where its
   constant did not.

Under profile U an instance otherwise prints as its constant does, since
no level and no sort but `Set` is printed.  What makes the instances
visible to Agda is `--prop`, a measurement and never a deliverable: it
prints a sort whose level is zero as `Prop` and states `--prop` in every
module.  Agda accepts a `Prop`-valued rewrite relation, and its rules
fire (probe `L03PropRewriteRelation`).

## The counts

`--stats` with `--specialize` appends the specialization's counts under
each rule, the emitted one first.  For the closure of `Nat.gcd_self`, the
closure of `Init.Core`'s declarations, and every constant of `Init` (631
modules), at the pin:

| | `Nat.gcd_self` | `Init.Core` | `Init` |
| --- | ---: | ---: | ---: |
| constants | 334 | 2,128 | 65,994 |
| with level parameters | 137 | 1,484 | 29,048 |
| level parameters | 202 | 2,525 | 43,639 |
| split parameters | 137 | 1,296 | 10,278 |
| constants with a split parameter | 105 | 954 | 8,905 |
| **instances** | 342 | 3,540 | 79,997 |
| possible instances, split parameters | 531 | 4,118 | 79,997 |
| possible instances, all parameters | 671 | 6,736 | 137,010 |
| entries, as rocq-lean-import counts them | 278 | 1,793 | 64,531 |
| possible instances, entries | 481 | 5,256 | 131,759 |
| split parameters, zeroness rule | 137 | 1,285 | 10,263 |
| instances, zeroness rule | 342 | 3,516 | 79,955 |

+  **Instances** are those made from the roots: every pattern of each
   root and what those use.  When the roots are every constant, as for
   `Init`, every pattern of every constant is made, which is the next
   row.
+  **Possible instances, split parameters** is one per pattern of each
   constant's split parameters; **all parameters**, one per pattern of
   all its parameters.
+  **Entries** counts as rocq-lean-import does (`finish` in its
   `src/lean.ml` at `2d28bbe`): an axiom, a definition, a theorem, an
   opaque constant and an inductive type are one entry each, a type's
   constructors and recursors are not counted, the quotient's four
   constants are one entry of two instances, and an entry of `n`
   universe parameters has `2^n` possible instances.  Its README gives
   24,081 possible instances for the 10,245 entries of Lean 3's standard
   library, 2.35 an entry; `Init` at the pin has 131,759 for 64,531,
   2.04 an entry.  Splitting only the parameters that matter makes 79,997
   declarations of `Init`'s 65,994 constants, 1.21 a constant, against
   2.08 a constant with every parameter split.
+  The run over `Init` takes 34 s, about 24 s of it the kernel's
   inference at projections; the closure of `Init.Core` takes 1.4 s, the
   same as without the switch.
+  Beyond the issue's scope, as a test that the pass gets through a
   larger library: over the 2,322 modules of `Init`, `Std` and `Lean`
   that `import Lean` brings in (206,647 constants, 146,831 level
   parameters) it splits 44,589 parameters and makes 257,366 instances,
   1.25 a constant against 2.10 with every parameter split, in 582 s on a
   loaded machine, with no level it could not decide.

The commands, from `translator/` inside the dev shell, are as follows:

```sh
lake exe lean2agda --specialize --stats Init.Data.Nat.Gcd -- Nat.gcd_self
lake exe lean2agda --specialize --stats Init.Core
lake exe lean2agda --specialize --stats $(lake env lean scripts/ModuleList.lean)
lake exe lean2agda --specialize --stats \
  $(MODULE_IMPORTS=Lean MODULE_PREFIXES="Init Std Lean" lake env lean scripts/ModuleList.lean)
```

## The measurements

On 2026-10-12, printing `Prop` for every sort at level zero without the
specialization raised Agda's refusals on two scaffolds from 6 to 17 and
from 7 to 20, every new one `UnequalSorts Prop != Set`
([`printing.md`][printing], "Sorts under profile U").  The scaffolds have
since gained recursors, the quotient's rules, modules and the operation
table, so the numbers are other ones and the class is the same.  Measured
on 2026-11-24 with `scripts/python/agda_check.py --refusals` (8G heap, four
Agda processes), each row a tree printed with the options named:

| Scaffold | Options | Declarations checked | Refused |
| --- | --- | --- | --- |
| `nat-gcd-self` | none (the golden) | 329 of 329 | 6 values, `UnequalTerms` |
| | `--prop` | 253 of 329 | 8 types and 57 values `UnequalSorts`, 2 values `SplitInProp` |
| | `--specialize` | 336 of 336 | 6 values, `UnequalTerms` |
| | `--specialize --prop` | 336 of 336 | 3 values, `UnequalTerms` |
| `nat-gcd-succ` | none (the golden) | 261 of 261 | 2 values, `UnequalTerms` |
| | `--prop` | 203 of 261 | 8 types and 35 values `UnequalSorts`, 2 values `SplitInProp` |
| | `--specialize` | 269 of 269 | 2 values, `UnequalTerms` |
| | `--specialize --prop` | 269 of 269 | 1 value, `UnequalTerms` |

+  **The control reproduces the class**.  Without the specialization a
   constant printed with `Set` is used at `Prop`, and Agda answers `Prop !=
   Set` for 65 and 43 declarations; the two `SplitInProp` are `Eq.rec` and
   `HEq.rec`, each one definition that must eliminate into `Set`.
+  **With the specialization the class is gone**, and every declaration
   checks or is a refusal of the unspecialized scaffold.  Under
   `--specialize` alone the refused values are exactly the instances of
   the golden's refused values (`dif_pos#n`, `dif_neg#n`, `eq_of_heq#z`
   and the three fuel lemmas of the operation table).
+  **Under `--specialize --prop` fewer are refused than under profile
   U**: `dif_pos`, `dif_neg` and `eq_of_heq` hold by proof irrelevance,
   which Agda's `Prop` has and profile U's `Set` gives up, and no theorem
   needs unfolding (0 unfoldings against 9, and 12 s against 85 s for the
   loop).  The values left are the fuel lemmas, [#31]'s documented cost.
+  **No large elimination is reached**.  Neither closure uses an instance
   of `Eq.rec`, `HEq.rec` or `Acc.rec` with a motive in a type over a
   proposition, so none is made, and `SplitInProp` does not occur.  The
   fixture's tree, which makes every pattern of its own constants, has
   one: `Eq:rec#nn`.

The fixture `TranslatorTests.Input.Levels` shows the same at the scale of
a test, which `tests/run.sh` pins: its tree of instances checks all 509
declarations (its two refusals are `eq_of_heq`'s instances, K-like,
[#26]'s); under `--specialize --prop` what is refused is `Eq:rec#nn`
(`SplitInProp`), `eq_of_heq#n`, which needs it, and one theorem that holds
only by the computation rule of a quotient of a proposition (below); and
under `--prop` alone 32 declarations are `UnequalSorts`.

### `Init.Core`'s closure

The closure of every declaration of `Init.Core`, as a tree, with the
options named (`lake exe lean2agda [options] --out DIR Init.Core`, then
the loop):

| Options | Declarations checked | Types and records | Recursors | Refused | Loop | Final tree, fresh |
| --- | --- | --- | --- | --- | --- | --- |
| none | 1,968 of 1,972 | 144 of 144 | 146 of 146 | 1 type, 21 values; 3 behind the type | 37 runs, 1,194 s | 24 s, 1,372 MiB |
| `--specialize` | 3,307 of 3,327 | 199 of 199 | 277 of 277 | 8 types, 30 values; 12 behind the types | 63 runs, 3,237 s | 51 s, 2,584 MiB |
| `--specialize --prop` | 3,200 of 3,327 | 195 of 199 | 271 of 277 | 3 types, 51 values; 124 behind the types | 186 runs in 3 passes, 5,360 s | 49 s, 2,035 MiB |

+  **Each refusal of an instance is a refusal of its constant**.  The 38
   refused instances are instances of the 22 declarations the
   unspecialized tree refuses, and each of those 22 has a refused
   instance; nothing else is refused.  The one refused type,
   `apply_eqRec`, is refused at each of its eight patterns, and the three
   declarations behind it at their four.  The unspecialized row is the
   figure of [#31] and [#23] again (1,968 of 1,972; 1,635 of 1,660
   values).
+  **Every data type, record and recursor of every instance checks**: 199
   blocks of types and 277 recursors, none refused by the termination
   checker.
+  **The times are a loaded machine's**.  Two other sessions were running
   Agda loops (load averages of 13 to 24 for the specialized loop, 7 to
   16 for the other), so the loops' seconds compare with nothing; [#23]
   measured the unspecialized loop at 424 s.  The fresh checks of the
   final trees ran at a load near 4: the specialized tree is 1.7 times
   the text (2.6 MB against 1.5 MB), takes 2.1 times as long and peaks at
   1.9 times the memory.

### What `--prop` leaves for the encoding of `Prop`

Under `--specialize --prop` no refusal of `Init.Core`'s closure is
`UnequalSorts`.  The 54 refusals, each read from Agda's full message for
a member of its group, are of four kinds, as follows:

| Kind | Refused | Agda's error | Whose |
| --- | --- | --- | --- |
| The elimination of `Eq` and `HEq` into a type | `Eq:rec#nn`, `Eq:rec#nz`, `HEq:rec#nn`, `HEq:rec#nz`, and 41 values that need one of them to compute | `SplitInProp` for the four; `UnequalTerms` (22) and `CannotApply` (19) for the values | [#27], [#32] |
| A proposition with a field that is not a proof, emitted as a record | `Exists#n`, `Nonempty#n`, `ByteArray.IsValidUTF8`; 124 declarations behind them | `ConstructorDoesNotFitInData` | [#27] |
| The computation rule of a quotient of a proposition | 5 values | `UnequalTerms` | [#27], [#30] |
| A fuel lemma of the operation table | `Nat.modCoreGo_lt` | `UnequalTerms` | [#31] |

+  **The large elimination is one recursor in two instances a relation**:
   the instances of `Eq.rec` and `HEq.rec` whose motive is in a type, over
   a type and over a proposition.  Agda refuses to match on `Eq:refl#n` in
   a `Prop` into `Set`, the loop makes the recursor a postulate, and what
   needs it to compute is refused in turn: 16 values whose message names
   it (`cast_eq`, `eqRec_heq`, `PSigma.eta`, `apply_eqRec` among them) and
   25 `noConfusion` values, whose `noConfusionType` is an `Eq.rec` into
   `PULift`.  The instances with a motive in `Prop` (`Eq:rec#zn`,
   `Eq:rec#zz`) check.  `And.rec`, `True.rec` and `PUnit.rec` at a motive
   in a type check too, their types being records whose fields are proofs,
   and `False.rec` by its absurd pattern.
+  **Three propositions are records with a field in `Set`**.  A record in
   `Prop` must have its fields in `Prop`; the same declaration as `data`
   is accepted.  Under profile U the three check, so the rule that decides
   record or `data` ([`inductives.md`][inductives]) needs the sort of the
   type and of its fields once `Prop` is printed.  They cost the most:
   everything that mentions `Exists` at a type is behind them.
+  **A quotient of a proposition does not compute**.  `Quot.{0} r` is a
   proposition, so `Quot.mk r a` is a proof, and Agda drops a rewrite rule
   whose left-hand side binds `a` only there (probe
   `L05PropQuotientRule`).  `Quot.liftBeta#zn`, `Quotient.exact#z` and
   three more hold in Lean by that rule.
+  **What `Prop` buys shows too**: of the 30 values the specialized tree
   refuses under profile U, 27 are not refused here, `proof_irrel`,
   `dif_pos`, `dif_neg`, `Subtype.eq`, `Fin.eq_of_val_eq` and `Char.ext`
   among them, which hold by proof irrelevance (some of the 27 are behind
   a refused type instead and were not reached); and none of the 14
   unfoldings of a theorem helped, a proof in `Prop` never needing one.

## What the instances hand on

+  **To [#29]**: an instance's parameters are those not fixed at zero,
   each split one standing for the level one below Lean's; every level is
   in normal form, a maximum of a constant and of parameters under
   successors; every sort is `Sort 0` or `Sort (ℓ + 1)` with `ℓ` written
   by `pred?`, which is Agda's `Set ℓ`; and every level passed to a
   parameter fixed as nonzero has a predecessor to pass in its place.  The
   shift by one, the `Level` binders and the constraints are [#29]'s.
+  **To [#27]**: with the instances, `Prop` can be printed; what Agda
   then refuses is the list above.

Not done here: deciding the encoding of `Prop`, moving `Eq`, `HEq` or
`Acc` into `Set`, or any part of large elimination ([#27], [#32]); `Level`
binders and level constraints ([#29]).

## Tests and probes

+  `translator/tests/Levels.lean` (`lake test -- levels`): the normal
   form; the masks of core constants and of the fixture's under both
   rules; the instance a use selects, and that `twice` at zero is not made
   for a closure that uses it only at a type; the four instances of an
   `imax`; identifiers, distinct over every constant of `Init` at three
   patterns, and the sidecars of version 2; what the scaffold prints for
   the fixture, with and without the switches; a projection through its
   recursor's instance; and, over the closure of `Init.Core`'s
   declarations, that no instance holds an `imax`, that every level is in
   normal form with a predecessor where the predecessor rule promises
   one, that every reference selects an instance that was made, and that
   Lean's kernel accepts each of the 3,540 instances (a definition, a
   theorem, an axiom and an opaque constant added as a declaration of
   their own; the type and rules of the others checked).
+  `translator/tests/run.sh`: the golden tree `levels`, the fixture's
   closure of instances with its listings; the listings of the same under
   `--specialize --prop` and under `--prop`; and the counts of `Init.Core`
   against `tests/expected/levels-init-core.txt`.
+  [`probes/`][probes], run with Agda 2.8.0 and Lean 4.33.1 on 2026-11-24:

| Probe | Options | Claim | Outcome |
| --- | --- | --- | --- |
| `L01InstanceNames.agda` | `--type-in-type --rewriting` | `#` in identifiers: declared, qualified, matched, before `-β`, in pragmas | accepted |
| `L02RewriteRelations.agda` | `--type-in-type --rewriting` | two `BUILTIN REWRITE` relations, a rule over each fires | accepted |
| `L03PropRewriteRelation.agda` | `--prop --type-in-type --rewriting` | `Prop`-valued rewrite relations, a rule fires | accepted |
| `L04NonzeroParameter.lean` | core Lean | `Level.normalize` and substitution on `imax`; the kernel on the two forms of a nonzero parameter | as expected |
| `L05PropQuotientRule.agda` | `--prop --type-in-type --rewriting` | the computation rule of `Quot.lift` over a quotient of a proposition | rejected: `RewriteVariablesNotBoundByLHS` at the pragma, then `UnequalTerms` |

[#23]: https://github.com/formalverification/lean2agda/issues/23
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#28]: https://github.com/formalverification/lean2agda/issues/28
[#29]: https://github.com/formalverification/lean2agda/issues/29
[#30]: https://github.com/formalverification/lean2agda/issues/30
[#31]: https://github.com/formalverification/lean2agda/issues/31
[#32]: https://github.com/formalverification/lean2agda/issues/32

[inductives]: inductives.md
[naming]: naming.md
[printing]: printing.md
[probes]: probes/
[related-work]: ../related-work.md
