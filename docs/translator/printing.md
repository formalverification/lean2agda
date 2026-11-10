<!-- File: docs/translator/printing.md -->

# Printing expressions

The printer turns a Lean kernel expression into Agda text under profile U
(`--type-in-type --rewriting`, postulates allowed), and the sharing pass
first moves repeated closed subterms into auxiliary definitions, so that
the text stays near the size of the shared term.  Issue [#17] implements
both, in `translator/Lean2Agda/Core/Print.lean` and `Core/Share.lean`, and
a scaffold, `Core/Scaffold.lean`, that tests them with Agda until the
emitter of [#19] exists; [#18] added the inductive types
([`inductives.md`][inductives]), [#20] gave the scaffold its rules for
definitions, theorems, opaque constants and axioms, and the fallback that
unfolds a theorem when a dependent needs it, and [#21] gave the quotient
primitives the kernel's computation rules as rewrite rules.  The
measurements behind the choices below are in the dated reports
[`printing-blowup`][report], [`opaque-theorems`][report-opaque] and
[`quotient-rules`][report-quot].

## Command line

`--out DIR` now also writes the scaffold as a tree of Agda modules
([#22], [`modules.md`][modules]): one module per Lean module of the
closure, each at the path of its names sidecar ([`naming.md`][naming]),
with the library file `U.agda-lib`, a `libraries` file naming it, the
module `U.Everything` importing every module, and `refusals.txt`, one line
per declaration the scaffold refuses (below).  For example, the following
writes `out/U/Init/Prelude.agda`, `out/U/Init/Core.agda` and the others
beside their sidecars, then checks them module by module in dependency
order, listing the refusals of each:

```sh
cd translator
lake exe lean2agda --out out Init.Data.Nat.Gcd -- Nat.gcd_self
python3 ../scripts/python/agda_check.py --refusals --messages --listings listed out
```

`--split BYTES` sets the size past which a module is cut into parts,
1,000,000 bytes of printed Agda by default; `--split 0` never cuts.

`--share N` sets the sharing threshold, 32 by default; `--share 0` turns
the pass off.  The listing, `closure.txt` and standard output are as
before.  The sidecars are those of the shared closure, so that they map the
auxiliary definitions' identifiers back to their structured names too.
`agda_check.py --refusals --without-rewrite` checks the tree with its
`REWRITE` pragmas removed (Quotients, below), as `scaffold_check.py
--without-rewrite` does for one module.

## The printer

The printer works in two pure stages.  `printExpr` turns an `Expr` into a
small Agda syntax tree, `AgdaTerm`, deciding names, visibilities and
projections; `AgdaTerm.render` lays the tree out by a precedence table.
The entry points are `Printer.type`, `Printer.clause` and
`Printer.telescope`, named in the hand-off below.

### Applications and visibility

A kernel application `f a₁ … aₙ` does not record whether each argument is
explicit, implicit or an instance, and Agda needs to know, so the printer
reads it from the type of the head.  When that type is not syntactically a
Pi type (an instance of `DecidableEq α` applied to two arguments), the
kernel's own `whnf` exposes one; when the head is neither a constant nor a
bound variable, the kernel's `check` infers its type.  Both are pure
functions of the environment (`Lean.Kernel.whnf`, `Lean.Kernel.check`).
To give them closed terms, the printer replaces each bound variable by a
free variable of its own, entered in a local context with its binder's
type.  An instance argument is always passed, in instance braces
`⦃ a ⦄`; Agda never searches for one.

### Binders

Lean's binder information maps to Agda's visibility as follows:

| Lean | Agda binder | Agda argument |
| --- | --- | --- |
| `default` | `(x : A)` | `a` |
| `implicit` | `{x : A}` | `{a}` |
| `strictImplicit` | `{x : A}` | `{a}` |
| `instImplicit` | `⦃ x : A ⦄` | `⦃ a ⦄` |

Agda has no strict implicit binders; an implicit one is the nearest.  A
Pi type whose body does not use its binder prints without a name:
`A → B`, `{_ : A} → B`, or `⦃ _ : A ⦄ → B`.  A lambda always carries its
binder's type, `λ (x : A) → b`, so that Agda can infer it as the head of
a beta redex.

A binder's name is a readable base followed by the subscript decimal of
its depth, the number of binders around it: `n₀`, `inst₁`, `α₂`.  The base
is the last string component of the Lean name with its macro scopes
erased, keeping ASCII letters, digits and Greek letters other than `λ`;
kernel binder names are often hygienic
(`x._@.Init.Data.List.Basic.1090560813._hygCtx._hyg.13`), and the base is
`x` whenever nothing readable is left.  The rule has three consequences,
as follows:

+  Binders in scope at once have different depths, so their names differ.
+  Every binder name contains a subscript digit, and every constant
   identifier is ASCII ([`naming.md`][naming]), so a binder never shadows a
   constant.
+  No Agda keyword ends in a subscript digit, so `data₂` is a name.  A
   sort name does (`Set₁`, `Setω₂`), so the bases `Set`, `Prop`, `SSet`,
   `Setω`, `Propω` and `SSetω` become `x`.

Lean's own binders test the first and third.  `ByteArray`'s field is
named `data`, and without the subscripts Agda stops on a parse error; in
`nat-gcd-self`'s closure, binders that share a base then shadow each
other, and the type of `HEq.rec` no longer checks.

### Binder repair

Lean accepts a lambda whose binder information differs from the Pi type it
is checked against; Agda refuses one whose visibility differs.  The printer
prints every lambda that Agda checks against a known type with that type's
visibility, exposing the Pi type by `whnf` when needed.  A lambda is
checked against a known type at the top of a definition's value (against
its declared type), as an argument (against the parameter's type), as a
`let` value, and as the body of another such lambda.  A projection function
is the common top-level case: `And.left : {a b : Prop} → a ∧ b → a` has the
value `fun a b self => self.1`.

A definition prints as a clause whose left-hand side takes the value's
leading lambdas as patterns, `And:left {a₀} {b₁} self₂ = …`, because Agda
inserts a definition's leading implicit patterns itself and would then
refuse an implicit lambda on the right.  The counts are in the report: in
every type and value of `nat-gcd-self`'s closure, 29 repairs at the top and
198 below it, which is what the scaffold now prints; when it printed the
types and the root's value only, it made 16, all below the top.  With the
repair turned off, Agda refuses four of that scaffold's types with
`WrongHidingInLambda`, one of which otherwise checks, and both repaired
definitions of the printing fixture.

### The precedence table

A binding form (`λ`, a Pi type, an arrow, `let`) extends as far right as
it can, so it binds loosest; application binds tighter and associates to
the left; atoms (names, `Set`, literals) bind tightest.  Each position asks
for a minimum, and a term below it is parenthesized, as follows:

| Position | Accepts without parentheses |
| --- | --- |
| an application's head | an application or an atom |
| an explicit argument | an atom |
| an implicit or instance argument, inside its braces | anything |
| an arrow's domain | an application or an atom |
| a binder's type, inside its delimiters | anything |
| the right of an arrow, a `λ` body, a `let` body | anything |

One lexical rule overrides the table: `{{` is Agda's ASCII instance brace,
so an implicit argument that is itself an implicit Pi type, the one term
that renders starting with `{`, is spaced inside its braces,
`f { {x : A} → B }`.  `real-sqrt-nonneg`'s scaffold had such an argument
and failed to parse until the rule was added.  `tests/Printing.lean`
checks the table on 28 cases.

### Sorts under profile U

Every sort prints as `Set`, `Prop` and `imax u v` included, and the
scaffold's one option about sorts is `--type-in-type` (its other,
`--rewriting`, is for the quotient's computation rules, below).  lyphyser's
output adds `--prop` and prints `Prop` for `Sort 0`
([`related-work.md`][related]),
but Agda's `Prop` and `Set` are different sorts, and a Lean constant whose
universe parameter is instantiated at zero then receives a `Prop` where its
printed type has `Set`.  Measured on the scaffolds of `nat-gcd-succ` and
`nat-gcd-self`, printing `Prop` for every sort whose level normalizes to
zero, under `--prop --type-in-type`, raises Agda's refusals from 6 to 17
and from 7 to 20, every new one `UnequalSorts Prop != Set`.  The cost of
`Set` everywhere is definitional proof irrelevance, which Agda's `Set`
lacks; the encoding of `Prop` is [#27]'s question, and specializing
constants by which universe parameters are zero is [#28]'s.

### Literals

A natural number literal prints as a decimal, of any size; the scaffold
binds Lean's `Nat` to `BUILTIN NATURAL`.  A string literal prints as an
Agda string, with `"` and `\` escaped and every character outside
printable ASCII written as a decimal escape closed by `\&` (`λ` becomes
`\955\&`), so that the output does not depend on how a reader decodes
Unicode; the scaffold binds Lean's `String` to `BUILTIN STRING`.  None of
the three corpus entries has a string literal; the printing fixture's
`greeting` does.

### Projections

`Expr.proj S i t` from a type `S` that the scaffold declares as a record
prints as Agda's projection of the field, `S.fᵢ {params} t`, its
parameters passed implicitly, or as instance arguments for those `S`
declares as instances, as Agda's projections take them
([`inductives.md`][inductives-projections]).  From a type with one
constructor that is not a record (`String`, a postulate for
`BUILTIN STRING`, or a type whose constructor binds a parameter
explicitly) it prints through the type's recursor, as every projection
did before [#18]: `S.rec {params} {λ self → Tᵢ} (λ f₀ … fₙ₋₁ → fᵢ) t`,
where `Tᵢ` is the field's type with each earlier field replaced by its
projection from `self`, as the kernel types a projection.  That checks
against a postulated recursor for a field whose type does not mention an
earlier field, and needs the recursor to compute ([#19]) for the others.
The printing fixture's dependent field `PrintFixtures.Dependent.value`,
which Agda refused printed through the recursor, checks as a field
projection.

### Other constructors

+  `letE` prints as `let x : A; x = v in b`; Agda's `let` substitutes, so it
   gives Agda's checker no sharing ([gap catalog][catalog-let]).
+  `mdata` is dropped.  lean4export strips it too, but the environment's
   values carry it.
+  `const` prints as `agdaIdent` inside the module that owns the constant,
   and with the owner's module path before it elsewhere
   (`Naming.qualified`, [`modules.md`][modules]).
+  A loose bound variable, a free variable and a metavariable are refused
   with a reason; none occurs in a compiled constant.

## The sharing pass

The pass looks at each declaration's type and value as a graph of distinct
subterms, identified by structural equality that keeps binder names and
binder information (`ExprStructEq`).  It counts how often each subterm
would occur in the printed tree, from the roots down, and shares a subterm
when all of the following hold:

+  it is closed (`hasLooseBVars` is false, a constant-time test);
+  it occurs twice or more in the printed tree, counting a shared subterm's
   contents once, since it is printed once;
+  it has at least the threshold's number of expression nodes, 32 by
   default;
+  it is not a lambda, since a lambda takes its visibility from where it
   occurs and a reference to a definition would lose it.

A shared subterm becomes an auxiliary definition named
`owner._share.k` (`owner:~ushare:~nk` in Agda), numbered in order inside its
owner, so that its name never depends on other declarations.  Its source
module is its owner's, its level parameters are the owner's that occur in
it, and its type is the kernel's, inferred from the subterm as it occurred.
The pass rewrites every occurrence to a reference, orders the closure again
by strongly connected groups so that each auxiliary precedes its users,
and `addAuxiliaries` adds the auxiliaries to the environment through the
kernel, which checks each one.

On the corpus entries the pass changes little, and the report says why:
their terms are not much shared.  Printing every type and value of
`nat-gcd-self`'s closure gives 431,486 bytes without the pass and 417,558
with it, against an export of 684,821 bytes and 10,818 expression records;
the printed tree has 4.4 nodes per distinct subterm overall and 23.5 in the
worst declaration without the pass.  The threshold trades repetition
against auxiliaries, each of which repeats its long name and adds a type:
at 32 the bytes are lowest for `nat-gcd-succ` and 2.2% above the lowest
for `nat-gcd-self`, with 9 and 15 auxiliaries where a threshold of 8 makes
133 and 218.  What Agda refuses does not change with the threshold, and
its checking time stays under a second.  On a term that is shared, the
pass is what keeps the text linear: the fixture `PrintFixtures.doubling`,
`Nat.add` doubled ten times, prints in 19,498 bytes without the pass and
1,288 with it, and the doubling of 2^20 leaves in `tests/Printing.lean`
prints 2^22 − 3 nodes without it and 100 with it.  The pass shares closed
subterms only, within one declaration; open repetition and sharing across
declarations are [#44]'s.

## The scaffold

The scaffold declares a closure's constants under
`{-# OPTIONS --type-in-type --rewriting #-}`, one Agda module per Lean
module ([`modules.md`][modules]); `--rewriting` is in every module's
pragma, since Agda refuses a module that imports one using it without it.
Issues [#18], [#20] and [#21] settled how each kind of declaration is
emitted, as follows:

+  the inductive types, each block of them one declaration: a record for
   each type with one constructor and no indices, a data type for each
   other, `Nat` among them, bound to `BUILTIN NATURAL`
   ([`inductives.md`][inductives]);
+  `String`, a postulate bound to `BUILTIN STRING`, with its constructor
   and recursor;
+  a definition (`defnInfo`) is a transparent definition, its signature
   and its printed clause, since Lean's terms rely on unfolding it; the
   projection functions of records, whose values print as the records'
   field projections, `partial` definitions' `_unsafe_rec` companions and
   the sharing pass's auxiliary definitions are definitions too;
+  a theorem (`thmInfo`) is a definition inside an `opaque` block of its
   own, under the comment `-- theorem`, so that Agda's conversion checking
   never unfolds a proof: Lean's kernel compares proofs by proof
   irrelevance before it unfolds anything ([gap catalog][catalog-irrel]),
   and under profile U, where every sort is `Set`, nothing stops Agda from
   unfolding a proof term while comparing two of them except the block;
+  one of Lean's opaque constants (`opaqueInfo`, which a `partial def`
   also makes, with an inhabitant of its type as the value) is a
   definition inside an `opaque` block, under `-- opaque constant`: the
   value Lean's kernel never unfolds, kept but never unfolded;
+  an axiom is a postulate, and so are the recursors until [#19] emits
   them, and the quotient primitives, `Quot.lift` and `Quot.ind` each
   followed by its computation rule as a rewrite rule (Quotients, below).

Three refinements, as follows:

+  **Instances** are definitions like any other, with no `instance`
   keyword on the Agda side.  The printer passes every instance argument
   explicitly, in instance braces, so Agda never searches for one; an
   `instance` declaration would add a second resolution, Agda's, that
   could pick a different instance from the one Lean's elaborator
   recorded; and Agda never considers an instance whose type has explicit
   arguments, warning `InstanceWithExplicitArg` (a probe on 2026-10-13),
   which many of Lean's have once their classes unfold
   (`instDecidableEqNat : DecidableEq Nat` is `(a b : Nat) → Decidable
   (a = b)`).
+  **Cycles**.  A definition whose printed value refers to itself, or to a
   definition that refers back to it, is postulated under the comment
   `-- cyclic definition, postulated`.  Lean's kernel accepts such a cycle
   only among the `_unsafe_rec` companions of `partial` definitions, whose
   safety is `partial` (`lean-findings.md`, LF-3), and Agda could check
   none of them.
+  **Refusals**.  `sorryAx`, every `unsafe` declaration, and whatever
   depends on one of those are left out of the module, and `refusals.txt`
   names each with its kind and the reason: `sorryAx: a proof left to
   sorry`, `unsafe: exempt from Lean's kernel`, or `depends on X, and
   through it on Y` naming the direct dependency and the root.  Each
   module's header counts those of its own Lean module.  An `unsafe` inductive type is refused
   with its constructors and recursor before `Inductive.lean` sees it, so
   the `NO_POSITIVITY_CHECK` block of [`inductives.md`][inductives]
   reaches a module only through a caller that declares one itself; the
   sharing pass leaves an `unsafe` declaration unshared, since the kernel
   would refuse a safe auxiliary definition made from a subterm of its
   value.  Nothing in the eight committed exports is refused.
   `Init.Prelude`'s closure (2,314 constants) refuses 22: `sorryAx`,
   eleven unsafe definitions, two unsafe opaque constants and the eight
   unsafe compiler axioms, with no dependents, since nothing safe rests on
   them (`lean-findings.md`, LF-2 and LF-3); its 32 `_unsafe_rec`
   companions are postulated as cycles.  The fixture
   `tests/TranslatorTests/Input/Kinds.lean` has one of each kind, and the
   inductive types' fixture has the unsafe type `Bad`.

Inside a module, declarations follow the closure's groups, and inside a
group (an inductive type with its recursor) the printed references decide.
A module sits at the path of its source module's sidecar, so a reverse
lookup of an identifier needs only the sidecar beside the module, or, for
a part of a split module, beside the module it is a part of.

### Quotients

Lean's kernel reduces `Quot.lift f h (Quot.mk r a)` to `f a` and
`Quot.ind mk (Quot.mk r a)` to `mk a` ([gap catalog][catalog-quot]).  A
postulated `Quot.lift` does not compute, so before [#21] Agda refused
`funext`, whose proof relies on the first rule, at
`Quot:lift (λ f₈ → f₈ x₇) (λ x₈ x₉ h₁₀ → h₁₀ x₇) (Quot:mk eqv₅ f₂)`.  The
scaffold keeps `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and the axiom
`Quot.sound` as postulates and states the two rules as Agda rewrite rules,
as follows:

+  every scaffold's options include `--rewriting`, and the block of `Eq`
   declares it the rewrite relation with `{-# BUILTIN REWRITE Eq #-}`, as
   `Nat`'s carries `BUILTIN NATURAL`;
+  after the postulate of `Quot.lift` comes a postulate `Quot:lift-β` of
   `Quot.lift f h (Quot.mk r a) = f a`, under the comment
   `-- computation rule` and followed by `{-# REWRITE Quot:lift-β #-}`, and
   after the postulate of `Quot.ind`, likewise, `Quot:ind-β` of
   `Quot.ind mk (Quot.mk r a) = mk a`; a closure without `Quot` has
   neither;
+  each rule's type is the statement of Lean's `Quot.liftBeta` or
   `Quot.indBeta`, which `tests/Scaffold.lean` checks in the kernel, built
   in `Scaffold.lean` rather than read from the environment, since
   `init_quot` is in `Init.Prelude` and the two theorems are in
   `Init.Core`; the printer prints it, so that its left-hand side applies
   `Quot:lift` and `Quot:mk` with the visibilities every printed
   application of them has,
   `Quot:lift {α₀} {r₁} {β₂} f₃ h₄ (Quot:mk {α₀} r₁ a₅)`;
+  the rules' identifiers end in `-β`, two characters no `agdaIdent`
   produces (it escapes both), so they cannot collide with a Lean
   constant's; they name no Lean constant, so no names sidecar has them.

A probe, run on 2026-10-13 and again on 2026-11-08, settled the two
questions the emission rests on, under Agda 2.8.0, as follows:

+  Agda accepts the emitted `Eq`, a data type with an implicit parameter
   and two indices, as the rewrite relation: the manual asks only that the
   relation take at least two arguments, the last two visible;
+  Agda accepts a rule whose left-hand side applies a postulate,
   `Quot:lift` or `Quot:ind`, to another, `Quot:mk`, and gives no
   `RewriteVariablesBoundInSingleton` warning.

With both rules the golden's `funext` checks, and without them it fails
with the golden's refusal, word for word; a lift into a function type
applied to one more argument, and a lift under a binder whose result is a
function only by eta (the shape of `funext`'s proof), fire as well.
`--safe` refuses `--rewriting` (`[SafeFlagPragma] The --safe mode does not
allow OPTIONS pragma --rewriting`), with `--confluence-check` too, so no
safe profile can state the rules; there the parameter record's
propositional rule and the normalizer's casts take their place ([#30]).

`agda_check.py --refusals --without-rewrite` checks a tree with its
`REWRITE` pragmas removed (`scaffold_check.py --without-rewrite` one
module), the rules left as postulates that never fire: a
declaration that checks with the pragmas and is refused without them is
one a rule fired for, and so one that needs a cast in the safe profiles.
The harness checks the fixture `tests/TranslatorTests/Input/Quotients.lean`
both ways; [`quotient-rules`][report-quot] gives the record for the corpus
scaffolds and `Init.Core`, beside the declarations whose check reduces
`Quot.lift` or `Quot.ind` in Lean's kernel.

### What Agda checks, and the fallback

Agda parsed and scope-checked every single-module scaffold, which is the
first acceptance criterion of [#17] ("prints and re-parses"), for the
three core-Lean corpus entries in `make test-translator` and for all
twelve entries of `corpus/manifest.json` in `make scaffold-corpus` (the
report gives the table).  Agda's time grew faster than the module: 6 s for
0.7 MB, 187 s for 3.0 MB, and 28 minutes for `real-sqrt-nonneg`'s 7.5 MB,
which is one reason for [#22]'s one module per Lean module.  In a tree,
Agda scope-checks a module only once the modules it imports type-check
(`--only-scope-checking` applies to the module named, not to its imports),
so the parse and scope check now happen inside the type-checking loop
below, whose first run of each module reports any such error.
Scope-checking does not see visibility or precedence errors, which still
parse, so the scaffold is type-checked in any case.  Not every declaration
can check: the postulated recursors withhold the iota reductions that
Lean's kernel used.  `scripts/python/scaffold_check.py` type-checks a
scaffold module anyway, running Agda on a scratch copy until the rest
checks, and `scripts/python/agda_check.py --refusals` runs it on each
module of a tree in dependency order ([`modules.md`][modules]).  At each
error it does one of three things, as follows:

+  when the error's message, before the lines saying what Agda was
   checking, names a theorem that is still in its `opaque` block, the
   theorem is re-emitted as a transparent definition, under the comment
   `-- theorem, unfolded for D` naming the declaration that needed it,
   and the listing records `unfolded T for D`: this is [#20]'s fallback,
   driven by Agda's own complaint rather than by hand;
+  otherwise, when Agda refuses a declaration's clause, the declaration
   becomes a postulate of its type, so that what uses it still checks
   (`refused value`);
+  when Agda refuses a declaration's type, the declaration and everything
   that refers to it are dropped (`refused type`, `dropped`).

The listing opens with two counts, the declarations that checked (and the
data types and records among them) and the theorems unfolded, and says of
an unfolding that it was `in vain` when the declaration it was made for
was refused or dropped all the same, which the first later event at or
beyond that declaration decides.  A closure whose every declaration is
refused (`lcProof` as the root) gives a module with a header and nothing
else, which Agda and the checker both accept.  The fallback re-emits the
theorem transparently rather than putting the dependent in an
`opaque unfolding T` block, because the dependent is usually a definition,
which must stay transparent for its own dependents, and a definition inside
an `unfolding` block is opaque; the count is the same either way.  The
harness compares the listing with a golden one.

With every value printed, the golden scaffolds stand as follows
(`values` counts the definitions, theorems and opaque constants printed
with their values; a value is `behind a refused type` when its declaration
was dropped with one; a declaration is a declaration of the Agda module,
a data type or a record with its constructors being one):

| Scaffold | Declarations | Data types and records | Values | Checked | Refused | Behind a refused type | Theorems | Unfolded |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `list-reverse-reverse` | 34 | 6 | 21 | 17 | 4 | 0 | 10 | 0 |
| `nat-gcd-succ` | 254 | 23 | 201 | 142 | 48 | 11 | 65 | 0 |
| `nat-gcd-self` | 322 | 24 | 266 | 183 | 61 | 22 | 103 | 0 |
| printing fixture | 333 | 41 | 248 | 199 | 49 | 0 | 47 | 0 |
| `Fixtures.selected` | 29 | 6 | 17 | 15 | 2 | 0 | 0 | 0 |
| inductives fixture | 77 | 24 | 29 | 27 | 2 | 0 | 1 | 0 |
| `kinds` | 333 | 41 | 246 | 195 | 51 | 0 | 51 | 2, one in vain |
| `quotients` | 18 | 2 | 8 | 8 | 0 | 0 | 5 | 0 |
| `Init.Core`'s inductive types | 539 | 144 | 246 | 197 | 49 | 0 | 48 | 0 |

Every type checks but three: the compiled matcher of
`Nat.zero_lt_of_ne_zero` and, in `nat-gcd-self`, `Nat.modCore.go.eq_1`,
both of which need `n + 1` to be `Nat.succ n`, that is `Nat.add` to
compute through `Nat.rec`.  The four matchers of the `Nat.le` lemmas that
[#18] and [#20] each left to the other check once both are in: `n ≤ m`
unfolds through the record projection `LE.le₁` and the transparent
`instLENat` to `Nat.le n m`.  Every refusal is an `UnequalTerms` in which
a postulate must compute, as follows:

+  a recursor's iota: `Nat.rec` under `Nat.add`, `Nat.ble`, `Nat.beq` and
   the `brecOn` definitions, `Bool.rec` under `decEq`, `Decidable.rec`
   under `ite` and `dite`'s lemmas, `PProd.rec` and `List.rec` under the
   structural-recursion helpers, and `Eq.rec` on `Eq.refl` ([#19]);
+  K-like reduction of `Eq.rec` on `h : α = α` in `eq_of_heq`, which
   under `--type-in-type` does not reduce on a variable and which the
   normalizer of [#26] is to make explicit.

`Quot.lift` in `funext` was a third class until [#21]: with the
computation rules, `funext` checks in both gcd scaffolds, which is the
only change in their listings, and each gains the two rules as
declarations.  `quotients`, the fixture of the rules, checks entirely,
and its listing with `--without-rewrite` refuses its four roots.

No refusal names a theorem: the fallback fired on none of the corpus and
inductive scaffolds, and on `kinds` twice, once for the pair written to
make it fire (`useAlias`, whose argument has type `Q alias` where `Q base`
is expected, which Lean accepts by proof irrelevance and Agda once `alias`
unfolds to `base`; the proposition is an equation, since a pair on `True`
is identified by Agda without any unfolding once [#18] declares `True` as
a record, whose eta rule makes any two of its elements equal, as Lean's
kernel does for a unit-like type) and once in vain, on a `CannotApply`
error whose message mentioned `heq_of_eq` as an argument of the stuck
term.  Lean's kernel compares proofs by proof irrelevance before it unfolds a
theorem, so a term that relies on a theorem's unfolding is rare by
construction; the place to expect one is a recursor on a proof, `Acc.rec`
under well-founded recursion or `Eq.rec` on a proof that must reduce to
`rfl`, once [#19] makes recursors compute.  On `Init.Core`'s closure
(1,963 declarations, 1,660 values), the checker ran Agda 320 times in 63
minutes: 1,344 values check, 312 are refused and 4 stand behind one
refused type; the fallback fired six times, and once it helped:
`Quotient.rec` is refused with `Quotient.sound p != Quot.sound p`, which
Lean accepts by proof irrelevance, and checks once `Quotient.sound`
unfolds to `Quot.sound`.  Eleven of its refusals are two proof variables
of one proposition compared (`property₇ != property₈`), which is [#27]'s
encoding of `Prop` to settle.  The dated report
[`opaque-theorems`][report-opaque] has the tables, the classes, and the
same run with the inductive types still postulates.  With the quotient's
computation rules ([#21]; 1,965 declarations, the two rules among them),
1,351 values check and 305 are refused: the rules fire for `funext`,
`Quot.liftBeta`, `Quot.indBeta`, `Quot.liftIndepPr1`,
`Quotient.lift₂._proof_2`, `Quotient.rel.refl` and `Quotient.exact`, the
seven declarations whose kernel check reduces `Quot.lift` or `Quot.ind`,
and for `Quotient.lift₂._proof_2` the fallback's two unfoldings, in vain
before, now help ([`quotient-rules`][report-quot]).

## Verification

`make test-translator` runs the following; the probes in the pull request
broke each rule in turn and showed which checks fail:

+  `tests/Printing.lean`: the precedence table, string escapes, clause
   patterns, binder names, each `Expr` constructor, both repairs, a
   telescope, qualified names, and the sharing pass's counting on the
   doubling of 2^20 leaves and its auxiliaries (kernel-checked, owned,
   printed in linear size);
+  `tests/Scaffold.lean`: on the fixture
   `tests/TranslatorTests/Input/Quotients.lean`, the two computation
   rules, each well typed and definitionally equal in the kernel to Lean's
   `Quot.liftBeta` or `Quot.indBeta`, their exact printed text, each after
   its primitive, `Quot.mk` and `Eq`, `Eq` declared the rewrite relation,
   and no rule in a closure without `Quot`; on the fixture
   `tests/TranslatorTests/Input/Kinds.lean`, the emission of each kind (a
   definition and an instance transparent, a theorem and an opaque
   constant in `opaque` blocks, a `partial` definition and its postulated
   companion, an axiom and a recursor as postulates, a class as a record),
   the six refusals with their reasons and their absence from the module,
   the header's count, a closure with nothing to refuse, and the sharing
   pass leaving an `unsafe` declaration alone; also the mutual `partial`
   companions of the printing fixture, and a `String` root's builtin;
+  `PrintingLexical.agda`, which `tests/Printing.lean` writes: a binder
   built from every Agda keyword and sort name, which Agda checks;
+  eight scaffolds against golden trees in `tests/expected/scaffolds/`
   ([`modules.md`][modules]), type-checked module by module with
   `agda_check.py --refusals` against golden listings, one per module and
   their sums in `checked.txt`: the three core-Lean corpus entries, the
   printing fixture (`tests/TranslatorTests/Input/Printing.lean`, which
   prints every constructor, every visibility and both repairs),
   `Fixtures.selected`, the inductive types' fixture of
   [`inductives.md`][inductives], `kinds`, whose golden `refusals.txt`
   names the six refused declarations and whose listings show the
   fallback, and `quotients`, whose four roots check, with a second set of
   listings of the same tree checked with `--without-rewrite`, which
   refuses all four; the scaffold of `Init.Core`'s inductive types,
   against its listings alone; and the declarations each scaffold's
   translator refuses, against a golden `refusals.txt` where one exists
   and required to be none otherwise;
+  `scripts/python/tests/test_scaffold_check.py`: the checker's parsing
   of every block shape, the fallback's trigger (only a theorem the message
   proper names, never the refused declaration itself), the transparent
   form, the postulate form, the `in vain` mark, a run in which the
   fake Agda names a theorem, and the removal of `REWRITE` pragmas, which
   leaves a rule a postulate under its label and `BUILTIN REWRITE` in
   place;
+  the scaffold of the printing fixture's whole module, mutual `partial`
   definitions included, which the refusal loop gets through.

`make scaffold-corpus` is the check over all twelve corpus entries; it
needs Mathlib's cache, and no CI job runs it.

## Hand-off to the emitters

The printer exposes the following, all pure:

+  `Printer.type p e` prints a closed type; `Printer.term p e` a closed
   term with no expected type.
+  `Printer.clause p type value` prints a definition's clause, the value's
   leading lambdas as patterns; `Clause.render name` lays it out.
+  `Printer.telescope p type n` prints the first `n` binders of a type as
   a telescope and the rest of it in their scope; `renderTelescope` lays
   the binders out.  `printExpr`, `printAgainst` and `Scope.enter` work at
   the level below, for printing a constructor's type in the scope of its
   type's parameters.
+  `shareClosure env threshold closure` shares a closure, and
   `addAuxiliaries env closure` returns the environment the printer needs
   for it.
+  Each call returns `PrintCounts`: repairs at the top and below,
   projections printed through a recursor, and projections printed as a
   record's field projection.
+  `Inductive.lean`, above the printer, declares a block of inductive
   types (`inductiveDecl`, from `blockMembers`), and
   `InductiveShape.lean`, below it, decides each type's shape
   ([`inductives.md`][inductives]).

It assumes the following of its callers:

+  Every constant an expression mentions is in the printer's environment,
   auxiliary definitions included.
+  The emitted Agda declares each constant under its `agdaIdent`, with the
   visibilities of its Lean type, since the printer passes arguments by
   the head's type.  A record field, a data constructor or a pattern-matching
   definition that changes a constant's visibilities breaks every
   application of it.
+  [#18] printed projections from records as field projections and
   declared every inductive type, `Nat` included; [#20] made definitions
   transparent and theorems opaque, and refuses `sorryAx` and `unsafe`;
   [#19] defines the recursors, which `projectionAsRecursor` still uses
   for the types with one constructor that are not records, and replaces
   the `postulateItem` case of `scaffoldItem` in `Core/Scaffold.lean` that
   recursors still reach.  [#21] left the quotient primitives postulates
   and added their computation rules beside them (`quotRule?`,
   `ruleItem`); an emitter that turns `Quot.lift` or `Quot.ind` into a
   definition must drop its rule, since a rewrite rule's left-hand side
   must not reduce.
+  The safe profiles cannot use the rules (`--safe` refuses
   `--rewriting`): the declarations that check only with them, which
   `agda_check.py --refusals --without-rewrite` finds, are where [#30]'s
   casts by the propositional rule must go.
+  The scaffold's golden listings measure that progress: a refusal that
   disappears is an emitter's success, and the listing should be
   regenerated with it.  A refusal that names a theorem is the fallback's,
   and its count is what [#20] asked to be reported.

[#17]: https://github.com/formalverification/lean2agda/issues/17
[#18]: https://github.com/formalverification/lean2agda/issues/18
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#20]: https://github.com/formalverification/lean2agda/issues/20
[#21]: https://github.com/formalverification/lean2agda/issues/21
[#22]: https://github.com/formalverification/lean2agda/issues/22
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#28]: https://github.com/formalverification/lean2agda/issues/28
[#30]: https://github.com/formalverification/lean2agda/issues/30
[#44]: https://github.com/formalverification/lean2agda/issues/44
[report]: ../reports/printing-blowup-2026-10-12.md
[report-opaque]: ../reports/opaque-theorems-2026-10-13.md
[report-quot]: ../reports/quotient-rules-2026-11-08.md
[catalog-quot]: ../foundations/gap-catalog.md#quotients
[naming]: naming.md
[modules]: modules.md
[catalog-irrel]: ../foundations/gap-catalog.md#proof-irrelevance
[inductives]: inductives.md
[inductives-projections]: inductives.md#projections
[related]: ../related-work.md
[catalog-let]: ../foundations/gap-catalog.md#projections-and-let
