<!-- File: docs/translator/printing.md -->

# Printing expressions

The printer turns a Lean kernel expression into Agda text under profile U
(`--type-in-type`, postulates allowed), and the sharing pass first moves
repeated closed subterms into auxiliary definitions, so that the text
stays near the size of the shared term.  Issue [#17] implements both, in
`translator/Lean2Agda/Core/Print.lean` and `Core/Share.lean`, and a
scaffold, `Core/Scaffold.lean`, that tests them with Agda until the
emitters of [#18], [#20] and [#21] exist.  The measurements behind the
choices below are in the dated report [`printing-blowup`][report].

## Command line

`--out DIR` now also writes the scaffold, an Agda module holding the whole
closure, at the path of its first root's names sidecar
([`naming.md`][naming]).  For example, the following writes
`out/U/Init/Data/Nat/Gcd.agda` beside `out/U/Init/Data/Nat/Gcd.names.ndjson`:

```sh
cd translator
lake exe lean2agda --out out Init.Data.Nat.Gcd -- Nat.gcd_self
agda --only-scope-checking out/U/Init/Data/Nat/Gcd.agda     # from out/
python3 ../scripts/python/scaffold_check.py --messages out/U/Init/Data/Nat/Gcd.agda
```

`--share N` sets the sharing threshold, 32 by default; `--share 0` turns
the pass off.  The listing, `closure.txt` and standard output are as
before.  The sidecars are those of the shared closure, so that they map the
auxiliary definitions' identifiers back to their structured names too.

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
198 below it; the scaffold, which prints types and the root's value, makes
16, all below the top.  With the repair turned off, Agda refuses four of
that scaffold's types with `WrongHidingInLambda`, one of which otherwise
checks, and both repaired definitions of the printing fixture.

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
scaffold's options are `--type-in-type` alone.  lyphyser's output adds
`--prop` and prints `Prop` for `Sort 0` ([`related-work.md`][related]),
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

Until [#18] emits records, the scaffold has no projection functions that
compute, so `Expr.proj S i t` prints through the structure's recursor,
`S.rec {params} {λ self → Tᵢ} (λ f₀ … fₙ₋₁ → fᵢ) t`, where `Tᵢ` is the
field's type with each earlier field replaced by its projection from
`self`, as the kernel types a projection.  For a field whose type does not
mention an earlier field (`Prod.fst`, `PProd.fst`), this type-checks against
a postulated recursor.  For a dependent field
(`PrintFixtures.Dependent.value`) the recursor's minor premise needs the
recursor to compute, and Agda refuses it until [#18] or [#19] gives it a
computation rule.  Once [#18] emits records, `projectionAsRecursor` is the
one function to change, to the record's field projection.

### Other constructors

+  `letE` prints as `let x : A; x = v in b`; Agda's `let` substitutes, so it
   gives Agda's checker no sharing ([gap catalog][catalog-let]).
+  `mdata` is dropped.  lean4export strips it too, but the environment's
   values carry it.
+  `const` prints as `agdaIdent`, unqualified within one module;
   `Naming.qualified` prefixes the owner's module path for [#22].
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

The scaffold is one Agda module per closure under
`{-# OPTIONS --type-in-type #-}`.  It declares every constant with its
printed type, each as a postulate, except the following:

+  `Nat`, a `data` type with Lean's constructors under their own
   identifiers, bound to `BUILTIN NATURAL`;
+  `String`, a postulate bound to `BUILTIN STRING`;
+  the type abbreviations: a definition whose type ends in a sort and whose
   value, under its leading lambdas, is a Pi type, a sort or one of its
   parameters (`outParam`, `optParam`, `DecidableEq`, `DecidablePred`);
   Agda cannot check `HAdd.hAdd`'s type unless `outParam Set` unfolds to a
   sort;
+  the closure's roots that have values, and the auxiliary definitions
   that anything printed uses, as definitions with their printed values,
   except that a definition whose printed value refers to itself, or to a
   definition that refers back to it, stays a postulate: Lean's kernel
   accepts such a cycle only among unsafe definitions, such as the
   `_unsafe_rec` companions of mutual `partial` definitions, and Agda
   could check none of them.

`Nat` and `String` are bound to their builtins whether or not they are
roots.

Declarations follow the closure's groups, and inside a group (an inductive
type with its constructors and recursor) the printed references decide.
The module sits at the path of its first root's sidecar until [#22] splits
it into one module per Lean module, so a reverse lookup of an identifier in
it may need any sidecar of the output directory.

### What Agda checks

Agda parses and scope-checks every scaffold, which is the first acceptance
criterion of [#17] ("prints and re-parses").  `make test-translator` does
so for the three core-Lean corpus entries; `make scaffold-corpus`, which
needs Mathlib's cache, does so for all twelve entries of
`corpus/manifest.json`, and all twelve pass (the report gives the table).
Agda's time grows faster than the module: 6 s for 0.7 MB, 187 s for
3.0 MB, and 28 minutes for `real-sqrt-nonneg`'s 7.5 MB, which is one
reason for [#22]'s one module per Lean module.  Scope-checking does not see
visibility or precedence errors, which still parse, so the scaffold is also
type-checked.  Not every declaration can check: the postulates withhold the
definitional unfolding (delta, iota, projections of instances) that Lean's
kernel used.  `scripts/python/scaffold_check.py` type-checks a scaffold
anyway.  When Agda refuses a definition's clause, the definition becomes a
postulate of its type; when it refuses a type, the declaration and
everything that refers to it are dropped; and it repeats until the rest
checks, listing each refusal in the order Agda met it.  The harness
compares that listing with a golden one.

| Scaffold | Declarations | Refused | Types checked |
| --- | --- | --- | --- |
| `list-reverse-reverse` | 41 | the root's value | 41 |
| `nat-gcd-succ` | 272 | the root's value, 5 types | 267 |
| `nat-gcd-self` | 337 | the root's value, 6 types | 331 |
| printing fixture | 377 | `Dependent.value`'s value, 4 types | 373 |
| `Fixtures.selected` | 34 | nothing | 34 |

Every value not listed checks: the type abbreviations', the auxiliary
definitions', `Fixtures.selected`'s, and the printing fixture's twelve
other roots.

Every refusal is an `UnequalTerms` that needs unfolding, as follows:

+  `List.reverse_reverse` ends in `rfl`, which needs `List.reverse` to
   unfold;
+  `Nat.gcd_self` and `Nat.gcd_succ` need `n + 1` to be `Nat.succ n`
   (instances, `Nat.add`, and its recursor), the identification the corpus
   notes describe;
+  four compiled matchers' types annotate a motive's binder with
   `n ≤ m` where `Nat.le n m` is expected, which needs the instance
   `instLENat` and the projection `LE.le` to compute;
+  a fifth matcher's type, and `Nat.modCore.go.eq_1`'s in
   `nat-gcd-self`, need `a + 1` to be `Nat.succ a`.

Printing every value of each closure, with every definition and theorem
as a root, Agda checks 139 of `nat-gcd-self`'s 266 values outright, refuses
54, and leaves 73 unchecked behind a refused type; every refusal is again
an `UnequalTerms`, and their causes are the recursors (`Nat.rec`,
`Decidable.rec`), instance projections, literals against `OfNat.ofNat`,
`Quot.lift` in `funext` ([#21]'s case), and K-like reduction in
`eq_of_heq`.  None is a wrong visibility, a scope error or a parse error.
These are the emitters' work, and the golden listings record where each
scaffold stands until then.

## Verification

`make test-translator` runs the following; the probes in the pull request
broke each rule in turn and showed which checks fail:

+  `tests/Printing.lean`: the precedence table, string escapes, clause
   patterns, binder names, each `Expr` constructor, both repairs, a
   telescope, qualified names, the sharing pass's counting on the doubling
   of 2^20 leaves and its auxiliaries (kernel-checked, owned, printed in
   linear size), and the type-abbreviation rule;
+  `PrintingLexical.agda`, which `tests/Printing.lean` writes: a binder
   built from every Agda keyword and sort name, which Agda checks;
+  five scaffolds against golden files in `tests/expected/scaffolds/`,
   scope-checked, and type-checked with `scaffold_check.py` against golden
   listings: the three core-Lean corpus entries, the printing fixture
   (`tests/TranslatorTests/Input/Printing.lean`, which prints every
   constructor, every visibility and both repairs in values that check
   against postulates) and `Fixtures.selected`;
+  the scaffold of the printing fixture's whole module, mutual `partial`
   definitions included, scope-checked.

`make scaffold-corpus` is the check over all twelve corpus entries; it
needs Mathlib's cache, takes about half an hour, and no CI job runs it.

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
+  Each call returns `PrintCounts`: repairs at the top and below, and
   projections printed through a recursor.

It assumes the following of its callers:

+  Every constant an expression mentions is in the printer's environment,
   auxiliary definitions included.
+  The emitted Agda declares each constant under its `agdaIdent`, with the
   visibilities of its Lean type, since the printer passes arguments by
   the head's type.  A record field, a data constructor or a pattern-matching
   definition that changes a constant's visibilities breaks every
   application of it.
+  [#18] replaces `projectionAsRecursor` with record projections, and
   `Nat`'s `data` declaration with its own; [#20] makes definitions
   transparent and theorems opaque, which turns most of the refusals
   above into checks; [#21] gives `Quot.lift` its rewrite rule.
+  The scaffold's golden listings measure that progress: a refusal that
   disappears is an emitter's success, and the listing should be
   regenerated with it.

[#17]: https://github.com/formalverification/lean2agda/issues/17
[#18]: https://github.com/formalverification/lean2agda/issues/18
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#20]: https://github.com/formalverification/lean2agda/issues/20
[#21]: https://github.com/formalverification/lean2agda/issues/21
[#22]: https://github.com/formalverification/lean2agda/issues/22
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#28]: https://github.com/formalverification/lean2agda/issues/28
[#44]: https://github.com/formalverification/lean2agda/issues/44
[report]: ../reports/printing-blowup-2026-10-12.md
[naming]: naming.md
[related]: ../related-work.md
[catalog-let]: ../foundations/gap-catalog.md#projections-and-let
