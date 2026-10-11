<!-- File: docs/translator/naming.md -->

# Names and module paths

The pure naming API translates structured Lean names, never their printed
strings.  A declaration has one Agda identifier regardless of its source
module, translation profile, dependency order, or the other declarations
selected.  Module paths prepend a root supplied by the caller.  Issue [#37]
will choose profile and layer roots; this scheme does not assign layers.
Issue [#17]'s printer should use `agdaIdent` for every constant reference.

## Identifier encoding, version 1

Lean's `Name` is a chain of string or natural-number components ending in
`anonymous`.  Preserve every component and its constructor.  Encode each
component as follows, then join the encoded components with `:`.

| Input | Encoding | Reason |
| --- | --- | --- |
| ASCII letters and digits | unchanged, subject to the prefix rules below | Keep ordinary names readable. |
| `_` inside a string | `~u` | Agda underscores mark argument holes in mixfix notation. |
| Any other character | `~xH~`, with its Unicode scalar value in lowercase hexadecimal | Use a small ASCII alphabet that Agda accepts, including in module filenames. |
| Empty string component | `~e` | Empty parts must remain distinct from an absent part. |
| String starting with an ASCII digit | `~s` followed by its character encoding | Avoid integer and floating-point literals. |
| Reserved string | `~s` followed by its character encoding | Avoid Agda keywords and universe names. |
| Numeric component `N` | `~nN`, with canonical decimal digits | Distinguish `Name.num` from a string containing digits. |
| Anonymous name, with no components | `~a` | Supply an identifier for the entire domain of `Name`. |

The prefix rules apply to the original string.  A reserved string means an
Agda 2.8.0 keyword, including the deprecated `codata`, the directive words
`as` and `to`, or the universe names `Set` and `Prop`.  The keyword list is
kept in `Core/Naming.lean`.  Other universe spellings contain non-ASCII
characters and receive character escapes.  Applying the rules separately
to every component also makes the components valid standalone module names.

Examples are as follows:

+  `Nat.gcd_self` becomes `Nat:gcd~uself`.  The colon joins namespace
   components inside one identifier; it never opens an Agda module.
+  `A.«b:c»` becomes `A:b~x3a~c`.  A literal colon cannot impersonate a
   component boundary.  `A.«b.c»` becomes `A:b~x2e~c`, whereas `A.b.c`
   becomes `A:b:c`.
+  `A.2` becomes `A:~n2`, whereas `A.«2»` becomes `A:~s2`.  Numeric and
   string components remain distinct.
+  `_private.Init.Data.Nat.Gcd.0.Nat.helper` becomes
   `~uprivate:Init:Data:Nat:Gcd:~n0:Nat:helper`.  Keeping the private prefix
   prevents helpers with the same user name in different modules from
   colliding.
+  `f._proof_1` becomes `f:~uproof~u1`, and `_uniq.231` becomes
   `~uuniq:~n231`.  Auxiliary and fresh names keep their full identity.
+  A string component `x✝` becomes `x~x271d~`; `_inaccessible` becomes
   `~uinaccessible`.  Inaccessible names use the same character rules.
+  `record` becomes `~srecord`.  The literal string `~srecord` becomes
   `~x7e~srecord`, so keyword escaping creates no collision.
+  `«a b»` becomes `a~x20~b`; `«λ»` becomes `~x3bb~`; an apostrophe in
   `f'` becomes `f~x27~`.  Whitespace, Unicode, punctuation, and controls
   have explicit scalar escapes.
+  The empty string becomes `~e`, the literal string `~e` becomes
   `~x7e~e`, and the anonymous name becomes `~a`.
+  The hygienic name `f._@.Init._hyg.2` becomes
   `f:~u~x40~:Init:~uhyg:~n2`.  Retain macro scope and context components;
   never call `eraseMacroScopes`.

The output alphabet consists of ASCII letters, digits, colons, and tildes.
It contains no dot, whitespace, underscore, quote, comment delimiter, or
Agda special symbol that cannot occur inside a name.  Colons and tildes
are legal inside Agda identifiers.  A component beginning with a tilde
cannot equal a keyword or a literal; unchanged components begin with an
ASCII letter and are checked against the reserved list.

The encoding is injective by construction: raw colons separate components;
escapes contain none.  The marker `~` is always escaped in input strings.
The codes `~u`, `~xH~`, `~e`, `~s`, and `~n` have distinct meanings, and
hexadecimal escapes have explicit terminators.  A numeric component cannot
be a string component, and the anonymous code cannot be a component code.
There is no truncation, normalization, hash suffix, or collision index.
Changing the input order therefore cannot change an identifier.  Escaping
Unicode sacrifices some readability to make lexical acceptance independent
of Unicode categories and the host filesystem's interpretation of them.

## Classification and predecessors

Classification is metadata, not a reason to discard or shorten a name.
Use Lean 4.33.1's predicates, as follows:

+  `isPrivateName` recognizes names under the root `_private`.
+  `Name.isInternal` detects a string component starting with `_`.
+  `Name.isInternalDetail` also recognizes numeric components and certain
   generated suffixes, such as `match_1` and `proof_1`.
+  `Name.isInaccessibleUserName` checks the final string component for `✝`
   or `_inaccessible`, descending through final numeric components.
+  `Name.hasMacroScopes` recognizes the trailing `_hyg` scope structure.

`_uniq` is the default fresh-name prefix in Lean's `NameGenerator`; it is
not a privacy predicate.  Preserve it as any other string component.
Some generated names are not internal according to `Name.isInternal`.
The naming API includes all names, regardless of these classifications.

At commit `fbd86b6`, [lyphyser's `stringifyIdent`][lyphyser] replaces `_`
with `-` and `.` with `:`.  It does not distinguish a literal dot in a
component from a component separator.  We retain its colon idea but encode
the structured components and reserve the escape marker.

At commit `2d28bbe`, [rocq-lean-import's `leanName.ml`][rocq-name] cleans
characters and joins components with underscores.  Its
[`name_for`][rocq-collision] asks Rocq for a fresh global identifier when a
label already exists; that source warns that constructor and recursor
collisions remain possible.  Our identifiers need no existing target
environment or collision allocation.  These are comparisons of the
schemes; no implementation is copied.

The pinned source references are [Lean's constructors][lean-name],
[internal-name predicates][lean-internal], [private names][lean-private],
[inaccessible names][lean-inaccessible], and [Agda's lexical rules][agda-lex].
[Agda's lexer][agda-lexer] includes `codata`, which the documentation's
keyword list omits.  Lean's [name printer][lean-printer] explicitly does
not guarantee a round trip for every name; reverse maps therefore use
components rather than trusting `toString`.

## Module paths and the printer seam

`Root` and `ModuleName` are aliases for structured Lean `Name` values.
`agdaModule : Root → ModuleName → List String` encodes the root components
and appends the encoded module components.  An anonymous root means no
prefix; an anonymous module has the single component `~a`.

For example, a caller-supplied root `CC.Constructive` and source module
`Mathlib.Data.Nat.Basic` give the following path components:

```text
[CC, Constructive, Mathlib, Data, Nat, Basic]
```

The qualified module name joins those components with dots.  Its future
Agda file joins them with filesystem separators and appends `.agda` to the
last component.  `A.B.C` stays `A.B.C` under any supplied root.  Quoted or
numeric module components use the identifier component rules; a literal
slash becomes `~x2f~`, so it cannot escape the output directory.  Two
source modules under the same root have distinct paths.  A root's choice
and length belong to the caller, so uniqueness across different roots
requires the caller to choose disjoint trees.

Namespace components inside constants stay flattened.  A namespace need
not be reopened in different files; each declaration stays in its owning
source module, and the printer can qualify `agdaIdent declaration.name`
with that module's `agdaModule` path.  Local declarations must be assigned
a source module before sidecar grouping.  Fresh printer binders and
sharing auxiliaries must be allocated as distinct structured names before
being passed through this API.

## Reverse maps

Use UTF-8 NDJSON sidecars, one beside each future generated `.agda` file,
with the same stem and suffix `.names.ndjson`.  The current `--out DIR`
command emits these sidecars for the dependency closure alongside its
existing `closure.txt`; it does not emit expressions.  `--root NAME`
supplies the tree root.  The diagnostic default is `U`, without a layer
assignment; the future emitter will pass the root selected by [#37].

Each file contains a versioned header, records sorted by Agda identifier,
and a footer giving the number of records.  A name is an array of tagged
components in root-to-leaf order.  A string component has `str`; a numeric
component has `num` with its canonical decimal representation as a string.
The string representation avoids loss of arbitrarily large natural numbers
in JSON consumers.  An empty array represents the anonymous name.

For source module `Init.Prelude`, root `U`, and declaration `Nat`, the
complete one-record sidecar is as follows:

```json
{"naming":{"version":1,"root":[{"str":"U"}],"source":[{"str":"Init"},{"str":"Prelude"}],"target":["U","Init","Prelude"]}}
{"agda":"Nat","lean":[{"str":"Nat"}]}
{"end":{"records":1}}
```

The pure reverse-map parser checks the version, tagged names, recomputed
identifier and target path, record ordering, uniqueness, footer count, and
absence of trailing data.  Duplicate input declarations are deduplicated
when building a map.  An inconsistent identifier or a collision fails
explicitly.  Lookup returns the original structured `Name`, including
private prefixes, empty strings, numeric components, and macro scopes.
JSON escapes protect control characters and quotes without changing them.

## Verification

`make test-translator` checks adversarial structured names, generated name
samples, the identifiers of every imported `Init` constant, module paths,
and reverse-map round trips and malformed input.  A golden listing covers
the names owned by `Init.Data.Nat.Gcd`.  Generated lexical fixtures declare
and use sample identifiers and module paths under the pinned Agda 2.8.0.

The separate atlas test reads the regenerable format-0 atlas and imports no
Mathlib modules.  Run it inside the pinned shell, as follows:

```sh
make test-naming-atlas ATLAS=atlas/mathlib-v4.33.1-0df444a.ndjson
```

Produce the input with `make atlas`, or use a previously verified file from
the same pins.  The test checks the atlas header against Lean and the Lake
manifest, validates every printed name with Lean's name-literal decoder,
and checks completeness and unique names.  It then times `agdaIdent` over
all names and checks for collisions, reporting the number of names that
needed escaping and the collision-index count (always zero).  The atlas's
text format cannot represent every possible `Name`; generated structured
samples and the direct `Init` scan cover cases absent from that format.

[#17]: https://github.com/formalverification/lean2agda/issues/17
[#37]: https://github.com/formalverification/lean2agda/issues/37
[lyphyser]: https://github.com/lyphyser/lean2agda/blob/fbd86b6/Lean2Agda/Aux/Ident.lean
[rocq-name]: https://github.com/rocq-community/rocq-lean-import/blob/2d28bbe/src/leanName.ml
[rocq-collision]: https://github.com/rocq-community/rocq-lean-import/blob/2d28bbe/src/lean.ml#L672-L684
[lean-name]: https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Prelude.lean#L4725-L4741
[lean-internal]: https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Data/Name.lean#L122-L156
[lean-private]: https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/PrivateName.lean
[lean-inaccessible]: https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Meta/Defs.lean#L152-L156
[lean-printer]: https://github.com/leanprover/lean4/blob/v4.33.1/src/Init/Data/ToString/Name.lean
[agda-lex]: https://agda.readthedocs.io/en/v2.8.0/language/lexical-structure.html
[agda-lexer]: https://github.com/agda/agda/blob/v2.8.0/src/full/Agda/Syntax/Parser/Lexer.x#L159-L207
