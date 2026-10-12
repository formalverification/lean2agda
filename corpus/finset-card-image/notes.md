<!-- File: corpus/finset-card-image/notes.md -->

# Finset.card_image_of_injective

The entry for a `Decidable` instance in a `Finset` statement, translated
by issue M1-9 ([#9]): the image of a finite set under an injective map
has as many elements as the set.  Mathlib declares
`Finset.card_image_of_injective` in `Mathlib.Data.Finset.Card`.  One
Agda file, `agda/FinsetCardImage.agda`, translates it under profile CC
(`--safe --cubical-compatible`), with Lean's quotient primitives,
propositional extensionality and function extensionality as module
parameters, in the shapes of the entries `multiset-map-map` and
`set-ext` ([#8]), and with no classical parameter.

## Statement

Lean's statement, as `#check` prints it:

    @Finset.card_image_of_injective : ∀ {α : Type u_1} {β : Type u_2} {f : α → β} [inst : DecidableEq β] (s : Finset α),
      Function.Injective f → (Finset.image f s).card = s.card

The Agda statement, inside `module _ (Q : Quotients) (pe : PropExt)
(fe : FunExt)` and `module _ (_≟_ : DecidableEquality B)`, with `A` and
`B` generalized variables:

    card-image-of-injective : {f : A → B} (s : Finset A) → Injective _≡_ _≡_ f → # image f s ≡ # s

They match up to notation and up to the definitions, which are as
follows:

+  `Finset`: Lean's structure of `val : Multiset α` and
   `nodup : Nodup val`; a record with the same two fields here.
+  `Multiset`: Lean's quotient of `List α` by `List.Perm`; here
   `Quot _↭_`, the parameter record's quotient by agda-stdlib's
   propositional permutation, as in `multiset-map-map`.
+  `Multiset.Nodup`: Lean's `Quot.liftOn s List.Nodup fun _ _ p =>
   propext p.nodup_iff`, a lift into `Prop`; here a `lift` into `Ω a`,
   whose target is a set by `Ω-uip` (The Agda version, below) and whose
   respect proof is `propext`, as in Lean.  Lean's `List.Nodup` is
   `Pairwise (· ≠ ·)`, and agda-stdlib's `Unique` is `AllPairs _≢_`, the
   same relation.
+  `card`: Lean's `Finset.card s = Multiset.card s.1`, with
   `Multiset.card = Quot.lift length`; written `#_` here as `#` in
   Mathlib's source, with `card` the multiset's.
+  `image`: Lean's `(s.1.map f).toFinset`, where
   `toFinset s = ⟨dedup s, nodup_dedup s⟩` and `Multiset.dedup` lifts
   `List.dedup`; the same here.  Lean's `List.dedup` is
   `pwFilter (· ≠ ·)`, which keeps the last copy of each element, and
   agda-stdlib's `deduplicate` keeps the first, so the two lists are
   permutations of each other: equal as multisets, by `sound`, and not
   definitionally.
+  `Function.Injective f` quantifies with strict-implicit binders,
   `∀ ⦃a₁ a₂⦄`, and agda-stdlib's `Injective _≡_ _≡_ f` with implicit
   ones; `DecidableEq β` is `(a b : β) → Decidable (a = b)`, and
   `DecidableEquality B` is `(x y : B) → Dec (x ≡ y)`, where `Dec` is a
   record of a `Bool` and its `Reflects` proof and Lean's `Decidable` an
   inductive type with constructors `isFalse` and `isTrue`.

## Tier

`#print axioms` prints `[propext, Classical.choice, Quot.sound]`, so the
entry is T2.  The selection expected a statement carrying a classical
`Decidable` instance, the seed of M4-4 ([#39]), and the issue's task is
to write the statement with the instance as a hypothesis.  Lean's
statement already has it as one: `[DecidableEq β]` is an argument, which
a caller may fill with `Classical.decEq` or with a computable instance.
So the abstraction M4-4 proposes changes nothing here, and
`Classical.choice` comes in through proofs only.  A shortest-path search
from the declaration through types and values (the probe under Remarks)
finds the routes, as follows:

1.  Through the definitions the statement mentions: `Finset.image`,
    `Multiset.toFinset`, `Multiset.dedup`, then `Multiset.dedup._proof_1`,
    the proof that `List.dedup` respects permutations, which is
    `List.Perm.dedup`, which cites Lean core's `List.perm_iff_count`.
    That lemma, stated under `[BEq α] [LawfulBEq α]`, splits a case
    with `by_cases h : b = a`; at this version `by_cases` expands to
    `open Classical in refine if h : e then ?pos else ?neg`, and with no
    `Decidable (b = a)` instance in scope the `if` takes
    `Classical.propDecidable`.  `#print axioms Finset.image` prints T2
    for this reason, though the function `image` computes uses only the
    given instance.
2.  Through the proof: `card_image_of_injective` passes
    `card_image_of_injOn` a proof of `Set.InjOn f ↑s`, and the coercion
    `↑s` is `Finset.instSetLike`, whose proof field
    (`Finset.instSetLike._proof_1`, that the coercion is injective)
    cites `Multiset.Nodup.ext`, then `List.perm_ext_iff_of_nodup`, which
    begins with the tactic `classical`.
3.  Through `Multiset.Nodup.dedup`, which `image_val_of_injOn` uses and
    which cites `Multiset.dedup`, so route 1 again.

In all, 22 constants of the closure outside the `Classical` namespace
cite one inside it, 14 of them in `grind`'s lemmas and in lemmas
about `Nat` and `Int` (the list is under Remarks).  `propext` and
`Quot.sound` reach the statement through `Finset` itself: `Finset.mk`'s
type mentions `Multiset.Nodup`, whose respect proof is `propext` and
cites `List.Perm.nodup_iff`, whose proof reaches `funext`, and so
`Quot.sound`, through `forall_congr`.

The statement survives de-classicalization: it states nothing classical,
and the Agda file proves it with no classical parameter.  Each lemma of
Lean's proof that was proved classically has a constructive proof in
that file (The Agda version), so a constructive proof is known, and here
it is.  The T1 parameters remain: the quotient, `propext` for
`Multiset.Nodup`, and `funext`.

## What the kernel term needed

The export holds 3,026 declarations: 143 inductive types, the 4
quotient primitives, 1,240 definitions, 1,634 theorems, 2 opaque
constants and the 3 axioms.  At 13,406,809 bytes it is recorded in
`lean/term.sidecar.json`.  Most of it is tactic machinery that lemmas
of the closure were proved with: `grind`'s commutative ring solver
(`Lean.Grind.CommRing`), reached through the proof of
`List.nodup_iff_count_eq_one`, which `List.Perm.dedup` reaches through
`List.count_eq_one_of_mem`; `omega`'s `Lean.Omega`, reached through
`Nat.right_eq_add`, which `List.perm_iff_count`'s `simp` uses and
`omega` proves; the linear normalizer `Nat.Internal.Linear`, reached
through the termination proofs of `grind`'s well-founded definitions;
and `Int.Internal.Linear` and `Lean.Data.AC`.  The two opaque
constants are `String.Internal.append`, reached through a
panic message in `List.get!Internal`, and `Lean.opaqueId`, in a proof
of a `grind` definition; the kernel never unfolds an opaque constant,
neither is an axiom, and neither changes the tier.  The export also
holds 8 `_autoParam` definitions, the default tactics of fields of
`LawfulGetElem` and of `grind`'s ring classes, with the `Lean.Syntax`
machinery the `order-hom-map-lfp` notes describe; leaving them out of
the walk shrinks the closure only from 3,267 constants to 3,258.

The probe of
[`../multiset-map-map/notes.md`](../multiset-map-map/notes.md), Remarks,
re-checked all 2,874 theorems and definitions in Lean's kernel with its
diagnostics on.  Nine reduced `Quot.lift`, 24 times in all:
`Multiset.Nodup.map_on` 5, `Multiset.Nodup.ext` 4, `Multiset.card_map`
3, and `Multiset.dedup_eq_self`, `Multiset.nodup_dedup`, `funext`,
`Quotient.exact`, `Quotient.rel.refl` and `Quotient.lift₂._proof_2` 2
each.  Eight reduced `Eq.rec`, a recursor that admits K-like reduction:
`eq_of_heq` twice, which is K-like reduction on a universe, and seven
equation lemmas of the ring solver's matchers
(`Lean.Grind.CommRing.Power.denote.match_1.eq_3` 6 times, the others 1
to 3), which were not read; as the other entries' notes say, a positive
count includes ordinary reductions on `Eq.refl`.  The elaborator's
re-check with structure eta off (the test of
[`../subtype-coe-eta/notes.md`](../subtype-coe-eta/notes.md), Remarks)
flagged two declarations, both in `Nat.Internal.Linear`:
`Nat.Internal.Linear.ExprCnstr.denote_toNormPoly` and
`Nat.Internal.Linear.Poly.denote_reverse`.  It could not judge 30
others, equation lemmas of the same machinery that its re-check rejects
with eta on as well.  By feature, as follows:

+  `decidable-and-noncomputable`: the hypothesis `[DecidableEq β]`,
   which `Finset.image` and `Multiset.dedup` use to decide `≠`; and
   `Classical.propDecidable`, `noncomputable`, in the proofs listed
   under Tier.  The Agda file takes the hypothesis as the module
   parameter `_≟_` and needs nothing classical.
+  `quotients`: `Multiset` is `Quot`, and the kernel reduces `Quot.lift`
   in the nine declarations above.  The CC file makes each reduction its
   proof needs a rewrite by the record's `lift-β`: `card-map` by
   `map-β` once and `card-β` twice, where Lean's `Multiset.card_map`
   has three reductions; `nodup-dedup`, `dedup-nodup` and `nodup-map` by
   `dedup-β`, `map-β`, and the transports `nodup⁻` and `nodup⁺` along
   `Nodup`'s computation rule.
+  `axioms`: `propext` and `Quot.sound`, in `Finset`'s own definition as
   the Tier section says, and `Classical.choice`, in proofs.  The CC
   file takes `propext` as the field of `pe`, `Quot.sound` as `sound`,
   and `funext`, which Lean proves from `Quot.sound`, as the field of
   `fe`.
+  `proof-irrelevance`: `Finset.eq_of_veq`, reached through
   `Finset.instSetLike` and `Finset.val_inj`, proves that two finite
   sets with equal multisets are equal by matching both, as
   `Subtype.ext` does in the `subtype-coe-eta` entry, so its `rfl`
   identifies the two proofs of `Nodup`.  The Agda proof never compares
   two finite sets, so it needs no counterpart; one would follow from
   the irrelevance proof that `Ω` carries.
+  `impredicative-prop`: `Function.Injective f` and `Set.InjOn f ↑s`
   are propositions quantifying over `α`, which Lean keeps in `Prop`
   and Agda places at `a ⊔ b`; and the `noConfusion` constants of
   `List`, `Option` and `Prod`, whose types have an `imax`, are used at
   level 0, for propositions, through their constructor forms
   (`List.cons.noConfusion.{0,u_1}` occurs 52 times in the printed
   terms), where the `imax` is not the maximum, as in
   `multiset-map-map`.
+  `k-and-uip` and `large-elimination`: `eq_of_heq` and its `cast`,
   reached, among other routes, through `List.mem_cons` in the proof of
   `Multiset.Mem`'s respect for permutations.  Neither Agda proof needs
   K or a large elimination.
+  `universe-levels`: two level parameters, `u_1` and `u_2`, for `α`
   and `β`.  `Finset α` lives in the universe of `α`; so does
   `Finset A : Set a` here, because the permutation relation and `Unique`
   live at the level of the lists.
+  `structure-eta`: the two `Nat.Internal.Linear` lemmas above, by the
   elaborator's test, which stands in for the kernel's.
+  `literals`: 53 `Nat` and 35 string literal records, in the solver
   machinery and the `_autoParam` syntax trees.
+  `nested-and-mutual-inductives`: `Lean.Syntax`, nested, from the
   `_autoParam` definitions.
+  `projections-and-let`: `Finset.val`, the projection `s.1`, in the
   statement's definitions; 358 declarations of the export contain a
   projection expression and 189 a `let`, most of them in the machinery.
   In Agda `val` is a record field.

The manifest listed `decidable-and-noncomputable`, `quotients`,
`proof-irrelevance` and `axioms`.  The other eight are added by the
rule the other translated entries follow, that a feature counts when
the exported closure uses it; of those eight, `impredicative-prop` and
`universe-levels` belong to the mathematics, and the rest come in
through `grind`, `omega`, `autoParam` and the injectivity lemmas of
constructors.  So the entry exercises every feature but
`trust-escape-hatches`, and the coverage table that M1-10 ([#10])
refreshes should say which of them a translation that unfolds
`autoParam` and reuses proofs of library lemmas would still meet.

## Instance arguments

The statement has one instance argument, `[inst : DecidableEq β]`, and
its elaborated type carries no instance constant: the instance is a
bound variable, passed to `Finset.image`.  The proof carries 4
occurrences of instance constants, of two distinct ones,
`Finset.instSetLike` and `Set.instMembership`, for the coercion `↑s`
and the membership in `Set.InjOn f ↑s` (counted with the `#instances`
command of
[`../order-hom-map-lfp/notes.md`](../order-hom-map-lfp/notes.md),
Remarks).

The Agda file has no instance arguments.  The decidable equality is a
module parameter, `_≟_ : DecidableEquality B`, as Mathlib's
`variable [DecidableEq β]` is a section variable, and outside the
modules the theorem takes it as an explicit argument after the three
parameters: a hypothesis, as the issue asks.  Agda's instance arguments
`⦃ ⦄` could carry it, but the corpus declares no instances for them to
find.  The coercion and the
membership of the proof do not appear, because the Agda proof states
injectivity outright instead of injectivity on `s`.

## The Agda version

One file, `agda/FinsetCardImage.agda`, profile CC, in three parts.

**The parameters**.  `Ω` and the record `Quotients` are those of
`multiset-map-map`, and `PropExt` and `FunExt` those of `set-ext`,
copied word for word, because the corpus has no shared module (the
`multiset-map-map` notes say why one should exist).  Issue M1-8's pull
request had merged when this entry was written, so its shape was
matched rather than reconciled later.

**Lists**, with no parameter: the lemmas Lean's proof cites that were
proved classically, proved constructively.

+  `Unique-resp-↭` is Lean's `List.Perm.nodup_iff`, by induction on the
   permutation.
+  `dedup-unique` is one direction of Lean's `List.dedup_eq_self`: a
   list without duplicates is its own deduplication.
+  `dedup-↭` is Lean's `List.Perm.dedup`, by induction on the
   permutation, with a case split on `_≟_` where Lean's
   `List.perm_iff_count` splits classically, and with `filter-comm`,
   that two filters commute, for the swap of two distinct elements.
   agda-stdlib's analogue of Lean's `List.perm_ext_iff_of_nodup` (two
   lists without duplicates with the same members are permutations of
   each other), `unique∧set⇒bag` in
   `Data.List.Membership.Propositional.Properties.WithK`, needs K, to
   identify the proofs of membership, so it cannot serve under CC, and
   the induction avoids it.

**Multisets and finite sets**, under the three parameters.

+  `Ω-uip`, that `Ω p` is a set, by Hedberg's argument (agda-stdlib's
   `Constant⇒UIP`): `propext` gives every equation `P ≡ Q` an endomap,
   constant by `funext` and the irrelevance of `P` and `Q`.  The
   `multiset-map-map` notes expected this obligation for the first
   entry that lifts a quotient into `Prop`, and `Multiset.Nodup` is that
   lift.
+  `Unique-irrelevant`, that `Unique xs` is a proposition, needs
   `funext`, because a proof of `x ≢ y` is a function into `⊥`.
+  The four lifts are `map` (into `Multiset B`, a set by `squash`),
   `card` (into `ℕ`, a set by agda-stdlib's `≡-irrelevant`, Hedberg
   again), `Nodup` (into `Ω a`, a set by `Ω-uip`, respecting
   permutations by `propext`) and `dedup`.
+  The four inductions are `card-map` (Lean's `Multiset.card_map`, whose
   motive is an equation in `ℕ`), `nodup-dedup` (Lean's
   `Multiset.nodup_dedup`, whose motive is `Nodup` itself, already in
   `Ω`), and `nodup-map` and `dedup-nodup` (Lean's
   `Multiset.Nodup.map` and `Multiset.Nodup.dedup`), whose motives are
   implications, propositions by `funext`.
+  The theorem is Lean's proof: `image f s`'s multiset is
   `dedup (map f (val s))` by definition, `dedup-nodup` rewrites it to
   `map f (val s)` (Lean's `image_val_of_injOn`, which is
   `(s.2.map_on H).dedup`), and `card-map` finishes.  It takes
   injectivity, where Lean's `card_image_of_injOn` takes injectivity on
   `s`; stating that would need membership in a finite set, another
   lift into `Prop`, which the theorem does not need.

Three things a translator will meet came up on the way.  First, Agda
2.8.0 warns `UnsupportedIndexedMatch` under `--cubical-compatible` for
a pattern on `Unique` at the index `x ∷ xs` ("relies on injectivity of
the data constructor `_∷_`") and for the patterns `yes` and `no`, which
match the indexed family `Reflects` ("injectivity of the data
constructor Agda.Builtin.Bool.Bool.true"); `make corpus-check` hides
the warnings of a passing file, so the file was checked with agda-mcp's
`check_file`, which reports them, and rewritten with `head`, `tail` and
`invert` until it had none.  Second, `with x ≟ y` in the swap case
abstracted `x ≟ y` in the goal, and after the pattern `yes refl` one
side still held `x ≟ x`, unreduced, so the two sides no longer matched;
a helper on `Dec (x ≡ y)` with a substitution replaced it.  Third, a generalized
variable `A : Set a` named beside the level `a` in one signature
(`IsNodup : Multiset A → Set a`) gets a level of its own, `A.a`, and
the definition fails with `Set A.a != Set a`; binding `{A : Set a}`
explicitly fixes it.

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 13,406,809 (recorded in `lean/term.sidecar.json`) |
| Export, records | 256,602 |
| Export, expression records | 231,887 |
| Export, declarations | 3,026: 143 inductive, 4 quot, 1,240 def, 1,634 thm, 2 opaque, 3 axiom |
| Agda, lines per file | 397, of which 233 are code |
| Agda, check time | 5.5 seconds (Agda 2.8.0, no `.agdai` files of the corpus) |

## Remarks

The export was made on 2026-10-11 with lean4export v4.33.0 (format
3.1.0) under Lean v4.33.1 (commit `819816b`), the pins of
[`docs/pinning.md`](../../docs/pinning.md).  Two runs gave the same
bytes, whose SHA-256 is the sidecar's.

For M4-4 ([#39]), the entry shows two things.  The abstraction it
proposes is often already done: Mathlib states this lemma with the
instance as a hypothesis, and the T2 comes from proofs.  And a test that
classifies a statement by the axioms of the constants it mentions calls
this statement classical, since `Finset.image` is T2 through a proof
inside it; detection has to look for classical instance terms, not
axiom sets.  A scan of the pinned Mathlib (the second probe below)
found 439,939 theorems, 304,066 of them T2, and 1,465 whose statement
cites one of `Classical`'s decidability constants directly, every one of
them T2.  That count misses a classical instance reached through a
definition the statement mentions, which is what M4-4's atlas fields are
for, and it includes Lean's auxiliary `_proof_` theorems.  The T2 count
is a lower bound, since `#print axioms` can leave out axioms at this
version (Lean issue 15226).

The routes of the Tier section, and those of the `order-hom-map-lfp`
notes, come from the following probe, run from `translator/` as
`lake env lean` on a scratch file on 2026-10-11.  It searches
breadth-first along the edges lean4export follows, so the path it prints
is a shortest one, and marks each link whose type is a proposition.

```lean
import Mathlib.Data.Finset.Card
import Mathlib.Order.FixedPoints
open Lean Elab Command

/-- Direct dependencies along lean4export's edges: types, values, constructors, recursors. -/
def deps (env : Environment) (c : Name) : List Name :=
  match env.find? c with
  | none => []
  | some ci =>
    let d := ci.type.getUsedConstants.toList ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants.toList)).getD []
    match ci with
    | .inductInfo v => d ++ v.ctors ++ v.all
    | .ctorInfo v => d ++ [v.induct]
    | .recInfo v => d ++ v.all
    | _ => d

/-- Breadth-first search from `root`: each constant reached, with the one it was reached from. -/
partial def bfs (env : Environment) (root : Name) : Std.HashMap Name Name := Id.run do
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut frontier := #[root]
  while !frontier.isEmpty do
    let mut next := #[]
    for c in frontier do
      for d in deps env c do
        unless seen.contains d do
          seen := seen.insert d
          parent := parent.insert d c
          next := next.push d
    frontier := next
  return parent

def pathTo (parent : Std.HashMap Name Name) (root t : Name) : List Name := Id.run do
  let mut p := [t]
  let mut c := t
  for _ in [0:200] do
    if c == root then break
    match parent.get? c with
    | some q => p := q :: p; c := q
    | none => break
  return p

/-- A shortest path from `root` to `target`, each link marked (P) when its type is a proposition. -/
elab "#path " root:ident target:ident : command => do
  let env ← getEnv
  let p := pathTo (bfs env root.getId) root.getId target.getId
  let marks ← liftTermElabM <| p.mapM fun c => do
    match env.find? c with
    | some ci => return s!"{c}{if (← Meta.isProp ci.type) then " (P)" else ""}"
    | none => return s!"{c} ?"
  logInfo m!"{" → ".intercalate marks}"

/-- The constants outside `Classical` in the closure of `root` that cite a `Classical` constant. -/
elab "#classical_citers " root:ident : command => do
  let env ← getEnv
  let closure := root.getId :: (bfs env root.getId).toList.map (·.1)
  let mut out : Array String := #[]
  for c in closure do
    if (`Classical).isPrefixOf c then continue
    let cl := (deps env c).filter fun d => (`Classical).isPrefixOf d
    unless cl.isEmpty do out := out.push s!"{c} cites {cl.eraseDups}"
  logInfo m!"{closure.length} constants, {out.size} citers\n{"\n".intercalate (out.qsort (· < ·)).toList}"

#path Finset.image Classical.choice
#path Finset.card_image_of_injective Classical.choice
#path Multiset.Nodup.dedup Classical.choice
#path Finset.card propext
#path Finset.card Quot.sound
#path Finset.card_image_of_injective Finset.eq_of_veq
#path Finset.card_image_of_injective Lean.Grind.CommRing.Poly.pow
#path Finset.card_image_of_injective String.Internal.append
#path Finset.card_image_of_injective Lean.opaqueId
#classical_citers Finset.card_image_of_injective
#path OrderHom.map_lfp propext
#path OrderHom.map_lfp Quot.sound
```

It printed the following:

```text


Finset.image → Multiset.toFinset → Multiset.dedup → Multiset.dedup._proof_1 (P) → List.Perm.dedup (P) → List.perm_iff_count (P) → Classical.propDecidable → Classical.choice
Finset.card_image_of_injective (P) → Finset.instSetLike → Finset.instSetLike._proof_1 (P) → Multiset.Nodup.ext (P) → List.perm_ext_iff_of_nodup (P) → Classical.propDecidable → Classical.choice
Multiset.Nodup.dedup (P) → Multiset.dedup → Multiset.dedup._proof_1 (P) → List.Perm.dedup (P) → List.perm_iff_count (P) → Classical.propDecidable → Classical.choice
Finset.card → Finset → Finset.mk → Multiset.Nodup → Multiset.Nodup._proof_1 (P) → propext (P)
Finset.card → Finset → Finset.mk → Multiset.Nodup → Multiset.Nodup._proof_1 (P) → List.Perm.nodup_iff (P) → List.Perm.pairwise_iff (P) → List.pairwise_middle (P) → forall_congr (P) → funext (P) → Quot.sound (P)
Finset.card_image_of_injective (P) → Finset.instSetLike → Finset.instSetLike._proof_1 (P) → Finset.val_inj (P) → Finset.val_injective (P) → Finset.eq_of_veq (P)
Finset.card_image_of_injective (P) → Finset.image → Multiset.toFinset → Multiset.dedup → Multiset.dedup._proof_1 (P) → List.Perm.dedup (P) → List.count_eq_one_of_mem (P) → List.nodup_iff_count_eq_one (P) → _private.Mathlib.Data.List.Nodup.0.List.nodup_iff_count_eq_one._proof_1_1 (P) → Lean.Grind.CommRing.le_norm_expr (P) → Lean.Grind.CommRing.Expr.toPoly_k → Lean.Grind.CommRing.Poly.pow
Finset.card_image_of_injective (P) → Finset.instSetLike → Finset.instSetLike._proof_1 (P) → Multiset.Nodup.ext (P) → List.perm_ext_iff_of_nodup (P) → List.perm_iff_count (P) → Nat.right_eq_add._simp_1 (P) → Nat.right_eq_add (P) → _private.Init.Data.Nat.Lemmas.0.Nat.right_eq_add._proof_1_1 (P) → Lean.Omega.LinearCombo.coordinate_eval_0 (P) → Lean.Omega.IntList.get_cons_zero (P) → List.instGetElem?NatLtLength → List.get!Internal → List.get!Internal._f → panicWithPosWithDecl → mkPanicMessageWithDecl → String.Internal.append
Finset.card_image_of_injective (P) → Finset.image → Multiset.toFinset → Multiset.dedup → Multiset.dedup._proof_1 (P) → List.Perm.dedup (P) → List.count_eq_one_of_mem (P) → List.nodup_iff_count_eq_one (P) → _private.Mathlib.Data.List.Nodup.0.List.nodup_iff_count_eq_one._proof_1_1 (P) → Lean.Grind.CommRing.le_norm_expr (P) → Lean.Grind.CommRing.Expr.toPoly_k → Lean.Grind.CommRing.Poly.combine_k → Lean.Grind.CommRing.Mon.grevlex_k → Lean.Grind.CommRing.Mon.revlex_k → Lean.Grind.CommRing.Mon.revlexWF → Lean.Grind.CommRing.Mon.revlexWF._unary → Lean.Grind.CommRing.Mon.revlexWF._unary._proof_1 (P) → Lean.opaqueId
3267 constants, 22 citers
DerivingHelpers.deriving_lawful_beq_helper_nd cites [Classical.propDecidable]
Lean.Grind.OrderedRing.nonneg_intCast_of_nonneg cites [Classical.byContradiction]
Lean.Grind.eq_false_of_imp_eq_false cites [Classical.not_imp._simp_1]
Lean.Grind.eq_true_of_imp_eq_false cites [Classical.not_imp._simp_1]
Lean.Grind.eq_true_of_not_eq_false cites [Classical.not_not._simp_1]
Lean.Grind.iff_eq cites [Classical.propDecidable]
Lean.Grind.not_eq_prop cites [Classical.propDecidable]
Lean.Grind.not_not cites [Classical.propDecidable]
Lean.Grind.of_eq_eq_true cites [Classical.propDecidable]
List.count_erase._f cites [Classical.propDecidable]
List.erase_eq_eraseP._f cites [Classical.propDecidable]
List.perm_ext_iff_of_nodup cites [Classical.propDecidable]
List.perm_iff_count cites [Classical.propDecidable]
_private.Init.Data.Int.LemmasAux.0.Int.ble'_eq_true._proof_1_4 cites [Classical.propDecidable]
_private.Init.Data.Int.LemmasAux.0.Int.blt'_eq_true._proof_1_4 cites [Classical.propDecidable]
_private.Init.Data.Int.LemmasAux.0.Int.neg_nonpos_iff._proof_1_1 cites [Classical.propDecidable]
_private.Init.Data.Nat.Lemmas.0.Nat.right_eq_add._proof_1_1 cites [Classical.propDecidable]
_private.Init.Grind.Ordered.Int.0.Lean.Grind.instLawfulOrderLTInt._proof_1 cites [Classical.propDecidable]
_private.Init.Grind.Ordered.Int.0.Lean.Grind.instOrderedAddInt._proof_1 cites [Classical.propDecidable]
_private.Mathlib.Data.List.Dedup.0.List.mem_dedup._simp_1_3 cites [Classical.not_not]
_private.Mathlib.Data.List.Nodup.0.List.nodup_iff_count_eq_one._proof_1_1 cites [Classical.byContradiction]
not_and_or cites [Classical.propDecidable]
OrderHom.map_lfp (P) → OrderHom.instPreorder → Preorder.lift → Function.Injective.preorder → Function.Injective.preorder._proof_1 (P) → propext (P)
OrderHom.map_lfp (P) → OrderHom.map_le_lfp (P) → le_sInf_iff (P) → le_isGLB_iff (P) → IsGLB.lowerBounds_eq (P) → Set.ext (P) → funext (P) → Quot.sound (P)
```

The scan for M4-4 ran as follows, on a scratch file importing all of
Mathlib, in 2 minutes 5 seconds of wall time:

```lean
import Mathlib
open Lean Elab Command

/-- Mathlib theorems: total, T2, and those whose statement cites a classical decidability constant. -/
elab "#classical_statements" : command => do
  let env ← getEnv
  let decs : List Name := [``Classical.propDecidable, ``Classical.decEq, ``Classical.decPred,
    ``Classical.decRel, ``Classical.dec, ``Classical.typeDecidableEq, ``Classical.typeDecidable]
  let decs := decs.filter env.contains
  let mut total : Nat := 0
  let mut t2 : Nat := 0
  let mut stmt : Nat := 0
  let mut stmtT2 : Nat := 0
  let mut examples : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let .thmInfo v := ci | continue
    let some idx := env.getModuleIdxFor? n | continue
    unless (`Mathlib).isPrefixOf env.header.moduleNames[idx.toNat]! do continue
    total := total + 1
    let axs ← liftCoreM (collectAxioms n)
    let isT2 := axs.contains ``Classical.choice
    if isT2 then t2 := t2 + 1
    let used := v.type.getUsedConstants
    if decs.any used.contains then
      stmt := stmt + 1
      if isT2 then stmtT2 := stmtT2 + 1
      if examples.size < 5 then examples := examples.push n
  logInfo m!"decidability constants: {decs}\nMathlib theorems {total}; T2 {t2}; statement cites one {stmt} (T2 {stmtT2}); e.g. {examples}"
#classical_statements
```

It printed the following:

```text


decidability constants: [Classical.propDecidable,
 Classical.decEq,
 Classical.decPred,
 Classical.decRel,
 Classical.dec,
 Classical.typeDecidableEq,
 Classical.typeDecidable]
Mathlib theorems 439939; T2 304066; statement cites one 1465 (T2 1465); e.g. [Finsupp.curry._proof_4,
 _private.Mathlib.Data.Fintype.EquivFin.0.Infinite.natEmbeddingAux._proof_11,
 PMF.toMeasure_pure_apply,
 Finset.map_comp_coe_apply,
 Ideal.Quotient.groupWithZero._proof_4]
```

[#8]: https://github.com/formalverification/lean2agda/issues/8
[#9]: https://github.com/formalverification/lean2agda/issues/9
[#10]: https://github.com/formalverification/lean2agda/issues/10
[#39]: https://github.com/formalverification/lean2agda/issues/39
