<!-- File: corpus/lists-subset-refl/notes.md -->

# Lists'.Subset.refl

The entry for mutual inductive types, translated by issue M1-7 ([#7]):
reflexivity of the subset relation on Mathlib's hereditarily finite lists,
declared in `Mathlib.SetTheory.Lists`, where `Lists.Equiv` and `Lists'.Subset`
form the one mutual block of inductive types in Mathlib's mathematics.  One
Agda file, `agda/ListsSubsetRefl.agda`, checks under profile CC
(`--safe --cubical-compatible`), with one warning, `UnsupportedIndexedMatch`,
discussed under The Agda version.

## Statement

Lean's statement, as `#check` prints it, and the definitions it rests on,
quoted from Mathlib v4.33.1, `Mathlib/SetTheory/Lists.lean`, lines 57 to 60, 67
to 68 and 118 to 131 (without two docstrings and the `deriving DecidableEq` of
line 61):

    @Lists'.Subset.refl : ∀ {α : Type u_1} {l : Lists' α true}, l ⊆ l

    inductive Lists'.{u} (α : Type u) : Bool → Type u
      | atom : α → Lists' α false
      | nil : Lists' α true
      | cons' {b} : Lists' α b → Lists' α true → Lists' α true

    def Lists (α : Type*) :=
      Σ b, Lists' α b

    mutual
      inductive Lists.Equiv : Lists α → Lists α → Prop
        | refl (l) : Lists.Equiv l l
        | antisymm {l₁ l₂ : Lists' α true} :
          Lists'.Subset l₁ l₂ → Lists'.Subset l₂ l₁ → Lists.Equiv ⟨_, l₁⟩ ⟨_,
          l₂⟩

      inductive Lists'.Subset : Lists' α true → Lists' α true → Prop
        | nil {l} : Lists'.Subset Lists'.nil l
        | cons {a a' l l'} :
          Lists.Equiv a a' →
            a' ∈ Lists'.toList l' → Lists'.Subset l l' → Lists'.Subset
            (Lists'.cons a l) l'
    end

The Agda statement, with `a` and `A` generalized variables:

    ⊆-refl : (l : Lists′ A true) → l ⊆ l

It matches up to notation and the implicitness of `l`, which the Agda proofs
take explicitly because they recurse on it.  The Agda file defines the Lean
definitions it needs, as follows:

+  `Lists′`, a `data` type indexed by agda-stdlib's `Bool`, with the
   constructors `atom`, `nil` and `cons′`; `Lists A` is `Σ Bool (Lists′ A)`,
   agda-stdlib's dependent pair, a record with eta, for Lean's `Sigma`, a
   structure; and `cons`, `toList` and `ofList` clause for clause as in Lean.
+  `Equiv` and `_⊆_`, in an Agda `mutual` block of two `Set`-valued data types
   for Lean's two `Prop`-valued inductive types.  Lean's `⊆` is the class
   `HasSubset` with the instance `Lists'.instHasSubsetTrue`, which unfolds to
   `Lists'.Subset`; the Agda file names the relation `_⊆_` directly.  The
   constructors `Lists'.Subset.nil` and `Lists'.Subset.cons` are renamed
   `⊆-nil` and `⊆-cons`, since Agda does not let the constructor `cons` share
   its name with the function `cons`; `refl` shares its name with the
   constructor of `_≡_`, and Agda tells them apart by type.
+  Lean's membership `a' ∈ l'.toList`, the inductive `List.Mem` with
   constructors `head` and `tail`, is agda-stdlib's `_∈_` from
   `Data.List.Membership.Propositional`, that is, `Any (a′ ≡_)` with
   `here refl` and `there`; the two are isomorphic.  Lean's `List.Subset`,
   `∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂`, is agda-stdlib's `_⊆_` on lists (renamed `_⊆ᴸ_`),
   `∀ {x} → x ∈ xs → x ∈ ys`.

## Tier

`#print axioms` prints `[propext, Quot.sound]`, so the entry is T1.  The term
of `Subset.refl` is the following:

    Eq.mpr (id (congrArg (fun _a => _a ⊆ _a) (Eq.symm (of_toList l))))
      (ofList_subset (List.Subset.refl l.toList))

It rewrites `l` as `ofList (toList l)` and applies `ofList_subset` to the
reflexivity of list inclusion, which depends on no axiom.  The axioms come from
the two lemmas, as follows:

+  `Lists'.of_toList` depends on `propext`, through the `simp` and `simpa` of
   its proof (`eq_self`, `true_and`, `heq_eq_eq`).
+  `Lists'.ofList_subset` depends on `propext` and `Quot.sound`: `propext`
   through `simp` and through `Lists'.to_ofList`, and `Quot.sound` through
   `List.cons_subset`, the `simp` lemma that splits `head :: tail ⊆ l₂`, which
   cites `forall_congr`, which is proved by `funext`.

Neither Agda proof uses an axiom.

## What the kernel term needed

The export holds 167 declarations: 20 inductive types (`Bool`, `Lists'`,
`Sigma`, `List`, `List.Mem`, `Eq`, `HEq`, `Nat`, `PUnit`, `PProd`, `PULift`,
`False`, `True`, `And`, `Or`, `Iff`, `Decidable`, the classes `HasSubset` and
`Membership`, and the mutual block of `Lists.Equiv` and `Lists'.Subset`, which
counts once), 88 definitions, 53 theorems, the 4 constants of `Quot`, and the
axioms `propext` and `Quot.sound`.  Re-checked in Lean's kernel with its
diagnostics on (the probe in
[`../nat-gcd-succ/notes.md`](../nat-gcd-succ/notes.md), Remarks), 6 of its 141
theorems and definitions made the kernel reduce a recursor that admits K-like
reduction, all of them `Eq.rec`: `Lists'.of_toList` 10 times,
`Lists'.noConfusion` 3, `Lists'.toList.eq_2`, `Lists'.to_ofList` and
`eq_of_heq` 2 each, and `Lists'.cons'.noConfusion` once.  Proof irrelevance was
not measured, for the reason `nat-gcd-succ`'s notes give.  The term uses no
`WellFounded` and no `Acc`: `toList` and `ofList` are structural recursions,
compiled to `Lists'.brecOn` and `List.brecOn`.  By feature, as follows:

+  `nested-and-mutual-inductives`: the block `Lists.Equiv` with `Lists'.Subset`
   is exported as one inductive declaration with two types and two recursors,
   `Lists.Equiv.rec` and `Lists'.Subset.rec`, each with two motives
   (`numMotives` 2), one per type, and four minor premises, one per constructor
   of either type.  No declaration of the export refers to either recursor: the
   proof uses the constructors only (`Subset.nil`, `Subset.cons` and
   `Equiv.refl` in `ofList_subset`), and its inductions are on `Lists'` and
   `List`.  The Agda file translates the block as a `mutual` block, and writes
   Lean's recursor by mutual pattern matching, `Equiv-rec` and `Subset-rec` in
   one `mutual` block of two functions over the same two motives and four minor
   premises; since Lean's block is a pair of propositions its motives must land
   in `Prop`, while the Agda motives land in any `Set ℓ`.  The Agda weakening
   lemma `⊆-weaken`, an induction on a proof of `⊆` alone, shows the difference
   in use: in Lean it would go through `Lists'.Subset.rec` and have to supply a
   motive for `Lists.Equiv` too, while Agda's pattern matching on `_⊆_` carries
   the `Equiv` proof without recursing on it.
+  `k-and-uip`: two of the six declarations need K-like reduction.
   `Lists'.of_toList` generalizes the index, since Lean's `induction` tactic
   needs it to be a variable: its proof is `Lists'.rec` with the motive
   `fun b l => ∀ (h : true = b), let l' := Eq.symm h ▸ l; ofList l'.toList = l'`,
   and in the cases `nil` and `cons'` the proof `h : true = true` is a bound
   variable, so the kernel reduces `Eq.symm h ▸ nil` to `nil` only by K-like
   reduction, which replaces `Eq.symm h`, of type `true = true`, by
   `Eq.refl true`.  `eq_of_heq` checks `rfl : cast h a = a` for a variable
   `h : α = α`, uniqueness of identity proofs on a universe; it reaches the
   term through `Lists'.noConfusion`, `Lists'.cons'.inj`, `List.mem_cons` and
   the compiled matcher of `toList`, `Lists'.toList.match_1`.  In
   `Lists'.toList.eq_2` and `Lists'.to_ofList` the reductions are in that
   matcher, which casts along `Eq.symm h` and `Eq.symm (eq_of_heq h)` for its
   index equation; applied to a constructor, as there, these are closed proofs
   (`Eq.symm (Eq.refl true)`, `Eq.symm (eq_of_heq (HEq.refl _))`) that reach
   `Eq.refl` by unfolding, so ordinary reduction suffices.  The reductions in
   the two `noConfusion` functions were not read further.  The Agda versions
   need no K; see The Agda version for the two ways they avoid it.
+  `large-elimination`: `Eq.symm h ▸ l` in `of_toList` eliminates `Eq` into the
   type `Lists' α true`; `Lists'.noConfusion` eliminates `Eq` into `Sort u_1`;
   and `eq_of_heq` uses `cast`.  The direct Agda proof eliminates `_≡_`, which
   is in `Set`, by `subst (Lists′ A)`.
+  `structure-eta`: `Lists'.to_ofList` holds at `head :: tail` only because the
   kernel rewrites `(ofList (head :: tail)).toList`, through `Lists'.cons`, a
   `match` on the pair `head`, that is, `Sigma.casesOn head`; with `head` a
   variable of type `Lists α`, the kernel reduces it by expanding `head` into
   `⟨head.1, head.2⟩`, the structure-eta rule, and identifies the result with
   `head` by eta again.  The same conversion is Mathlib's `Lists'.toList_cons`,
   proved by `rfl`, and the cons step of `to_ofList` alone,
   `(ofList (head :: tail)).toList = head :: (ofList tail).toList`, is accepted
   by `rfl` at the pin.  The Agda `to-ofList` relies on the same rule:
   `cons x l` is `cons′ (proj₂ x) l`, and `(proj₁ x , proj₂ x)` is `x` because
   `Σ` is a record with eta.  The manifest did not list this feature; it is
   added.
+  `projections-and-let`: 14 projection expressions, the first fields of
   `PProd` in the structural recursions of `Lists'`, `List` and `Nat` (8),
   `And` (3), and one each of `HasSubset`, `Membership` and `PULift`, the first
   two being `⊆` and `∈` themselves; and 14 `let` expressions, 8 of them in
   `of_toList`, the `let l' := Eq.symm h ▸ l` of its motive in each place the
   motive is instantiated.  The eta expansion above also has the kernel
   introduce the projections `head.1` and `head.2`, which are not in the term.
   The direct Agda proof keeps Lean's `let` in the type of `of-toList-gen`; `⊆`
   and `∈` are not class projections in Agda.
+  `universe-levels`: one universe parameter, `u_1`, for `α : Type u_1`, which
   becomes `A : Set a`; `Lists α` lives in `Type (max 0 u)`, which Agda writes
   `Set a`, since `Bool : Set` and `0ℓ ⊔ a` is `a`.  110 of the export's 147
   constants other than inductive types have universe parameters, and `imax`
   occurs in the types of `Lists'.toList.match_1`, of the elimination and
   no-confusion machinery of `Lists'` (`ctorElimType`, `ctorElim`, `atom.elim`,
   `nil.elim`, `cons'.elim`, `noConfusion`) and of `List.noConfusion`, `congr`,
   `congrFun'`, `funext` and `implies_congr`.
+  `literals`: constructor indices as `Nat` literals.  `Bool.ctorIdx` (`0`,
   `1`) and `Lists'.ctorIdx` (`0`, `1`, `2`) number the constructors for the
   no-confusion machinery, and `of_toList` disposes of the case `atom`, where
   `h : true = false`, with `noConfusion_of_Nat Bool.ctorIdx h`, whose type is
   `Bool.rec False True (Nat.beq 0 1)`: the kernel evaluates `Nat.beq` on the
   literals `0` and `1`, one of its accelerated operations, to reach `False`.
   The manifest did not list this feature; it is added.  In Agda the case is
   the absurd pattern `()` on `true ≡ false`, by the disjointness of
   constructors, with no numbers involved.
+  `decidable-and-noncomputable`: `Lists'.noConfusionType` compares the
   constructor indices of its two arguments with `dite` on `Nat.decEq`, which
   computes.  Nothing is `noncomputable`.  Agda's constructor disjointness is
   built into unification.  The manifest did not list this feature; it is
   added.
+  `axioms`: `propext` and `Quot.sound`, as under Tier.

All four features the manifest listed are used; `k-and-uip`, `structure-eta`,
`literals`, `decidable-and-noncomputable` and `universe-levels` are added.  The
last three come from machinery Lean generates for every inductive type
(`ctorIdx`, `noConfusionType`, the compiled matchers); the first two from the
proofs Mathlib wrote.

## Instance arguments

The statement carries one instance argument, `Lists'.instHasSubsetTrue` for `⊆`
on `Lists' α true`.  The proof adds `List.instHasSubset` for list inclusion and
`List.instMembership` for `∈`.  In Agda the three are a data type,
agda-stdlib's `_⊆_` on lists and agda-stdlib's `_∈_`, with no instance
arguments.

## The Agda version

One file, `agda/ListsSubsetRefl.agda`, profile CC
(`--safe --cubical-compatible`), with the definitions above, two proofs of the
statement, and the mutual recursor.

The idiomatic proof, `⊆-refl`, is an induction on the list, matched at index
`true` directly: `⊆-refl nil = ⊆-nil` and
`⊆-refl (cons′ x l) = ⊆-cons (refl _) (here refl) (⊆-weaken (⊆-refl l))`, where
`⊆-weaken`, by induction on the proof of `⊆`, adds an element to the right-hand
list.  The case `atom` is excluded by unification, because `false` and `true`
are different constructors, and no K is needed.  Agda 2.8.0 accepts the
function under `--cubical-compatible` with a warning,
`UnsupportedIndexedMatch`: the clauses rely on the injectivity of `true` in an
index, so they "will not compute when applied to transports" in Cubical Agda.
The warning is common to indexed families under these flags: agda-stdlib 2.3
and the cubical library 0.9 both turn it off for all their modules in their
`.agda-lib` files (`--warning=noUnsupportedIndexedMatch`,
`-WnoUnsupportedIndexedMatch`).  The file keeps the warning visible rather than
adding a flag the profile does not name; `make corpus-check` does not print it,
since it shows Agda's output only for files that fail.

The direct proof, `⊆-refl-direct`, follows the kernel term: it rewrites `l` as
`ofList (toList l)` with `of-toList` and applies `ofList-⊆`, Lean's
`ofList_subset`, to the identity on membership proofs, Lean's
`List.Subset.refl`.  `ofList-⊆` places each element with `to-ofList`, Lean's
`to_ofList`.  `of-toList` is `of-toList-gen refl`, the translation of Mathlib's
generalized statement, transport and `let` included; where Lean's kernel used
K-like reduction on `h : true = true`, the Agda proof uses `subst-true`:
transport along any proof of `true ≡ true` is the identity, because `Bool` has
decidable equality and so, by Hedberg's theorem (agda-stdlib's `Decidable⇒UIP`,
applied to `Data.Bool.Properties._≟_`), any two such proofs are equal.  This is
the strategy the gap catalog gives for profile CC, a proof that the type is a
set wherever Lean used K, here for `Bool` (M3-9, [#34]).  It needs no matching
at a constructor index, and draws no warning.

The mutual recursor, `Equiv-rec` and `Subset-rec`, is described under
`nested-and-mutual-inductives` above.  The term of `Subset.refl` does not apply
it; it is there to show what a term that did would become.

What the translation removes: the generalization of the index and its transport
(idiomatic proof), the instances `HasSubset` and `Membership`, the numbered
constructors and `noConfusion_of_Nat`, and the axioms.  What it makes explicit:
in the direct proof, the uniqueness of identity proofs on `Bool` that Lean's
kernel used silently.

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 441,284 |
| Export, records | 8,355 |
| Export, expression records | 7,042 |
| Export, declarations | 167: 20 inductive, 88 def, 53 thm, 4 quot, 2 axiom |
| Agda, lines per file | 198, of which 90 are code and the rest comments and blank lines |
| Agda, check time | 1.2 seconds (Agda 2.8.0, no `.agdai` files of the entry) |

## Remarks

The export was made on 2026-10-07 with lean4export v4.33.0 (format 3.1.0) under
Lean v4.33.1 (commit `819816b`) and Mathlib v4.33.1, the pins of
[`docs/pinning.md`](../../docs/pinning.md), from Mathlib's cache.  Two runs
gave the same bytes (SHA-256 `ed1013f3...3997d599ef`).

The entry was chosen for the mutual block, and the block turned out to be the
part of the term that needed the least: the proof never recurses on it.  What
the term did need, K-like reduction for a transport along `true = b`, comes
from the indexed family `Lists'` and from Lean's `induction` tactic, which
cannot take a constructor as an index; for the gap catalog's entry `k-and-uip`
(M1-5, [#5]) it is an instance of K-like reduction in Mathlib's mathematics, on
a type with decidable equality, where the reduction can be replaced by
Hedberg's theorem.  For the translator, the recursor of a mutual block is M2-5
([#19]) and the block itself M2-4 ([#18]); the `UnsupportedIndexedMatch`
warning bears on whether translated code meant to be imported from Cubical
Agda, profile CU, may match at constructor indices.

[#5]: https://github.com/formalverification/lean2agda/issues/5
[#7]: https://github.com/formalverification/lean2agda/issues/7
[#18]: https://github.com/formalverification/lean2agda/issues/18
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#34]: https://github.com/formalverification/lean2agda/issues/34
