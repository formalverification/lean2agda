<!-- File: corpus/multiset-map-map/notes.md -->

# Multiset.map_map

The entry for a quotient, translated by issue M1-8 ([#8]).  Mathlib
declares `Multiset.map_map` in `Mathlib.Data.Multiset.MapFold`; it is
about `Multiset`, which `Mathlib.Data.Multiset.Defs` defines as the
quotient of `List` by permutation, and about `Multiset.map`, defined by
`Quot.liftOn`.  Two Agda files translate it: `agda/MultisetMapMap.agda`
under profile CC (`--safe --cubical-compatible`), with Lean's quotient
primitives as a module parameter, and `agda/MultisetMapMapCubical.agda`
under profile CU (`--safe --cubical --guardedness`), with the cubical
library's set quotients.

## Statement

Lean's statement, as `#check` prints it:

    @Multiset.map_map : ∀ {α : Type u_2} {β : Type u_1} {γ : Type u_3} (g : β → γ) (f : α → β) (s : Multiset α),
      Multiset.map g (Multiset.map f s) = Multiset.map (g ∘ f) s

The Agda statement, the same in both files, with `A`, `B` and `C`
generalized variables:

    map-map : (g : B → C) (f : A → B) (s : Multiset A) → map g (map f s) ≡ map (g ∘ f) s

They match up to notation and up to the definitions of `Multiset` and
`map`, which are as follows:

+  Lean: `Multiset α = Quotient (List.isSetoid α)`, which unfolds to
   `Quot (Setoid.r (List.isSetoid α))`, the quotient by `List.Perm`; and
   `map f s = Quot.liftOn s (fun l => ↑(l.map f)) (fun _ _ p =>
   Quot.sound (p.map f))`, where `↑` is `Multiset.ofList`, which is
   `Quot.mk _`.
+  CC: `Multiset A = Quot _↭_`, the parameter record's quotient by
   agda-stdlib's propositional permutation `_↭_`, with no setoid in
   between; `map f = lift squash (λ l → ⟦ List.map f l ⟧) (λ _ _ p →
   sound (map⁺ f p))`, where `⟦_⟧` is `mk _↭_`.
+  CU: `Multiset A = List A / Perm`, the cubical library's set quotient
   by `Perm`, which transcribes Lean's `List.Perm`; `map f = SQ.rec
   squash/ (λ l → [ List.map f l ]) (λ _ _ p → eq/ _ _ (Perm-map f p))`.

The cubical library has no permutation relation on lists, so the CU
file writes Lean's, constructor for constructor (`nil`, `cons`, `swap`
of the first two elements, `trans`), and proves Lean's `List.Perm.map`
by induction on it.  The CC file uses agda-stdlib's `_↭_` (`refl`,
`prep`, a `swap` under a permutation of the tails, `trans`) and its
`map⁺`.  Both relations define permutation; the files do not prove them
equivalent, since neither needs to.  `List.map` and function composition
are each library's own and agree with Lean's clause by clause.  Lean's
`List.map_map`, `map g (map f l) = map (g ∘ f) l`, is the cubical
library's `map-∘` and the symmetric form of agda-stdlib's `map-∘`.  The
cubical library also has finite multisets as a higher inductive type,
`FMSet` in `Cubical.HITs.FiniteMultiset`, with a constructor that swaps
two heads; the CU file uses the set quotient instead, because it mirrors
Lean's definition and is the shape every Lean quotient takes.

## Tier

`#print axioms` prints `[propext, Quot.sound]` for `Multiset.map_map`
and for `Multiset.map`, so the entry is T1.  The axioms come in as
follows:

+  `Quot.sound` through `Multiset.map`, whose proof that `List.map f`
   respects permutations, `Multiset.map._proof_1`, is
   `Quot.sound (List.Perm.map f p)`; and again through `funext`, which
   Lean proves from `Quot.sound` and which `List.filterMap_eq_map` uses,
   since `List.Perm.map` rewrites by `filterMap (some ∘ f) = map f`.
+  `propext` through `simp`, which closes and rewrites goals with
   `eq_self` and `eq_true` in `List.map_map`, `List.filterMap_eq_map`
   and `List.Perm.filterMap` (the seed entry's notes explain the
   mechanism); and through `Option.some.injEq`, the injectivity rewrite
   that the last two cite, which is proved by `Eq.propIntro`, that is,
   by `propext`.

The export's axiom declarations are the same two.  That cross-check
matters at this pin: `#print axioms` can leave axioms out of the set it
prints for a constant whose dependencies form a cycle, such as an
inductive type and its constructors (Lean issue [lean4#15226], open),
and the export, which holds every constant the declaration reaches,
does not depend on that walk.

The statement is constructive, and so are both Agda proofs: the CC file
uses `sound`, its parameter record's counterpart of `Quot.sound`, and
nothing standing for `propext` or `funext`; the CU file uses the
constructor `eq/`.

## What the kernel term needed

The export holds 83 declarations: 11 inductive types (`Equivalence`,
`Setoid`, `Eq`, `List`, `List.Perm`, `PUnit`, `PProd`, `Option`, `True`,
`Iff`, `HEq`), the 4 quotient primitives (`Quot`, `Quot.mk`,
`Quot.lift`, `Quot.ind`), 32 definitions, 34 theorems, and the axioms
`Quot.sound` and `propext`.  Most of it proves `List.Perm.map`, through
`List.Perm.filterMap`, `List.filterMap_eq_map`, `funext`, and the
injectivity of `Option.some` (`Option.some.inj`, `Option.noConfusion`,
`eq_of_heq`, `cast`).

Which of Lean's definitional rules the check relied on was measured in
Lean's own kernel.  The probe under Remarks re-checks each of the
closure's 66 theorems and definitions under a fresh name with the
kernel's diagnostics on, which count, by name, every definition the
kernel unfolds and every recursor and quotient primitive it reduces.
Two declarations reduce `Quot.lift` (next section).  One reduces a
recursor that admits K-like reduction: `eq_of_heq`, two reductions of
`Eq.rec`.  The second count over-counts, since it includes ordinary
reductions on a constructor: of two controls, `cast h a = a` for a
variable `h : Nat = Nat`, which only K-like reduction accepts, and
`cast (Eq.refl Nat) a = a`, which the ordinary rule accepts, each counts
one `Eq.rec`.  A zero is conclusive, and a positive count has to be
read in the term.

By feature, the term uses the following, each named by its entry in the
gap catalog ([`docs/foundations/gap-catalog.md`][catalog]):

+  [`quotients`][cat-quotients]: `Multiset` is `Quot`, `Multiset.ofList` is
   `Quot.mk`, `Multiset.map` is `Quot.lift` (through `Quot.liftOn`), its
   soundness is `Quot.sound`, and `map_map` is `Quot.ind` (through
   `Quot.inductionOn`).  The kernel reduces `Quot.lift` five times, listed in
   the next section; the CC file makes three of them explicit.
+  [`axioms`][cat-axioms]: `propext` and `Quot.sound`, as the Tier section
   says.  The CC file takes `Quot.sound` as the field `sound` of its parameter;
   the CU file needs no parameter.
+  [`impredicative-prop`][cat-impredicative-prop]:
   `Option.noConfusion.{u_1, u}` rewrites by `Eq.ndrec` at the level
   `imax (u+1) u_1`, and `Option.some.inj` uses it, through
   `Option.some.noConfusion`, at `u_1 = 0`, for a proposition, where
   `imax (u+1) 0` is `0` and not the maximum.  A translation of the closure
   has to specialize the constant, that is, emit a copy of it at that
   instantiation with the `imax` resolved ([#28]).  It goes with the
   injectivity of `Option.some`, which neither Agda file proves (next item).
+  [`k-and-uip`][cat-k-and-uip]: one use, measured as above, in
   `eq_of_heq`, which `Option.noConfusion` calls and the injectivity
   lemmas `Option.some.inj` and `Option.some.injEq` reach;
   `List.Perm.filterMap` and `List.filterMap_eq_map`, both in the proof
   of `List.Perm.map`, cite `Option.some.injEq`.  The proof of
   `eq_of_heq` applies `HEq.rec` to the minor premise `fun _ => rfl`,
   whose expected type is `(h : α = α) → cast h a = a`; `cast h a`
   reduces to `a` only by K-like reduction of `Eq.rec` on the variable
   proof `h`.  Since `α : Sort u`, that is uniqueness of identity proofs
   on a universe, which profile CC cannot prove and univalence refutes
   (`not` gives `Bool = Bool` a second proof), so a translation of the
   whole closure would have no CC counterpart for `eq_of_heq` and would
   have to avoid it.  Neither Agda file proves `Option.some` injective:
   both prove `List.Perm.map` by induction on the permutation.
+  [`large-elimination`][cat-large-elimination]: `cast` eliminates `Eq` into
   `Sort u` (`Eq.rec` with the motive `fun x _ => x`), and `Option.some.inj`
   uses it at `Type`, through `eq_of_heq.{u+1}`.  It goes with the injectivity
   proof.
+  [`universe-levels`][cat-universe-levels]: three level parameters, one for
   each of `α`, `β` and `γ` (`#check` names them `u_2`, `u_1` and `u_3`, the
   export `u_1`, `v` and `u_2`).  `Multiset α` lives in the universe of `α`
   because `Quot r : Sort u` for `α : Sort u`, whatever the relation; Agda's
   quotient of `A : Set a` by `R : A → A → Set r` lives in `Set (a ⊔ r)`, and
   both permutation relations live at the level `a` of the lists, so
   `Multiset A : Set a` as in Lean.  `imax` also appears in the types of
   `funext`, `congr` and `congrFun'`, which the term instantiates only at
   successor levels, where it is the maximum.
+  [`projections-and-let`][cat-projections-and-let]: `Setoid.r` is a
   projection, and the kernel reduces `Setoid.r (List.isSetoid α)` to
   `List.Perm`, unfolding the instance `List.isSetoid = ⟨Perm, Perm.eqv⟩`, when
   `Multiset.map._proof_1` passes a proof of `Setoid.r … l₁ l₂` to
   `List.Perm.map`, and again for the proof it returns.  Agda quotients by the
   relation itself, so neither projection nor reduction appears.  Three `let`
   expressions, `eqv` and `extfunApp` in `funext` and `this` in `eq_of_heq`, go
   with those proofs.  `PProd` projections appear in the structural recursions
   `List.brecOn` compiles, as in the seed entry, and Agda's pattern matching
   replaces them.

Reading the term finds no use of definitional proof irrelevance other
than the K-like reduction above, and no literals, structure eta, or
`Decidable` instances (`instDecidableEqList.match_1` in the export is
the matcher that the compiled `List.map` shares with that instance, not
the instance).  Proof irrelevance is the one rule the kernel's
diagnostics do not count, since it is a conversion, not a reduction; as
the seed entry says, Lean4Less (M3-1, [#26]) will settle it
mechanically.

### Definitional computations of `Quot.lift`

Lean's kernel reduces `Quot.lift f h (Quot.mk r a)` to `f a`.  In the
CC file, `Quot.lift` is the field `lift` of a module parameter, which
does not compute, and the rule is the field `lift-β`, a propositional
equation (`lift-β uip f h x : lift uip f h (mk R x) ≡ f x`).
Re-checked in the kernel with its diagnostics on (the probe under
Remarks), exactly two of the closure's 66 theorems and definitions
reduce `Quot.lift`, and none reduces `Quot.ind`: `Multiset.map_map`,
three times, and `funext`, twice.  The five reductions are as
follows:

1.  `Multiset.map_map`'s term is
    `Quot.inductionOn s (fun x => map g (map f x) = map (g ∘ f) x)
    (fun l => congr_arg (Quot.mk _) (List.map_map …))`.  The function's
    result has the type `⟦List.map g (List.map f l)⟧ =
    ⟦List.map (g ∘ f) l⟧`, and the kernel accepts it as the motive at
    `Quot.mk _ l`, `map g (map f ⟦l⟧) = map (g ∘ f) ⟦l⟧`, by three
    reductions, each after unfolding `Multiset.map` and `Quot.liftOn`
    and followed by unfolding `Multiset.ofList` to `Quot.mk`.  The CC
    file makes each a step of an equational proof by `map-β`, the rule
    at `map`'s arguments, as follows:
    1.  `map f ⟦l⟧ ⇝ ⟦List.map f l⟧`, inside the left side:
        `cong (map g) (map-β f l)`;
    2.  `map g ⟦List.map f l⟧ ⇝ ⟦List.map g (List.map f l)⟧`, the left
        side: `map-β g (List.map f l)`;
    3.  `map (g ∘ f) ⟦l⟧ ⇝ ⟦List.map (g ∘ f) l⟧`, the right side:
        `sym (map-β (g ∘ f) l)`.
2.  `funext`, reached through `Multiset.map._proof_1`, `List.Perm.map`
    and `List.filterMap_eq_map`, is
    `id (f = g) (congrArg extfunApp (Quot.sound h))`, where
    `extfunApp q x = Quot.liftOn q (fun f => f x) _`.  The argument's
    type is `extfunApp (Quot.mk eqv f) = extfunApp (Quot.mk eqv g)`,
    which the kernel accepts as `f = g` by one reduction on each side,
    under the binder `x`: `extfunApp (Quot.mk eqv f)` is
    `fun x => Quot.liftOn (Quot.mk eqv f) (fun f => f x) _`, which
    reduces to `fun x => f x`, and that is `f` by eta.  Neither Agda
    file makes these two reductions explicit, since neither proves
    `List.Perm.map` through `funext`.  Lean's proof of `funext` could
    not be replayed with rewrites anyway: `lift-β` applies under the
    binder only pointwise, giving `(x : A) → extfunApp (mk R f) x ≡ f x`,
    and passing from that to `extfunApp (mk R f) ≡ f` is `funext`
    itself.  The `set-ext` entry therefore takes `funext` as a parameter
    of its own.

The CU file makes none of the five explicit: `SQ.rec` computes on
`[ l ]` by definition, so `cong [_] (map-∘ g f l)` has the type of the
motive at `[ l ]` without a rewrite, as Lean's term does.  In Lean, the three
reductions of item 1 are checked by `rfl` at the pin, for instance
`Multiset.map g (Multiset.map f ↑l) = ↑((l.map f).map g) := rfl`.

## Instance arguments

None in the statement.  The term's one instance is `List.isSetoid α`
(`instance isSetoid (α) : Setoid (List α) := .mk Perm (Perm.eqv α)`, in
Lean's `Init.Data.List.Perm`), an ordinary argument of `Quotient` and
`Setoid.r` after elaboration.  Neither Agda file has a setoid, so
neither has an instance argument or a record in its place.

## The Agda version

**`agda/MultisetMapMap.agda`**, profile CC, takes one module parameter,
`Q : Quotients`, a record in `Setω` whose fields quantify over levels,
so that one record serves every quotient, as Lean's `Quot` does.  Its
fields are `Quot`, `mk`, `lift`, `ind`, `sound`, `lift-β` and `squash`.
Three of them differ from a word-for-word rendering of Lean's
primitives, such as the gap catalog's probe
[`P24QuotParam`][p24], each because Lean's `Prop` is proof irrelevant
and Agda's `Set` is not, as follows:

+  `ind`'s motive takes values in `Ω p = Σ (Set p) Irrelevant`, the
   propositions among the types of `Set p`, which is how the file reads
   Lean's `Prop` (encoding A of [#27], h-propositions in `Set` with a
   proof that any two elements are equal; the gap catalog's
   [`proof-irrelevance`][cat-proof-irrelevance] entry uses the two
   letters the other way round).  With a motive in all of
   `Set`, `ind (λ x → x , refl)` proves that every quotient map has a
   section, `(q : Quot R) → Σ A (λ x → mk R x ≡ q)`; a scratch module
   checked that under `--safe --cubical-compatible`, and the proof is
   that one line.  That section is Mathlib's `Quot.out`
   (`Mathlib/Data/Quot.lean`, line 361), defined with `Classical.choice`
   (its axioms at the pin are `[Classical.choice]`), so a T1 declaration
   translated against such a record would rest on a T2 principle.
   Encoding B of [#27] would give the motive a sort in Agda's `Prop`
   instead; but `map_map`'s motive is an equation, and Lean's `Eq`,
   which eliminates into `Type`, stays in `Set` under either encoding,
   so this entry cannot tell the encodings apart.
+  `lift` asks for `UIP B`, that its target is a set, which every Lean
   type is.  Lean's `Quot.lift` needs no such argument, but the cubical
   library's set quotients, the model the CU file instantiates the
   record with, eliminate only into sets.  The library's type quotients
   `_/ₜ_` (`Cubical.HITs.TypeQuotients`) eliminate into any type, as Lean's
   `Quot.lift` does, but they are not sets, so an equation between their
   elements is not a proposition and cannot be an `ind` motive; the
   record follows the set quotients because `map_map`'s motive is such
   an equation.
+  `squash : UIP (Quot R)` says that a quotient is a set.  Lean has it
   for every type; here it makes an equation between multisets a
   proposition, hence a motive for `ind`, and makes `Multiset B` a target
   for `lift`.

The relation `R` may be any `Set`-valued relation, not only an
`Ω`-valued one: a Lean inductive proposition such as `List.Perm` read
as an inductive family in `Set` has distinct proofs (agda-stdlib's
`_↭_` does), and the quotient does not need them identified.  A
translator using encoding A would emit an `Ω`-valued relation (a
truncation of its translation of `List.Perm`, say), which the record
accepts too; this file uses agda-stdlib's `_↭_`, so the translator's
`Multiset` and the oracle's will differ in the relation, not in the
record.  `Quot R` lives in `Set (a ⊔ r)`, which is above Lean's
universe when the relation lives above the carrier, as the translation
of a Lean relation that quantifies over a larger universe would.

The price of the three changes is two obligations per use, both
discharged here by `squash`: a proof that the target of each `lift` is
a set, and a proof that the motive of each `ind` is a proposition.
Under profile K, `UIP` holds for every type by pattern matching, which
meets the first obligation everywhere and the second whenever the
motive is an equation; a motive that translates an inductive
proposition still needs a proof that it is one, which is the `Prop`
encoding's business ([#27]).  Under profile CC the `UIP` proofs are the
`k-and-uip` obligations of [#34].  Two cases deserve a name.  Lean
often lifts into `Prop` (`Multiset.Mem` does), and under CC
`UIP (Ω p)` should follow from `PropExt` and `FunExt` by Hedberg's
argument (a type whose path spaces have constant endofunctions is a
set), which this entry neither needs nor proves.  A lift into a
universe has no such proof, and under univalence a universe is not a
set, so a Lean declaration that lifts a quotient into `Type` cannot be
translated against this record.

The record is satisfiable without classical principles: the last
section of the CU file builds it from the cubical library's set
quotients (`Quot R = A / R`, `lift` by `SQ.rec`, `ind` by
`SQ.elimProp`, `sound` by `eq/`, `squash` from `squash/`, and `lift-β`
by reflexivity, since `SQ.rec` computes on points), with the cubical
library's conversions between paths and agda-stdlib's inductive
equality, and so obtains the CC theorem in cubical Agda as well.

The proof is Lean's: `ind` with the motive packaged with `squash`, and
for a list `l` the image of agda-stdlib's `map-∘` under `⟦_⟧`, between
the three rewrites by `map-β` listed above.  `Multiset.ofList` becomes
`⟦_⟧`, `Quot.liftOn` becomes `lift` with its arguments reordered, and
Lean's `List.Perm.map` becomes agda-stdlib's `map⁺`, proved by
induction on the permutation, so the file needs neither `funext` nor
`Option.some`'s injectivity.

The corpus has no shared library, so the record stays in the entry's
file, and `set-ext` defines the same `Ω`.  A shared module should
exist: `Ω`, `Quotients`, and the `PropExt` and `FunExt` of `set-ext`
are the parameters every translated module that uses quotients or
extensionality takes, the prelude that [#30] and [#33] produce for the
generated library, and the corpus entries should import it then, so
that the translator's output and the oracle use the same records.

**`agda/MultisetMapMapCubical.agda`**, profile CU, has no parameters.
`Multiset A` is the set quotient `List A / Perm`, `map` is `SQ.rec`,
with `squash/` as the proof that the target is a set and `eq/` for
soundness, and `map-map` is `SQ.elimProp`, Lean's `Quot.ind`, whose
motive is a proposition because `squash/` makes `Multiset C` a set.
The proof needs no rewrite.  The file's last section instantiates the
CC record, as described above, and states the CC theorem for the set
quotient by agda-stdlib's `_↭_`; it imports `MultisetMapMap`, which
Agda checks under that module's own flags, as a cubical module may.

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 236,925 |
| Export, records | 4,700 |
| Export, expression records | 3,986 |
| Export, declarations | 83: 11 inductive, 4 quot, 32 def, 34 thm, 2 axiom |
| Agda, lines per file | `MultisetMapMap.agda` 139, of which 63 are code; `MultisetMapMapCubical.agda` 124, of which 66 are code |
| Agda, check time | 9.3 seconds for the two files (Agda 2.8.0, no `.agdai` files of the corpus) |

The check time is `make corpus-check`'s for the entry: the CC file
first, then the CU file, which loads the CC file's interface.

## Remarks

The export was made on 2026-10-08 with lean4export v4.33.0 (format
3.1.0) under Lean v4.33.1 (commit `819816b`), the pins of
[`docs/pinning.md`](../../docs/pinning.md).  Two runs gave the same
bytes (SHA-256 `c0eddfd3...f56ee790`).

The reduction counts above come from the following probe, run from
`translator/` as `lake env lean` on a scratch file on 2026-10-08.  Its
closure walk is the one lean4export performs, and its re-check is the
kernel's `addDecl` with the diagnostics of `Kernel.Environment.enableDiag`
on; the same method measured the entries of [#7].

```lean
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Set.Defs
open Lean Elab Command

/-- The constants `n` depends on, `n` included, through types, values,
constructors and recursors: the closure lean4export exports. -/
partial def closure (env : Environment) (n : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [n]
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let mut deps := ci.type.getUsedConstants.toList
    if let some v := ci.value? (allowOpaque := true) then
      deps := deps ++ v.getUsedConstants.toList
    match ci with
    | .inductInfo v => deps := deps ++ v.ctors ++ v.all
    | .ctorInfo v => deps := deps ++ [v.induct]
    | .recInfo v => deps := deps ++ v.all
    | _ => pure ()
    todo := deps ++ todo
  return seen

/-- The recursors with `k = true` and the quotient primitives among a
kernel check's reduction counters. -/
def watched (env : Environment) (kenv : Kernel.Environment) : List (Name × Nat) :=
  kenv.diagnostics.unfoldCounter.toList.filter fun (r, _) =>
    r == ``Quot.lift || r == ``Quot.ind ||
      match env.find? r with
      | some (.recInfo v) => v.k
      | _ => false

/-- Re-check every theorem and definition in the closure of `n` in the kernel,
under a fresh name, with diagnostics on; list those whose check reduced a
watched constant. -/
elab "#reductions " nm:ident : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut hits : Array String := #[]
  for c in (closure env nm.getId).toList do
    let decl? := match env.find? c with
      | some (.thmInfo v) => some (Declaration.thmDecl { v with name := c ++ `_recheck })
      | some (.defnInfo v) => some (Declaration.defnDecl { v with name := c ++ `_recheck })
      | _ => none
    let some decl := decl? | continue
    checked := checked + 1
    match (env.toKernelEnv.enableDiag true).addDecl {} decl with
    | .error _ => hits := hits.push s!"  {c}: rejected"
    | .ok kenv =>
      let ws := watched env kenv
      unless ws.isEmpty do hits := hits.push s!"  {c}: {ws}"
  logInfo m!"{nm.getId}: {checked} re-checked\n{"\n".intercalate hits.toList}"

#reductions Multiset.map_map
#reductions Set.ext

-- Controls: K-like reduction only, and the ordinary rule only.
theorem kOnly (h : Nat = Nat) (a : Nat) : cast h a = a := rfl
theorem iotaOnly (a : Nat) : cast (Eq.refl Nat) a = a := rfl
#reductions kOnly
#reductions iotaOnly
```

It printed the following:

```text
Multiset.map_map: 66 re-checked
  funext: [(Quot.lift, 2)]
  eq_of_heq: [(Eq.rec, 2)]
  Multiset.map_map: [(Quot.lift, 3)]
Set.ext: 11 re-checked
  funext: [(Quot.lift, 2)]
kOnly: 3 re-checked
  kOnly: [(Eq.rec, 1)]
iotaOnly: 3 re-checked
  iotaOnly: [(Eq.rec, 1)]
```

K-like reduction, large elimination, an `imax` at a proposition, and
`funext` enter the closure through how Lean's core library proves
`List.Perm.map`, not through `Multiset`: a translator that emits the
whole closure meets all four, while a hand translation that proves the
lemma by induction meets none.  The atlas ([#11]) could count how many
Mathlib declarations reach `eq_of_heq`, and so K-like reduction, through
the injectivity theorems Lean generates for each constructor
(`Option.some.inj`, `Option.some.injEq`), which `simp` rewrites with.

[#7]: https://github.com/formalverification/lean2agda/issues/7
[#8]: https://github.com/formalverification/lean2agda/issues/8
[#11]: https://github.com/formalverification/lean2agda/issues/11
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#28]: https://github.com/formalverification/lean2agda/issues/28
[#30]: https://github.com/formalverification/lean2agda/issues/30
[#33]: https://github.com/formalverification/lean2agda/issues/33
[#34]: https://github.com/formalverification/lean2agda/issues/34
[catalog]: ../../docs/foundations/gap-catalog.md
[cat-axioms]: ../../docs/foundations/gap-catalog.md#axioms
[cat-impredicative-prop]: ../../docs/foundations/gap-catalog.md#impredicative-prop
[cat-k-and-uip]: ../../docs/foundations/gap-catalog.md#k-and-uip
[cat-large-elimination]: ../../docs/foundations/gap-catalog.md#large-elimination
[cat-projections-and-let]: ../../docs/foundations/gap-catalog.md#projections-and-let
[cat-proof-irrelevance]: ../../docs/foundations/gap-catalog.md#proof-irrelevance
[cat-quotients]: ../../docs/foundations/gap-catalog.md#quotients
[cat-universe-levels]: ../../docs/foundations/gap-catalog.md#universe-levels
[lean4#15226]: https://github.com/leanprover/lean4/issues/15226
[p24]: ../../docs/foundations/probes/agda/P24QuotParam.agda
