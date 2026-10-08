<!-- File: corpus/set-ext/notes.md -->

# Set.ext

The entry for set extensionality, translated by issue M1-8 ([#8]).
Mathlib declares `Set.ext` in `Mathlib.Data.Set.Defs`, where `Set α` is
`α → Prop`; its proof is `funext (fun x ↦ propext (h x))`, so it needs
both extensionality principles, and `funext` is where Lean's quotients
come in.  Two Agda files translate it: `agda/SetExt.agda` under profile
CC (`--safe --cubical-compatible`), with `propext` and `funext` as
module parameters, and `agda/SetExtCubical.agda` under profile CU
(`--safe --cubical --guardedness`), where both are theorems of the
cubical library.

## Statement

Lean's statement, as `#check` prints it:

    @Set.ext : ∀ {α : Type u_1} {a b : Set α}, (∀ (x : α), x ∈ a ↔ x ∈ b) → a = b

The Agda statements, with `A` (and, in the CC file, `p`) generalized
variables:

    ext : {s t : ℙ A p} → ((x : A) → x ∈ s ⇔ x ∈ t) → s ≡ t      -- CC
    ext : {s t : ℙ A} → ((x : A) → x ∈ s ↔ x ∈ t) → s ≡ t        -- CU

They match up to notation and up to the reading of Lean's `Prop`, which
is as follows:

+  Lean: `Set α = α → Prop`, and `x ∈ a` is `Membership.mem a x` for the
   instance `Set.instMembership`, which unfolds to `Set.Mem a x` and then
   to `a x`.  `↔` is `Iff`, a structure with the fields `mp` and `mpr`.
+  CC: Lean's `Prop` is read as `Ω p = Σ (Set p) Irrelevant`, the
   propositions among the types of `Set p` (encoding A of [#27]; the gap
   catalog's [`proof-irrelevance`][cat-proof-irrelevance] entry uses the
   two letters the other way round); Lean's
   `Set α` is `ℙ A p = A → Ω p`, and `x ∈ s = proj₁ (s x)`.  `Iff` is
   agda-stdlib's `_⇔_`, a record with the fields `to` and `from` (and
   two congruence fields that hold trivially for `_≡_`).
+  CU: Lean's `Prop` is the cubical library's `hProp ℓ`, the same idea
   with the library's `isProp`; Lean's `Set α` is the library's
   `ℙ A = A → hProp ℓ`, with its `_∈_`.  `Iff` is a product of the two
   implications, defined in the file, since the library's `_⇔_` (in
   `Cubical.Functions.Logic`) relates elements of `hProp` rather than
   types.

The CC file's `ℙ A p` leaves the level `p` of the propositions free, as
agda-stdlib's `Pred A p` does; the cubical library's `ℙ` fixes it at the
level of `A`.

## Tier

`#print axioms` prints `[propext, Quot.sound]`, so the entry is T1.
`propext` is used by name in the proof; `Quot.sound` comes in through
`funext`, whose own axioms at the pin are `[Quot.sound]`.  `propext` is
not an artifact of the proof: `Set.ext` at a one-element type gives it
back (and gives `funext` for predicates, though not in general).  Under
CC both principles are module parameters, and under CU both are
theorems, `propext` by univalence and `funext` by the interval.  The
statement is constructive.

The export's axiom declarations are the same two, so the set is
complete even though `#print axioms` can leave axioms out at this pin
(Lean issue [lean4#15226], open; the `multiset-map-map` entry's notes
say more).

## What the kernel term needed

The export holds 20 declarations: 3 inductive types (`Iff`,
`Membership`, `Eq`), the 4 quotient primitives, 8 definitions (`Set`,
`outParam`, `Membership.mem`, `Set.Mem`, `Set.instMembership`,
`Quot.liftOn`, `id`, `rfl`), 3 theorems (`congrArg`, `funext`,
`Set.ext`), and the axioms `Quot.sound` and `propext`.

The reductions the kernel performs were measured as for
`multiset-map-map`, by the probe printed in that entry's notes, which
re-checks each theorem and definition of the closure in Lean's kernel
with its diagnostics on.  Of the 11, only `funext` reduces a quotient
primitive (`Quot.lift`, twice), and none reduces a recursor that admits
K-like reduction, which proves that the check uses none.

By feature, the term uses the following, each named by its entry in the
gap catalog ([`docs/foundations/gap-catalog.md`][catalog]):

+  [`quotients`][cat-quotients]: only inside `funext`, which forms the quotient
   of the function space by pointwise equality and computes with `Quot.lift`
   twice (next section).  Neither Agda file has a quotient: CC takes `funext`
   as a parameter, and CU proves it with the interval.
+  [`axioms`][cat-axioms]: `propext` and `Quot.sound`, as the Tier section
   says.  The CC file takes `propext` and `funext` as two records, `PropExt`
   and `FunExt`; the CU file needs neither.
+  [`impredicative-prop`][cat-impredicative-prop] and
   [`universe-levels`][cat-universe-levels]: one level parameter, `u`,
   for `α : Type u`.  Lean's `Set α = α → Prop` lives in `Type u`, the
   universe of `α`, because `Prop` holds every proposition, whatever
   universe it mentions, and is itself a type in `Type`.  Agda has no
   such type: the propositions of `Set p` form `Ω p`, which contains
   `Set p` and so lives in `Set (suc p)`, and `ℙ A p` lives in
   `Set (a ⊔ suc p)`.  The predicates a Lean set usually holds, such as
   equations between elements of `A`, need `p = a`, which is also the
   level the cubical library's `ℙ` fixes; there `ℙ A` lives in
   `Set (suc a)`, one universe above Lean's `Set α`.  This is the
   impredicativity of `Prop` showing up as a level.  Here it does no
   harm, because `Set.ext` holds at every level `p`, so the translation
   can choose one: this use of impredicativity is inessential.
   `funext` is instantiated at `.{u+1, 1}`, so its `imax` is the
   maximum, and the equation `propext (h x)` proves, `a x = b x`, is an
   equation between propositions, `@Eq Prop`, one universe up, which CC
   renders as `_≡_` on `Ω p` and CU as a path in `hProp ℓ`.
+  [`projections-and-let`][cat-projections-and-let]: `Membership.mem` is a
   projection, and the kernel accepts
   `h x : Membership.mem a x ↔ Membership.mem b x` where `propext` expects
   `a x ↔ b x` by unfolding the instance `Set.instMembership = ⟨Set.Mem⟩`,
   projecting, and unfolding `Set.Mem`.  In both Agda files `_∈_` is an
   ordinary function, so the step is a definition unfolding.  `funext`'s
   proof binds `eqv` and `extfunApp` with `let`.

Reading the term finds no use of definitional proof irrelevance, large
elimination, literals or structure eta.  Proof irrelevance is the one
rule the kernel's diagnostics do not count, since it is a conversion,
not a reduction; as the seed entry says, Lean4Less (M3-1, [#26]) will
settle it mechanically.

### Definitional computations of `Quot.lift`

Two, both in `funext`, as the kernel's count above says, and neither
made explicit by the CC file.  Lean proves

    theorem funext {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
        (h : ∀ x, f x = g x) : f = g := by
      let eqv (f g : (x : α) → β x) := ∀ x, f x = g x
      let extfunApp (f : Quot eqv) (x : α) : β x :=
        Quot.liftOn f
          (fun (f : ∀ (x : α), β x) => f x)
          (fun _ _ h => h x)
      change extfunApp (Quot.mk eqv f) = extfunApp (Quot.mk eqv g)
      exact congrArg extfunApp (Quot.sound h)

(`src/Init/Core.lean`, lines 2280 to 2288, at Lean v4.33.1), and its kernel
term is `id (f = g) (congrArg extfunApp (Quot.sound h))`.  The
argument's type is `extfunApp (Quot.mk eqv f) = extfunApp (Quot.mk eqv
g)`, and the kernel accepts it as `f = g` by computing, on each side,
under the binder `x`, as follows:

1.  `extfunApp (Quot.mk eqv f)`, that is,
    `fun x => Quot.lift (fun f => f x) _ (Quot.mk eqv f)`, reduces to
    `fun x => f x`, and that is `f` by eta;
2.  the same for `g`.

At the pin, the first is checked by `rfl`.  A parameter record whose
computation rule is propositional cannot replay this proof: `lift-β`
applies under the binder only pointwise, giving
`(x : A) → extfunApp (mk R f) x ≡ f x`, and passing from that to
`extfunApp (mk R f) ≡ f` is `funext` itself.  Whether `funext` follows
from such a record by another route is not settled here; the CC file
takes `funext` as a parameter and no record of quotient primitives, so
the computations are not rewritten but removed, with the proof that
needed them.  The
`multiset-map-map` entry's closure contains the same two computations,
through `List.Perm.map`, and its CC file avoids them the same way.

## Instance arguments

One, `Set.instMembership α : Membership α (Set α)`, through the `∈`
notation in the statement; the term passes it to `Membership.mem`
explicitly.  Both Agda files replace the class by a plain function
`_∈_`, so there is no instance argument and no record.

## The Agda version

**`agda/SetExt.agda`**, profile CC, takes two module parameters, each a
record in `Setω` with one field, as follows:

+  `PropExt`, whose field
   `propext : {P Q : Ω p} → proj₁ P ⇔ proj₁ Q → P ≡ Q` is Lean's
   `propext : (a ↔ b) → a = b` with `Prop` read as `Ω p`.  The reading is
   necessary, not a matter of style: stated for all of `Set p`, the
   field would be refutable, since `Bool ⇔ ⊤` holds and `Bool ≡ ⊤` would
   make `Bool` a proposition.  A scratch module derived `⊥` from it
   under `--safe --cubical-compatible` in one line: transport the proof
   `λ _ _ → refl` that `⊤` is a proposition back along `Bool ≡ ⊤`, and
   apply the result to `true` and `false`.
+  `FunExt`, whose field is agda-stdlib's `Extensionality a b` at every
   pair of levels; it stands for a theorem of Lean, not an axiom, for
   the reason given above.

With those, `ext h = funext (λ x → propext (h x))` is Lean's term word
for word: `h x : x ∈ s ⇔ x ∈ t` has the type `propext` asks for,
because `x ∈ s` is `proj₁ (s x)` by definition, and `propext (h x)` is
an equation in `Ω p`, as Lean's is in `Prop`.

The records are satisfiable without classical principles: the last
section of the CU file builds `PropExt` from `hPropExt` (with the proof
that agda-stdlib's `Irrelevant T` is itself a proposition) and `FunExt`
from the cubical library's `funExt` for the inductive equality, and so
obtains the CC theorem in cubical Agda.

The corpus has no shared library, so the records stay in the entry's
file, and `multiset-map-map` defines the same `Ω`.  A shared module
should exist, holding `Ω`, `PropExt`, `FunExt` and the `Quotients`
record of `multiset-map-map` (that entry's notes give the argument).

**`agda/SetExtCubical.agda`**, profile CU, has no parameters and two
proofs: `ext`, the idiomatic one, is the cubical library's
`⊆-extensionality`, which states Lean's `Set.ext` for `ℙ` with the two
inclusions; `ext-direct` is Lean's term, `funExt (λ x → ⇔toPath (fst
(h x)) (snd (h x)))`, where `⇔toPath` is `hPropExt` packaged for `hProp`
(propositional extensionality, which univalence proves) and `funExt` is
proved with the interval.  The file's last section instantiates the CC
records, as described above, and states the CC theorem; it imports
`SetExt`, which Agda checks under that module's own flags.

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 29,267 |
| Export, records | 533 |
| Export, expression records | 424 |
| Export, declarations | 20: 3 inductive, 4 quot, 8 def, 3 thm, 2 axiom |
| Agda, lines per file | `SetExt.agda` 69, of which 29 are code; `SetExtCubical.agda` 92, of which 45 are code |
| Agda, check time | 2.4 seconds for the two files (Agda 2.8.0, no `.agdai` files of the corpus) |

The check time is `make corpus-check`'s for the entry: the CC file
first, then the CU file, which loads the CC file's interface.

## Remarks

The export was made on 2026-10-08 with lean4export v4.33.0 (format
3.1.0) under Lean v4.33.1 (commit `819816b`), the pins of
[`docs/pinning.md`](../../docs/pinning.md).  Two runs gave the same
bytes (SHA-256 `af06067a...3f036242`).

That Lean's proof of `funext` does not carry over to a quotient record
with a propositional computation rule bears on [#30], one of whose
tasks is "`Init.Core`'s `funext` check under profile K with no
postulates": the proof needs the rule under a binder, where inserting
rewrites by `lift-β` needs `funext` already.  The simplest course is the
one [#33] already describes, `funext` as a module parameter beside
`propext`, quotients and `Classical.choice`, with the translator
mapping Lean's `funext` to the parameter rather than translating its
proof; whether [#30]'s task should change to say so is open.

[#8]: https://github.com/formalverification/lean2agda/issues/8
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#30]: https://github.com/formalverification/lean2agda/issues/30
[#33]: https://github.com/formalverification/lean2agda/issues/33
[catalog]: ../../docs/foundations/gap-catalog.md
[cat-axioms]: ../../docs/foundations/gap-catalog.md#axioms
[cat-impredicative-prop]: ../../docs/foundations/gap-catalog.md#impredicative-prop
[cat-projections-and-let]: ../../docs/foundations/gap-catalog.md#projections-and-let
[cat-proof-irrelevance]: ../../docs/foundations/gap-catalog.md#proof-irrelevance
[cat-quotients]: ../../docs/foundations/gap-catalog.md#quotients
[cat-universe-levels]: ../../docs/foundations/gap-catalog.md#universe-levels
[lean4#15226]: https://github.com/leanprover/lean4/issues/15226
