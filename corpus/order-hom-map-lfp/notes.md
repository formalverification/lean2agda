<!-- File: corpus/order-hom-map-lfp/notes.md -->

# OrderHom.map_lfp

The entry for lattices, translated by issue M1-9 ([#9]): the fixed-point
half of Knaster and Tarski, that the least fixed point of a monotone map
of a complete lattice is a fixed point.  Mathlib declares
`OrderHom.map_lfp` in `Mathlib.Order.FixedPoints`.  One Agda file,
`agda/OrderHomMapLfp.agda`, translates it under profile CC
(`--safe --cubical-compatible`), with Lean's `Prop` read as encoding A of
[#27], the `Ω` of the entries `multiset-map-map` and `set-ext`.

## Statement

Lean's statement, as `#check` prints it:

    @OrderHom.map_lfp : ∀ {α : Type u_1} [inst : CompleteLattice α] (f : α →o α), f (OrderHom.lfp f) = OrderHom.lfp f

The Agda statement, inside `module _ (L : CompleteLattice A ℓ)` and
`module _ (f : OrderHom preorder preorder)`, with `A`, `a` and `ℓ`
generalized variables:

    map-lfp : f ⟨$⟩ (lfp ⟨$⟩ f) ≡ lfp ⟨$⟩ f

Outside the two modules its type is
`(L : CompleteLattice A ℓ) (f : OrderHom (preorder L) (preorder L)) →
f ⟨$⟩ (lfp L ⟨$⟩ f) ≡ lfp L ⟨$⟩ f`, with `preorder L` the lattice's
preorder.  The two match up to notation and up to the records, as
follows:

+  Lean applies a bundled map through a coercion, `DFunLike.coe` with
   the instance `OrderHom.instFunLike`, which unfolds to the projection
   `OrderHom.toFun`; Agda's `_⟨$⟩_` is that projection.
+  Lean's `lfp : (α →o α) →o α` is itself a bundled monotone map, from
   the monotone maps of `α`, ordered pointwise by the instance
   `OrderHom.instPreorder`, to `α`; so is the Agda `lfp`, from the
   preorder `pointwise preorder preorder`.
+  `CompleteLattice`, `PartialOrder` and `Preorder` are records with the
   fields the proof uses, fewer than Lean's classes have (Instance
   arguments, below).  A structure with fewer fields is a weaker
   hypothesis, so the Agda theorem gives Lean's for every structure that
   Lean's classes translate to.

## Tier

`#print axioms` prints `[propext, Quot.sound]`, so the entry is T1.  A
shortest-path search from the declaration through types and values (the
probe of [`../finset-card-image/notes.md`](../finset-card-image/notes.md),
Remarks) finds where each axiom comes in, as follows:

+  `propext` through the statement's own definitions: `OrderHom.lfp`
   (T1, `[propext]`) is a bundled map from monotone maps with the order
   `OrderHom.instPreorder`, which Mathlib builds with `Preorder.lift`
   along the coercion, that is, with `Function.Injective.preorder`, one
   of whose proof fields (`Function.Injective.preorder._proof_1`) cites
   `propext`.
+  `Quot.sound`, and `propext` again, through the proof of
   `map_le_lfp`: `le_sInf_iff`, `le_isGLB_iff`, `IsGLB.lowerBounds_eq`,
   `Set.ext`, and `Set.ext`'s `funext`, which Lean proves from
   `Quot.sound`.

Both come in through proofs, an instance's proof field and a lemma's
proof.  The Agda file needs neither: its pointwise order proves its laws
pointwise, and `map-le-lfp` uses the infimum's law directly where Lean
cites `le_sInf_iff`.  It takes no parameter.  The statement is
constructive, and Lean's own proof, with those two detours removed, is a
constructive proof of it.

## What the kernel term needed

The export holds 446 declarations: 67 inductive types, the 4 quotient
primitives, 257 definitions, 116 theorems, and the axioms `propext` and
`Quot.sound`.  Most of it is not about lattices.  The field
`lt_iff_le_not_ge` of Lean's `Preorder` has a default proof, the tactic
`by intros; rfl`, and Lean keeps that tactic's syntax in the field's
type: the type is `autoParam T Preorder.lt_iff_le_not_ge._autoParam`,
where the second definition is a closed `Lean.Syntax` tree.  The
closure therefore reaches `Lean.Syntax`, `Lean.Name`, `String`, `Char`,
`ByteArray` and its UTF-8 validity, `UInt32`, `BitVec`, `Fin`, the
arithmetic classes `HAdd` to `HPow`, and `Decidable`.  Measured (the
probe under Remarks): of the 514 constants the walk lean4export
performs reaches from `OrderHom.map_lfp`, constructors and recursors
counted, 194 remain when it does not enter `autoParam` and the
`_autoParam` definitions, and `eq_of_heq`, `cast`, `Lean.Syntax`,
`String`, `Char` and `Decidable` are no longer among them; `funext` and
`Quot.lift` still are.  `autoParam α stx` is a reducible definition
whose value is `α`, so a translator that unfolds it emits none of that.

The probe of
[`../multiset-map-map/notes.md`](../multiset-map-map/notes.md), Remarks,
re-checked 347 theorems and definitions in Lean's kernel with its
diagnostics on.  The export holds 373; the other 26 are `String.ofList`,
`Char.ofNat` and what they need, which lean4export adds for a term with
a string literal (here, the syntax tree's), and which
`Expr.getUsedConstants`, the probe's walk, does not report.  Two
declarations reduced a watched constant: `funext`, `Quot.lift` twice,
and `eq_of_heq`, `Eq.rec` twice.  None needed structure eta (the test
of [`../subtype-coe-eta/notes.md`](../subtype-coe-eta/notes.md),
Remarks: 347 checked, none flagged).  By feature, as follows:

+  `impredicative-prop`: three uses, none of them through an `imax`.
   +  `CompleteLattice`'s field `sInf : Set α → α` takes a subset, and
      `Set α = α → Prop` is a type of `Type u_1`, small, because `Prop`
      is.  In Agda a subset of `A` at level `ℓ` is `ℙ A ℓ = A → Ω ℓ`,
      in `Set (a ⊔ suc ℓ)`, and the record must say for which level of
      subsets it has infima.  The file's decision is the level of the
      order, `⋀ : ℙ A ℓ → A`, because the one infimum the proof takes is
      of `{x | f x ≤ x}`, whose values are instances of `_≤_`; the field
      `≤-prop`, that `x ≤ y` is a proposition, makes that predicate a
      subset.  A lattice with infima at a level `p` above `ℓ` would
      serve as well after lifting the predicate (`Level.Lift`); a
      translator has to pick the level of each `sInf` from its uses
      (M3-4, [#29]).  What no level fixes is a subset defined by
      quantifying over the subsets themselves: it lives at `suc p` and
      cannot be passed to the `⋀` of level `p`.  That is the essentially
      impredicative case the gap catalog says must be reported.
   +  The infimum's law, Lean's field `isGLB_sInf s : IsGLB s (sInf s)`,
      says that `sInf s` is the greatest element of
      `lowerBounds s = {x | ∀ ⦃a⦄, a ∈ s → x ≤ a}`, a subset whose
      values quantify over `α` and stay in `Prop`.  In Agda that subset
      lives at `a ⊔ ℓ`, above the subsets `⋀` takes.  The record avoids
      it by taking the law's two halves, Lean's lemmas `sInf_le` and
      `le_sInf`, as its fields `⋀-lower` and `⋀-greatest`.
   +  `OrderHom.instPreorder` orders maps by `∀ x, f x ≤ g x`, again a
      proposition quantifying over `α`; the Agda `pointwise` order lives
      at `a ⊔ ℓ′`, so `lfp`'s source preorder sits a level above its
      target.
   The kernel never writes these levels: it computes
   `imax (u+1) 0 = 0` when it types a `∀` over `α` into `Prop`, so the
   term has no `imax` here.  The export's only `imax` is in the type of
   `funext`, instantiated at successor levels, where it is the maximum.
   A translator has to compute the level of every proposition (M3-4,
   [#29]) whether or not an `imax` marks it.
+  `projections-and-let`: the statement applies two bundled maps through
   `DFunLike.coe` and the instance `OrderHom.instFunLike`, which unfold
   to the projection `OrderHom.toFun`, and reaches the order of the
   lattice through instance projections (`PartialOrder.toPreorder` and
   others, next section).  80 declarations of the export contain a
   projection expression and 14 a `let`, the latter all in the `Nat`
   arithmetic of the string machinery (`Nat.mod_lt`, `Nat.le_trans`).
   In Agda the projections are record fields and `_⟨$⟩_`.
+  `axioms`: `propext` and `Quot.sound`, as the Tier section says; the
   Agda file uses neither.
+  `quotients`: through `funext` only, whose proof reduces `Quot.lift`
   twice, as in `set-ext`.  The Agda file needs no quotient.
+  `k-and-uip` and `large-elimination`: `eq_of_heq`, the K-like
   reduction on a universe that
   [`../multiset-map-map/notes.md`](../multiset-map-map/notes.md) reads,
   and the `cast` it uses.  Both are reached only through the
   `autoParam` (measured above): `Preorder.mk`'s field type cites the
   syntax tree, whose names are `String`s, whose UTF-8 validity proofs
   use `Nat.decLe`, whose lemmas match on `Nat.le` through `eq_of_heq`.
+  `literals`, `decidable-and-noncomputable` and
   `nested-and-mutual-inductives`: only through the `autoParam` too.
   The syntax tree holds string literals (`"Lean"`, `"Parser"`,
   `"Tactic"`, `"tacticSeq"`, `"intros"`, `"rfl"`), the validity of
   `Char` holds `Nat` literals (`1114112`, the bound of Unicode), the
   checks use `Decidable` instances (`instDecidableAnd`,
   `Decidable.decide`), and `Lean.Syntax` is a nested inductive type,
   its nodes holding an `Array Syntax`.
+  `universe-levels`: one level parameter, `u_1`, for `α : Type u_1`;
   the Agda file has `a` for `A` and `ℓ` for the order, and the
   pointwise order at `a ⊔ ℓ′`, as above.

The manifest listed `impredicative-prop`, `projections-and-let` and
`axioms`; the other seven are added by the rule the other translated
entries follow, that a feature counts when the exported closure uses
it, with the evidence above saying which come only through the
`autoParam`.  Proof irrelevance was not measured, for the reason the
other entries give: the kernel's diagnostics do not count it.

## Instance arguments

The statement has one instance argument, `[inst : CompleteLattice α]`,
and its elaborated type carries 109 occurrences of instance constants,
counted as a tree, of five distinct ones: `OrderHom.instFunLike`,
`OrderHom.instPreorder`, `PartialOrder.toPreorder`,
`ChainCompletePartialOrder.toPartialOrder` and
`ChainCompletePartialOrder.instOfCompleteLattice`.  The proof carries
478, adding `Preorder.toLE`.  The last two show that Lean's instance
search reached the preorder of a complete lattice through
`ChainCompletePartialOrder`, an instance from
`Mathlib.Order.BourbakiWitt`, which `Mathlib.Order.FixedPoints` imports,
rather than through `CompleteLattice`'s own parents; the kernel term
records whichever path the search took.

The Agda file has no instance arguments.  The lattice is a module
parameter, `L : CompleteLattice A ℓ`, as Mathlib's
`variable [CompleteLattice α]` is a section variable, and the map is an
explicit argument.  Each instance projection becomes a record field
(`partialOrder`, then `preorder`), opened, so no instance search runs
and the path Lean's search chose does not matter.  The records carry
these fields:

+  Lean's `CompleteLattice` has 22 fields once its parents are
   flattened: `le`, `lt`, `le_refl`, `le_trans`, `lt_iff_le_not_ge`,
   `le_antisymm`, `sup`, `le_sup_left`, `le_sup_right`, `sup_le`, `inf`,
   `inf_le_left`, `inf_le_right`, `le_inf`, `sSup`, `isLUB_sSup`, `sInf`,
   `isGLB_sInf`, `top`, `le_top`, `bot` and `bot_le`.
+  The Agda `CompleteLattice` has 8: `_≤_`, `≤-refl`, `≤-trans`
   (`Preorder`), `≤-antisym` (`PartialOrder`), and `≤-prop`, `⋀`,
   `⋀-lower` and `⋀-greatest`.  `≤-prop` has no Lean field, since Lean's
   order is `Prop`-valued; the last two are `isGLB_sInf`'s halves.
+  `OrderHom` has two fields on both sides, `toFun` and `monotone'`
   (`monotone` in Agda).

## The Agda version

One file, `agda/OrderHomMapLfp.agda`, profile CC, with no parameters
beyond the lattice and the map.  The definitions and the proof are
Lean's, lemma for lemma:

+  `lfp` is Lean's `lfp`, a bundled monotone map whose function is
   `⋀ {x | f x ≤ x}` and whose monotonicity is Lean's `sInf_le_sInf`
   argument, inlined: from `f ≤ g` pointwise, every `x` with `g x ≤ x`
   has `f x ≤ x`.
+  `lfp-le` is `⋀-lower` (Lean's `lfp_le`, by `sInf_le`), and `le-lfp`
   is `⋀-greatest` (Lean's `le_lfp`, by `le_sInf`).
+  `map-le-lfp` is Lean's `map_le_lfp`, with Lean's step
   `le_sInf_iff.1 ha _ hb : a ≤ b` written `≤-trans ha (lfp-le hb)`.
+  `map-lfp` is Lean's `map_lfp`: `h : f (lfp f) ≤ lfp f` from
   `map-le-lfp` at reflexivity, and the equation by antisymmetry from
   `h` and `lfp-le (monotone f h)`.

Nothing had to be made explicit: the term computes with no quotient,
and its uses of propositional and function extensionality are in the
lemmas the Agda proof does not cite.  The `Ω`, `ℙ` and `_∈_` of
`set-ext` are copied, since the corpus has no shared module (the
`multiset-map-map` notes say why one should exist).

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 964,985 |
| Export, records | 17,286 |
| Export, expression records | 14,232 |
| Export, declarations | 446: 67 inductive, 4 quot, 257 def, 116 thm, 2 axiom |
| Agda, lines per file | 149, of which 74 are code |
| Agda, check time | 0.3 seconds (Agda 2.8.0, no `.agdai` files of the corpus) |

The export is 96.5 percent of the 1 MB limit of
[`../SCHEMA.md`](../SCHEMA.md), so it is committed as `term.ndjson`; a
move of the pin that grows it past the limit turns it into a sidecar.

## Remarks

The export was made on 2026-10-11 with lean4export v4.33.0 (format
3.1.0) under Lean v4.33.1 (commit `819816b`), the pins of
[`docs/pinning.md`](../../docs/pinning.md).  Two runs gave the same
bytes (SHA-256 `59e03619...01283b39`).

The `autoParam` finding generalizes: every Mathlib structure whose field
has a tactic default carries a `Lean.Syntax` tree in that field's type,
so every closure that reaches the structure reaches `Lean.Syntax`,
`String` and their proofs.  `Preorder` sits at the root of Mathlib's
order hierarchy, so every closure that reaches an order does; the
`finset-card-image` export holds 8 `_autoParam` definitions.  The
translator should erase
`autoParam`, and `optParam`, its sibling for default values, by
unfolding them before emitting, and the atlas (M4-1, [#36]) could count
the constants whose closure shrinks most when it does.

The counts above come from the following probe, run from `translator/`
as `lake env lean` on a scratch file on 2026-10-11.  `#without_autoparam`
walks the closure as lean4export does, once in full and once without
entering `autoParam` and the `_autoParam` definitions; `#instances`
counts instance-implicit binders and occurrences of instance constants
in a declaration's type and value, as trees.

```lean
import Mathlib.Order.FixedPoints
open Lean Elab Command

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

/-- The closure of `root`, not entering any constant `skip` accepts. -/
partial def closureSkipping (env : Environment) (root : Name) (skip : Name → Bool) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := [root]
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if seen.contains c || skip c then continue
    seen := seen.insert c
    todo := deps env c ++ todo
  return seen

def isAutoParam (n : Name) : Bool := match n with
  | .str _ s => s == "_autoParam" || n == ``autoParam
  | _ => false

elab "#without_autoparam " nm:ident : command => do
  let env ← getEnv
  let full := closureSkipping env nm.getId (fun _ => false)
  let cut := closureSkipping env nm.getId isAutoParam
  let watch := [``eq_of_heq, ``cast, ``Lean.Syntax, ``String, ``Char, ``Decidable,
    ``Quot.lift, ``funext]
  logInfo m!"{nm.getId}: closure {full.size}, without autoParam {cut.size}; still present: {watch.filter cut.contains}"

/-- Instance-implicit binders, and occurrences of instance constants, in a term. -/
partial def instStats (env : Environment) : Expr → Nat × Nat × List Name
  | .forallE _ t b bi | .lam _ t b bi =>
    let (a1, b1, c1) := instStats env t
    let (a2, b2, c2) := instStats env b
    ((if bi.isInstImplicit then 1 else 0) + a1 + a2, b1 + b2, c1 ++ c2)
  | .app f x =>
    let (a1, b1, c1) := instStats env f
    let (a2, b2, c2) := instStats env x
    (a1 + a2, b1 + b2, c1 ++ c2)
  | .const n _ => if Meta.isInstanceCore env n then (0, 1, [n]) else (0, 0, [])
  | .letE _ t v b _ =>
    let (a1, b1, c1) := instStats env t
    let (a2, b2, c2) := instStats env v
    let (a3, b3, c3) := instStats env b
    (a1 + a2 + a3, b1 + b2 + b3, c1 ++ c2 ++ c3)
  | .mdata _ e | .proj _ _ e => instStats env e
  | _ => (0, 0, [])

elab "#instances " nm:ident : command => do
  let env ← getEnv
  let some ci := env.find? nm.getId | throwError "unknown constant"
  let (bt, ot, nt) := instStats env ci.type
  logInfo m!"type: {bt} instance binders, {ot} instance occurrences, distinct {nt.eraseDups}"
  if let some v := ci.value? (allowOpaque := true) then
    let (bv, ov, nv) := instStats env v
    logInfo m!"value: {bv} instance binders, {ov} instance occurrences, distinct {nv.eraseDups}"

#without_autoparam OrderHom.map_lfp
#instances OrderHom.map_lfp
#eval show CoreM Unit from do
  let fs := getStructureFieldsFlattened (← getEnv) ``CompleteLattice (includeSubobjectFields := false)
  IO.println s!"CompleteLattice: {fs.size} fields"
```

It printed the following:

```text
OrderHom.map_lfp: closure 514, without autoParam 194; still present: [Quot.lift, funext]
type: 1 instance binders, 109 instance occurrences, distinct [PartialOrder.toPreorder,
 ChainCompletePartialOrder.toPartialOrder,
 ChainCompletePartialOrder.instOfCompleteLattice,
 OrderHom.instFunLike,
 OrderHom.instPreorder]
value: 1 instance binders, 478 instance occurrences, distinct [PartialOrder.toPreorder,
 ChainCompletePartialOrder.toPartialOrder,
 ChainCompletePartialOrder.instOfCompleteLattice,
 Preorder.toLE,
 OrderHom.instFunLike,
 OrderHom.instPreorder]
CompleteLattice: 22 fields
```

[#9]: https://github.com/formalverification/lean2agda/issues/9
[#27]: https://github.com/formalverification/lean2agda/issues/27
[#29]: https://github.com/formalverification/lean2agda/issues/29
[#36]: https://github.com/formalverification/lean2agda/issues/36
