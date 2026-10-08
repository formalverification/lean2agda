<!-- File: corpus/nat-gcd-succ/notes.md -->

# Nat.gcd_succ

The entry for well-founded recursion, translated by issue M1-7 ([#7]): the
definition of `Nat.gcd` together with its equation at a successor,
`Nat.gcd_succ`, both in Lean's core library, in `Init.Data.Nat.Gcd`.  One Agda
file, `agda/NatGcdSucc.agda`, checks under profile CC
(`--safe --cubical-compatible`).

The issue asked this entry to document that Lean's kernel needs K-like
reduction for the defining equation of `Nat.gcd` to hold definitionally.  That
is the reason Lean4Less gives for not treating `Nat.gcd` as a kernel primitive;
Lean4Less is Deducteam's translator from Lean into Lean⁻, Lean's theory without
definitional proof irrelevance and K-like reduction (M3-1, [#26]).  At the
pinned Lean, v4.33.1, the premise no longer holds, as follows:

+  Since Lean v4.27.0, a definition by well-founded recursion on a `Nat`
   measure is compiled through `WellFounded.Nat.fix`, a fixpoint that recurses
   on a natural number larger than the measure, its fuel.  The fuel is
   `WellFounded.Nat.eager (m + 1)`, which is
   `if Nat.beq n n = true then n else n` and stays stuck while `n` contains a
   variable, so on variables neither side of the equation unfolds; if they did,
   they would carry different fuel.  The equation does not hold definitionally
   at all: the kernel rejects `fun x y => Eq.refl _` as a proof of it.
   `Nat.gcd_succ` is a theorem, proved through `funext`.
+  Computing the definition, `Nat.gcd._unary` (the kernel computes `Nat.gcd`
   itself on literals with GMP and never unfolds it there), reduces only
   `Nat.rec`, `Bool.rec`, `Decidable.rec` and `PSigma.rec`, and no recursor
   that admits K-like reduction.
+  K-like reduction remains in the term's closure in one place, `eq_of_heq`,
   which lemmas about `≤` cited by the termination proofs use, not the
   equation; that keeps the feature `k-and-uip` on this entry.
+  For a hand-written copy of `gcd` compiled the old way, through
   `WellFounded.fix` and `Acc`, the pin's kernel does accept the equation by
   conversion, but without any reduction that admits K; what identifies the two
   sides is proof irrelevance.

The evidence is in "What the kernel term needed" below.

## Statement

Lean's statement, as `#check` prints it, and the definition it is about (lines
35 to 40 of `Init/Data/Nat/Gcd.lean`, with the `if` on one line and without the
`decreasing_by` proof):

    Nat.gcd_succ : ∀ (x y : Nat), x.succ.gcd y = (y % x.succ).gcd x.succ

    def gcd (m n : @& Nat) : Nat :=
      if m = 0 then n else gcd (n % m) m
      termination_by m

The Agda statements, one for each of the file's two definitions of `gcd`:

    gcd-succ      : (x y : ℕ) → gcd (suc x) y ≡ gcd (y % suc x) (suc x)
    gcd-fuel-succ : (x y : ℕ) → gcd-fuel (suc x) y ≡ gcd-fuel (y % suc x) (suc
    x)

They match Lean's up to notation.  `Nat.succ` is `suc`, Lean's `Nat` is
agda-stdlib's `ℕ` (both the builtin natural numbers), and Lean's `%`,
`HMod.hMod` through the instance `Nat.instMod`, is agda-stdlib's `_%_` from
`Data.Nat.Base`, which takes an instance argument `NonZero n` that the pattern
`suc x` supplies.  The two `%` agree on every pair of numbers, as functions
computed by different definitions: Lean's `Nat.mod` through `Nat.modCore`,
Agda's through the builtin `mod-helper`.  The `gcd` of the statement is the
file's own translation of Lean's definition, not agda-stdlib's
`Data.Nat.GCD.gcd`, which compares its arguments first and recurses through an
auxiliary `gcd′`; the file does not prove the two equal (the entry
`nat-gcd-self` is stated over agda-stdlib's).

## Tier

`#print axioms` prints `[Quot.sound]` for `Nat.gcd_succ` and nothing for
`Nat.gcd`, so the equation is T1 (its only axioms are among `propext` and
`Quot.sound`) and the definition T0 (no axiom).  The axiom comes from function
extensionality.  Lean proves `gcd_succ` by `rw [gcd]; rfl`: the rewrite uses
the equation lemma
`Nat.gcd.eq_1 : gcd m n = if m = 0 then n else gcd (n % m) m` (private,
generated on demand), which goes through `Nat.gcd.eq_def` and
`Nat.gcd._unary.eq_def` to `WellFounded.Nat.fix_eq`, and `rfl` closes
`(if succ x = 0 then y else …) = …` by computation.  `WellFounded.Nat.fix_eq`
proves `fix h F x = F x (fun y _ => fix h F y)` by
`congrArg (F x) (funext fun _ => funext fun _ => Nat.fix.go_congr ..)`, and
`go_congr` uses `funext` too; `funext` is proved from `Quot.sound`.  (At this
version `WellFounded.fix_eq`, the unfolding lemma of the older fixpoint,
depends on no axiom; it is not in the term.)

Neither Agda proof uses an axiom.  Function extensionality is not needed
because `gcd`'s step applies its recursive argument at one point, so an
equality of the two results at that point is enough; Lean's lemmas are stated
for an arbitrary step `F`, for which it is not.

## What the kernel term needed

The export holds 220 declarations: 23 inductive types (among them `Nat`, `Eq`,
`HEq`, `PSigma`, `Nat.le`, `Decidable`, `Bool`, `False`, `True`, `And`, `Or`
and the classes `LT`, `LE`, `OfNat`, `HAdd`, `Add`, `HMod`, `Mod`, `HSub`,
`Sub`), 127 definitions, 65 theorems, the 4 constants of `Quot`, and the axiom
`Quot.sound`.  `Nat.gcd` is `fun m n => Nat.gcd._unary ⟨m, n⟩`, and
`Nat.gcd._unary` is `WellFounded.Nat.fix` applied to the measure
`fun ⟨m, _⟩ => m` and a step that does `PSigma.casesOn` on the pair and
`if h : m = 0 then n else rec ⟨n % m, m⟩ _`.  `WellFounded.Nat.fix h F x` is
`go (eager (h x + 1)) x _`, where `go` recurses by `Nat.rec` on the fuel and
its zero case, unreachable, eliminates `False`.  The export contains no `Acc`,
no `Acc.rec`, no `WellFounded` (the type) and no `WellFounded.fix`.

How much K-like reduction the term needs was measured in Lean's own kernel,
with its diagnostics on.  K-like reduction applies only to the recursors of
inductive propositions with one constructor and no fields, such as `Eq.rec`,
which the kernel marks `k = true`.  The kernel counts, under the recursor's
name, every reduction of a recursor that `whnf_core` performs, whether by
K-like reduction or by the ordinary rule on a constructor (`type_checker.cpp`
at v4.33.1, lines 526 to 531; in `inductive.h`, lines 90 to 92, a recursor with
`k = true` passes through `to_cnstr_when_K` first).  So the count of `k = true`
recursors over-counts: a zero proves that no K-like reduction was performed,
and a positive count has to be read.  Two controls confirmed this at the pin:
`cast h a = a` by `rfl`, for a variable `h : Nat = Nat`, which only K-like
reduction accepts, counted one `Eq.rec`, and so did `cast (Eq.refl Nat) a = a`,
which the ordinary rule accepts.  The probe under Remarks re-checks every
theorem and definition of the closure under fresh names.  Of the 192 theorems
and definitions of this export, one made the kernel reduce a recursor that
admits K-like reduction: `eq_of_heq`, with two reductions of `Eq.rec`.
`Nat.gcd_succ` itself reduced `Nat.rec` 10 times, `Decidable.rec`, `Bool.rec`
and `PSigma.rec` once each; `WellFounded.Nat.fix_eq` reduced only `Nat.rec`,
and `go_congr` only `Nat.rec` and `Bool.rec`.  Proof irrelevance was not
measured: the kernel's diagnostics count reductions, not the conversions that
proof irrelevance decides, and the elaborator's switch
`Meta.Config.proofIrrelevance` is no substitute, since a control showed that
with it off `isDefEq` still identifies `h₁ = h₁` with `h₁ = h₂` for two proofs
`h₁ h₂` of one proposition.  By feature, as follows:

+  `k-and-uip`: one use, in `eq_of_heq`, which the term contains because of the
   termination proofs, not the equation.  Its proof checks `rfl : cast h a = a`
   for a variable `h : α = α` with `α : Sort u`, which the kernel accepts only
   by K-like reduction, that is, by uniqueness of identity proofs on a
   universe.  It reaches the term through the termination proofs:
   `WellFounded.Nat.fix._proof_1` cites `Nat.lt_of_lt_of_le`, which cites
   `Nat.le_trans`, whose compiled `match` on the indexed family `Nat.le` uses
   `eq_of_heq` for index unification (as do the matchers of `Nat.pred_le_pred`,
   `Nat.succ_le_succ` and `Nat.ble_eq_true_of_le`).  Neither Agda version needs
   it: they match on `_<_` only to discard the impossible case, and cite
   agda-stdlib's lemmas.  A mechanical translation of the closure would have to
   translate `eq_of_heq`, which has no proof under profile CC (it is uniqueness
   of identity proofs on a universe), unless it replaces the compiled matchers
   that cite it by Agda's own pattern matching, as the hand translations do;
   that choice belongs to M2-5 ([#19]), and the declarations that need UIP on
   types to the study of M6-5 ([#55]).  The manifest expected this feature from
   the gcd equation, on the strength of Lean4Less's README; at this pin the
   equation does not use it, and the feature stays only for `eq_of_heq` (see
   the next paragraphs and Remarks).
+  `large-elimination`: `False.elim` into the motive `Nat`, in
   `WellFounded.Nat.fix.go`'s zero case
   (`(Nat.not_succ_le_zero _ hfuel).elim`), and `cast`, an elimination of `Eq`
   into a type, in `eq_of_heq`.  `Acc` does not occur.  The Agda versions
   eliminate agda-stdlib's `Acc`, which is in `Set`, by pattern matching, and
   write the zero case as an absurd pattern.
+  `literals`: the literals `0` and `1` (`m = 0`, `h x + 1`), and the kernel's
   arithmetic on literals: `Nat.gcd`, `Nat.mod` and `Nat.beq` are among the
   fifteen operations the kernel computes with GMP (`reduce_nat`), so on
   literal arguments it never unfolds `Nat.gcd`.  `@[extern "lean_nat_gcd"]` is
   the compiler's replacement and plays no part in the kernel.
   `Nat.gcd._unary` is not accelerated, and computing
   `Nat.gcd._unary ⟨12, 18⟩ = 6` by `rfl` made the kernel reduce `Nat.rec` 3
   times (once per step of Euclid's algorithm), `Bool.rec` 5, `Decidable.rec` 4
   and `PSigma.rec` 4; `Nat.gcd._unary ⟨1000000007, 998244353⟩ = 1` by `decide`
   checks too.  The helper `WellFounded.Nat.eager` keeps the fuel from
   unfolding until it is a literal (see the opening section).  Agda has builtin
   `_%_` and no builtin `gcd`; both Agda versions compute
   `gcd 1000000007 998244353 ≡ 1` by `refl` in about 2 seconds of checking
   (Agda 2.8.0), the `Acc` version only with agda-stdlib's
   `<-wellFounded-fast`, since with the plain `<-wellFounded`, which builds
   each accessibility proof in unary, the check did not finish in 120 seconds.
+  `decidable-and-noncomputable`: `if h : m = 0` is
   `dite (m = 0) (instDecidableEqNat m 0)`, and `instDecidableEqNat` is
   `Nat.decEq`, which matches on `Nat.beq n m` with the equation
   `h : n.beq m = b` and computes.  The `rfl` step of `gcd_succ` decides
   `succ x = 0` by unfolding `Nat.decEq` and `Nat.beq` on `succ x` and `0`.
   Nothing in the term is `noncomputable`.  The Agda versions split on `zero`
   and `suc` instead; agda-stdlib's `m ≟ 0`, a `Dec` built from `_≡ᵇ_`, would
   decide the same way.
+  `axioms`: `Quot.sound`, through `funext` in `WellFounded.Nat.fix_eq` and
   `WellFounded.Nat.fix.go_congr` (see Tier).  The Agda versions need none.
+  `projections-and-let`: 13 projection expressions and 15 `let` expressions,
   none in `gcd`'s own definition: the projections are the first fields of
   `PProd` in `Nat.brecOn` (4) and the fields of the classes `LT`, `LE`,
   `OfNat`, `HAdd`, `Add`, `HMod`, `Mod`, `HSub` and `Sub`, through which `<`,
   `+` and `%` reach `Nat.lt`, `Nat.add` and `Nat.mod`; the `let`s are in
   lemmas and in the compiled recursions of definitions, such as `Nat.le_trans`
   and `Nat.eq_of_beq_eq_true._f`.  The Agda version uses agda-stdlib's
   operations directly.
+  `universe-levels`: the statement and the definition have no universe
   parameter, but 75 of the export's 197 constants other than inductive types
   do, `WellFounded.Nat.fix.{u, v}` among them, instantiated at the levels of
   the pair type and of `Nat`, and `imax` occurs in the types of
   `WellFounded.Nat.fix.go`, `fix_eq`, `go_congr`, `funext`, `congr` and
   `congrFun'`.  The Agda version lives in `Set`.

Two constructions outside the gap catalog are recorded for the translator: the
packing of a function of two arguments into one of a pair (`Nat.gcd._unary` on
`PSigma`, taken apart by `PSigma.casesOn`), because `WellFounded.Nat.fix` takes
one argument, and the fuel-based fixpoint itself.  The Agda versions keep the
two arguments.

Lean4Less's README says that "for the equation
`Nat.gcd (succ y) x = Nat.gcd (mod x (succ y)) (succ y)` to hold definitionally
in Lean, the typechecker must use K-like reduction".  The paragraph was written
on 2025-01-12, when Lean's current release was v4.15.0 (2025-01-04).  `Nat.gcd`
has the same source there as at v4.33.1 (`if m = 0`, `termination_by m`); what
changed is its compilation.  `src/Lean/Elab/PreDefinition/WF/Fix.lean` does not
use `WellFounded.Nat.fix` at v4.26.0, and at v4.27.0 (released 2026-01-23) uses
it whenever the relation is a `Nat` measure (`isNatLtWF`), and
`WellFounded.fix`, which recurses on `Acc`, otherwise; `Init/WF.lean` defines
`WellFounded.Nat.fix` from v4.27.0 on.  Three measurements at the pin bear on
the README's claim, as follows:

+  On the pin's `Nat.gcd` the claim's condition does not arise: the equation is
   not definitional (the kernel rejects `Eq.refl` as its proof over variables),
   and nothing about `gcd` reduces a recursor that admits K.
+  On a hand-written copy compiled the old way,
   `gcdOld := WellFounded.fix Nat.lt_wfRel.wf gcdOldF` (curried, where the old
   compiler packed the two arguments into a pair), the pin's kernel accepts
   `∀ x y, gcdOld (x + 1) y = gcdOld (y % (x + 1)) (x + 1)` by `Eq.refl`,
   reducing `Nat.rec` 11 times, `WellFounded.rec` twice, `Acc.rec`, `Bool.rec`
   and `Decidable.rec` once each, and no recursor that admits K.  After the one
   `Acc.rec` step the two sides are `Acc.rec` applications whose major premises
   are different proofs of the same `Acc` proposition, and `Acc.rec` on a proof
   that is not a constructor does not reduce, so what identifies them is
   definitional proof irrelevance.  For this copy, in this kernel, the equation
   holds by proof irrelevance, not by K-like reduction.
+  Computing the copy on literals is where `Acc` costs: at `1071 462` the
   kernel reduced `Acc.rec` 1,072 times, `Nat.rec` 664,298, `Or.rec` 331,380
   and `Eq.rec` 4 (from `subst e` in the proof of `Nat.lt_wfRel.wf`), where the
   copy through `WellFounded.Nat.fix` reduced `Nat.rec` 5 times, `Bool.rec` 7
   and `Decidable.rec` 6.  Whether those 4 `Eq.rec` reductions were K-like is
   not settled here.

Lean⁻ has neither proof irrelevance nor K-like reduction, so the README's
conclusion, that the old equation fails there, does not depend on which of the
two Lean used; the reason it states does not match what this kernel does with
the copy.  None of this tests the old compiler's own term or an old kernel.
Whether Lean4Less still refuses `Nat.gcd` at the pin needs a run of Lean4Less,
whose own toolchain (v4.28.0-rc1) is already past v4.27.0; that is M3-1
([#26]).  If the pin's closed computation also needs no proof irrelevance,
which the counter cannot show, Lean⁻ computes the pin's `Nat.gcd` by unfolding
as Lean does, and the reason to refuse it as a primitive is gone.

## Instance arguments

The statement carries one instance argument, twice: `instHMod Nat Nat.instMod`
for `%`.  The definition adds `instOfNatNat 0` for the literal,
`instDecidableEqNat m 0` for the `if`, and the termination relation
`InvImage (· < ·)` carries `instLTNat`; `WellFounded.Nat.fix` adds `instHAdd`
and `instAddNat` for `h x + 1`.  In Agda, `_%_` and `m%n<n` take an irrelevant
instance argument `.{{NonZero n}}`, found by instance search for `n = suc _`;
nothing else is an instance.

## The Agda version

One file, `agda/NatGcdSucc.agda`, profile CC (`--safe --cubical-compatible`),
with two translations of the definition, each with its equation, as follows:

+  The idiomatic one, `gcd`, is well-founded recursion on the first argument by
   pattern matching on agda-stdlib's `Acc _<_ m`, the way agda-stdlib writes
   its own `gcd′` in `Data.Nat.GCD`: `gcd-acc zero n _ = n` and
   `gcd-acc m@(suc _) n (acc rs) = gcd-acc (n % m) m (rs (m%n<n n m))`, started
   from `<-wellFounded-fast m`.  The equation `gcd-succ` is an instance of
   `gcd-acc-irrelevant`, which proves by induction on `Acc` that the result
   does not depend on the accessibility proof: `<-wellFounded-fast (suc x)`
   computes to `acc _`, so the left side unfolds once by computation to
   `gcd-acc` at the right arguments with a different accessibility proof.
   Lean's kernel would get the irrelevance for free from definitional proof
   irrelevance if its `gcd` recursed on `Acc`; Agda's `Acc` is in `Set`, so it
   is a lemma, by an induction that needs neither K nor function
   extensionality.
+  The direct one, `gcd-fuel`, follows the kernel term: `gcd-go` recurses on
   fuel, with the zero case an absurd pattern, and
   `gcd-fuel m n = gcd-go (suc m) m n ≤-refl`.  As in Lean, the two sides of
   the equation unfold with different fuel; `gcd-go-congr`, Lean's `go_congr`
   for this step, proves by induction on the fuel that the fuel does not
   matter, without `funext`.  The bound `m < fuel` is passed along and never
   matched on: matching `s≤s` would rely on the injectivity of `suc` in an
   index, which `--cubical-compatible` accepts with the warning
   `UnsupportedIndexedMatch` (the function would not compute on transports in
   Cubical Agda), so the predecessor is taken by agda-stdlib's `s≤s⁻¹`.

agda-stdlib's `Induction.WellFounded.FixPoint.unfold-wfRec` packages the
idiomatic argument for definitions by `All.wfRec`, but it does not fit Lean's
shape: its hypothesis on the step leaves the smaller argument implicit, and
with Lean's pair and measure (`_<_ on proj₁`) the second component of that
argument cannot be inferred, so the module application fails with unsolved
constraints.  The pair is not needed in Agda, and the two-argument `Acc`
recursion is shorter.

What the translation removes: the pair and `PSigma.casesOn`, `Decidable` and
`Nat.beq` behind the `if`, the `eager` gadget, the axiom, and `eq_of_heq` with
its use of K.  What it makes explicit: the irrelevance of the accessibility
proof (idiomatic) or of the fuel (direct), each a short induction.

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 527,857 |
| Export, records | 9,897 |
| Export, expression records | 8,131 |
| Export, declarations | 220: 23 inductive, 127 def, 65 thm, 4 quot, 1 axiom |
| Agda, lines per file | 113, of which 40 are code and the rest comments and blank lines |
| Agda, check time | 2.2 seconds (Agda 2.8.0, no `.agdai` files of the entry) |

## Remarks

The export was made on 2026-10-07 with lean4export v4.33.0 (format 3.1.0) under
Lean v4.33.1 (commit `819816b`), the pins of
[`docs/pinning.md`](../../docs/pinning.md).  Two runs gave the same bytes
(SHA-256 `8a308395...b0de33a3`).

The measurement of K recursors used the following probe, run from `translator/`
as `lake env lean` on a scratch file; it walks the same closure lean4export
exports (it found 192 theorems and definitions for `Nat.gcd_succ`, the export's
count) and re-checks each declaration in the kernel under a fresh name.  On
2026-10-07 it printed, for the four entries of [#7], that `Nat.gcd_self` (251
re-checked) and `Nat.gcd_succ` (192) reduced a K recursor only in `eq_of_heq`,
`Lists'.Subset.refl` (141) in six declarations (see that entry's notes), and
`List.reverse_reverse` (21) in none.

```lean
import Mathlib.SetTheory.Lists
open Lean Elab Command

/-- The theorems and definitions that `n` depends on, `n` included. -/
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

/-- Re-check each theorem and definition in the closure of `n` in the kernel
with its diagnostics on; list those whose check reduced a recursor with
`k = true`. -/
elab "#k_reductions " id:ident : command => do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut hits : Array String := #[]
  for c in (closure env id.getId).toList do
    let decl? := match env.find? c with
      | some (.thmInfo v) => some (Declaration.thmDecl { v with name := c ++ `_recheck })
      | some (.defnInfo v) => some (Declaration.defnDecl { v with name := c ++ `_recheck })
      | _ => none
    let some decl := decl? | continue
    checked := checked + 1
    match (env.toKernelEnv.enableDiag true).addDecl {} decl with
    | .error _ => hits := hits.push s!"{c}: rejected"
    | .ok kenv =>
      let ks := kenv.diagnostics.unfoldCounter.toList.filter fun (r, _) =>
        match env.find? r with
        | some (.recInfo v) => v.k
        | _ => false
      unless ks.isEmpty do hits := hits.push s!"{c}: {ks}"
  let report := "\n".intercalate hits.toList
  logInfo m!"{id.getId}: {checked} re-checked; {hits.size} reduced a K recursor\n{report}"

#k_reductions Nat.gcd_succ
```

The comparison with the old compilation, the rejected `rfl` and the two
controls used the following file, run the same way; `#kernel_rfl` adds
`theorem name : ∀ xs, lhs = rhs := fun xs => Eq.refl rhs` to the kernel with
the diagnostics on, and prints whether the kernel accepted it and the recursors
it reduced.

```lean
import Lean
open Lean Elab Command Meta

def gcdOldF (m : Nat) (rec : (k : Nat) → k < m → Nat → Nat) (n : Nat) : Nat :=
  if h : m = 0 then n else rec (n % m) (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) m

def gcdOld : Nat → Nat → Nat := WellFounded.fix Nat.lt_wfRel.wf gcdOldF
def gcdNew : Nat → Nat → Nat :=
  WellFounded.Nat.fix (motive := fun _ => Nat → Nat) id gcdOldF

elab "#kernel_rfl " name:ident " : " stmt:term : command => do
  let (ty, val) ← liftTermElabM do
    let t ← instantiateMVars (← Term.elabTerm stmt (some (mkSort .zero)))
    let v ← forallTelescope t fun xs body => do
      let some (_, _, r) := body.eq? | throwError "not an equation"
      mkLambdaFVars xs (← mkEqRefl r)
    pure (t, v)
  let env ← getEnv
  let decl := Declaration.thmDecl
    { name := name.getId, levelParams := [], type := ty, value := val }
  match (env.toKernelEnv.enableDiag true).addDecl {} decl with
  | .error _ => logInfo m!"{name.getId}: rejected"
  | .ok kenv =>
    let recs := kenv.diagnostics.unfoldCounter.toList.filter fun (c, _) =>
      match env.find? c with
      | some (.recInfo _) => true
      | _ => false
    logInfo m!"{name.getId}: accepted; recursors reduced {recs}"

#kernel_rfl oldMid : gcdOld 1071 462 = 21
#kernel_rfl newMid : gcdNew 1071 462 = 21
#kernel_rfl oldEq : ∀ x y : Nat, gcdOld (x + 1) y = gcdOld (y % (x + 1)) (x + 1)
#kernel_rfl pinEq : ∀ x y : Nat, Nat.gcd (x + 1) y = Nat.gcd (y % (x + 1)) (x + 1)
#kernel_rfl kOnly : ∀ (h : Nat = Nat) (a : Nat), cast h a = a
#kernel_rfl iotaOnly : ∀ (a : Nat), cast (Eq.refl Nat) a = a
```

The first finding, with the second measurement of the Lean4Less paragraph (the
old copy's equation holds by proof irrelevance), is for the gap catalog's
entries `k-and-uip`, `proof-irrelevance` and `literals` (M1-5, [#5]), which
leave this question to this entry; the second, that `FixPoint` does not fit a
pair with a measure, is for M3-7 ([#32]), which translates well-founded
recursion; and the treatment of `Nat.gcd` in the operation table of M3-6
([#31]) no longer needs to assume that its equation rests on K.

[#5]: https://github.com/formalverification/lean2agda/issues/5
[#7]: https://github.com/formalverification/lean2agda/issues/7
[#19]: https://github.com/formalverification/lean2agda/issues/19
[#26]: https://github.com/formalverification/lean2agda/issues/26
[#31]: https://github.com/formalverification/lean2agda/issues/31
[#32]: https://github.com/formalverification/lean2agda/issues/32
[#55]: https://github.com/formalverification/lean2agda/issues/55
