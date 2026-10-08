<!-- File: corpus/nat-gcd-self/notes.md -->

# Nat.gcd_self

An entry for constructive arithmetic and lists, translated by issue M1-7
([#7]): the idempotence of `Nat.gcd`, declared in Lean's core library, in
`Init.Data.Nat.Gcd`, and the declaration lyphyser's translator shipped as its
one example.  One Agda file, `agda/NatGcdSelf.agda`, checks under profile CC
(`--safe --cubical-compatible`).  The definition of `Nat.gcd` and its equation
at a successor, which this proof cites, are the entry `nat-gcd-succ`, whose
notes ([`../nat-gcd-succ/notes.md`](../nat-gcd-succ/notes.md)) carry the
measurements this entry shares.

## Statement

Lean's statement, as `#check` prints it:

    Nat.gcd_self : ∀ (n : Nat), n.gcd n = n

The Agda statement:

    gcd-self : (n : ℕ) → gcd n n ≡ n

They match up to notation, with agda-stdlib's `gcd` from `Data.Nat.GCD` for
Lean's `Nat.gcd`.  The two are the same function with different definitions, as
follows:

+  Lean: `gcd m n = if m = 0 then n else gcd (n % m) m`, by well-founded
   recursion on `m`;
+  agda-stdlib: `gcd m n` compares `m` and `n` with `<-cmp`, returns `m` when
   they are equal, and otherwise runs an auxiliary `gcd′` on the larger and the
   smaller, by recursion on `Acc _<_` of the larger, with `gcd′ m zero _ _ = m`
   and `gcd′ m n (acc rec) _ = gcd′ n (m % n) _ _` for `n` a successor.

They agree on every pair of numbers, both being the greatest common divisor
(agda-stdlib proves its own `gcd` is one, `gcd-GCD`), but not definitionally:
on variables neither reduces, and the two recursions take different steps.
agda-stdlib has no lemma `gcd n n ≡ n`, so the file proves it.

## Tier

`#print axioms` prints `[propext, Quot.sound]`, so the entry is T1.  Lean's
proof is `cases n <;> simp [gcd_succ]`.  The term is `Nat.casesAuxOn` on `n`,
with the motive `fun a => n = a → gcd n n = n` that records the case split as
an equation, followed by a `▸` along that equation in each case, as follows:

+  at `0`, `simp` rewrites with `Nat.gcd_zero_right 0` and closes `0 = 0` with
   `eq_self`;
+  at `k + 1`, `simp` rewrites with `Nat.gcd_succ`, `Nat.mod_self`
   (`(k + 1) % (k + 1) = 0`) and `Nat.gcd_zero_left`, and closes
   `k + 1 = k + 1` with `eq_self`.

`propext` comes from `eq_self` (how `simp` closes a goal), from `Nat.mod_self`,
and from `Nat.gcd_zero_right`; `Quot.sound` comes from `Nat.gcd_succ` and
`Nat.gcd_zero_left`, which rewrite `gcd` with its equation lemma `Nat.gcd.eq_1`
(stored as the private `_private.Init.Data.Nat.Gcd.0.Nat.gcd.eq_1`), whose
proof uses `funext` in `WellFounded.Nat.fix_eq` (see `nat-gcd-succ`), and from
`Nat.gcd_zero_right`, which cites those two.  Neither Agda proof uses an axiom.

## What the kernel term needed

The export holds 281 declarations: 24 inductive types (those of `nat-gcd-succ`
and `Iff`), 148 definitions, 103 theorems, the 4 constants of `Quot`, and the
axioms `propext` and `Quot.sound`.  It contains the whole closure of
`Nat.gcd_succ`, and so the definition of `Nat.gcd` through
`WellFounded.Nat.fix`; it contains no `Acc`, no `Acc.rec` and no
`WellFounded.fix`.  Re-checked in Lean's kernel with its diagnostics on (the
probe in `nat-gcd-succ`'s Remarks), 1 of its 251 theorems and definitions made
the kernel reduce a recursor that admits K-like reduction: `eq_of_heq`, as in
`nat-gcd-succ`.  `Nat.gcd_self` itself reduced only `Nat.rec`, 4 times.  Proof
irrelevance was not measured, for the reason `nat-gcd-succ`'s notes give.  By
feature, as follows:

+  `axioms`: `propext` and `Quot.sound`, from the steps named under Tier.  The
   Agda proofs need none.
+  `literals`: the literals `0` and `1`.  At Lean v4.33.1 the `cases` tactic
   produces `Nat.casesAuxOn`, whose minor premises are stated at `0` and
   `n + 1` (a literal and `HAdd.hAdd`) rather than at `Nat.zero` and
   `Nat.succ n`, so the kernel has to identify the literal `0` with `Nat.zero`
   and `n + 1` with `Nat.succ n` when it checks the case split; the proof also
   computes `(k + 1) % (k + 1)` only through the lemma `Nat.mod_self`, not by
   kernel arithmetic, since `k` is a variable.  The definition of `gcd` brings
   in the kernel's accelerated `Nat.gcd`, `Nat.mod` and `Nat.beq`, as in
   `nat-gcd-succ`.  The Agda proofs use `zero` and `suc` patterns, and
   agda-stdlib's `gcd` computes on closed numbers by `refl`.
+  `decidable-and-noncomputable`: only through the definition of `gcd`, whose
   `if m = 0` decides by `instDecidableEqNat`, which computes (see
   `nat-gcd-succ`).  agda-stdlib's `gcd` decides by `<-cmp`, a `Tri` of `<`,
   `≡` and `>`.
+  `large-elimination`: only through the definition of `gcd`, the `False.elim`
   into `Nat` in `WellFounded.Nat.fix.go`'s unreachable case, and `cast` in
   `eq_of_heq`.  The proof's own eliminations of `Eq` (`▸` along the case
   equation) have motives in `Prop`.  The direct Agda proof discards two cases
   with `contradiction`, an elimination of `⊥` into the goal.
+  `k-and-uip`: only `eq_of_heq`, through the termination proofs of `gcd`, as
   in `nat-gcd-succ`.  The Agda proofs need no K.
+  `projections-and-let`: 15 projection expressions and 15 `let` expressions in
   the closure, those of `nat-gcd-succ` and the two projections of `And` that
   define `And.left` and `And.right`; none in the proof itself.
+  `universe-levels`: none in the statement; the closure's polymorphic
   constants and `imax`, as in `nat-gcd-succ`.

Of the features the manifest listed, `axioms` and `literals`, the term uses
both; the other five are added because the term's closure contains the
definition of `gcd` and the lemmas behind it, which the schema counts
(`SCHEMA.md`, Features: the declaration, the definitions it unfolds, and the
lemmas it cites).  What the proof of `gcd_self` itself needs, apart from what
it cites, is the case split with its equation, the two axioms, and the literals
of `Nat.casesAuxOn`.

## Instance arguments

The statement has none.  The proof carries the instances of its arithmetic,
`instHAdd Nat instAddNat` for `k + 1`, `instHMod Nat Nat.instMod` for `%` (in
the rewrite by `Nat.mod_self`), and `instOfNatNat 0` and `instOfNatNat 1` for
the literals, and the definition of `gcd` adds `instDecidableEqNat`.  The Agda
proofs use none: `gcd`, `∣-antisym` and `<-cmp` take no instance argument.

## The Agda version

One file, `agda/NatGcdSelf.agda`, profile CC (`--safe --cubical-compatible`),
with two proofs of the statement, as follows:

+  `gcd-self`, the idiomatic one, is
   `∣-antisym (gcd[m,n]∣m n n) (gcd-greatest ∣-refl ∣-refl)`: `gcd n n` divides
   `n`, `n` divides `gcd n n` because it divides both arguments, and
   divisibility on `ℕ` is antisymmetric.  It is the proof chosen because it
   follows agda-stdlib's own discipline for `gcd`, whose source says that "all
   other properties of `gcd` should be inferable from the 3 core properties",
   `gcd[m,n]∣m`, `gcd[m,n]∣n` and `gcd-greatest`; so it does not depend on how
   `gcd` computes, and it would hold unchanged over any `gcd` with those
   properties, the translation of Lean's included.
+  `gcd-self-direct` computes instead.  agda-stdlib's `gcd` compares its
   arguments first, so at `gcd n n` the comparison `<-cmp n n` is the whole
   proof: the equal case holds by `refl`, and the two others contradict the
   irreflexivity of `<`.  It is as short as the idiomatic proof and depends on
   agda-stdlib's definition.

Lean's proof does neither, because Lean's `gcd` recurses on its first argument:
it splits `n`, and at `k + 1` it rewrites by the defining equation, by
`(k + 1) % (k + 1) = 0` and by `gcd 0 n = n`.  The same proof over the
translation of Lean's definition in `nat-gcd-succ` would read the same way,
with `gcd-succ`, agda-stdlib's `n%n≡0` and a computation of `gcd 0 n`, and
would need no axiom either: the two places where Lean's term uses `eq_self`
hold by `refl` in Agda.  It is not written here, because corpus entries are
checked separately and the definition lives in the other entry.

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | 684,821 |
| Export, records | 13,047 |
| Export, expression records | 10,818 |
| Export, declarations | 281: 24 inductive, 148 def, 103 thm, 4 quot, 2 axiom |
| Agda, lines per file | 45, of which 16 are code and the rest comments and blank lines |
| Agda, check time | 2.1 seconds (Agda 2.8.0, no `.agdai` files of the entry) |

## Remarks

The export was made on 2026-10-07 with lean4export v4.33.0 (format 3.1.0) under
Lean v4.33.1 (commit `819816b`), the pins of
[`docs/pinning.md`](../../docs/pinning.md).  Two runs gave the same bytes
(SHA-256 `402a52b2...bea2ffa3`).

lyphyser's translator shipped this declaration as its one example,
`examples/Nat.gcd_self.agda`, 6,942 lines, made under an older Lean whose `gcd`
compiled through `WellFounded.fix`; it postulated the `Set`-valued instances of
`Acc.rec` and `WellFounded.fixFEq`
([`docs/related-work.md`](../../docs/related-work.md), lyphyser/lean2agda).  At
this pin the term of `Nat.gcd_self` contains neither: the definition goes
through the fuel-based `WellFounded.Nat.fix`, and what took a postulate there
is now `Nat.rec` on a natural number.  The comparison with lyphyser's tool is
the work of M2-10 ([#24]).

[#7]: https://github.com/formalverification/lean2agda/issues/7
[#24]: https://github.com/formalverification/lean2agda/issues/24
