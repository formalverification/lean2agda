<!-- File: corpus/notes-template.md -->

<!--
The template for corpus/<id>/notes.md.  Copy it, replace every
bracketed placeholder, and delete these comments.  Keep the headings:
issue M1-10's gap report reads every entry's notes by them.  A
section that does not apply says so in one line ("No instance
arguments.") rather than disappearing.  Name gap-catalog features by
the slugs of SCHEMA.md, in backquotes, so that the report can count
them.
-->

<!-- File: corpus/<id>/notes.md -->

# [lean_name]

[One paragraph: the theme the entry stands for, the module that
declares it, the issue that translated it, and the profile of each
Agda file.]

## Statement

[The Lean statement as `#check` prints it, the Agda statement, and
whether the two match up to notation.  Name the library definitions
the Agda statement uses in place of Lean's (agda-stdlib's `reverse` for
Lean's `List.reverse`, say) and whether they agree definitionally,
propositionally, or only up to a translation.]

## Tier

[What `#print axioms` prints at the pinned revision, the tier, and
which step of the proof brings each axiom in.  For a classical entry:
whether the statement is constructive once its classical instances are
abstracted, and whether a constructive proof is known.]

## What the kernel term needed

[One bullet per gap-catalog feature the term exercises, in the form
`slug`: the evidence from `lean/term.ndjson` (which declaration, which
construct), and what the Agda version does instead.  Look in
particular for definitional proof irrelevance, K-like reduction,
large elimination from `Prop` (`Eq`, `Acc`, `False` into a type),
definitional computation of `Quot.lift`, `Nat` literals and kernel
arithmetic, `WellFounded` and `Acc`, structure eta, universe levels
and `imax`, projections and `let`.  End with the features the manifest
lists that the term turned out not to use, if any, and correct the
manifest.]

## Instance arguments

[How many instance arguments the kernel term carries for the
statement and how they map to Agda: explicit records, instance
arguments `⦃ ⦄` or `{{ }}`, or module parameters.]

## The Agda version

[The files and their profiles; the library lemmas used; what the
idiomatic version does that the kernel term does not, and the reverse;
what had to be made explicit (a quotient computation turned into a
rewrite, a use of K justified by an `isSet` proof, a classical
principle taken as a module parameter).  For an entry with a plain and
a cubical file, a paragraph for each.]

## Sizes

| Measure | Value |
| --- | --- |
| Export, bytes | [`wc -c < lean/term.ndjson`] |
| Export, records | [`wc -l < lean/term.ndjson`] |
| Export, expression records | [`grep -c '"ie":' lean/term.ndjson`] |
| Export, declarations | [count and kinds, from the jq command below] |
| Agda, lines per file | [`wc -l agda/*.agda`] |
| Agda, check time | [seconds, from `make corpus-check`] |

The declarations of an export, by kind, are counted as follows (jq is
in the default shell; a mutual block of inductive types counts once):

```sh
jq -r 'to_entries[] | select(.key | IN("thm","def","axiom","opaque","quot","inductive")) | .key' \
  lean/term.ndjson | sort | uniq -c
```

## Remarks

[Anything else a later reader needs: a surprise, an open question, a
relation to another library (for the model-theory entry, how Mathlib's
first-order structures relate to agda-algebras's signatures and
algebras), with issue numbers for follow-ups.]
