<!-- File: docs/outreach/lyphyser.md -->

# Outreach draft: lyphyser

A message for William to send to the author of lyphyser/lean2agda, in
his own name (issue M1-14, [#14]).  Drafted 2026-10-07 by the
related-work survey (issue M1-4, [#4]); nothing has been sent.  The
natural channel is an issue on their repository, since the README gives
no other address; the Lean Zulip is the fallback if they are there.
Record the answer, or silence after a month, in the lyphyser section of
`docs/related-work.md`.

## Subject

A Lean 4 to Agda translator that builds on your lean2agda

## Body

Hello,

I am starting a project called lean2agda, a translator from Lean 4 to
Agda, at https://github.com/formalverification/lean2agda.  The aim is
to turn Lean libraries, Mathlib first, into Agda libraries that check
under `--safe`, split into a constructive part and a classical part,
and to measure on the way which features of Lean's type theory its
libraries actually use.

Your lean2agda from September 2024 is the closest thing to it that
exists, and I have read it carefully.  The pass structure (deduplication
of closed subterms, binder fixing, level clauses, records for structure-
like inductives, recursors by pattern matching) is the right shape, and
our M2 ends roughly where your tool stops: one Agda file under `--prop --type-in-type`, checked on `Nat.gcd_self`
work (`docs/related-work.md` in the repository) has a section on your
tool, and every idea we take from it is credited there and in the design
notes.  We have not copied any code; if a later side-by-side comparison
shows a pass of yours worth taking as it is, it would keep your
copyright notice and be listed in our NOTICE file, under the Apache-2.0
license you chose.

Two things I would like to ask.

First, is the description in our survey fair?  If anything in it
misstates what your tool does or why, I would rather fix it now.

Second, would you like to be involved?  That could be anything from
answering a question now and then, to reviewing what we do with the
level-clause idea, to contributing.  The project is public and the
roadmap is in the repository; there is no obligation either way, and a
"no" is a perfectly good answer.

Thank you for having built it and for making it available under the Apache-2.0
license.

Best regards,

William DeMeo

## References

[#4]: https://github.com/formalverification/lean2agda/issues/4
[#14]: https://github.com/formalverification/lean2agda/issues/14
