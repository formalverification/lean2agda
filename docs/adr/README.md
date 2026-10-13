<!-- File: docs/adr/README.md -->

# Design records

Architecture decision records for lean2agda.  A record states decisions
and the evidence that earned them; explanation of a component goes in a
companion note beside that component, which the record links.

Each record has a plain title (`ADR 0001: translation architecture`), a
`File:` line, bullets for Status, Date, Tracking and Ancestry, an
executive summary, one section per decision area with Decision,
Evidence and Status, a numbered decision log, and a References section
with reference-style links for every issue, pull request and document.
Every term is defined on first use.

The records are as follows:

+  [ADR 0001, translation architecture](0001-translation-architecture.md)
   (issue M1-12; proposed 2026-10-13), with its companion note
   [`docs/architecture.md`](../architecture.md), which explains the
   pipeline.

Planned records are as follows:

+  ADR 0002, the encoding of Lean's `Prop` (issue M3-2);
+  the layering record (issue M4-2).
