# Lean proof of compact sound summary reuse

This directory contains the machine-checked counterpart of the proof note in
[`../doc/main.tex`](../doc/main.tex).

[`CompactSoundSummaryCore.lean`](CompactSoundSummaryCore.lean) is the verified,
dependency-free proof. It formalizes the four propositions from the compact
proof note and provides the assembled theorem
`end_to_end_sound_summary_reuse`. [`CompactSoundSummary.lean`](CompactSoundSummary.lean)
is the same development written with Lean's standard `Set` API. Both versions
also prove Proposition 5 through `sound_and_precise_frame_preserving_reuse` and
assemble P1--P5 in `end_to_end_sound_frame_preserving_reuse`.

The formalization is deliberately generic:

- concrete agreement is equality of field observations;
- the concrete semantics is an arbitrary transition relation;
- the abstract domain is an arbitrary type with a concretization function;
- `analyze`, `relate`, and `filter` are arbitrary operations constrained by the
  semantic properties stated in the note;
- Separation is an explicit diagnostic predicate, independent of P1--P5;
- `ProductionInput` and the match-based reuse theorem expose the weaker
  semantic contracts used inside the exact-filter and equality-key routes.

The reuse theorems take successful lookup as a hypothesis, corresponding to the
accepted branch of the paper's partial reuse operations.

Frame-preserving reuse combines the stored output with the consumer filtered
to fields outside the write set. Its soundness uses Write Frame, Filter Sound,
and Meet Sound. Its precision relative to coarse reuse uses Meet Reductive.
Actual preservation of the consumer frame additionally uses
`FrameFilterReductive` and the filter side of Meet Reductive.

The core file begins with `prelude`, defines a powerset as `α → Prop`, and has
no imports. The standard-API file imports the logical `Set` API from Mathlib.

Run `lake build` in this directory to check both files.
