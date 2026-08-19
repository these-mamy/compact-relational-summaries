# Compact Relational Summaries

This repository contains a compact semantic proof of sound summary production
and reuse for relational abstract domains, together with its Lean 4
formalization.

The proof develops five propositions:

1. replay set correctness;
2. exact filtering of the producer input;
3. summary soundness;
4. sound coarse reuse;
5. sound, coarse-refining, and semantically frame-preserving reuse.

## Contents

- `doc/main.tex`: source of the compact proof note;
- `lean/CompactSoundSummary.lean`: formalization using Mathlib's `Set` API;
- `lean/CompactSoundSummaryCore.lean`: dependency-free, proof-term version;
- `.github/workflows/ci.yml`: Lean checking, PDF construction, and release.

## Build

Check both Lean developments:

```sh
cd lean
lake build
```

Build the document:

```sh
cd doc
latexmk -xelatex -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

Pushes and pull requests build both artifacts. A successful push to `main`
creates or updates release `v0.1.0` with the generated PDF.
