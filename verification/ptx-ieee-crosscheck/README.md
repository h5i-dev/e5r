# Cross-check of the PTX rounding core against lean-ieee754

`verification/ptx` defines the rounding of every correctly rounded `.f32` and
`.f64` instruction in `Ptx/Semantics/FloatCore.lean`, on core Lean `Rat`
with no Mathlib. This project proves, in Lean with Mathlib, that those
definitions agree with an independently written IEEE 754 specification,
`FP.IEEE.Spec.roundWithMode` and `OverflowWithMode` of lean-ieee754
(docs/verification/ptx.md, "Floating point").

It compiles `Ptx/Semantics/FloatCore.lean` from the main project's source
tree (`srcDir = "../ptx"`), so the file checked here is the file the model
uses. Nothing in `verification/ptx` imports this project.

Run: `scripts/check-ptx-ieee-crosscheck.sh` (builds under a memory cap and
runs the axiom audit in `Audit.lean`).

## Third-party code

This project depends on, and does not copy, lean-ieee754
(https://github.com/tunnellm/lean-ieee754, commit
529ed78d9b8cda5592e3cad3849ecfff52c7ece3), Copyright its authors, licensed
under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). It is fetched by Lake into
`.lake/packages/FP` together with its own pinned dependencies (Mathlib
0df444a3 and others, see `lake-manifest.json`), each under its own license.
Its README states it is mostly LLM-written without expert review of its
IEEE 754 correspondence; this project therefore uses it as a second,
independent statement of IEEE rounding to compare against, not as an
authority.
