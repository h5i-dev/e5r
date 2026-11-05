# Independent fp-lean cross-check

Run from the repository root:

```sh
scripts/check-ptx-fp-crosscheck.sh
```

This separate Lake project pins [opencompl/fp-lean](https://github.com/opencompl/fp-lean/tree/bf6fa4c4e981e9a18052517370f66699f2261cf4)
at `bf6fa4c4e981e9a18052517370f66699f2261cf4`, version 0.1.0,
Apache-2.0 (`LICENSE.txt` in the fetched package). Its manifest has no external
Lake dependencies: no Mathlib, SMT solver or Python package is needed here.
Upstream's auxiliary documentation/test tooling is not used. No upstream
implementation or fixture is vendored. We inspected the upstream APIs and
proofs for this evaluation, as explicitly authorized; production source is unchanged.

The exact upstream toolchain is `nightly-2026-06-30`, Lean 4.33.0-pre,
commit `28b99ec01f6275235fedecbac8e382cac682bf80`. The production project
continues to use v4.35.0 with no external dependencies. This project compiles
`../ptx/Ptx/Semantics/FloatCore.lean` and `Float.lean` directly on the nightly,
without copying them. Compilation succeeds on that nightly. A separate fresh-source probe on
v4.35.0 fails in upstream tactic APIs (details below).

The script uses two Lean threads, a 4 GB systemd scope when available, and a
1200-second timeout per phase. Override `LEAN_NUM_THREADS`, `PTX_FP_LEAN_MEMORY`
and `PTX_FP_TIMEOUT` as needed. Without systemd, the timeout still applies but
there is no aggregate memory cap. The first run fetches the pinned dependency
and toolchain. No production build runs this script implicitly.

## Coverage and trust boundary

`Crosscheck/Adapter.lean` maps `.rn/.rz/.rm/.rp` to
`RNE/RTZ/RTN/RTP`, and PTX f32/f64 to `PackedFloat 8 23`/`11 52`.
It compares add, sub, mul, div, fused multiply-add and sqrt. Upstream's fraction
width excludes the hidden bit. `observe` maps every upstream NaN to `none`,
matching the production result's meaning; all other bits, including zero signs,
must agree exactly. The production NaN oracle remains outside this adapter.

PTX `.ftz`, `.sat`, min/max, comparisons, conversions and approximate operations
remain in production's PTX adapter. They are not claimed to be implemented by
fp-lean or independently checked here. In particular, merely flushing an IEEE
rounded result would not establish the production `.ftz` tininess rule.

`Main.lean` generates its own corpus: 112 patterns per format, spanning both
signs, zero/subnormal/normal/overflow boundaries, half-fraction boundaries,
infinities and multiple NaNs. Every pair is checked for four binary operations;
every pair has five FMA addends (signed zeros, one, and negated operands).
Sqrt covers every corpus operand. All four modes run. Another 256 deterministic
full-width pseudorandom triples per format exercise all six operations and
modes. These are executable comparisons, not proofs of universal equivalence.
The runner stops with operands, format, mode and both results on the first mismatch.
For 880 inputs per format it additionally compares bit round-trips, sign and
NaN/infinity/zero/subnormal classification, and finite rational decoding against
upstream `toRat?`. Nonzero finite inputs also check E5R's encode/decode
round-trip (that final round-trip is a production self-check).

`Crosscheck/Proofs.lean` contains kernel-checked symbolic observation/NaN
lemmas and individual ground arithmetic bridge proofs. `Symbolic.lean` proves
a multiplication-chain rewrite with explicit canonicality side conditions.
`SpecBridge.lean` lifts upstream's six rational correctness theorems through
our NaN observation, providing generic and f32/f64 corollaries for all inputs
and rounding modes. This is a bridge to upstream's rational specification,
not to E5R's production arithmetic. `agrees_iff_reference` formally reduces
`Agrees` to agreement between that rational reference and production, precisely
isolating the remaining proof obligation. The sqrt reference is a noncomputable
bracket specification; it stays outside the executable imports. It uses no `sorry`,
extra axiom or `native_decide`. `Agrees` explicitly states the still-unproved
bounded-bit-pattern arithmetic bridge. It is a definition, not an assumption.

`Audit.lean` strictly audits every declaration in `Ptx.*` and `Crosscheck.*`,
and the six used upstream arithmetic definitions, rejecting axioms and any
transitive dependency outside `propext`, `Quot.sound`, `Classical.choice`. It
also inventories every declaration in the imported `Fp.*` module closure,
reporting rejected declarations separately. The minimal closure includes
upstream auxiliary/example theorems with native `bv_decide` axioms; they are not used or
accepted by our proofs. `ArithmeticAudit.lean`
separately audits the exact upstream rational-spec correctness theorems for
all six operations. Importing an unrelated axiom does not taint a theorem:
only its actual transitive dependency graph determines acceptance.

## Remaining obligations before production adoption

Prove `Agrees` for f32/f64, six operations and four modes, including bit decode,
finite-value interpretation, encoding, overflow/underflow, special operands and
signed zeros. The existing lean-ieee754 cross-check proves rational rounding
identities, not this packed bridge. Upstream's rational SMT-LIB specification
also needs a bridge to E5R's rational rounding and bit representation.

Port and validate on the production compiler; measure elaboration/kernel
reduction costs and useful finite-input symbolic proofs. Any future integration
must preserve the PTX NaN oracle and modifiers rather than silently adopting
upstream's deterministic NaN policy. Avoid normalization theorems with extra
axioms; use explicit canonicality proofs where available.

## Source-gap triage

At this pin, `FpAgainstFloatModel` contains 13 actual `sorry` proof terms:
`Add:14`, `Sub:11`, `Mul:40,46`, `Div:12`, `Sqrt:13`, `Basic:197`,
`Compare:15,19,23,35`, `MinMax:17,21`. Those modules are not imported here.
Their scaffolding is not evidence of equivalence to Lean's `Float.Model`.

By contrast, the `sorry` mentions in
`Fp/Theorems/UnpackedFloat/Round/Normalize.lean:92` and
`Fp/Theorems/Division.lean:72` are comments, not proof holes. The audit checks
actual theorem dependencies rather than treating those comments as admissions.
`Fp/PackUnpackNormalize.lean:159` really declares the private axiom
`Canonical_all`; its unconditional cancellation theorem is deliberately
rejected. `Symbolic.lean` uses the conditional canonicality-preservation path.

The symbolic examples assess reference transport and removal of an intermediate
representation round-trip. They do not establish that E5R can automatically
prove general finite arithmetic program specifications, error bounds or
nonlinear identities using fp-lean.

## Production compiler compatibility probe

After fetching the parent project's pin, reproduce the optional diagnostic:

```sh
cd verification/ptx-fp-crosscheck/compat-v435
LEAN_NUM_THREADS=2 timeout 300 systemd-run --scope --quiet \
  -p MemoryMax=4G -p MemorySwapMax=0 -- \
  lake build +Fp.Addition +Fp.Subtraction +Fp.Multiplication +Fp.Division +Fp.FMA +Fp.Sqrt
```

This builds into its own `.lake`, using the parent's pinned source without
editing it. On v4.35.0 it fails in `Fp/Tactics/Simps.lean`:
`Nat.reduceUnary`, `Nat.reduceBin` and `[bv_normalize_proc]` are unavailable.
The associated `sorryAx` diagnostics are elaborator error recovery, not
additional source proof gaps. This is a source compatibility failure, not
merely an incompatible cached `.olean`. No upstream port was attempted.
The exact-nightly cross-check remains runnable independently.

## Validated results and recommendation (2026-11-05)

`scripts/check-ptx-fp-crosscheck.sh` completed with exit 0 under its 4 GB cap.
`bash -n scripts/check-ptx-fp-crosscheck.sh` and `git diff --check` also pass.
After adding the final obligation-reduction theorem, focused
`lake build ArithmeticAudit` and `lake env lean ArithmeticAudit.lean` pass;
executable inputs and behavior are unchanged from the full successful run.

| Check | Result |
| --- | --- |
| f32 arithmetic | 458,176 comparisons, zero mismatches |
| f64 arithmetic | 458,176 comparisons, zero mismatches |
| Representation | 880 inputs per format, zero mismatches |
| Own/production imported declarations | 293 accepted, standard axioms only |
| Minimal upstream closure | 3,301 inventoried; 14 declarations with native proof dependencies excluded |
| Six upstream arithmetic correctness theorems | Each exactly `propext`, `Classical.choice`, `Quot.sound` |
| Canonicality-based multiply-chain proofs | Same three standard axioms |
| Generic/f32/f64 reference transport and obligation reduction | Same three standard axioms |
| Unconditional `EUnpackedFloat.pack_unpack` | Rejected: additionally `_private.Fp.PackUnpackNormalize.0.EUnpackedFloat.Canonical_all` |
| v4.35.0 source compatibility | Fails in upstream tactic APIs |

[axiom-results.txt](axiom-results.txt) records exact transitive axiom output,
including all 14 excluded declarations (seven auxiliary/example theorems and
their seven generated native axioms). Those imports do not imply that an
accepted theorem depends on them. No accepted proof depends on `sorryAx`,
`Lean.ofReduceBool` or a native `bv_decide` axiom.

The negative control temporarily replaced the runner's `actual` expression
with `(upstream F m op a b c).map (· + 1)`, rebuilt `crosscheck-runner`, and ran
it. It exited 1 on sqrt(+0): production `some 0`, mutated reference `some 1`.
The source was restored in a `finally` block and the executable rebuilt before
the final successful full run. This tests that mismatches are observable.

**Recommendation:** retain this independently pinned evaluation, and pursue
selective arithmetic adoption only after a compiler port and the rational
reference-to-production bridge. fp-lean is a promising executable reference:
it avoids Mathlib, supports the required arithmetic, and its six principal
correctness theorems pass the exact axiom policy. The representation and
arithmetic comparisons found no disagreement in this corpus, and explicit
canonicality permits useful staged rewrites without `Canonical_all`.

The current evidence does not justify replacing production arithmetic. The
compiler incompatibility is concrete, generic production equivalence is open,
and proof performance for real E5R finite-arithmetic programs remains
unmeasured. Preserve the PTX adapter, NaN oracle, existing lean-ieee754
rounding proofs and GPU differential checks during any later migration.
