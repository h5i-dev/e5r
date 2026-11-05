# Unified verification core

`e5r-verify` uses one maintained execution, proof policy and provenance core for
PTX and RV32 firmware. The backends retain their semantics, input validation,
platform assumptions, statement construction and automation. The core has no ISA,
board, ELF or PTX namespace dependency. The dispatch layer in `verification.rs`
selects the existing typed backend requests; it is not a dynamic plugin system.

## Ownership and acceptance

| Layer | Responsibility | Used by |
| --- | --- | --- |
| `src/core/process.rs` | Command lifetime, group RSS, time/output limits, diagnostics | Both backends, `e5r exec`, Lean check script |
| `src/core/workspace.rs` | Owned temporary directories, OS project locks | Both backend entry points |
| `src/core/proof.rs` | Standard axiom policy, source screening, replay, checker report validation | Both backends |
| `verification/common/E5rVerification` | Kernel replay and transitive axiom traversal, exact/named theorem checks | Firmware audit, PTX supplied checker, PTX library audit |
| `src/core/artifact.rs` | Content identities, inventory and toolchain freshness, common evidence | Both backends |
| `src/verification.rs` | Legacy adapters, typed invocations, source bundles and replay | Both CLIs |
| `src/job.rs`, `src/ptx/` | RV32 firmware and PTX semantics-facing policy | Respective backend only |

Only `propext`, `Quot.sound` and `Classical.choice` are allowed proof axioms.
Kernel replay and transitive axiom auditing are separate checks. Replaying a
module does not establish that a chosen theorem expresses an intended property.

Firmware rebuilds each checked module from source by default, restricts imports
to previously checked modules, replays every module with `leanchecker`, and uses
the common checker to require actual theorem declarations and audit their
transitive axioms. It also validates actual compiled import headers. The model,
board, exported image, image fidelity and proof modules remain an ordered closure.
`--resume` binds both the source dependency chain and compiled `.olean` bytes;
it still replays the kernel and audits theorems. Old resume manifests rebuild.

Firmware evidence uses `reviewed_theorem_names`. Image fidelity is independently
proved, but the relationship between a named property theorem, that image and a
user's intended contract still requires review of the proposition and assumptions.
This infrastructure does not turn a function theorem into whole-firmware safety.

PTX automation generates the program and class proposition. Generated proof and
counterexample modules must elaborate, pass the axiom policy, and undergo
independent `leanchecker` replay of their declarations. These claims use
`generated_claim`; statement translation remains reviewed Rust code.

Supplied PTX proofs use `exact_generated_statement`. The common checker receives
the allowed trusted module prefixes from the PTX adapter, checks actual imports,
replays both the generated statement module and every supplied declaration,
rejects declared axioms, requires the theorem to belong to the supplied module
and have exactly the generated statement constant as its type, then audits its
transitive axioms. The statement source and compiled bytes must remain unchanged
during supplied elaboration and replay. The checker executable is fingerprinted
before elaboration and must remain unchanged before and after replay. Compiled
project model dependencies are
snapshotted before acceptance and must remain unchanged. A JSON success line
cannot override a failed or resource-limited checker process.

The PTX model modules are trusted semantics, not supplied proofs. Their complete
library axiom audit uses the same shared traversal, retaining a visited set across
declarations. Firmware's interrupt/device/reachability logic and PTX's SIMT/race/
termination logic remain separate. No semantics or generic reachability theory
was moved without demonstrated common use. The shared Lean package depends only
on Lean core. Both production projects use a local path dependency; neither
Mathlib nor fp-lean is a production dependency.

## Execution contract

Bounded verification currently requires Linux with readable `/proc`, POSIX process
groups and the `kill` executable. Unsupported hosts return an execution error;
they do not silently omit memory enforcement. `e5r-verify` requires Rust 1.89 or
newer for safe standard-library OS file locking; other workspace crates retain
their existing requirements.

Each command starts in its own process group with closed stdin. The runner
samples aggregate resident memory of group members every 50 ms, checks wall time,
and samples log size. It kills the whole group and reaps the direct child on
exhaustion, errors, scope exit and completion, including a successful parent with
background descendants. It captures stdout and stderr in one uniquely created
log, keeps at most the final 8 MiB of log bytes in the result, and removes the log.
The output limit is independently reported as resource exhaustion. After group
termination the runner polls for live members for up to one second; zombies do
not count as live. `cleanup_complete` records the result. Incomplete cleanup is
an execution failure even if the direct child succeeded. Uninterruptible kernel
waits can delay reaping; no hard cleanup deadline is claimed.

RSS and on-disk log thresholds are sampled, not hard cgroup limits: allocations
and writes can overshoot between samples. Aggregate RSS can count shared pages
more than once. Wall time can exceed its threshold by sampling, scheduling and
cleanup time. `SIGKILL` from outside the runner is not guessed to be a memory
exhaustion. No hard allocation, disk, or host availability guarantee is claimed.

Process groups are cooperative lifecycle control, not a security sandbox.
A descendant that deliberately creates a new session can escape the group.
Lean metaprograms and firmware build recipes execute code with the caller's OS
permissions. Untrusted executable inputs require an external sandbox. Source and
artifact checks protect proof acceptance under the ordinary assumption that the
verifier, toolchain, model files and checker process are not concurrently tampered
with by another OS process. Killing the verifier itself with SIGKILL or a host
crash bypasses Rust destructors; use an external supervisor/cgroup for that case.

The CLI handles SIGINT, SIGTERM and SIGHUP with an atomic cancellation flag;
the runner then kills its process group and reaps its child. Embedding applications
can use `run_with_cancel` with their own atomic flag. Cancellation is distinct
from resource exhaustion. In-process backend search observes cancellation at
its stage boundaries.

OS project locks exclude concurrent cooperating e5r checks on the same Lean
project and release even when the owning process dies. External `lake` commands
must also avoid changing the project during a check. Owned temporary workspaces
clean up on ordinary failure paths; `--keep` retains reviewable generated sources.
`TMPDIR` selects scratch placement. `e5r exec` exposes the same execution policy:

```sh
e5r exec --timeout 1800 --memory-mib 4096 --cwd verification/ptx -- lake build
```

`exec` returns the command's exit code, 124 for sampled resource exhaustion, or
1 for execution errors. The limit applies per command/stage, not to total job
wall time or in-process Rust counterexample search.

## Schemas, identities and compatibility

Existing `e5r.verify.job.v1`, `e5r.verify.result.v1`, and `e5r.ptx.result.v1`
fields remain. Results with readable, identifiable inputs add `verification`, schema
`e5r.verification.evidence.v1`. Its request separately names backend, architecture,
platform assumptions and a typed replay invocation. Its binding explicitly records
the claim model above; the full detailed backend theorem/counterexample evidence
remains available and is included in the common claim identity. Accepted results
require this evidence. Early missing-input or tool failures can carry only the
legacy failure details; they never become accepted evidence.

The evidence content ID hashes the request, outcome, binding, file/tool identities,
claim and axiom policy. File identities contain SHA-256 and byte length. PTX
captures the program, spec, optional proof, complete project source inventory and
shared support; added and removed dependencies make results stale. Compiled model
libraries used at acceptance are pinned as additional inputs. Firmware captures
its ordered model/proof closure, board, generated image/fidelity, ELF, job, shared
support, checker adapter, and build-source inventory (`rs`, `ld`, `toml`, `lock`,
`py`, `sh`, `json`). Its job itself pins the property names and build recipe.

Tool identities include pinned Lean/Lake version output, actual Lean, leanchecker
and Lake executable hashes and the executing verifier's hash. Changing the
verifier requires rechecking. Source inventories deliberately exclude `.git`,
`.lake`, `build`, `target`, Python caches and the cooperative lock, except explicit
artifact inputs. PTX inventories are conservative: an unrelated project source
change can invalidate a result. Arbitrary build recipes can read undeclared files
or external environments; the recorded source inventory is not a hermetic build
proof. The output ELF and theorem subject are nevertheless pinned directly.

| Common outcome | Firmware legacy status | PTX legacy verdict / exit |
| --- | --- | --- |
| `proved` | `proved` / 0 | `proved` / 0 |
| `refuted` | Reserved checked counterexample | `refuted` / 1 |
| `inconclusive` | `failed` / 10 | `unknown` / 3 |
| `unsupported` | `unsupported` / 11 | `unsupported` / 2 |
| `resource_exhausted` | `resource_exhausted` / 12 | Existing `unknown` / 3, build `error` / 4, or class `unsupported` / 2 |
| `error` | `error` / 13 | `error` / 4 |

A failed proof is inconclusive. A refutation requires a checked Lean replay;
search output alone never establishes one. PTX execution records carry the actual
limit category, sampled peak RSS and monitoring method, so the common outcome
can separate exhaustion without changing legacy exit semantics.

Old firmware results remain readable through the legacy freshness adapter. Old
PTX results lack model/dependency provenance and must be regenerated for common
freshness, replay or bundles. Unknown common schema versions fail closed. Adding
optional legacy fields is additive; incompatible future evidence changes require
a new common schema. Content hashes are not signatures: `verify-result` checks
freshness and internal consistency, not authenticity of an untrusted JSON file.
Use replay to obtain new checked evidence.

## Replay and bundles

```sh
e5r verify-result RESULT.json
e5r replay-result RESULT.json > replay.json
e5r bundle-result RESULT.json --out BUNDLE
e5r replay-bundle BUNDLE > replay.json
```

These commands work for fresh accepted results from either backend, including
checked PTX refutations. Replay reruns the backend, including proof generation or
supplied-proof checking, and requires the recorded outcome and detailed claim.
A bundle manifest must match its original hashed verification request and identity;
a different captured program is not a replay of that request. A bundle contains the
hashed source/input snapshot, original result, portable typed invocation and
`e5r.verification.bundle.v1` manifest. It can be moved; path validation and hashes
are checked before execution. Build commands remain executable policy, not a
sandbox. Bundles require the same verifier and pinned external toolchains. Source
builds may need their existing locked firmware dependencies. They do not include
an OS, Rust compiler, CUDA, or Lean distribution. Extra compiled library blobs
record the accepted model provenance; replay rebuilds from bundled sources.

The original `e5r bundle JOB.json --out DIR` remains a firmware-specific,
Lean-only recheck format and does not require e5r or Rust for its `recheck.sh`.
The common source bundle serves a different reproduction contract and does not
replace it.

## Adding a backend

1. Define the ISA decoding and transition semantics from public specifications.
   Validate them against an independent execution oracle. Keep architecture apart
   from platform memory, devices, scheduling and environment assumptions.
2. Define the supported input envelope and fail-closed exporter. Prove or check
   the binding from actual program bytes to the model's program object. If a
   translation is not proved, list it in the trusted base. A decompiler IR is not
   a substitute for trusted semantics or translation correctness.
3. State the property contract. Use exact generated statement acceptance when
   the tool constructs it. Otherwise expose reviewed named propositions honestly.
   Supply the platform/environment assumptions explicitly. Prove the ISA- and
   platform-specific safety, reachability, race or termination obligations needed
   for that contract; this core supplies none of those semantic proofs.
4. Supply an ordered checked module closure or a reviewed trusted model module
   policy, and a separate supplied-proof import policy. Use the shared kernel
   replay, checker and standard axiom allowlist. Never accept printed names or a
   theorem's existence as evidence of an intended proposition.
5. Define a typed invocation in the adapter dispatch, an architecture identity and
   platform identity, and capture program/spec/property/model/tool dependencies.
   Guard mutation during checking and fail if provenance cannot be established.
   Reuse the common execution, workspace, evidence and bundle services.
6. Map the common outcomes to the backend CLI explicitly. Add wrong subject,
   stale dependency, wrong statement, disallowed axiom/import, kernel bypass,
   resource and checked counterexample controls. Add an end-to-end relocated
   bundle replay. Document exact unsupported scope and external trust obligations.

Regression commands, executed coverage and remaining environmental limits are in
[unified-validation.md](unified-validation.md).
