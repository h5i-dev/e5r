# RMK proof checkpoint

This checkpoint preserves the RMK RV32 work before the PTX investigation.
It is a collection of machine-code proofs and verification infrastructure,
**not a proof of RMK or `SessionSafe`**. The runtime target is one hart on QEMU
virt RV32, upstream RMK revision `71556128` (full pin in the R0 records).

## Accepted results and remaining assumptions

| Result | Evidence | Limits |
| --- | --- | --- |
| RAM ELF export and independent Lean image reconstruction | `e5r-verify`, `RamElf`, generated fidelity theorem | Exact pinned ELF and board; not a verified compiler |
| memmove, all sizes, directions and alignments in its contract | `Memmove.contractAll`, `Deframer.copy_contract` | Contract's address/stack bounds |
| COBS decoder and Deframer tail/park/unpark/next | `Cobs.Bridge`, `RmkSessionDischarged.deframer` | Explicit entry and memory invariants |
| Session receive/unpark and one-round decomposition | `RmkSessionDischarged`, `RmkFragments.round` | Quiet entry; stops at Some/read-future boundaries |
| UART send bytes, send loop, continuation to unpark | `RmkSend.send_round`, `send_to_loop`, `nonvacuous` | `SendAt`, extras and deframer facts; yield poll remains a boundary |
| Actual encode_frame code, including callees | `Encode.encode_spec`, `encPre_witness`, `encode_reaches` | `EncPre`; caller bridge also needs write-set separation |
| Initialization fragment and satisfying entry | `Init.init_round`, `initAt_real` | **Assumes `TopicsNewContract`**; no boot-to-entry proof |

The quantified device-read behaviours and event-aware composition live in
`Trees.lean`. The proof runner recompiles from source, replays declarations
through `leanchecker`, audits theorem axioms and binds results to source,
board, toolchain and ELF identities. The semantics and specifications remain
part of the trusted interpretation; kernel acceptance alone does not show
that they match all hardware behaviours or the intended application spec.

### Results excluded from safety claims

`SomeRound.some_round` and `RmkFragments.round_some` are historical conditional
implications. The old universal `EncodeContract` is refuted; these implications
are **vacuous** and must not be counted as safety progress. The dispatch
interface now takes an explicit world invariant, but no full dispatch proof
is supplied. See `verification/rv32/Projects/rmk/review/SomeAudit.lean` and
[the interface audit](../verification/rv32/rmk/some-interfaces.md).

The independent encode proof does not discharge that false contract.
Establishing `EncPre` and the bridge's write-set separation at the caller,
and establishing `SendAt` after encoding, remain integration tasks.

Also open: dispatch/world invariants, the 0xff path, UART read futures,
executor and other tasks, interrupt preservation, and boot reachability.
The LR/SC semantics allow spurious SC failure; unconditional yield-loop
termination needs an appropriate progress assumption or a safety-only proof.

## Recheck the integrated checkpoint

Prerequisites: Rust, elan with `leanprover/lean4:v4.35.0`, `leanchecker` on PATH,
and the pinned ELF at
`verification/rv32/build/rmk-qemu-riscv-rynk.elf` with SHA-256
`f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30`.
The ELF is an ignored local input, not included in this source checkout.

```sh
cargo build --release -p e5r-verify -j 2
./target/release/e5r-verify check \
  verification/rv32/jobs/rmk/rmk-checkpoint.json \
  --out /tmp/rmk-checkpoint.json
./target/release/e5r-verify verify-result /tmp/rmk-checkpoint.json
```

The job lists the import closure of `Projects.ramimage.RmkCheckpoint` (102
project modules, plus runner model/board/image modules) and 17 audited theorem
endpoints, including explicit non-vacuity witnesses. Conditional Some
continuations compile for interface regression checking but are excluded
from the accepted endpoint list. `Init.init_round` stays conditional as above.
Do not use `--resume` for release evidence. The result records failures as
well as successes; require `status: proved` and successful `verify-result`.

R0 reproducibility is **not accepted**. The f39d image has an in-place rebuild
record, not two accepted independent clean builds. Another fixed-path image
has separate records but has not replaced this proof target. Existing R0
records and historical receipts are retained without upgrading their claims.
See [the roadmap](ROADMAP.md#r-rmk-on-risc-v-2026-10-29-owner-authorization)
and `verification/rv32/rmk-audit/`.

The standard firmware CI script checks `jobs/*.json`; RMK jobs are under
`jobs/rmk/` and need the separately supplied ELF. A green firmware CI run
does not imply that this RMK checkpoint ran. Historical receipts name their
original revisions and are not fresh evidence for this integration.

## Integration scope

The preparation branch combines `support-lean4` at `b3050cc`, ISA/encode review
at `947fab0`, and exporter/UART work at `20b2f66` (including `61a39eb`).
It preserves backward-memmove checks during conflict resolution, updates stale
session wrappers to current signatures, and provides the aggregate job above.
No PTX implementation or claim of whole-session correctness is introduced.

Fresh integration validation and the source/kernel replay receipt are linked
from [the validation record](rmk-checkpoint-validation.md).
