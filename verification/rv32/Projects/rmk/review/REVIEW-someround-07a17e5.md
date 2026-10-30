# Review: Some round against named callee contracts (support-lean4 07a17e5)

This is the independent review worker's audit of:
- `Deframer/SomeRound.lean`: `DispatchContract`, `EncodeContract`, `Kept`, `CallPost`, `DispEnv`, `EncEnv`, `EncRes`, `some_pos`, `some_round`;
- the `SessionInv.lean` changes: `SW` widened to 0x8002a7b0..0x8002a7f4 and sp+0x140..sp+0x148, and `Extras.spTop` raised to sp+0x148.

**Pinned to commit 07a17e5.** No main module was changed.

## Verdict

Main's proofs are correct relative to their hypotheses. The hypotheses, however, are false. Both named callee contracts are refuted by kernel-checked runs of the real image code. Their conjunction is also false for a machine that satisfies `SomeAt`. **So `some_pos` and `some_round` are vacuous as stated.**

The repair needs two things:
- contracts that the real callees can satisfy;
- facts in `SomeAt`/`SessInv` that make their preconditions derivable.

Details are under "Actionable gaps" below.

## How it was checked

- **Fresh build.** A clean `/dev/shm` worktree of 07a17e5 was built from source, with `Elf.lean` regenerated from the pinned ELF (f39d833f…).
  - The build ran module by module through `build_main.sh`, in the order of `some-order.txt`.
  - All 79 modules compile, and the log ends `BUILD-DONE` / `build-exit=0`.
- **Axioms.**
  - Main's `some_round`, and this review's refutations except `encode_control`: propext, Classical.choice, Quot.sound.
  - `encode_control`: propext, Quot.sound.
  - There is no sorry, native_decide, bv_decide or `axiom` in SomeRound, SomeSegs, SessionInv or SomeAudit.
- **Regression.** `SessAudit.lean` (the 094b8c6 witnesses) still compiles against 07a17e5. So the real-layout `SessInv` witness survives the widened `SW` and the `spTop` change. The real sp+0x148 is 0x80ffff58 ≤ 0x81000000.
- **`SomeAudit.lean`** holds the refutations described below.
- **`test_some_controls.py`** holds 12 adversarial controls; the results are in `some-controls-07a17e5.txt`.

## How a `Lands` claim is refuted (`badK_sound`)

`Lands.step` requires two things: no fault under every oracle, and `Lands` for every successor. So a single run that faults, without passing a checkpoint, refutes `Lands`.

`badK` follows that run on a concrete machine, with oracle 0:
- **Instructions** come from a fetch table that the kernel checks against the packed ELF (`tblOK`, through main's `fetchDecode_of`).
- **Read-only loads** come from a `.rodata` table checked the same way (`rtOK`, `romRead_ro`). Loads below 0x80000000 yield none (`romRead_low`), and anything else falls back to the model itself.
- **Execution** uses `interpK`, which is main's `interp` with the read-only lookup factored out; `interpK_eq` proves it equal to `interp`.
- **Checkpoints.** At each step `badK` checks a decidable under-approximation of `¬ P`.

`badK_sound` is proved by induction, and the result is a plain `¬ Lands B img P m`.

## Findings

### G1. `DispatchContract` is false (`dispatch_contract_false`)

`DispEnv` constrains the dispatch future's three words relative to RAM and s9, but it never says what they point to.

The counterexample:
- the machine satisfies `DispEnv`;
- s9 = msgA, and the message header holds kind 0x0202, a kind dispatch handles;
- the RynkService pointer is [0x8002a780] = 0, so the future's service word is 0.

The real dispatch closure then runs:
- the prologue (frame 0x3e0);
- the state jump table at 0x800210dc, read from `.rodata`;
- the kind test, which goes to 0x800020ea and then 0x8000026e;
- `lbu a0,0x4d(s2)` at 0x8000026e, which faults on address 0x4d after 37 instructions.

The same works with s9 = 0. The contract quantifies over environments that include invalid service and message pointers, so no proof of it can exist.

### G2. `EncodeContract` is false (`encode_contract_false`)

`EncEnv` fixes `encode_frame`'s arguments, but it does not separate `Kept` from what `encode_frame` writes.

`Kept` includes the Uart16550 base and stride bytes at [uPtr]+0x1c..+0x20. With [uPtr] = 0x8002a795, those bytes are 0x8002a7b1.., which is the frame buffer itself.

The run then goes as follows:
- `encode_frame` runs 207 distinct instructions, through postcard's `index_mut` and `serialize`.
- It overwrites buf[0], which was 0x55.
- It returns to 0x80003f1e with `CallPost.kept` false.
- The caller continues. `EncEnv` leaves s6 free, here 0, so the caller faults on `lw a0,0x2cb(s6)`, a misaligned access.

Control `encode_control`: with the real pointer 0x8002a1c0, the same run is not refuted. `badK` stops at the return because the struct bytes are intact. So the refutation depends exactly on the missing separation.

### G3. The hypotheses are jointly false under `SomeAt` (`some_state_faults`, `some_hyps_false`)

`mS` is a machine with:
- the observed loop layout;
- a message at msgA with header 0x0202 (non-negative);
- s9 = msgA and x26 = 0x8002a7f0;
- the service pointer 0.

`mS` satisfies `SomeAt` and `h26`. From it, the real code runs through main's `sCall` into dispatch and faults, so `¬ Lands B img SomeQ mS`.

Combined with main's `some_pos`, this gives `¬ (DispatchContract ∧ EncodeContract)`.

The consequence goes beyond the contracts. `SomeAt` itself admits states that really fault, because it fixes neither s9 nor the service pointer. Strengthening only `DispEnv` would therefore make `some_pos` unprovable, since `DispEnv` would no longer follow from `SomeAt`. The missing facts must enter `SomeAt`/`SessInv` (I8 to I11 below).

### G4. Frame sufficiency, given the contracts

`Kept` is exactly what the post-call code needs: no part of it can be dropped. The controls show this:
- dropping the stride byte (k < 4) is rejected in `extras_ctx`;
- dropping the top byte of the flag-pointer word is rejected in `extras_ctx`;
- letting the callee change s10 is rejected in `ctx_call`;
- allowing `encode_frame` length 8 is rejected in `slice_ok`. With length 8, the 7-byte slice check would branch to the panic at 0x80004210.

The poll's own Some-path writes (`PW`) lie inside the widened `SW`. Reverting the widening is rejected in `kept_pw`.

### G5. Boundaries

`SomeQ` has three unproved exits: 0x80004204 (Pending, back to the executor), 0x80003fa6 (the 0xff result) and 0x8000429e (the send loop). Removing any one is rejected (`post_disp`, `post_disp`, `post_enc`), so all three are reachable exits rather than decoration.

**Uncovered resume path.** After Pending, the executor re-polls the task. The task resumes at the await, and dispatch's future then has a state byte ≠ 0 (the jump table at 0x800210dc dispatches on it). `DispEnv.futState = 0` covers only the first poll. A resumed-future contract is a separate, uncovered obligation.

### G6. `h26` (s10 = 0x8002a7f0) is necessary, not decoration

Changing the value to 0x8002a7f4 throughout is rejected in `post_enc`. The empty-response store [s10] then leaves `PW`, so the frame proof depends on s10's real value.

s10 is set by `addi s10,s6,0x333` at 0x800034d2 (poll entry) and at 0x80003b38. Neither `SomeAt` nor `SessInv` carries it.

### G7. A correct service pointer alone is not enough (simulation evidence)

This is a compiled `#eval` of the model's own `stepInstr` on the pinned image (`Sim3.lean` in /dev/shm). It is untrusted evidence: no kernel proof covers it.

The setup is the same as G1, but with the real pointers:
- [0x8002a780] = [0x8002a7b0] = 0x8002a4c0;
- the service object and futArg's memory zeroed.

Dispatch still faults for every message kind tried:
- kind 0x0004 faults after 35 instructions at 0x80002490, on a byte load through a zero pointer at offset 0x1e;
- kinds 0x0101, 0x0102, 0x0202 and 0x0302 fault after 410 to 446 instructions at 0x800098d4. That is `lbu s4,0x20(s2)` inside the UART write routine 0x800098a6, reading the stride byte of a Uart16550 struct whose pointer is 0.

Two consequences:
- **Dispatch writes to the UART itself.** It emits device events, so the session's send loop is not the only UART writer.
- **`DispEnv` needs a deep invariant.** It must cover the service object's pointer fields and futArg's object. futArg is [sp+0x20] = s6+0x53 = 0x8002a510, stored at 0x800034e6 on every poll entry and filled at 0x80003dc4..0x80003de8 from service fields. It must also cover a valid Uart16550 reachable from them.

## Actionable gaps

A1. **Restate the callee contracts as write-set frames.**
- The form is `∀ x ∉ W_callee, m.ram x = m₀.ram x`, where W is the callee's stack below sp plus its own output and buffer arguments.
- Such a frame is a property of the callee alone, independent of the caller's layout.
- The caller then derives `Kept` from `SomeAt`'s separation facts (`uSep` and similar), which is where those facts already live.

A2. **`DispEnv` needs the real preconditions of dispatch.** At least:
- the service pointer is the real RynkService object, and that object satisfies whatever invariant dispatch reads from it (keymap/state fields, e.g. the byte at +0x4d);
- s9 = msgA, with the message's data, len and cap (already in `SomeAt.msg`);
- a sane futArg;
- stack headroom: sp − (0x3e0 + nested depth) stays above static data, and `Kept`/`SW` lie outside the callee frames.

A3. **`EncEnv` needs separation** of `Kept`, or of the caller's needed cells, from the buffer [0x8002a7b1, +7), the out slot [sp+0x40, sp+0x48) and the callee frame. Alternatively, A1 removes the need.

A4. **New initial execution obligations.** These extend I1 to I7 of the 094b8c6 review and must be proved from the code before the Some point, not assumed:
- I8. **Service pointer.** [0x8002a780] (s6+0x2c3) holds the RynkService object, and that object's invariant holds.
  - The pointer is stored by `sw a0,0x2c3(s6)` at 0x80003da6, with a0 = s7+0xf1 = **0x8002a4c0**. That is a fixed address inside the task's own state, built by `RynkService::new` (call at 0x80003b30).
  - The object lies outside `SW`.
  - Its fields at +0x38/+0x44/+0x48/+0x4c are read at 0x80003db6..0x80003dbc, and dispatch reads +0x4d.
  - Like I2, this needs "never written afterwards" across the executor, other tasks and dispatch itself, except through dispatch's own documented writes.
- I9. **Message pointer.** s9 = msgA at 0x80003e70; recv_step's Some outcome should export it.
- I10. **s10.** x26 = 0x8002a7f0: `addi s10,s6,0x333` at 0x800034d2 on every poll entry, so it can be established per poll, like I3.
- I11. **Stack headroom.** sp − depth(dispatch, encode_frame, the send loop) stays above the end of static data. The real sp is 0x80fffe10. The bound needs the executor's stack depth (I4) plus the callees' maximal frames.
- I13. **futArg.** [sp+0x20] = s6+0x53 (0x8002a510), stored at 0x800034e6 on every poll entry. Its object is filled at 0x80003dc4..0x80003de8 before the loop, and its pointers must be valid for dispatch (G7). Neither `SomeAt` nor `DispEnv` says this.
- I12. **Resume path.** The re-poll of a Pending dispatch future (state byte ≠ 0) needs its own contract and an executor obligation (G5).

A5. **Exporter/runner.** The pinned `DispatchContract`/`EncodeContract` bodies are refutable, so any job conditional on them proves a vacuous implication. Label it so, and re-pin after the repair.

## Non-vacuity after repair

Once the contracts and `SomeAt` are repaired, this review can rerun the same machinery the other way round. A positive witness, such as `lands_hits` from a real-layout `SomeAt` with a valid service object, would show that the repaired `some_round` is entered by a real run.
