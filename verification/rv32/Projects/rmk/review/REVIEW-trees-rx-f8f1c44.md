# Review: checkpoint trees, device reads, UART receive poll (support-lean4 f8f1c44)

These are the independent review worker's findings on three files:
- `Projects/rmk/Trees.lean`
- `Projects/rmk/DevRead.lean`
- `Projects/rmk/Deframer/Rx.lean` (with `Reach.lean`, `RxSegs.lean` and `Theories/Platform.lean`)

No main module was changed. The evidence is in this directory.

## How it was checked

- Main was built fresh from source in a clean `/dev/shm` worktree of f8f1c44, with no `.lake` copied in.
  - `Elf.lean` was regenerated from the pinned ELF (sha256 f39d833f…) with main's own `gen_elf.py`.
  - The build ran module by module, `lean -o`, in the order given by `rx-order.txt` (`build_main.sh`).
  - All 27 modules compile.
- Axioms:
  - `rx_loop`: propext, Classical.choice, Quot.sound.
  - `lands_lbu_dev` and `reach_no_escape`: propext, Quot.sound.
  - There is no sorry, native_decide, bv_decide or `axiom` in the audited files.
- `RxAudit.lean` holds the proofs listed below, against main's definitions.
- `test_rx_controls.py` holds 9 adversarial controls. All 9 are rejected in the expected declaration (`rx-controls-f8f1c44.txt`).

## Findings

**F1. The oracle quantification and fault exclusion in `Lands` are sound.**
- `Lands.step` requires three things:
  - no fault under every oracle;
  - `Quiet`;
  - `Lands` for every `Step` successor, whatever events it emits.
- `Result` has only `ok` and `fault`. So "no fault under every oracle" means every oracle has an `ok` successor, and a tree never has a dead end.
- Proved:
  - `lands_hits`: every `Lands` tree is reached by an actual `Reach` run from its root.
  - `lands_false`: `Lands _ _ (fun _ => False) m` is never true. The landing is not vacuous.
- Control `weak_vacuous`: without the no-fault field, a quiet machine at an odd pc (it faults under every oracle) "lands" in the empty checkpoint set. Main's `Lands` rejects the same claim.

**F2. Interrupt exclusion is necessary and correctly placed.**
- `Quiet` is required at every internal node, and `Rx` carries it along by `sameCsr`.
- `irq_counter` shows why. At the loop head, a core with mstatus.MIE and mie.MTIE set has a `Step` to mtvec (0x80000000) that is no instruction step under any oracle.
- `step_oracle` and `reach_no_escape` therefore depend on `Quiet`. Whoever enters the receive loop must establish it (`RxAt.quiet`).

**F3. The device reads are modelled as fully nondeterministic.**
- In `lands_lbu_dev` the successors are quantified over every `v : Word`.
  - The read is `devVal .b v` (masked) and then zero-extended.
  - The board's registers are `uart0.lsr` 0x10000005 (read, width 1) and `uart0.rbr_thr_dll` 0x10000000 (read/write, width 1).
- Controls:
  - dropping the width check is rejected;
  - restricting the successors to v = 0 is rejected;
  - an LSR address off by one (0x10000004, not a device) is rejected.
- Scope: LSR and RBR are independent and memoryless. This over-approximates the UART, which is sound for safety. But no claim can rely on "data ready implies valid data" or on any ordering of bytes.

**F4. Obligation for main: cap ≥ 1 at loop entry. This is the important one.**
- The back edge is `bne s4, s1` (0x800043a2), and i is incremented before the test.
- Entered with cap = 0 while LSR reports data ready, the loop would:
  - store to buf[0] (outside a 0-byte buffer);
  - compare 1 ≠ 0 and keep going, overrunning the buffer.
- `RxEnv.cap` (1 ≤ cap) and `RxAt.lt` (i < cap) are hypotheses. Weakening them to cap ≥ 0 and i ≤ cap is rejected (control 4).
- The code before 0x80004374, which `Rx.lean` lists as not proved, must establish cap ≥ 1 wherever the Deframer composes `rx_loop`. That means proving that the remaining buffer capacity is nonzero on this path, or that there is a guard.

**F5. Obligation for main: the UART addresses come from RAM.**
- `RxEnv.rbr` and `RxEnv.lsr` (s3 = 0x10000000, s5 = 0x10000005) are read from the `Uart16550` struct by 0x80004362..0x8000436a.
- That struct's contents are assumed, not proved, as `Rx.lean` says. A composition must carry an invariant on that RAM, for example that the struct is never written by the copied ranges (dst ∩ struct = ∅).

**F6. `RxOut` does not say what the bytes are (it is a frame property only).**
- It says pc = 0x800043a8, registers outside ra/s0/s1/a0-a2 unchanged, and s1 ≤ cap.
- RAM outside buf[dst, dst+cap) and the one `assert_offset` stack byte is unchanged.
- It does not relate buf contents to the bytes read, and it allows all of buf[0, cap) to change, not only buf[0, s1).
  - That is enough for "no write outside the buffer".
  - It is not enough for any claim about decoded frame content.
  - It is not enough for "bytes beyond s1 are preserved".
- No device write happens in the loop, but `RxOut` does not state that no events are emitted. `Lands` ignores events by design, and `Reach` accumulates them.

**F7. Termination.**
- `Lands` is inductive, so every path is finite. There is no uniform bound, since each read value has its own subtree.
- In `rx_loop`, each path is bounded by cap - i iterations (the induction measure).
- No fairness assumption on the UART is needed: when data is never ready, the loop exits at once.

**F8. Non-vacuity of `rx_loop`.**
- `rx_witness` gives a concrete quiet core at 0x80004374 (s3/s5 = UART, cap = 16, buffer and stack byte in RAM) that satisfies `RxEnv` and `RxAt _ _ _ _ 0`.
- `rx_exit_reached` then shows the exit 0x800043a8 is actually reached by some behaviour.
- Control: the same witness with cap = 0 is rejected.

**F9. `assert_offset` is called with a1 = s8, which is unconstrained.**
- This is harmless: 0x8001692e..0x8001693e only stores a0 to the stack byte and checks a0 < 8.

No soundness defect was found in the audited proofs. F4 and F5 are integration obligations for main, and F6 is a scope limit to keep in mind for content claims.
