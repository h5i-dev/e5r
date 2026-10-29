# Independent ISA / execution-model review (F3, F6, F8)

Reviewer: a second Claude worker (Opus 5.5), requested by the owner, working
independently of the production worker on branch
`verify/isa-review-20261029t042314z`. This is a partial review with stated
coverage. It does **not** mark F3, F6 or F8 done, and it is not a claim of
exhaustive RISC-V conformance.

## What was reviewed

| | |
| --- | --- |
| Commit reviewed and tested | `593ed31c7ac61f92129ffdbe2582eaa9ba46acbf` (Theories/Hart.lean, Platform.lean, Board/Hifive1Revb.lean, tools/Replay.lean, tools/qemu_trace.py) |
| Firmware | `verification/rv32/firmware/hifive1-embassy` built here with `cargo +1.98.1 build --release`; ELF SHA-256 `3a6742afa9fe1ff26f71288132a08eb16fab3516f288af3a64717c3be8cd7bf7` (same as the production worker reported) |
| QEMU | `qemu-system-riscv32` 8.2.2 (Debian 1:8.2.2+ds-0ubuntu1.18), `-M sifive_e,revb=true`, from the production worker's extracted tools (read only) |
| Binutils | GNU 2.42 (`riscv64-linux-gnu-as/ld/objdump/nm`), from the earlier V0 tools (read only) |
| Lean | 4.35.0 (pinned `lean-toolchain`) |
| Specifications | RISC-V Unprivileged ISA 20240411 and Privileged Architecture 20240411, the versions `Hart.lean` cites. Source text read at `https://github.com/riscv/riscv-isa-manual/tree/20240411/src` (`a-st-ext.adoc`, `machine.adoc`, `c-st-ext.adoc`, `rv32.adoc`, `m-st-ext.adoc`). FE310-G002 Manual v1p5 and E31 Core Complex Manual as cited by `boards/hifive1-revb.json` (not re-read; claims about the E31 below are marked where they rest on them). |

**Stale-source caveat.** The production worker has advanced since `593ed31`
(uncommitted `Absint.lean`, `Analyze.lean`, a modified firmware `main.rs` and
`lakefile.lean` in its checkout at the time of review). Nothing here was
tested against those. Every result below names `593ed31`; re-run the
commands on a later commit before relying on them.

## Summary

* **One confirmed model bug against the specification (F1).** A store-
  conditional that fails never checks its address, so a misaligned SC, or an
  SC to an unmapped or device address, executed without a reservation is a
  normal step in the model. Zalrsc requires an exception. `Escapes` is
  therefore false on a state where the specification says the hart traps.
  QEMU 8.2 has the same behavior, so neither the production replay nor any
  QEMU differential test can see it. Minimal reproducer and a two-line fix
  are below (fix committed separately on this branch).
* **No other model disagreement** in 1725 boundary cases run on the board in
  QEMU, covering every opcode class of RV32IMAC + Zicsr + Zifencei + MRET/WFI
  and interrupt entry, except five places where QEMU itself departs from the
  specification or the E31 (listed; the model follows the specification).
* **Mutation controls.** 44 seeded single-span model bugs: 43 are detected by
  the harness; the one survivor widens an over-approximation (interrupt
  enabling), which a differential test cannot detect by construction.
* **Replay audit.** The production replay compares registers and CSRs
  correctly and its environment oracle does not mask RAM or CSR computation.
  Its gaps: device write *values* are not compared with QEMU, RAM is never
  compared directly, and the firmware trace contains **no M-extension
  instruction at all** and no halfword access, so "every opcode class" cannot
  rest on the trace. An independent replay with explicit device-traffic and
  interrupt-boundary comparison was added (results below).

## 1. Source audit of Hart.lean and Platform.lean

Checked by hand against the specification text, field by field.

| Area | Result |
| --- | --- |
| x0 | `Core.get` returns 0 for x0 and `Core.set` ignores writes to it; checked on every writing instruction class including CSR, AMO, LR/SC, loads and C hints. |
| Immediates | I/S/B/U/J bit positions and sign extension match the RV32I encoding figures. All RVC immediates (CIW, CL/CS, CI, CI-16SP, CI-LUI, CSS, CJ, CB) match the RVC tables bit by bit. |
| Shifts | Register shifts use `rs2[4:0]`; `SLLI/SRLI/SRAI` with `imm[5]=1` (RV32) and other funct7 values decode illegal; `C.SRLI/C.SRAI/C.SLLI` with `shamt[5]=1` are illegal (RV32 NSE); `shamt=0` C forms are HINTs executing as shifts by 0. |
| Signedness | `SLT/SLTI` signed, `SLTU/SLTIU` unsigned after sign-extending the immediate; branches distinct; LB/LH sign-extend, LBU/LHU zero-extend. |
| M | `MULH/MULHSU` use Lean `Int` `/` (Euclidean; equals floor for the positive divisor 2^32, as required); division by zero returns all-ones / the dividend; `INT_MIN / -1` returns `INT_MIN` with remainder 0, by `tdiv`/`tmod` plus wrap. |
| C reserved/HINT | `C.ADDI4SPN` nzuimm=0 and `0x0000` illegal; `C.LWSP rd=0`, `C.JR rs1=0`, `C.LUI/C.ADDI16SP` imm=0 reserved; `C.SUBW/C.ADDW` and the other `bit12=1` CA forms reserved; FP compressed loads/stores illegal (no F/D on the E31); `C.ADDI/C.LI/C.LUI/C.MV/C.ADD/C.SLLI` to x0 are HINTs. |
| A | funct5 values match; `LR` with `rs2≠0` illegal; aq/rl ignored (one hart). AMO and LR on misaligned addresses fault; outside RAM they are `unsupported`. **SC: see F1.** The reservation is a Boolean with no address: after `LR a`, `SC b` may succeed in the model. That is a wider set of behaviors than the hardware has (sound for safety) but the docs only say "an SC with a reservation may succeed or fail"; recommend stating it. |
| CSR | Read-only (`addr[11:10]=3`) writes trap illegal; `CSRRS/CSRRC` with `rs1=x0` and the `I` forms with `uimm=0` do not write; old value read before the write and `rd==rs1` handled. `mepc[0]` cleared (IALIGN=16). `mie` masked to 0x888 (FE310 manual). `mip` read environmental, write no effect on MSIP/MTIP/MEIP. Unmodeled CSRs, `mcause` writes, `mtvec` modes 2/3 and `mstatus` fields outside MIE/MPIE/MPP are `unsupported` (deliberate, documented in the board file). |
| MRET / WFI | MRET requires MPP=M (else `unsupported`), sets MIE←MPIE, MPIE←1, MPP←U; U is the least-privileged supported mode on the E31 (misa from QEMU confirms U). WFI is a NOP, which with interrupts allowed at every boundary covers every stall. |
| Interrupt entry | mepc←pc, mcause←2^31+code, MPIE←MIE, MIE←0, MPP←M, target = base (+4·code when vectored). Taken only when MIE and the source's mie bit are set; pending is left to the environment (over-approximation). Codes 3/7/11 only. |
| Fetch / decode | 16-bit when `bits[1:0]≠3`, otherwise 32-bit; `≥48-bit` prefixes decode illegal; fetch only from executable image segments (fetch from RAM is `unsupported`, a deliberate restriction). |
| Platform | All misaligned loads/stores/AMOs fault (E31 has no misaligned support — board-file claim, not checkable in QEMU, see D1); device registers word-only; flash read-only (store `unsupported`); RAM bounds checked on the whole access. |

Not re-derived: the generated board file's device list against the FE310
manual (out of scope here), and the Lean ELF/flash reader.

## 2. Findings

### F1 (bug, model vs specification): a failing SC never checks its address

`exec` for `.sc` returns the failure result (`rd = 1`) without any effect when
there is no reservation, and also on the environment's "fail" branch. Only the
success branch issues the `store` that `interp` checks for alignment and RAM.
The Unprivileged ISA 20240411, "A" extension 2.1, *Zalrsc*: "If the address
is not naturally aligned, an address-misaligned exception or an access-fault
exception will be generated." The sentence is unconditional.

Consequence: `Escapes B img m` is false for a machine about to execute
`sc.w rd, rs2, (rs1)` with a misaligned, unmapped or device `rs1` and no
reservation, although the hart traps there. With a reservation, the success
branch faults, so `Escapes` holds; the hole is the no-reservation case. A
safety theorem of the form "never escapes" would then be claimed for a binary
that raises an exception. Compiled Rust rarely issues an SC without a preceding
LR, so practical severity is low, but this is the semantic TCB.

Reproducer (model only): `lake env lean --run review/Repro.lean` on `593ed31`:

```
FAIL misaligned SC, no reservation: ok, x13 = 00000001, 0 events
FAIL misaligned SC, reservation, env says fail: ok, x13 = 00000001, 0 events
PASS misaligned SC, reservation, env says succeed: fault E5R.Fault.misaligned
FAIL SC to an unmapped address, no reservation: ok, x13 = 00000001, 0 events
FAIL SC to a device register, no reservation: ok, x13 = 00000001, 0 events
PASS control: aligned SC without reservation writes rd = 1
```

QEMU 8.2 also completes these (harness cases `sc misaligned no resv`,
`sc unmapped no resv`, `lr;sc misaligned` all return `rd = 1` with no trap),
which is why no QEMU-based test can find this. Whether the E31 itself traps
was not checked on hardware.

Fix (this branch, separate commit; file overlap: `Theories/Hart.lean`, the
`.sc` case only): the failure path first issues an atomic word load of the
address and ignores the value, so `interp` applies exactly the checks a
successful SC gets. A RAM load has no effect in the model, so no successful
behavior changes. After the fix `Repro.lean` prints all PASS, the harness
still agrees on every case, and the production proofs that build here were
re-checked (see section 6).

### Oracle divergences: QEMU 8.2 `sifive_e` departs from the spec/E31

These are not model bugs. Each is a place where agreement with QEMU would be
the wrong criterion, so the harness marks them `oracle-divergence` and
requires the model to *disagree* with QEMU there (a mutant that makes the
model agree with QEMU is caught, e.g. `load-misaligned-unchecked`,
`mepc-keeps-bit0`).

| | QEMU 8.2 | Spec / E31 | Model |
| --- | --- | --- | --- |
| D1 misaligned LH/LHU/LW/SH/SW | performs the access | E31 traps (board file; FE310 manual) — the ISA permits either | faults (`misaligned`) |
| D2 `mepc` bit 0 | kept on write and read back | "`mepc[0]` is always zero" (Privileged 20240411, mepc) | cleared |
| D3 `mie` unimplemented bits | `csrrs mie, -1` reads back `0xffffeaaa` | "Bits of `mie` that are not writable must be read-only zero"; FE310: only MSIE/MTIE/MEIE | `0x888` |
| D4 `sfence.vma` | executes in M-mode | illegal without S-mode (the E31 has none) | illegal |
| D5 misaligned AMO cause | load-misaligned (4) | an address-misaligned or access-fault exception; QEMU's choice of 4 rather than 6 is QEMU's | `misaligned` (either cause accepted) |

D1 matters for the production replay: QEMU would silently perform a
misaligned access the real board traps on, so a firmware trace can never show
that the model's misaligned-fault rule is right or wrong. The rule rests on
the E31 documentation alone.

## 3. Differential harness (new, `review/harness.py`)

Independent of `tools/oracle.py`, `tools/qemu_trace.py` and `tools/Replay.lean`
(it does not parse QEMU's `-d cpu` log). One bare-metal M-mode image runs on
`qemu-system-riscv32 -M sifive_e,revb=true -accel tcg,one-insn-per-tb=on`.
Per case it sets every GPR, `mstatus/mie/mtvec/mepc/mcause/mscratch`, CLINT
`msip`/`mtimecmp` and a 64-byte RAM window from a descriptor in flash, runs
the candidate (one instruction or a short straight-line sequence), and saves
the post-state from the firmware: landing pads (fall-through vs taken) store
x1..x31 through a base register the candidate does not name; an mtvec handler
(direct or 16-entry vectored table) saves x1..x31 via an mscratch swap plus
mcause/mepc/mstatus and the entry address reached. Results go to UART0.
`Diff.lean` rebuilds the model's pre-state from the dump only, runs
`stepInstr` (and `takeIrq` for interrupts), and compares PC, x0..x31, the six
CSRs, the RAM window and msip. Only environmental choices (SC success, mip
and device reads) are read off QEMU's result register.

Oracle-setup validation (run on every invocation, a failure stops the run):
QEMU must report every case and reach the end marker; the dumped descriptor
must equal the generator's intent with link-time symbols resolved by `nm`;
the CSR values QEMU reads back after setup must equal the intended pre-state
(so a QEMU legalization is not silently fed to the model); the fetched
candidate bytes must equal the generator's encoding (encoders in `encode.py`
written from the spec tables, not from `Hart.lean`); and each case's QEMU
outcome (normal / trap cause / interrupt code) must equal what the case says.

Coverage on `593ed31`, 1725 cases (`results/harness-593ed31.json`):

| Family | Cases | Content |
| --- | --- | --- |
| rv32i-op / rv32i-imm | 454 / 256 | all OP and OP-IMM ops × signed/unsigned extremes, shifts by 0/1/15/31/32/33/63/…, every rd, LUI/AUIPC extremes |
| rv32m | 520 | all 8 M ops × 64 operand pairs incl. ÷0, INT_MIN/−1, negative non-exact products/quotients, aliasing |
| branch / jump | 73 / 14 | 6 branches taken/untaken, ±8, −4096, +4094, x0 operands, 2-aligned targets; JAL ±, max +1048574, far back; JALR imm extremes, bit-0 clearing, rd = rs1 |
| load / store / device | 57 / 29 / 3 | all widths/signedness, offsets ±2048, store-then-load byte order, flash loads, flash store, unmapped/past-RAM, CLINT word and byte access |
| amo / lrsc | 82 / 8 | 9 AMOs × 6 value pairs, rd = x0, rd = rs2, aq/rl, misaligned, device; LR/SC pairs, SC without LR, double SC, other-address SC, misaligned/unmapped SC, reserved encodings |
| rvc / rvc-jump / rvc-hint / rvc-illegal | 53 / 16 / 9 / 22 | every RV32C instruction with immediate extremes, every HINT form, every reserved RV32 encoding in the tables |
| csr / system / illegal / x0 | 53 / 8 / 28 / 28 | every CSR op form on mscratch/mepc/mtvec/mie/mstatus/mcause/mip/mhartid, read-only writes, unmodeled CSRs; ECALL/EBREAK/FENCE variants/FENCE.I/WFI; RV64, F, custom, long-prefix and reserved-funct encodings |
| mret / irq | 5 / 7 | MRET with each MIE/MPIE combination and a 2-aligned mepc; MSIP and MTIP entry in direct and vectored mode, interrupt raised by a CLINT store, enabled via mie; pending-but-disabled control |

Verdicts: AGREE 1609, AGREE-TRAP 65 (same trap class, faulting PC and
unchanged registers), AGREE-IRQ 6, DECLINE 15 (model `unsupported`: expected
restrictions, listed in the JSON), oracle-divergence 30 (D1–D4; the model
must differ there). No unexpected verdict. Wall time 13 s. After the F1 fix
(`90b12ad`, `results/harness-90b12ad.json`) the three SC cases move from AGREE
to oracle-divergence (2) and DECLINE (1); everything else is unchanged.

Not covered: external interrupts (PLIC, code 11), timer *values* (mtime is
environmental), MRET to U-mode (QEMU enters U-mode, then the landing pad
traps; the model declines, checked by reading the source), multi-instruction
interleavings beyond the few sequences listed, and random/exhaustive
encodings.

Reproduce (from `verification/rv32`):

```sh
lake build Theories
python3 review/harness.py --summary /tmp/summary.json     # exit 0 = every case as expected
python3 review/mutants.py --summary /tmp/mutants.json     # ~13 min
lake env lean --run review/Repro.lean                     # F1
```

Tool paths default to the two extracted tool roots and can be overridden with
`E5R_BINUTILS_ROOT` / `E5R_QEMU_ROOT`.

## 4. Negative controls (`review/mutants.py`)

Each mutant replaces one exact span of a scratch copy of `Hart.lean` or
`Platform.lean` (a span that no longer occurs exactly once stops the run, so
a stale mutant cannot silently test the original), builds only what
`Diff.lean` imports, and re-runs the comparison on the recorded QEMU run.
A failed build or comparison is reported `TOOL`, never as a kill.

44 mutants (`results/mutants-593ed31.json`): MULH/MULHSU/DIV/REM/REMU edge
semantics, SRA/SLL/SLTU, x0, LB/LHU extension, B/J/S immediates, C.LUI sign,
C.SRLI shamt[5], C.ADDI4SPN scale, C.LWSP rd=0, CJ bit order, JALR bit 0,
link value, JALR read-after-link, AMOMAX, AMO rd, SC/LR reservation, MRET
MPIE/MPP, interrupt mepc/vector/MPIE/enable, mstatus layout, mie mask, mepc
bit 0, read-only CSR writes, CSRRS x0, CSR rd ordering, FENCE.I, ECALL cause,
halfword byte order, misaligned-load check, device read source.

* 43 KILLED. `x0-writable` survived the first run because x0 had no
  comparison slot; `Diff.lean` now requires x0 to read 0 and two
  write-then-read cases were added, after which it is killed by 44 cases.
* 1 SURVIVED by design: `irq-ignores-mie-reg` lets an interrupt be taken
  while its `mie` bit is clear. That only adds behaviors; a differential test
  observes what QEMU did and cannot show the model allows too much. It is
  sound for safety but makes proofs weaker; only a review or a proof against
  a reference spec can rule it out.

## 5. Audit of the production replay (`tools/qemu_trace.py`, `tools/Replay.lean`)

| Question | Finding |
| --- | --- |
| Does the oracle mask RAM/CSR computation? | No. `oracleFor` returns QEMU's next `rd` for every load and CSR instruction, but `interp` consults the oracle only for device reads, `mip` reads and SC success; RAM, flash and every other CSR come from the model's own state. The `device-read-from-ram` mutant confirms the device path is the only one using it. |
| Parsing / deduplication | Dropping a state equal to the previous one is safe (every in-scope instruction changes the PC except a jump to itself). But a state missing a register is skipped anywhere in the log, not only at the end as the comment says; a skipped middle state would normally surface as a mismatch two steps later, so it fails closed in practice. `review/fwtrace.py` errors instead. On the same 20 000-state log both converters produce the same states and both drop 56 repeated entries. |
| Interrupt boundary | Inferred: "step first if `next.mepc ≠ pc`". Correct given one instruction per log entry (the only ambiguity is a self-loop, where stepping changes nothing), but implicit. `review/FwReplay.lean` uses QEMU's own `epc` from the `riscv_cpu_do_interrupt` line and requires the model to reach exactly that PC with at most one instruction. |
| Device traffic | **Not compared.** `Replay.lean` counts the model's device events and prints the PWM values, but never checks them against QEMU. A model bug in a device *write value or address* that leaves registers equal would pass. F6 asks for replay that "covers device traffic". `FwReplay.lean` compares every model device event with QEMU's `memory_region_ops_write` trace, address and value, in order. |
| RAM | Never compared directly; a store bug is seen only if the firmware reloads the bytes into a register. The harness compares its RAM window after every case. |
| Opcode coverage of the trace | Disassembling the firmware (objdump after removing the ELF's `rv32im`-only attribute, which makes objdump print C/A/Zicsr as `.insn`) gives 55 mnemonics, all executed in the trace. **No M-extension instruction occurs in the firmware**, nor `LH/LHU/SH`, 32-bit `SUB/SLL/SRA/SLT/XOR/OR/AND`, `BGE`, AMO add/xor/min/max, `C.LUI/C.SUB/C.SRAI/C.JAL`. The F3 criterion "instruction-level differential cases cover every supported opcode class" therefore cannot rest on the trace; the review harness covers those classes. |
| Initial state | Replay starts from QEMU's state at the entry point with all-zero RAM, one boot state, not "every boot state the board allows". Expected; it is a test. |

### Firmware replay results

Trace: the firmware above, run with

```sh
(printf 'A\x05\xffZ\x80\x01q'; sleep 12) | timeout 10 qemu-system-riscv32 -M sifive_e,revb=true \
  -display none -bios none -kernel <elf> -accel tcg,one-insn-per-tb=on -icount shift=10 \
  -d cpu,int -D cpu.log -trace memory_region_ops_write -monitor none -serial stdio
python3 review/fwtrace.py cpu.log trace.txt 120000
(cd review && lake build fwreplay && .lake/build/bin/fwreplay trace.txt)
```

UART input is needed: without it the firmware never writes PWM. Input timing
through stdin is not deterministic, so traces differ between runs.

| Run | Model | Result |
| --- | --- | --- |
| `tools/qemu_trace.py` + production `replay`, first 20 000 states | `593ed31` | agree: 19 999 transitions, 50 interrupts, 313 device writes (counted, not compared); PWM 15, 15, 47, 58, 74, 75, 89; 99 s |
| `review/fwtrace.py` + `review/FwReplay.lean`, 120 000 states | `90b12ad` (F1 fix; every SC in the firmware follows an LR) | agree: 119 999 transitions, 330 timer interrupts at QEMU's epc, **1987 device writes equal to QEMU's** (1980 CLINT mtimecmp, 7 PWM); 582 s, 90 MB |

On the same log both converters produce the same first 20 000 states and drop
the same 56 repeated entries.

Negative controls (`results/replay-negatives.txt`):

| Control | Production replay | Review replay |
| --- | --- | --- |
| one GPR bit flipped in state 5000 | rejects (x10) | rejects (x10) |
| first PWM write removed from QEMU's traffic | cannot express (no traffic input) | rejects at step 1145 |
| first PWM write value changed to 0x65 | cannot express | rejects at step 1145 |
| interrupt epc moved by 2 | cannot express (mepc heuristic) | rejects at step 2345 |
| interrupt line removed | n/a | rejects at step 2345 |
| **model mutant: every device write value + 1** (`Platform.lean`) | **passes** ("model and QEMU agree", prints PWM 16, 16, 48, …) | rejects at step 294 (mtimecmp_hi) |

The last row is the concrete reproducer for the device-traffic gap: the
production replay accepts a model whose every device write is wrong.

## 6. Fix and re-checks (commit `90b12ad`)

| Check | Result |
| --- | --- |
| `lake env lean --run review/Repro.lean` | 5 PASS + control PASS (4 FAIL on `593ed31`) |
| `python3 review/harness.py` | 1725 cases, every case as expected (the three SC cases are now a QEMU divergence or a decline) |
| `lake env lean -j1 Projects/hifive1/Duty.lean` (image regenerated with `e5r-verify flash` from the 3a6742af ELF) | checks; `duty_contract` axioms `propext, Classical.choice, Quot.sound` |
| `Projects/hifive1/clamp/Proof.lean` (ELF rebuilt with `rustc +1.98.1 --target riscv32imac-unknown-none-elf -C opt-level=2 -C panic=abort -C relocation-model=static -C link-arg=-Tlink.ld`, byte-identical to the production worker's `hifive1-clamp-O2.elf`, SHA-256 `0294b5dd…9544`) | checks; `clamp_all` axioms `propext, Quot.sound` |
| review firmware replay | agrees (section 5) |

Not re-run: `tools/check.py` (the V0 runner) and the workspace cargo suite;
the fix touches only `Theories/Hart.lean`, which V0 does not import.

## 7. Commits on this branch and overlap with the production worker

| Commit | Content | Files the production worker also edits |
| --- | --- | --- |
| `8828273` | harness, cases, encoders, Diff.lean, mutants.py | none (all under `review/`) |
| `55fc9da` | mutant results, x0 comparison, alignment fix, fwtrace/FwReplay/Repro | none |
| `90b12ad` | **F1 fix** | `verification/rv32/Theories/Hart.lean` (the `.sc` case only). Cherry-pick by hand; do not merge. The production worker's uncommitted `Theories/Absint.lean` may enumerate SC's effect tree; it would now see an extra `load` node on the failure path. |
| last | replay fixes, review Lake package, results, this document | none |

Nothing was merged or cherry-picked into `support-lean4`.


## 8. Integration round (continuation 20261029T111106Z)

Base: published `origin/support-lean4` @ `e9e71a1`, merged into this branch
(`acaafd0`); Hart.lean taken from support-lean4, whose `dcd2b33` probes the
SC address on every path (equivalent to `90b12ad` for faults).
`review/Repro.lean` on the merged head: 5 PASS + control PASS. Harness: one
case changed expectation (`csrrw mtvec 0x20010041` is now declined by
`dcd2b33`'s 128-byte vectored-base rule, which is conservative); 1726 cases,
every one as expected (`results/harness-e9e71a1.json`).

The production replay now checks device traffic (owned by this branch for
this round; `tools/Replay.lean`, `tools/qemu_trace.py`):

* `qemu_trace.py` writes trace format 2: `V 2` header, `S` states, `R`/`W`
  MMIO reads/writes from `-trace memory_region_ops_read/_write`, `I cause
  epc` from QEMU's interrupt line, and an `E` end marker with the counts. A
  state with missing fields in the middle of the log is an error. `--user`
  (ReplayIsa) still writes format 1.
* `Replay.lean` follows each step's effect tree the way `interp` does and
  answers each device read with QEMU's next MMIO read, which must be at the
  same address and a word; it then runs `stepInstr` with those values and
  compares registers, CSRs and device writes (address, value, width, order)
  with QEMU. The walk is checked against `stepInstr` on every step (exit 2
  if they differ). Interrupts use QEMU's epc. Exit 0 agree, 1 semantic
  mismatch, 2 trace or tool error.
* `tools/test_replay_controls.py` (run by `run_firmware_replay.py`): 14
  edited traces and 4 model mutants, each required to fail with a specific
  exit code and message (`results/replay-controls-e9e71a1.txt`).

Firmware trace (2 s host time, the `run_firmware_replay.py` input): 64 472
transitions, 175 timer interrupts, 2 279 device reads and 1 059 device writes
equal to QEMU's; PWM 15, 30, 38, 70, 70, 80 = the input's expected duties.

Decoder sweep (`review/decode_sweep.py`, `review/DecodeSweep.lean`, commit
`36808c5`): all 49 152 16-bit parcels and 1 004 352 seeded 32-bit words
(half in-scope major opcodes, half any 32-bit major, every SYSTEM funct12,
every AMO funct5 x funct3) decoded by the model and by binutils 2.42 objdump
(`rv32imac_zicsr_zifencei`, `-M no-aliases,numeric`; RVC expanded by this
script from the spec's table). Result (`results/decode-sweep-e9e71a1.json`):
no WRONG (model decodes something objdump rejects, or another instruction)
and no unexplained STRICT. Where they differ the spec decides: reserved
FENCE/FENCE.I fields are executed as a fence (14 285, objdump rejects),
RV32 shamt[5]=1 (1 536 RVC + 176) and C.ADDI16SP nzimm=0 are reserved
(objdump accepts; the model traps), and S/U/debug-mode instructions (38) are
illegal on the M-only E31. Five decoder mutants are each reported WRONG
(`results/decode-controls-e9e71a1.txt`). Decoding only: execution of the
decoded instruction is the harness's and replay's job.

Residual gaps of the replay: RAM is compared only through values loaded
back into registers; SC success is read from `rd` (unobservable for
`rd = x0`), not from a memory write; the trace has only timer interrupts;
QEMU differs from the E31 (D1–D5); the trace length depends on host timing.

## Residual gaps

* No result here says the model matches the E31. QEMU is the only executable
  reference and differs from the E31 in D1–D4; those rules rest on the
  E31/FE310 documentation alone.
* Over-approximations (interrupt pending, SC success, the unaddressed
  reservation) cannot be tested differentially; they were reviewed in source.
* Not covered: PLIC/external interrupts, UART/PWM device behavior beyond
  word writes, MRET to U-mode in QEMU, an exhaustive (rather than sampled)
  32-bit decode sweep, and
  the boot-state/initial-RAM generality of the safety theorem.
* F8 "independent review recorded": this document is that record for the ISA
  and execution-model part only. Board-file device list, ELF/flash reader,
  checker orchestration and the proof statements were not reviewed.
