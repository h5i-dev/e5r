# encode_frame on the pinned RMK image: proved

`Projects/rmk/Encode/*` proves `encode_frame` (0x80008d5c) of the pinned `rmk-qemu-riscv` ELF (sha256 f39d833f…), as the session's Some path calls it at 0x80003f1a.

The proof covers the actual code, callees included:
- postcard `Slice::index_mut` (0x8001dfe4), including its bounds check: the panic path is shown not taken;
- `Result<(), RynkError>::serialize` (0x80011a46);
- `RynkError::serialize` (0x80014078), through its jump table at 0x80026410.

No callee is assumed.

Owner: the review/encode worker (branch `verify/isa-review-20261029t042314z`). Main consumes this and does not duplicate it.

## Statement

| | |
|---|---|
| `encode_spec` (Spec.lean) | `∀ m₀, EncPre m₀ → Lands B img (EncPost m₀) m₀` |
| `encode_callPost` (Bridge.lean) | the same, as main's `SomeP.CallPost 0x80003f1e m₀ m ∧ SomeP.EncRes m₀ m`, given `∀ x, Kept m₀ x → ¬ EncW sp x` |
| `encPre_witness`, `encode_reaches` | `EncPre` holds for the observed call site (sp 0x80fffe10, response 8), and a real run from it reaches `EncPost` |

### `EncPre m` (Encode.lean)

- **Entry state:**
  - pc = 0x80008d5c;
  - `Quiet`;
  - x1 = 0x80003f1e;
  - x10 = sp+0x40 (result slot);
  - x11 = 0x8002a7b1 (frame buffer);
  - x12 = 7;
  - x15 = sp+0x140 (response byte).
- **Stack:**
  - sp % 4 = 0;
  - 0x8002a854 ≤ sp: the callee frames, down to sp-0x60, lie above the session's static cells;
  - sp+0x148 ≤ 0x81000000.
- **Response byte:** [sp+0x140] ≤ 8 (a RynkError discriminant) or = 0xff (Ok). Any other value makes `RynkError::serialize` jump through its table into unrelated data. Control 1 shows this is necessary.
- **Everything else is arbitrary:** x13/x14 (the header halfword and third byte), all other registers, and all other RAM.

### `EncPost m₀ m`

- pc = 0x80003f1e, `Quiet`, and x1 = 0x80003f1e;
- sp, gp, tp and s0..s11 are unchanged;
- **frame:** `∀ x, ¬ EncW sp x → m.ram x = m₀.ram x`, where `EncW sp` = [0x8002a7b1, 0x8002a7b8) ∪ [sp+0x40, sp+0x48) ∪ [sp-0x60, sp);
- `EncRes`: tag [sp+0x40] = 1, or 0 with length [sp+0x44] ≤ 7.

## Method

**`Sym.lean`** is a symbolic executor for RV32 code, proved sound against the model's `stepInstr`.
- Registers are expressions over the entry registers and RAM.
- Memory is the entry RAM under a list of writes.
- Addresses are linear in the entry sp, for every sp in a range.
- Reads are resolved by exact match, by disjointness, or byte by byte (`rdByte`/`rdCat`).
- A branch on unknown data has two successors.
- `astepI_sound` proves each supported instruction (lui, auipc, jal, jalr, branch, load, store, op, opimm) against `exec`/`interp`.
- `check_sound` turns a kernel-evaluated `check … = true` into `Lands`. It covers no fault under any oracle, `Quiet` through unchanged CSRs, and interrupt steps excluded.

**`Table.lean`** holds the 390 instructions reached on every input class. It is generated from the model's own decoder, and `encTbl_ok` checks it against the packed ELF in the kernel.

**`Encode.lean`** has the contract, the rodata jump table (`encRom_ok`, kernel-checked) and `enc_check`. `enc_check` combines ten separately kernel-checked evaluations for the admitted response values; each data branch (zero or non-zero header and third bytes) is explored both ways. The historical monolithic check took about 340 s; the integrated checkpoint splits it to bound temporary kernel evaluation memory.

**`Spec.lean`** has the entry relation (`rel_init`), the leaf test's soundness (`leaf_sound`), `encode_spec` and the non-vacuity results.

**Axioms:** propext, Classical.choice, Quot.sound. There is no sorry, native_decide or bv_decide.

## Receipts and controls

- **Build:** `build-ce52b08.txt` is a fresh-source build (14 modules, in the order of `encode-order.txt`) through `review/build_main.sh`.
- **Controls:** `test_encode_controls.py` holds 8 negative controls; the results are in `encode-controls.txt` once run:
  - the response byte 9 admitted;
  - the callee stack bounded at sp-0x50;
  - the old sp bound 0x8002a808;
  - a0 claimed preserved;
  - a jump-table word misstated;
  - an instruction misstated;
  - the executor reading through an overlapping write;
  - the executor following only one side of an undecided branch.

## For the caller (main)

1. `SomeAt` must give sp ≥ 0x8002a854.
2. The response byte passed is either dispatch's result byte or 8. 0xfe and 0xff branch away before 0x80003ec6, so dispatch's contract must give a result byte ≤ 8 on the path that reaches encode.
3. `Kept` must lie outside `EncW`. The real layout has the UART struct at 0x8002a1c0 and the flag word at sp+0x24, so it does.
