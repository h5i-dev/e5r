# RMK (RISC-V) feasibility reconnaissance

Review worker, 2026-10-29. Untrusted evidence for choosing a first RMK verification target;
nothing here is a proof, and nothing about RMK is claimed verified.

## Target

- Upstream `https://github.com/rmk-rs/rmk` at `71556128fa72881fc35f0bf6c292d5e28ad9568d`
  (commit date 2026-10-29 15:38 +0800), example `examples/use_rust/qemu-riscv-rynk`.
- Built with `recon.sh` (clean shallow checkout in `/dev/shm`, sources and `Cargo.lock` unchanged):
  `RUSTUP_TOOLCHAIN=1.98.1 cargo build --release --locked`, 55 s, `CARGO_BUILD_JOBS=2`.
  - Deviation from upstream: `run.py` builds the **dev** profile; this recon builds **release**
    (e5r policy). The repository's `rust-toolchain.toml` says `channel = "stable"`; the
    recon pins 1.98.1 (the e5r firmware toolchain) explicitly so no channel sync is triggered.
  - ELF `target/riscv32imac-unknown-none-elf/release/rmk-qemu-riscv`, 454 024 bytes,
    sha256 `f39d833f520ba4de6c7085423a8dc3ee475ec19bdfb55c10c81c6ae868f43c30`.
    Reproducibility across machines not yet checked (paths are embedded in panic locations).

## Platform the ELF expects (not the FE310)

- QEMU `virt` (run.py: `qemu-system-riscv32 -M virt -cpu rv32 -semihosting -bios none -kernel ELF`).
  QEMU 8.2.2 is available read-only in the main worker's tools root.
- Everything is in RAM: `memory.x` RAM = 0x80000000, 16 MiB; text/rodata/data/bss/stack all in RAM
  (no flash). Entry 0x80000000. `.text` 135 364 B, `.rodata` 32 544 B, `.data` 5 B, `.bss` 4 049 B,
  `.stack` NOBITS up to 16 MiB. Code lives in writable RAM: a store into `.text` is not a fault on
  this board, so "code is never overwritten" becomes a proof obligation (unlike FE310 flash).
- MMIO: UART 16550 at 0x1000_0000 (register stride 1), `uart_16550 0.8`, polled (no interrupts).
- Semihosting: 7 `ebreak` sites, all in the `semihosting` crate (stdout write/close for `println!`).
  QEMU `-semihosting` treats `slli x0,x0,0x1f; ebreak; srai x0,x0,7` as a host call; the e5r model
  treats `ebreak` as a breakpoint exception. A model of the semihosting call (or a proof the calls
  are only on startup paths outside the property) is needed.
- Interrupts: startup writes `mie = 0` and `mip = 0`; the only other CSR writes are `mtvec`, a
  critical section (`csrrci mstatus, 8` / `csrs mstatus`), `wfi` in the executor idle loop and
  `_mp_hook`, one `mret` in `_start_trap`. Time is `embassy-time` mock driver. So IRQs look never
  enabled (to be proved: no write sets `mie` bits), which would make the run deterministic modulo
  UART input.
- ISA attribute `rv32i2p1_m2p0_a2p1_c2p0_zmmul1p0_zaamo1p0_zalrsc1p0_zca1p0`. Instruction mix
  (45k instructions): RV32IMC plus `lr.w.aq`/`sc.w.rl` (3 each), AMOs (`amoswap/amoor/amoand`, 4),
  `fence` (9), `wfi` (2), `mret`, `csr*`, `ebreak` (7), `unimp` (8). Each has an `Instr`
  constructor in Theories/Hart.lean (lr, sc, amo, fence, csr, ebreak, mret, wfi); decoding of these
  exact encodings (fence pred/succ, aq/rl bits) is still to be checked with the decode sweep.

## Host input path (what parses untrusted bytes)

`main` loops `HostService::run_session(rx, tx)` (rmk/src/host/rynk/mod.rs:153):
UART bytes -> `Deframer` (rmk-types/src/protocol/rynk/deframer.rs: `tail`, `commit`, `next`,
`park_pending`, `unpark_pending`; COBS via `cobs::decode_in_place_report`) -> `RynkMessage::from_decoded`
-> `RynkService::dispatch` (postcard decode per command, handlers in rmk/src/host/rynk/handlers/).
`RYNK_BUFFER_SIZE` = 488 (generated constant). `LockConfig { insecure: true }` makes
`HostLock::is_unlocked()` always true, so in THIS example every command is authorized: an
"authorized mutation" property is vacuous here and should not be claimed.

## Panic sites on the input path (from `panic_sites.py`, release ELF)

Panic = `panic-halt` (`rust_begin_unwind` loops forever: the keyboard stops answering).
Call sites by callee, selected:

| callee | sites | in |
| --- | --- | --- |
| `slice_index_fail` | 25 | `Deframer::tail` 3, `next` 2, `park_pending` 2, `unpark_pending` 1, `RynkMessage::frame`/`payload` 1+1, `dispatch` 1, main task 4, macros/morse codecs ... |
| `panic_bounds_check` | 11 | `cobs::decode_in_place_report` 2, `KeyMapInner::get_action_at` 3, `set_action_at` 1, `set_default_layer` 1, `HostLock::poll/status` 2, ... |
| `panic_const_div_by_zero` / `rem_by_zero` | 2 / 2 | `RynkService::dispatch` closure (2+1), `uart_16550::calc_divisor` 1 |
| `unwrap_failed`/`expect_failed` | 18 | pubsub `get_message`, `TopicSubscribers::new` 5, `RynkMessage::from_decoded` 1, uart init/send |
| `panic_const_async_fn_resumed` | 70 | async state machines (unreachable unless polled after completion) |

`Deframer` methods are separate symbols of 26-114 instructions; `dispatch` is 3 606.

## Candidate properties (falsifiable, binary-level, selected from the code)

1. **Deframer memory safety (first target).** For the emitted `Deframer::{tail,next,park_pending,
   unpark_pending}` and `cobs::decode_in_place_report`, with the invariant
   `consumed <= filled <= 488` (+ `parked <= 488`) and `commit(n)` with `n <= 488 - filled`:
   every call returns, never reaches a panic call, only writes inside the 488-byte buffer, and
   preserves the invariant. Direct machine-code proofs (masked/no-IRQ, deterministic) on QEMU-virt
   RAM semantics; needs a `virt` board (RAM only for these functions). Negative controls:
   `n > 488 - filled` (or a corrupted `consumed > filled`) must reach `slice_index_fail`.
   The `n` bound depends on `Uart::read`: `uart_16550::receive_bytes` returns at most
   `buffer.len()` (map_while over the slice; source), to be proved on the binary as well.
2. **No division by zero in `dispatch` on host input**: identify the divisor (bulk paging?) and
   prove it non-zero from decoded request fields or show a host frame that reaches it (a real bug
   would be a finding for upstream).
3. **Keymap writes stay in the keymap**: `SetKeyAction`/`SetKeymapBulk` -> `check_key_position` ->
   `set_action_at` only writes inside the keymap array (3x3x2 here) for every decoded request.
4. Whole `run_session` panic-freedom for any byte stream: the end goal; needs the async executor,
   postcard decoders and the UART model. Not a first step.

## Not done / open

- QEMU run of the example (needs the rynk host client `qemu_behavior`; host build not attempted).
- No e5r image export of this ELF yet; no `virt` board model in e5r (main owns boards/integration).
- ELF reproducibility from a second checkout path.
