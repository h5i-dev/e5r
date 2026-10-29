# Deframer: machine-level contracts to prove (RMK ELF f39d833f)

Derived by reading the release disassembly of the pinned ELF (llvm-objdump 1.98.1). These are the
statements a direct proof should establish. They are NOT proved yet; a reading error here is possible,
which is exactly what the proof checks.

## ABI facts read from the code

- `Deframer` (rmk-types/src/protocol/rynk/deframer.rs) in memory: `consumed: u32 @ +0`,
  `filled: u32 @ +4`, `discarding: u8 @ +8` (`lbu s7, 0x8(a0)` / `sb .., 0x8(s3)` in `next`).
- Methods take `a0 = &mut Deframer`, `(a1, a2) = buf.as_mut_ptr(), buf.len()`; `unpark_pending` takes
  `a3 = parked`. `tail` returns the slice `(a0, a1) = (buf + filled', len - filled')`; `park_pending`
  returns `a0 = filled - consumed`; `next` returns `Option<usize>` in `(a0, a1)`.
- All use `memmove` (0x80020c1e, a tail jump to `compiler_builtins::mem::memmove`).
- Panic exits are calls to `core::slice::index::slice_index_fail` (0x8001fafc), which reaches
  `rust_begin_unwind` -> `panic-halt` (infinite loop: the keyboard stops responding).

## Contracts (state invariant `Inv`: consumed <= filled <= len, len = 488 in the firmware)

| function | pc range | panic branch taken iff (read from the code) | under `Inv`: effect |
| --- | --- | --- | --- |
| `tail` | 0x8001d576..0x8001d606 | `consumed != 0 && (filled > len \|\| consumed > filled)`, or `filled' > len` | if consumed > 0: buf[0..filled-consumed) := old buf[consumed..filled), consumed := 0, filled := filled-consumed; returns (buf+filled, len-filled); no panic |
| `park_pending` | 0x8001d388..0x8001d3f2 | `filled > len \|\| consumed > filled` | buf[len-k..len) := old buf[consumed..filled) with k = filled-consumed; consumed := filled := 0; returns k <= len; no panic |
| `unpark_pending` | 0x8001d3f2..0x8001d43a | `parked > len` | buf[0..parked) := old buf[len-parked..len); consumed := 0; filled := parked; no panic |
| `next` | 0x8001d43a..0x8001d576 | `filled > len \|\| consumed > filled` (entry checks at 0x8001d45c/60) and two inner range checks around the COBS decode (0x8001d4b2/b6) | to be derived: COBS `decode_in_place_report` (2 bounds checks) and the copy to the front |

Required alongside: `memmove(dst, src, n)` writes exactly `dst[0..n)` with the old `src[0..n)`, for
overlapping ranges, returns, and touches nothing else (a loop proof over the compiler_builtins code),
and `commit(n)` (inlined in `run_session`) keeps `Inv` when `n <= len - filled`, which holds when the
UART `read` returns at most the length of the `tail` slice it was given (uart_16550 `receive_bytes`
is `map_while` over the slice: source-level argument, to be proved on the inlined machine code).

Falsifiable negative controls for the proof: from a state with `filled = len + 1` (or `consumed > filled`)
each of `tail`/`park_pending`/`next` must reach `slice_index_fail`; `unpark_pending` with `parked = len+1`.

Platform obligations before any of this means something for QEMU: see README.md ALERT (fetch from
image vs writable RAM: these functions and memmove store only into `buf` and the Deframer, which must be
shown disjoint from `.text`) and the MROM entry state.
