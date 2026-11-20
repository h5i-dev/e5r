# rustc into the profile: conformance of the refinement targets

Item 7 of the refinement plan (`spec-v1-refine.md`, "Targets", step 0):
compile the candidate crates with rustc into the profile and count their
functions per level, before choosing tasks. This is the first benchmark
result. Measured 2026-11-20.

```bash
examples/refine/conformance.sh [--markdown] [--list]
EXTRA_RUSTFLAGS="-C llvm-args=-disable-block-placement" examples/refine/conformance.sh   # the other layout
```

`examples/refine/targets` is a `no_std` staticlib whose `#[no_mangle]`
entry points (`w_*`) call the public functions of each candidate, so that
their code is generated: cobs 0.5.1, memchr 2.8.3, httparse 1.10.1,
bytecount 0.6.9 (uutils `wc` counts lines with it), crc32fast 1.5.5 (`cksum`),
base64 0.23.1, and compiler-builtins' `mem` functions (through `copy`,
`write_bytes`, slice comparison). It is linked with ld.lld into one ELF,
checked with `nocompiler check --json`, and each function is attributed to
the crate whose object in the archive defines it (`conformance.py`).

## The flags

| | |
| --- | --- |
| toolchain | `nightly-2026-11-01` (rustc 1.101.0-nightly), `-Zbuild-std=core,compiler_builtins` with `compiler-builtins-mem` |
| target | `riscv64im-unknown-none-elf`, `-C target-feature=+m,+zba,+zbb` (no C, no A: R1). `riscv64imac` sets the RVC flag in its objects even with `-c`, which the loader refuses |
| relocation | `-C code-model=medium` (medany), `-C relocation-model=static` |
| control | `-C jump-tables=no` (R2); `-Z trap-unreachable=no` (no `unimp` after noreturn calls: `unimp` is not in the profile, R1) |
| panics | `panic = "abort"`; the panic handler exits with status 101 through `ecall`, so no panic reaches `core::fmt` |
| optimisation | `opt-level = 3`, `codegen-units = 1` (the fairness rule: the baseline is rustc's best conforming output) |

**Block placement.** `nocompiler cc` passes `-disable-block-placement` to
clang, because clang's placement rotates loops so they are entered in the
middle (R3). For rustc that trade goes the other way, and placement stays on
by default:

* with placement **on**, loops are rotated and entered past their head;
* with placement **off**, rustc's IR order puts a function's return block
  early, so a loop exit jumps back to it (not a loop head: R3), and some
  loops keep their latch before their header (`memcmp`).

Neither tail-merge (`-enable-tail-merge=false`), tail duplication
(`-tail-dup-size=8`) nor IR rotation limits (`-rotation-max-header-size=0`)
changed the counts.

## Results

Block placement on (the default configuration of `conformance.sh`):

| crate | functions | L2 | L1 | L0 | below L0 | rules behind the misses (functions) |
| --- | --- | --- | --- | --- | --- | --- |
| base64 | 23 | 10 | 0 | 13 | 0 | R2 control (8), R3 structure (5) |
| bytecount | 5 | 3 | 0 | 2 | 0 | R3 structure (2) |
| cobs | 20 | 9 | 0 | 11 | 0 | R3 structure (9), R2 control (2) |
| crc32fast | 5 | 3 | 0 | 2 | 0 | R3 structure (1), R2 control (1) |
| httparse | 21 | 16 | 0 | 5 | 0 | R3 structure (5) |
| memchr | 15 | 8 | 0 | 7 | 0 | R2 control (4), R3 structure (3) |
| (byteorder, hash32, heapless, thiserror: dependencies) | 11 | 8 | 0 | 3 | 0 | R2 control (3) |
| compiler_builtins | 558 | 359 | 2 | 174 | 23 | R3 structure (174), R1 decode (23), R6c sp access (2) |
| core | 550 | 240 | 10 | 300 | 0 | R2 control (229), R3 structure (71), R6e save (10), R4 registers (10) |

Block placement off: base64 11/23 at L2, bytecount 1/5, cobs 8/20, crc32fast
3/5, httparse 14/21, memchr 7/15; compiler_builtins 393/558, core 231/550.

compiler-builtins' `mem` functions (target 2): `memcpy`, `memmove`,
`memset`, `bcmp` (= `memcmp`) and `strlen` all reach **L2** with placement
on; with it off, `memset` and `bcmp` are L0 (R3). RISC-V uses the generic
implementations.

**The headline numbers flatter rustc.** Most of the L2 functions are small:
`fmt` shims, constructors, the `w_*` entry points. The functions a
refinement task would be about mostly miss:

| at L2 | at L0 |
| --- | --- |
| `cobs::decode_in_place`, `decode_in_place_with_sentinel`, `decode_with_sentinel`, `CobsDecoder::{feed, push}` | `cobs::encode`, `try_encode`, `decode`, `decode_in_place_report` (R3) |
| `httparse::Request::parse`, `parse_headers`, `parse_version`, `parse_code` | `parse_headers_iter_uninit`, `parse_reason`, `parse_chunk_size` (R3) |
| `bytecount::naive::{naive_count, naive_count_32, naive_num_chars}` | `bytecount::count`, `num_chars` (the SWAR paths, R3) |
| `crc32fast::baseline::update_4_to_15`, `Hasher::write` | `update_fast_16` (R2: ends in a noreturn call) |
| `memchr::memmem` one-byte searcher, `rabinkarp::is_equal_raw` | `memchr::memchr`'s callers (the `w_memchr*` loops, R3), the two-way searcher (R2 indirect, R3) |
| base64 alphabet/engine constructors | `GeneralPurpose::internal_encode`, `internal_decode` (R3) |

## The reasons, and what would change them

1. **R3, loops entered in the middle** (25 of the 43 misses in the candidate
   crates). Block placement rotates loops; without it, the IR's order
   leaves return blocks and latches in the way. Flags do not give
   head-first contiguous loops for rustc: that is the LLVM side of the
   roadmap (a structuring pass such as WebAssembly's CFGSort before
   emission).
2. **R2, a noreturn call at the end** (12): a panic path ends the function
   with a call that never returns, which R2 reads as falling through past
   the function (the same case `hello` in examples/hello.c avoids by hand).
   The checker could accept it when the callee provably never returns (it
   has no reachable `ret`); a profile change, not a flag.
3. **R2, indirect calls** (6): `core::fmt` (`dyn Write`) and memchr's
   searcher function pointers. Outside v1 by design.
4. **R1, `unimp`** (23 in compiler_builtins, all in functions that trap on
   purpose); gone from rustc's own code with `-Z trap-unreachable=no`.

## For choosing tasks

Refinement tasks need the baseline at L1 or above (the paired execution
works on the trees). With today's profile that leaves, among the real
targets: cobs' in-place decoders and its decoder state machine, httparse's
request/header/version/code parsers, bytecount's naive loops, crc32fast's
small-update path, and the five compiler-builtins `mem` functions. The SWAR
and table-driven loops a speed-up would most likely come from
(`bytecount::count`, crc32fast's `update_fast_16`, base64's engine,
memchr's search loops) are L0, by R3 or R2 above.
