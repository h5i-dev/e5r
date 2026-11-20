# Toolchain and workflow

## Today: `nocompiler cc`

```
nocompiler cc -O2 f.c g.c -o f.elf         # compile, link, record .nocompiler.struct, check
nocompiler disasm f.elf                    # the code, nested by block and loop
nocompiler export f.elf --namespace My.Image -o lean/My/Image.lean
```

`nocompiler cc` runs clang on each source and ld.lld on the objects (entry
`_start`, static), with the profile's flags before the user's (`-O2` unless
an `-O` is given). If every function conforms it writes the binary with
`.nocompiler.struct`; otherwise it writes it without and lists the violations, and
exits 1. `CLANG` and `LLD` name the tools. The flags (`nocompiler::cc::CFLAGS`),
and what clang emits without each:

| Flag | Without it |
| --- | --- |
| `--target=riscv64-unknown-elf -march=rv64im_zba_zbb -mabi=lp64` | C, A, F or D instructions (R1) |
| `-mcmodel=medany` | data addresses as absolute `lui`/`addi` pairs (medlow): with medany every address in the code is pc-relative (`auipc` with `R_RISCV_PCREL_HI20`/`LO12`), so a function can be relinked at another address ([v1.md](v1.md), relocation) |
| `-mno-relax` | the linker rewrites calls after the code is checked |
| `-fno-pic`, static link | PLT and GOT: indirect calls (R2) |
| `-fno-jump-tables` | a dense `switch` becomes an indirect jump (R2) |
| `-mllvm -disable-block-placement` | loops rotated so that their header is in the middle, entered by a forward jump into the loop (R3) |
| `-ffreestanding -nostdlib` | libc, whose code would have to conform too |

`crates/nocompiler/tests/toolchain.rs` checks this on a corpus (`crates/nocompiler/tests/cc`):
nested loops with `break`, `continue` and a `goto` out of two loops,
do-while, dense and sparse `switch`, recursion and mutual recursion, struct
copies (lowered to calls to a `memcpy` the program supplies, which conforms
too) all conform; without `-disable-block-placement`, three of the five
loop functions break R3. What stays outside version 0 is what the source
asks for: calls through function pointers (R2).

`examples/build.sh` predates `nocompiler cc` and keeps its own flags (without
`-disable-block-placement`), because the committed examples are the bytes
the proofs are about; their code conforms either way. `nocompiler check --json`
gives the report as JSON.

## Proving a function

1. Build and annotate the binary; commit the ELF the proof is about (proofs
   are about exact bytes; `examples/elf/` holds the committed ones).
2. `nocompiler export` it into a Lean module. The module has the `.text` words, an
   `@[nocompiler_image]` lemma per address naming its instruction, and for every
   conforming function `<name>_entry` and `<name>_dom` (its code and its
   callees').
3. Write the specification and the proof, as in `lean/Examples/Sum.lean`
   ([spec.md](spec.md)). Loop invariants go at the loop heads `nocompiler disasm`
   shows.
4. Add the ELF and its image to `images` in `lean/Audit.lean`, and the
   theorems to its axiom checks.
5. `lake build && lake exe nocompiler-audit` in `lean/`.
6. Add mutations of the instructions the proof depends on to
   `scripts/core/check-proof-controls.sh`; each must make the proof fail.

## Next: inside LLVM

Doing the structure in the compiler means the tree is the compiler's own
(no recovery), loops keep the layout block placement prefers (which
`-disable-block-placement` gives up), and the profile can grow what flags
cannot give: jump tables and typed indirect calls. The plan, not started:
it needs an LLVM build, which the development machine cannot hold (an LLVM
build tree is tens of GB, against about 10 GB free), so it waits for a
machine that can.

- **A target feature on the RISC-V backend** (`+nocompiler`) rather than a new
  backend: the profile is a way of using RISC-V.
- **Structured control flow from the WebAssembly backend's passes:**
  `WebAssemblyFixIrreducibleControlFlow` (make the CFG reducible),
  `WebAssemblyCFGSort` (make loops contiguous) and `WebAssemblyCFGStackify`
  (compute the block/loop nesting), run after block placement and branch
  folding, with the tree emitted as `.nocompiler.struct` by the AsmPrinter.
- **Jump tables** as a fixed pseudo-instruction sequence (bounds check, then
  a table of offsets in `.rodata`) expanded late, so the checker can
  recognise the pattern. Version 0 rejects them.
- **Typed indirect calls** for function pointers, C++ virtual calls and Rust
  `dyn Trait` (which `core::fmt` uses): a call through a table of known
  entries with matching signatures. Version 0 rejects indirect calls.
- **Rust** through a custom target specification: `arch` riscv64, features
  `+m,+zba,+zbb,-c,+forced-atomics`, `panic-strategy` abort, static
  relocation, built with `-Z build-std`, starting from `no_std`.
  `+forced-atomics` lowers atomics to plain loads and stores, which is sound
  for one thread, the profile's model.
- **Proof hints:** loop and source information from the compiler (DWARF line
  tables, Rust's non-aliasing of `&mut`) written next to the tree, as input
  to whoever writes the invariants.

The compiler stays untrusted in all of this: what it writes is either
checked (`nocompiler check`) or used only as a hint.
